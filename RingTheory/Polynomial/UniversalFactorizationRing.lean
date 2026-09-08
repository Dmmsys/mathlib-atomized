/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Submersive
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Polynomial.IsIntegral
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal


/-!

# Universal factorization ring

Let `R` be a commutative ring and `p : R[X]` be monic of degree `n` and let `n = m + k`.
We construct the universal ring of the following functors on `R-Alg`:
- `S ↦ "monic polynomials over S of degree n"`:
  Represented by `R[X₁,...,Xₙ]`. See `MvPolynomial.mapEquivMonic`.
- `S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`:
  Represented by an `R`-algebra (`Polynomial.UniversalFactorizationRing`) that is finitely-presented
  as an `R`-module. See `Polynomial.UniversalFactorizationRing.homEquiv`.
- `S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`:
  Represented by an etale `R`-algebra (`Polynomial.UniversalCoprimeFactorizationRing`).
  See `Polynomial.UniversalCoprimeFactorizationRing.homEquiv`.

-/

@[expose] public section

open scoped Polynomial TensorProduct

open RingHomClass (toRingHom)

variable (R S T : Type*) [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
variable (n m k : ℕ) (hn : n = m + k)

noncomputable section

namespace Polynomial

/-- The free monic polynomial of degree `n`, as a polynomial in `R[X₁,...,Xₙ][X]`. -/
/-
**Polynomial.freeMonic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：freeMonic : (MvPolynomial (Fin n) R)[X]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free monic polynomial of degree `n`, as a polynomial in `R[X₁,...,Xₙ][X]`.
-/
def freeMonic : (MvPolynomial (Fin n) R)[X] :=
  .X ^ n + ∑ i : Fin n, .C (.X i) * .X ^ (i : ℕ)
/-
**Polynomial.coeff_freeMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：coeff_freeMonic : (freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ el
se if k = n then 1 else 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
（共 34 条，此处仅展示前 30 条）
-/
lemma coeff_freeMonic :
    (freeMonic R n).coeff k = if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0 := by
  simp only [freeMonic, Polynomial.coeff_add, Polynomial.coeff_X_pow, Polynomial.finsetSum_coeff,
    Polynomial.coeff_C_mul, mul_ite, mul_one, mul_zero]
  by_cases h : k < n
  · simp +contextual [Finset.sum_eq_single (ι := Fin n) (a := ⟨k, h⟩),
      Fin.ext_iff, @eq_comm _ k, h, h.ne']
  · rw [Finset.sum_eq_zero fun x _ ↦ if_neg (by cases x; lia), add_zero, dif_neg h]
/-
**Polynomial.degree_freeMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_freeMonic [Nontrivial R] : (freeMonic R n).degree = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_eq_of_le_of_coeff_ne_zero`：degree_eq_of_le_of_coeff_ne
_zero (pn : p.degree <= n) (p1 : p.coeff n != 0) : p.degree = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.degree_le_iff_coeff_zero`：degree_le_iff_coeff_zero (f : R[X])
 (n : WithBot Nat) : degree f <= n ↔ forall m : Nat, n < m -> coeff f m = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.coeff_freeMonic`：coeff_freeMonic : (freeMonic R n).coeff k = 
if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma degree_freeMonic [Nontrivial R] : (freeMonic R n).degree = n :=
  Polynomial.degree_eq_of_le_of_coeff_ne_zero ((Polynomial.degree_le_iff_coeff_zero _ _).mpr
    (by simp +contextual [coeff_freeMonic, LT.lt.not_gt, LT.lt.ne']))
    (by simp [coeff_freeMonic])
/-
**Polynomial.natDegree_freeMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_freeMonic [Nontrivial R] : (freeMonic R n).natDegree = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用引理 `Polynomial.degree_freeMonic`：degree_freeMonic [Nontrivial R] : (freeMoni
c R n).degree = n
-/
lemma natDegree_freeMonic [Nontrivial R] : (freeMonic R n).natDegree = n :=
  natDegree_eq_of_degree_eq_some (degree_freeMonic R n)
/-
**Polynomial.monic_freeMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：monic_freeMonic : (freeMonic R n).Monic
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_freeMonic`：natDegree_freeMonic [Nontrivial R] : (fr
eeMonic R n).natDegree = n
· 使用引理 `Polynomial.coeff_freeMonic`：coeff_freeMonic : (freeMonic R n).coeff k = 
if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma monic_freeMonic : (freeMonic R n).Monic := by
  nontriviality R
  simp [Polynomial.Monic, ← Polynomial.coeff_natDegree, natDegree_freeMonic, coeff_freeMonic]

omit [Algebra R S] in
/-
**Polynomial.map_map_freeMonic** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：map_map_freeMonic (f : R ->+* S) : (freeMonic R n).map (MvPolynomial.map f
) = freeMonic S n
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_add`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p + q)
 = Polyn…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_pow`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p :
 Polynomial R} [inst_1 : Semiring S] (f : R →+* S) (n : ℕ),   Polynomial.map f (
p ^ n) =…
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_sum`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [ins
t_1 : Semiring S] (f : R →+* S) {ι : Type u_1}   (g : ι → Polynomial R) (s : Fin
set ι), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma map_map_freeMonic (f : R →+* S) :
    (freeMonic R n).map (MvPolynomial.map f) = freeMonic S n := by
  simp [freeMonic, Polynomial.map_sum]

open Polynomial (MonicDegreeEq)

/-- The free monic polynomial of degree `n`, as a `MonicDegreeEq` in `R[X₁,...,Xₙ][X]`. -/
@[simps]
/-
**Polynomial.MonicDegreeEq.freeMonic** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial.Monic
DegreeEq`。
形式化陈述：(R : Type u_1) → [inst : CommRing R] → (n : ℕ) → Polynomial.MonicDegreeEq 
(MvPolynomial (Fin n) R) n
参数：Fin n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The free monic polynomial of degree `n`, as a `MonicDegreeEq` in `R[X₁,...,Xₙ][X
]`.
-/
def MonicDegreeEq.freeMonic : MonicDegreeEq (MvPolynomial (Fin n) R) n :=
  ⟨.freeMonic R n, by simp +contextual [coeff_freeMonic, not_lt_of_gt, LT.lt.ne']⟩

end Polynomial

namespace MvPolynomial

open Polynomial

/-- `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
with the universal element being `freeMonic`. -/
/-
**MvPolynomial.mapEquivMonic** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquivMonic : (MvPolynomial (Fin n) R ->ₐ[R] S) ≃ MonicDegreeEq S n wher
e toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
with the universal element being `freeMonic`.
-/
def mapEquivMonic : (MvPolynomial (Fin n) R →ₐ[R] S) ≃ MonicDegreeEq S n where
  toFun f := .map (.freeMonic _ _) f.toRingHom
  invFun p := aeval (p.1.coeff ·)
  left_inv f := by ext i; simp [coeff_freeMonic]
  right_inv p := by
    suffices ∀ i ≥ n, (if i = n then 1 else 0) = p.1.coeff i by
      ext i; simp +contextual [coeff_freeMonic, apply_dite, this]
    intro i hi
    split_ifs with hi'
    · simp [hi', p.2.1]
    · simp [p.2.2 _ (hi.lt_of_ne' hi')]

variable {R S T} in
/-
**MvPolynomial.coe_mapEquivMonic_comp** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_mapEquivMonic_comp (f : MvPolynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R]
 T) : (mapEquivMonic R T n (g.comp f)).1 = (mapEquivMonic R S n f).1.map g
参数：f : MvPolynomial (Fin n) R ->ₐ[R] S；g : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
-/
lemma coe_mapEquivMonic_comp (f : MvPolynomial (Fin n) R →ₐ[R] S) (g : S →ₐ[R] T) :
    (mapEquivMonic R T n (g.comp f)).1 = (mapEquivMonic R S n f).1.map g :=
  (Polynomial.map_map ..).symm

variable {R S T} in
/-
**MvPolynomial.coe_mapEquivMonic_comp'** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：coe_mapEquivMonic_comp' (f : MvPolynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R
] T) : mapEquivMonic R T n (g.comp f) = (mapEquivMonic R S n f).map g
参数：f : MvPolynomial (Fin n) R ->ₐ[R] S；g : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `MvPolynomial.coe_mapEquivMonic_comp`：coe_mapEquivMonic_comp (f : MvPolyn
omial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T) : (mapEquivMonic R T n (g.comp f)).1 
= (mapEquivMonic R S n f)…
-/
lemma coe_mapEquivMonic_comp' (f : MvPolynomial (Fin n) R →ₐ[R] S) (g : S →ₐ[R] T) :
    mapEquivMonic R T n (g.comp f) = (mapEquivMonic R S n f).map g :=
  Subtype.ext (coe_mapEquivMonic_comp ..)

variable {R S T} in
/-
**MvPolynomial.mapEquivMonic_symm_map** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：mapEquivMonic_symm_map (p : MonicDegreeEq S n) (g : S ->ₐ[R] T) : (mapEqui
vMonic R T n).symm (p.map g) = g.comp ((mapEquivMonic R S n).symm p)
参数：p : MonicDegreeEq S n；g : S ->ₐ[R] T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用引理 `MvPolynomial.coe_mapEquivMonic_comp'`：coe_mapEquivMonic_comp' (f : MvPol
ynomial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T) : mapEquivMonic R T n (g.comp f) = 
(mapEquivMonic R S n f).ma…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mapEquivMonic_symm_map (p : MonicDegreeEq S n) (g : S →ₐ[R] T) :
    (mapEquivMonic R T n).symm (p.map g) = g.comp ((mapEquivMonic R S n).symm p) := by
  obtain ⟨f, rfl⟩ := (mapEquivMonic R S n).surjective p
  exact (mapEquivMonic R T n).symm_apply_eq.mpr (by simp [coe_mapEquivMonic_comp'])

variable {R S T} in
/-
**MvPolynomial.mapEquivMonic_symm_map_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `MvPo
lynomial`。
形式化陈述：mapEquivMonic_symm_map_algebraMap (p : MonicDegreeEq S n) [Algebra S T] [I
sScalarTower R S T] : (mapEquivMonic R T n).symm (p.map (algebraMap S T)) = (IsS
calarTower.toAlgHom R S T).comp ((mapEquivMonic R S n).symm p)
参数：p : MonicDegreeEq S n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MvPolynomial.mapEquivMonic_symm_map`：mapEquivMonic_symm_map (p : MonicDe
greeEq S n) (g : S ->ₐ[R] T) : (mapEquivMonic R T n).symm (p.map g) = g.comp ((m
apEquivMonic R S n).symm …
· 使用定理 `IsScalarTower.coe_toAlgHom`：coe_toAlgHom : ↑(toAlgHom R S A) = algebraMa
p S A
-/
lemma mapEquivMonic_symm_map_algebraMap
    (p : MonicDegreeEq S n) [Algebra S T] [IsScalarTower R S T] :
    (mapEquivMonic R T n).symm (p.map (algebraMap S T)) =
      (IsScalarTower.toAlgHom R S T).comp ((mapEquivMonic R S n).symm p) := by
  rw [← mapEquivMonic_symm_map, IsScalarTower.coe_toAlgHom]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- In light of the fact that `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`,
this is the map `R[X₁,...,Xₘ₊ₖ] → R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₖ]` corresponding to the multiplication
`MonicDegreeEq · m × MonicDegreeEq · k → MonicDegreeEq · (m + k)`. -/
/-
**MvPolynomial.universalFactorizationMap** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial
`。
形式化陈述：universalFactorizationMap (hn : n = m + k) : MvPolynomial (Fin n) R ->ₐ[R]
 MvPolynomial (Fin m) R otimes[R] MvPolynomial (Fin k) R
参数：hn : n = m + k。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
In light of the fact that `MonicDegreeEq · n` is representable by `R[X₁,...,Xₙ]`
,
this is the map `R[X₁,...,Xₘ₊ₖ] → R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₖ]` corresponding to 
the multiplication
`MonicDegreeEq · m × MonicDegreeEq · k → MonicDegreeEq · (m + k)`.
-/
def universalFactorizationMap (hn : n = m + k) :
    MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R :=
  (mapEquivMonic R _ n).symm
  ⟨(mapEquivMonic R _ m Algebra.TensorProduct.includeLeft).1 *
    (mapEquivMonic R _ k Algebra.TensorProduct.includeRight).1, by
    nontriviality R
    nontriviality MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R
    refine (MonicDegreeEq.mk _ ?_ ?_).2
    · exact ((monic_freeMonic R m).map _).mul ((monic_freeMonic R _).map _)
    dsimp [mapEquivMonic]
    rw [((monic_freeMonic R m).map _).natDegree_mul ((monic_freeMonic R k).map _)]
    simp_rw [(monic_freeMonic R _).natDegree_map, natDegree_freeMonic, hn]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.universalFactorizationMap_freeMonic** 是 Mathlib 中的一个引理，位于命名空间 `Mv
Polynomial`。
形式化陈述：universalFactorizationMap_freeMonic : (freeMonic R n).map (toRingHom <| un
iversalFactorizationMap R n m k hn) = (freeMonic R m).map (algebraMap _ _) * (fr
eeMonic R k).map (toRingHom <| Algebra.TensorProduct.includeRight)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
lemma universalFactorizationMap_freeMonic :
    (freeMonic R n).map (toRingHom <| universalFactorizationMap R n m k hn) =
      (freeMonic R m).map (algebraMap _ _) *
        (freeMonic R k).map (toRingHom <| Algebra.TensorProduct.includeRight) := by
  change (mapEquivMonic _ _ _ (universalFactorizationMap R n m k hn)).1 = _
  simp [universalFactorizationMap]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**MvPolynomial.universalFactorizationMap_comp_map** 是 Mathlib 中的一个引理，位于命名空间 `MvP
olynomial`。
形式化陈述：universalFactorizationMap_comp_map : (universalFactorizationMap S n m k hn
).toRingHom.comp (map (algebraMap R S)) = .comp (Algebra.TensorProduct.lift (S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ringHom_ext'`：ringHom_ext' {A : Type*} [Semiring A] {f g : 
MvPolynomial σ R ->+* A} (hC : f.comp C = g.comp C) (hX : forall i, f (X i) = g 
(X i)) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
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
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.map_map_freeMonic`：map_map_freeMonic (f : R ->+* S) : (freeMo
nic R n).map (MvPolynomial.map f) = freeMonic S n
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `MvPolynomial.aeval_X`：aeval_X (s : σ) : aeval f (X s : MvPolynomial σ R)
 = f s
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…
（共 33 条，此处仅展示前 30 条）
-/
lemma universalFactorizationMap_comp_map :
    (universalFactorizationMap S n m k hn).toRingHom.comp (map (algebraMap R S)) =
    .comp (Algebra.TensorProduct.lift (S := R)
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId R S)))
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp (mapAlgHom (Algebra.ofId R S)))
      fun _ _ ↦ .all _ _).toRingHom
      (universalFactorizationMap R n m k hn).toRingHom := by
  ext
  · simp
  · dsimp [universalFactorizationMap, mapEquivMonic]
    simp only [map_X, aeval_X, ← AlgHom.coe_toRingHom, ← Polynomial.coeff_map, Polynomial.map_mul,
      Polynomial.map_map, ← map_map_freeMonic (f := algebraMap R S)]
    congr 2 <;> ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-- Lifts along `universalFactorizationMap` corresponds to factorization of `p` into
monic polynomials with fixed degrees. -/
/-
**MvPolynomial.universalFactorizationMapLiftEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvP
olynomial`。
形式化陈述：universalFactorizationMapLiftEquiv (p : MonicDegreeEq S n) : { f // AlgHom
.comp f (universalFactorizationMap R n m k hn) = (mapEquivMonic _ _ n).symm p } 
≃ { q : MonicDegreeEq S m × MonicDegreeEq S k // q.1.1 * q.2.1 = p } where toFun
 f
参数：p : MonicDegreeEq S n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Lifts along `universalFactorizationMap` corresponds to factorization of `p` into
monic polynomials with fixed degrees.
-/
def universalFactorizationMapLiftEquiv (p : MonicDegreeEq S n) :
    { f // AlgHom.comp f (universalFactorizationMap R n m k hn) =
        (mapEquivMonic _ _ n).symm p } ≃
    { q : MonicDegreeEq S m × MonicDegreeEq S k // q.1.1 * q.2.1 = p } where
  toFun f := ⟨(mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeLeft),
    mapEquivMonic R _ _ (f.1.comp Algebra.TensorProduct.includeRight)), by
      conv_rhs => rw [← (Equiv.eq_symm_apply _).mp f.2]
      simp [MvPolynomial.coe_mapEquivMonic_comp, MvPolynomial.universalFactorizationMap]⟩
  invFun q := ⟨Algebra.TensorProduct.lift ((mapEquivMonic _ _ _).symm q.1.1)
    ((mapEquivMonic _ _ _).symm q.1.2) fun _ _ ↦ .all _ _, by
    refine (mapEquivMonic R S n).eq_symm_apply.mpr <| Subtype.ext ?_
    simp only [universalFactorizationMap, coe_mapEquivMonic_comp, Equiv.apply_symm_apply,
      Polynomial.map_mul]
    simp [← coe_mapEquivMonic_comp, ← q.2]⟩
  left_inv f := by ext <;> simp
  right_inv q := by ext <;> simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.ker_eval** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ker_eval₂Hom_universalFactorizationMap :
    RingHom.ker (eval₂Hom (S₁ := MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)
      (universalFactorizationMap R n m k hn) (Sum.elim (.X · ⊗ₜ 1) (1 ⊗ₜ .X ·))) =
    Ideal.span (Set.range fun i ↦ C (X i) - map C (tensorEquivSum _ _ _ _
      (universalFactorizationMap R n m k hn (X i)))) := by
  set f := eval₂Hom (R := MvPolynomial (Fin n) R)
    (S₁ := MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)
    (universalFactorizationMap R n m k hn) (Sum.elim (.X · ⊗ₜ 1) (1 ⊗ₜ .X ·))
  have H (i : _) : tensorEquivSum _ _ _ _ (f (.X i)) = .X i := by aesop
  apply le_antisymm
  · intro x hx
    convert_to x - (tensorEquivSum _ _ _ _ (f x)).map C ∈ Ideal.span _ using 1
    · simp_all only [RingHom.mem_ker, map_zero, sub_zero]
    clear hx
    induction x using MvPolynomial.induction_on with
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i _ => simp only [map_mul, H, map_X, ← sub_mul]; exact Ideal.mul_mem_right _ _ ‹_›
    | C x =>
    induction x using MvPolynomial.induction_on with
    | C a => simp [f]
    | add p q _ _ => simp only [map_add, add_sub_add_comm]; exact add_mem ‹_› ‹_›
    | mul_X p i IH =>
      simp only [map_mul]
      exact Ideal.mul_sub_mul_mem _ IH (Ideal.subset_span ⟨i, by simp [f]⟩)
  · simp only [Ideal.span_le, Set.range_subset_iff, SetLike.mem_coe, RingHom.mem_ker, map_sub,
      eval₂Hom_C, RingHom.coe_coe, eval₂Hom_map_hom, coe_eval₂Hom, sub_eq_zero, f]
    simp only [← algebraMap_eq, AlgHom.comp_algebraMap_of_tower, ← aeval_def]
    intro i
    generalize universalFactorizationMap R n m k hn (X i) = p
    change AlgHom.id R _ p = ((aeval _).comp (tensorEquivSum R _ _ R).toAlgHom) p
    congr 1
    ext <;> simp

set_option backward.isDefEq.respectTransparency false in
/-- The canonical presentation of `universalFactorizationMap`. -/
/-
**MvPolynomial.universalFactorizationMapPresentation** 是 Mathlib 中的一个定义，位于命名空间 `
MvPolynomial`。
形式化陈述：(R : Type u_1) →   [inst : CommRing R] →     (n m k : ℕ) →       (hn : n =
 m + k) →         Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R)    
       (TensorProduct R (MvPolynomial (Fin m) R) (MvPolynomial (Fin k) R)) (Fin 
m ⊕ Fin k) (Fin n)
参数：Fin n；MvPolynomial (Fin m) R；MvPolynomial (Fin k) R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical presentation of `universalFactorizationMap`.
-/
@[simps] def universalFactorizationMapPresentation :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    Algebra.PreSubmersivePresentation (MvPolynomial (Fin n) R)
      (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) (Fin m ⊕ Fin k) (Fin n) :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  { val := Sum.elim (.X · ⊗ₜ 1) (1 ⊗ₜ .X ·)
    σ' f := (tensorEquivSum _ _ _ _ f).map C
    aeval_val_σ' s := by
      change ((aeval _).restrictScalars R |>.comp (mapAlgHom (Algebra.ofId _ _)) |>.comp
          (tensorEquivSum R (Fin m) (Fin k) R).toAlgHom) s = AlgHom.id R _ s
      congr 1
      ext <;> simp
    algebra := (aeval _).toAlgebra
    algebraMap_eq := rfl
    relation i := .C (.X i) - (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (.X i))).map C
    span_range_relation_eq_ker := by
      exact (ker_eval₂Hom_universalFactorizationMap R n m k hn).symm,
    map := finSumFinEquiv.symm ∘ finCongr hn
    map_inj := finSumFinEquiv.symm.injective.comp (finCongr hn).injective }

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.pderiv_inl_universalFactorizationMap_X** 是 Mathlib 中的一个引理，位于命名空间 
`MvPolynomial`。
形式化陈述：pderiv_inl_universalFactorizationMap_X (i j) : pderiv (Sum.inl i) (tensorE
quivSum R (Fin m) (Fin k) R (universalFactorizationMap R n m k hn (X j))) = if ↑
j < (i : Nat) then 0 else if h : ↑j - ↑i < k then X (.inr ⟨↑j - ↑i, h⟩) else if 
↑j - ↑i = k then 1 else 0
参数：i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.MonicDegreeEq.map_coe`：∀ {R : Type u} {S : Type v} {n : ℕ} [i
nst : Semiring R] [inst_1 : Semiring S] (p : Polynomial.MonicDegreeEq R n)   (f 
: R →+* S), ↑(p.map f)…
· 使用定理 `Polynomial.MonicDegreeEq.freeMonic_coe`：∀ (R : Type u_1) [inst : CommRin
g R] (n : ℕ), ↑(Polynomial.MonicDegreeEq.freeMonic R n) = Polynomial.freeMonic R
 n
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用引理 `Polynomial.coeff_freeMonic`：coeff_freeMonic : (freeMonic R n).coeff k = 
if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用引理 `dite_mul`：dite_mul (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a
 h else b h) * c = if h : P then a h * c else b h * c
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 82 条，此处仅展示前 30 条）
-/
lemma pderiv_inl_universalFactorizationMap_X (i j) :
    pderiv (Sum.inl i) (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (X j))) =
    if ↑j < (i : ℕ) then 0 else if h : ↑j - ↑i < k then X (.inr ⟨↑j - ↑i, h⟩)
      else if ↑j - ↑i = k then 1 else 0 := by
  trans ∑ x ∈ Finset.antidiagonal ↑j,
    if h : x.2 < k then if x.1 < m ∧ x.1 = ↑i then X (Sum.inr ⟨x.2, h⟩) else 0
    else if x.2 = k ∧ x.1 < m ∧ x.1 = ↑i then 1 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal, Prod.forall]
      intro a b hab
      simp [show a ≠ i by lia]
    rw [Finset.sum_eq_single ⟨i.1, j.1 - i.1⟩, if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, Prod.forall, Prod.mk.injEq, not_and]
      intro a b e h
      simp [show a ≠ i by lia]
    · simp [h]

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPolynomial.pderiv_inr_universalFactorizationMap_X** 是 Mathlib 中的一个引理，位于命名空间 
`MvPolynomial`。
形式化陈述：pderiv_inr_universalFactorizationMap_X (i j) : pderiv (Sum.inr i) (tensorE
quivSum R (Fin m) (Fin k) R (universalFactorizationMap R n m k hn (X j))) = if ↑
j < (i : Nat) then 0 else if h : ↑j - ↑i < m then X (.inl ⟨↑j - ↑i, h⟩) else if 
↑j - ↑i = m then 1 else 0
参数：i j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.MonicDegreeEq.map_coe`：∀ {R : Type u} {S : Type v} {n : ℕ} [i
nst : Semiring R] [inst_1 : Semiring S] (p : Polynomial.MonicDegreeEq R n)   (f 
: R →+* S), ↑(p.map f)…
· 使用定理 `Polynomial.MonicDegreeEq.freeMonic_coe`：∀ (R : Type u_1) [inst : CommRin
g R] (n : ℕ), ↑(Polynomial.MonicDegreeEq.freeMonic R n) = Polynomial.freeMonic R
 n
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用引理 `Polynomial.coeff_freeMonic`：coeff_freeMonic : (freeMonic R n).coeff k = 
if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用引理 `dite_mul`：dite_mul (a : P -> α) (b : ¬P -> α) (c : α) : (if h : P then a
 h else b h) * c = if h : P then a h * c else b h * c
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
（共 78 条，此处仅展示前 30 条）
-/
lemma pderiv_inr_universalFactorizationMap_X (i j) :
    pderiv (Sum.inr i) (tensorEquivSum R (Fin m) (Fin k) R
      (universalFactorizationMap R n m k hn (X j))) =
    if ↑j < (i : ℕ) then 0 else if h : ↑j - ↑i < m then
      X (.inl ⟨↑j - ↑i, h⟩) else if ↑j - ↑i = m then 1 else 0 := by
  trans ∑ x ∈ Finset.antidiagonal ↑j, if x.2 < k then if h : x.1 < m then if x.2 = ↑i then
    X (Sum.inl ⟨x.1, h⟩) else 0 else if x.1 = m ∧ x.2 = ↑i then 1 else 0 else 0
  · simp [universalFactorizationMap, mapEquivMonic, Polynomial.coeff_mul, coeff_freeMonic,
      apply_dite, apply_ite, ← Algebra.TensorProduct.one_def,
      Pi.single_apply, Fin.ext_iff, ← ite_and]
  · obtain h | h := lt_or_ge j.1 i.1
    · rw [Finset.sum_eq_zero, if_pos h]
      simp only [Finset.mem_antidiagonal]
      lia
    rw [Finset.sum_eq_single ⟨j.1 - i.1, i.1⟩, if_neg h.not_gt]
    · simp
    · simp only [Finset.mem_antidiagonal, ne_eq, ite_eq_right_iff, Prod.forall, Prod.mk.injEq]
      intro a b _ _ _
      simp [show b ≠ i by lia]
    · simp [h]
/-
**MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix** 是 Mathlib 中的
一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：universalFactorizationMapPresentation_jacobiMatrix : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobiMatrix_apply`：jacobiMatrix_apply
 (i j : σ) : P.jacobiMatrix i j = MvPolynomial.pderiv (P.map i) (P.relation j)
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.universalFactorizationMapPresentation_map`：∀ (R : Type u_1)
 [inst : CommRing R] (n m k : ℕ) (hn : n = m + k) (a : Fin n),   (MvPolynomial.u
niversalFactorizationMapPresentation R n m k…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `finCongr_refl`：∀ {n : ℕ} (h : optParam (n = n) ⋯), finCongr h = Equiv.re
fl (Fin n)
· 使用定理 `finSumFinEquiv_symm_apply_castAdd`：finSumFinEquiv_symm_apply_castAdd (x 
: Fin m) : finSumFinEquiv.symm (Fin.castAdd n x) = Sum.inl x
· 使用定理 `MvPolynomial.universalFactorizationMapPresentation_relation`：∀ (R : Type
 u_1) [inst : CommRing R] (n m k : ℕ) (hn : n = m + k) (i : Fin n),   (MvPolynom
ial.universalFactorizationMapPresentation R n m k…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `MvPolynomial.derivation_C`：derivation_C (D : Derivation R (MvPolynomial 
σ R) A) (a : R) : D (C a) = 0
· 使用定理 `MvPolynomial.pderiv_map`：pderiv_map {S} [CommSemiring S] {φ : R ->+* S} 
{f : MvPolynomial σ R} {i : σ} : pderiv i (map φ f) = map φ (pderiv i f)
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `MvPolynomial.pderiv_inl_universalFactorizationMap_X`：pderiv_inl_universa
lFactorizationMap_X (i j) : pderiv (Sum.inl i) (tensorEquivSum R (Fin m) (Fin k)
 R (universalFactorizationMap R n m k hn …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
（共 45 条，此处仅展示前 30 条）
-/
lemma universalFactorizationMapPresentation_jacobiMatrix :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobiMatrix =
    -((Polynomial.sylvester
      ((freeMonic R m).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inl)).toRingHom))
      ((freeMonic R k).map (((mapAlgHom (Algebra.ofId _ _)).comp (rename Sum.inr)).toRingHom))
      m k).reindex (finCongr (by lia)) (finCongr (by lia))).transpose := by
  let := (universalFactorizationMap R n m k hn).toAlgebra
  subst hn
  ext i j : 1
  dsimp [Polynomial.sylvester]
  rw [Algebra.PreSubmersivePresentation.jacobiMatrix_apply]
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;>
    induction j using Fin.addCases <;>
      simp [pderiv_map, coeff_freeMonic, apply_dite (DFunLike.coe _), apply_ite (DFunLike.coe _),
        pderiv_inl_universalFactorizationMap_X, pderiv_inr_universalFactorizationMap_X] <;> grind
/-
**MvPolynomial.universalFactorizationMapPresentation_jacobian** 是 Mathlib 中的一个引理
，位于命名空间 `MvPolynomial`。
形式化陈述：universalFactorizationMapPresentation_jacobian : letI
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det`：jacobian
_eq_jacobiMatrix_det : P.jacobian = algebraMap P.Ring S P.jacobiMatrix.det
· 使用引理 `MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix`：univers
alFactorizationMapPresentation_jacobiMatrix : letI
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Matrix.det_neg`：det_neg (A : Matrix n n R) : det (-A) = (-1) ^ Fintype.c
ard n * det A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `Matrix.det_reindex_self`：det_reindex_self (e : m ≃ n) (A : Matrix m m R)
 : det (reindex e e A) = det A
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用引理 `Algebra.Generators.algebraMap_apply`：algebraMap_apply (x) : algebraMap P
.Ring S x = aeval (R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
（共 53 条，此处仅展示前 30 条）
-/
lemma universalFactorizationMapPresentation_jacobian :
    letI := (universalFactorizationMap R n m k hn).toAlgebra
    (universalFactorizationMapPresentation R n m k hn).jacobian =
    (-1) ^ n * (Polynomial.resultant
      ((freeMonic R m).map Algebra.TensorProduct.includeLeftRingHom)
      ((freeMonic R k).map Algebra.TensorProduct.includeRight.toRingHom)) := by
  cases subsingleton_or_nontrivial R
  · exact Subsingleton.elim _ _
  let := (universalFactorizationMap R n m k hn).toAlgebra
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
    MvPolynomial.universalFactorizationMapPresentation_jacobiMatrix]
  simp only [AlgHom.toRingHom_eq_coe, Matrix.det_neg, Matrix.det_transpose, Matrix.det_reindex_self,
    Algebra.Generators.algebraMap_apply, ← Polynomial.resultant.eq_def,
    Fintype.card_fin, map_mul, map_pow, map_neg, map_one]
  congr 1
  rw [← (aeval _).coe_toRingHom, ← Polynomial.resultant_map_map,
    Polynomial.map_map, Polynomial.map_map]
  congr 2
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · ext <;> simp [-algebraMap_apply, -AddMonoidAlgebra.coe_algebraMap, ← algebraMap_eq]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]
  · rw [(monic_freeMonic ..).natDegree_map, natDegree_freeMonic]
/-
**MvPolynomial.finitePresentation_universalFactorizationMap** 是 Mathlib 中的一个引理，位
于命名空间 `MvPolynomial`。
形式化陈述：finitePresentation_universalFactorizationMap : (universalFactorizationMap 
R n m k hn).FinitePresentation
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.Presentation.finitePresentation_of_isFinite`：finitePresentation_
of_isFinite [Finite σ] [Finite ι] (P : Presentation R S ι σ) : FinitePresentatio
n R S
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
-/
lemma finitePresentation_universalFactorizationMap :
    (universalFactorizationMap R n m k hn).FinitePresentation :=
  letI := (universalFactorizationMap R n m k hn).toAlgebra
  (universalFactorizationMapPresentation R n m k hn).finitePresentation_of_isFinite

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.finite_universalFactorizationMap** 是 Mathlib 中的一个引理，位于命名空间 `MvPol
ynomial`。
形式化陈述：finite_universalFactorizationMap : (universalFactorizationMap R n m k hn).
Finite
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.IsIntegral.to_finite`：RingHom.IsIntegral.to_finite (h : f.IsInte
gral) (h' : f.FiniteType) : f.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MulEquiv.isDomain_iff`：isDomain_iff {A B : Type*} [Semiring A] [Semiring
 B] (e : A ≃* B) : IsDomain A ↔ IsDomain B where mp _
· 使用定理 `AddMonoidAlgebra.smulCommClass`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `MvPolynomial.instIsDomainOfIsCancelAdd`：∀ {R : Type u} {σ : Type u_1} [i
nst : CommSemiring R] [IsCancelAdd R] [IsDomain R], IsDomain (MvPolynomial σ R)
· 使用定理 `IsOrderedCancelAddMonoid.toIsCancelAdd`：∀ {α : Type u_1} [inst : AddComm
Monoid α] [inst_1 : PartialOrder α] [IsOrderedCancelAddMonoid α], IsCancelAdd α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Polynomial.coeff_freeMonic`：coeff_freeMonic : (freeMonic R n).coeff k = 
if h : k < n then .X ⟨k, h⟩ else if k = n then 1 else 0
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Polynomial.isIntegral_coeff_of_dvd`：isIntegral_coeff_of_dvd (p : R[X]) (
q : S[X]) (hp : p.Monic) (hq : q.Monic) (H : q ∣ p.map (algebraMap R S)) (i : Na
t) : IsIntegral R (q.coe…
· 使用引理 `Polynomial.monic_freeMonic`：monic_freeMonic : (freeMonic R n).Monic
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `MvPolynomial.universalFactorizationMap_freeMonic`：universalFactorization
Map_freeMonic : (freeMonic R n).map (toRingHom <| universalFactorizationMap R n 
m k hn) = (freeMonic R m).map (algebra…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.map_X`：map_X (n : σ) : map f (X n : MvPolynomial σ R) = X n
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
（共 59 条，此处仅展示前 30 条）
-/
lemma finite_universalFactorizationMap :
    (universalFactorizationMap R n m k hn).Finite := by
  refine RingHom.IsIntegral.to_finite ?_
    (.of_finitePresentation (finitePresentation_universalFactorizationMap R n m k hn))
  let := (universalFactorizationMap R n m k hn).toAlgebra
  have : IsDomain (MvPolynomial (Fin m) ℤ ⊗[ℤ] MvPolynomial (Fin k) ℤ) :=
    (MvPolynomial.tensorEquivSum ℤ (Fin m) (Fin k) ℤ).toRingEquiv.isDomain_iff.mpr inferInstance
  let := (universalFactorizationMap ℤ n m k hn).toAlgebra
  let F : MvPolynomial (Fin m) ℤ ⊗[ℤ] MvPolynomial (Fin k) ℤ →ₐ[ℤ]
      MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R :=
    Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft.comp (mapAlgHom (Algebra.ofId ℤ R)))
      ((Algebra.TensorProduct.includeRight.restrictScalars ℤ).comp (mapAlgHom (Algebra.ofId ℤ R)))
      fun _ _ ↦ .all _ _
  have H₁ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (.X i ⊗ₜ 1) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap ℤ n m k hn).IsIntegralElem (.X i ⊗ₜ 1) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _) ⟨_, universalFactorizationMap_freeMonic ℤ n m k hn⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap ℤ R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂, ← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  have H₂ (i : _) : (universalFactorizationMap R n m k hn).IsIntegralElem (1 ⊗ₜ .X i) := by
    obtain ⟨p, hp, hp'⟩ : (universalFactorizationMap ℤ n m k hn).IsIntegralElem (1 ⊗ₜ .X i) := by
      simpa [coeff_freeMonic] using! Polynomial.isIntegral_coeff_of_dvd _ _ (monic_freeMonic _ _)
        ((monic_freeMonic _ _).map _)
        ⟨_, (universalFactorizationMap_freeMonic ℤ n m k hn).trans (mul_comm _ _)⟩ i
    refine ⟨p.map (MvPolynomial.map (algebraMap ℤ R)), hp.map _, ?_⟩
    apply_fun F.toRingHom at hp'
    rw [Polynomial.hom_eval₂, ← MvPolynomial.universalFactorizationMap_comp_map] at hp'
    simpa [← Polynomial.eval₂_map, F] using! hp'
  intro x
  induction x with
  | zero => exact RingHom.isIntegralElem_zero _
  | add x y _ _ => exact RingHom.IsIntegralElem.add _ ‹_› ‹_›
  | tmul x y =>
    suffices (universalFactorizationMap R n m k hn).IsIntegralElem (x ⊗ₜ 1 * 1 ⊗ₜ y) by simpa
    refine RingHom.IsIntegralElem.mul _ ?_ ?_
    · induction x using MvPolynomial.induction_on with
      | C a => simpa using! (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.add_tmul, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₁ i)
    · induction y using MvPolynomial.induction_on with
      | C a => simpa [← algebraMap_eq, ← algebraMap_apply, Algebra.algebraMap_eq_smul_one] using!
          (universalFactorizationMap R n m k hn).isIntegralElem_map (x := .C a)
      | add p q _ _ => simp only [TensorProduct.tmul_add, RingHom.IsIntegralElem.add, *]
      | mul_X p i IH => simpa [← map_mul] using! IH.mul _ (H₂ i)

end MvPolynomial

namespace Polynomial

open TensorProduct

variable {R n} (p : Polynomial.MonicDegreeEq R n)

attribute [-instance] leftModule in
/-- The universal factorization ring of a monic polynomial `p` of degree `n`.
This is the representing object of the functor
`S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`.
See `UniversalFactorizationRing.homEquiv`. -/
/-
**Polynomial.UniversalFactorizationRing** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：UniversalFactorizationRing : Type _
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The universal factorization ring of a monic polynomial `p` of degree `n`.
This is the representing object of the functor
`S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`.
See `UniversalFactorizationRing.homEquiv`.
-/
def UniversalFactorizationRing : Type _ :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  R ⊗[MvPolynomial (Fin n) R] (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R)
  deriving CommRing, Algebra R

local notation "𝓡" => UniversalFactorizationRing m k hn p

set_option backward.isDefEq.respectTransparency false in
/-- The canonical map `R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₙ] → UniversalFactorizationRing`. -/
/-
**Polynomial.UniversalFactorizationRing.fromTensor** 是 Mathlib 中的一个定义，位于命名空间 `Po
lynomial.UniversalFactorizationRing`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {n : ℕ} →       (m k : ℕ) →  
       (hn : n = m + k) →           (p : Polynomial.MonicDegreeEq R n) →        
     TensorProduct R (MvPolynomial (Fin m) R) (MvPolynomial (Fin k) R) →ₐ[R]    
           Polynomial.UniversalFactorizationRing m k hn p
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；MvPolynomial (Fin m) 
R；MvPolynomial (Fin k) R。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The canonical map `R[X₁,...,Xₘ] ⊗ R[X₁,...,Xₙ] → UniversalFactorizationRing`.
-/
def UniversalFactorizationRing.fromTensor :
    (MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) →ₐ[R] 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  Algebra.TensorProduct.includeRight.restrictScalars _

/-- The image of `p` in the universal factorization ring of `p`. -/
/-
**Polynomial.UniversalFactorizationRing.monicDegreeEq** 是 Mathlib 中的一个定义，位于命名空间 
`Polynomial.UniversalFactorizationRing`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {n : ℕ} →       (m k : ℕ) →  
       (hn : n = m + k) →           (p : Polynomial.MonicDegreeEq R n) →        
     Polynomial.MonicDegreeEq (Polynomial.UniversalFactorizationRing m k hn p) n
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomial.UniversalF
actorizationRing m k hn p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `p` in the universal factorization ring of `p`.
-/
@[simps] def UniversalFactorizationRing.monicDegreeEq :
    MonicDegreeEq 𝓡 n :=
  ⟨p.1.map (algebraMap _ _), by simp +contextual only [Polynomial.coeff_map, p.2,
    map_one, map_zero, gt_iff_lt, implies_true, and_self]⟩
/-
**Polynomial.UniversalFactorizationRing.fromTensor_comp_universalFactorizationMa
p** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.UniversalFactorizationRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} (m k : ℕ) (hn : n = m + k) (p
 : Polynomial.MonicDegreeEq R n),   (Polynomial.UniversalFactorizationRing.fromT
ensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =     (
Algebra.ofId R (Polynomial.UniversalFactorizationRing m k hn p)).comp ((MvPolyno
mial.mapEquivMonic R R n).symm p)
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomial.UniversalF
actorizationRing.fromTensor m k hn p；MvPolynomial.universalFactorizationMap R n 
m k hn；Algebra.ofId R (Polynomial.UniversalFactorizationRing m k hn p)；(MvPolyno
mial.mapEquivMonic R R n).symm p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.TensorProduct.tmul_one_eq_one_tmul`：tmul_one_eq_one_tmul (r : R)
 : algebraMap R A r otimesₜ[R] 1 = 1 otimesₜ algebraMap R B r
-/
lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap :
  (fromTensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =
    (Algebra.ofId R _).comp ((MvPolynomial.mapEquivMonic R _ n).symm p) := by
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  exact AlgHom.ext fun x ↦ (Algebra.TensorProduct.tmul_one_eq_one_tmul x).symm
/-
**Polynomial.UniversalFactorizationRing.fromTensor_comp_universalFactorizationMa
p'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.UniversalFactorizationRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} (m k : ℕ) (hn : n = m + k) (p
 : Polynomial.MonicDegreeEq R n),   (Polynomial.UniversalFactorizationRing.fromT
ensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =     (
MvPolynomial.mapEquivMonic R (Polynomial.UniversalFactorizationRing m k hn p) n)
.symm       (Polynomial.UniversalFactorizationRing.monicDegreeEq m k hn p)
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomial.UniversalF
actorizationRing.fromTensor m k hn p；MvPolynomial.universalFactorizationMap R n 
m k hn；MvPolynomial.mapEquivMonic R (Polynomial.UniversalFactorizationRing m k h
n p) n；Polynomial.UniversalFactorizationRing.monicDegreeEq m k hn p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.UniversalFactorizationRing.fromTensor_comp_universalFactoriza
tionMap`：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} (m k : ℕ) (hn : n = m + k)
 (p : Polynomial.MonicDegreeEq R n),   (Polynomial.UniversalFactoriza…
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `MvPolynomial.coe_mapEquivMonic_comp`：coe_mapEquivMonic_comp (f : MvPolyn
omial (Fin n) R ->ₐ[R] S) (g : S ->ₐ[R] T) : (mapEquivMonic R T n (g.comp f)).1 
= (mapEquivMonic R S n f)…
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap' :
  (fromTensor m k hn p).comp (MvPolynomial.universalFactorizationMap R n m k hn) =
    ((MvPolynomial.mapEquivMonic _ _ n).symm (monicDegreeEq m k hn p)) := by
  rw [UniversalFactorizationRing.fromTensor_comp_universalFactorizationMap, Equiv.eq_symm_apply]
  ext1
  simp [MvPolynomial.coe_mapEquivMonic_comp, monicDegreeEq]

/-- The first factor of `p` in the universal factorization ring of `p`. -/
/-
**Polynomial.UniversalFactorizationRing.factor** 是 Mathlib 中的一个定义，位于命名空间 `Polyno
mial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first factor of `p` in the universal factorization ring of `p`.
-/
def UniversalFactorizationRing.factor₁ : MonicDegreeEq 𝓡 m :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.1

/-- The second factor of `p` in the universal factorization ring of `p`. -/
/-
**Polynomial.UniversalFactorizationRing.factor** 是 Mathlib 中的一个定义，位于命名空间 `Polyno
mial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second factor of `p` in the universal factorization ring of `p`.
-/
def UniversalFactorizationRing.factor₂ : MonicDegreeEq 𝓡 k :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).1.2
/-
**Polynomial.UniversalFactorizationRing.factor** 是 Mathlib 中的一个引理，位于命名空间 `Polyno
mial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniversalFactorizationRing.factor₁_mul_factor₂ :
    (factor₁ m k hn p).1 * (factor₂ m k hn p).1 = (monicDegreeEq m k hn p).1 :=
  (MvPolynomial.universalFactorizationMapLiftEquiv _ _ n m k hn _
    ⟨fromTensor m k hn p, fromTensor_comp_universalFactorizationMap' m k hn p⟩).2

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] leftModule in
/-- The universal factorization ring represents
`S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`. -/
/-
**Polynomial.UniversalFactorizationRing.homEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Poly
nomial.UniversalFactorizationRing`。
形式化陈述：{R : Type u_1} →   (S : Type u_2) →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           {n : ℕ} →          
   (m k : ℕ) →               (hn : n = m + k) →                 (p : Polynomial.
MonicDegreeEq R n) →                   (Polynomial.UniversalFactorizationRing m 
k hn p →ₐ[R] S) ≃                     { q // ↑q.1 * ↑q.2 = Polynomial.map (algeb
raMap R S) ↑p }
参数：S : Type u_2；m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomi
al.UniversalFactorizationRing m k hn p →ₐ[R] S；algebraMap R S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The universal factorization ring represents
`S ↦ "factorizations of p into (monic deg m) * (monic deg k) in S"`.
-/
def UniversalFactorizationRing.homEquiv :
    (𝓡 →ₐ[R] S) ≃ { q : MonicDegreeEq S m × MonicDegreeEq S k //
      q.1.1 * q.2.1 = p.1.map (algebraMap R S) } where
  toFun f := ⟨((factor₁ m k hn p).map f, (factor₂ m k hn p).map f), by
    simp [← Polynomial.map_mul, factor₁_mul_factor₂ m k hn p, Polynomial.map_map]⟩
  invFun q :=
    letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    letI := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    haveI : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    letI f := ((MvPolynomial.universalFactorizationMapLiftEquiv R _ n m k hn
          (p.map (algebraMap R S))).symm q)
    Algebra.TensorProduct.lift (R := MvPolynomial (Fin n) R) (S := R) (A := R)
      (B := MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R) (C := S) (Algebra.ofId R S)
      { toRingHom := f.1.toRingHom
        commutes' r := congr($(f.2) r).trans
          (by simp [MvPolynomial.mapEquivMonic_symm_map_algebraMap]; rfl) } fun _ _ ↦ .all _ _
  left_inv f := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    let := Algebra.compHom S ((MvPolynomial.mapEquivMonic R _ n).symm p).toRingHom
    have : IsScalarTower (MvPolynomial (Fin n) R) R S := .of_algebraMap_eq' rfl
    have : IsScalarTower R (MvPolynomial (Fin n) R) S := .of_algebraMap_eq fun r ↦ by
      simp [Algebra.compHom_algebraMap_apply]
    refine Algebra.TensorProduct.ext (by ext) ?_
    refine AlgHom.restrictScalars_injective R (Algebra.TensorProduct.ext ?_ ?_)
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₁, coeff_freeMonic]; rfl
    · ext; simp [MvPolynomial.universalFactorizationMapLiftEquiv, MvPolynomial.mapEquivMonic,
        UniversalFactorizationRing.factor₂, coeff_freeMonic]; rfl
  right_inv q := by
    let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
    let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
    simp only [UniversalFactorizationRing, MvPolynomial.mapEquivMonic, AlgHom.toRingHom_eq_coe,
      Equiv.coe_fn_symm_mk, MvPolynomial.coe_aeval_eq_eval, factor₁,
      MvPolynomial.universalFactorizationMapLiftEquiv, Equiv.coe_fn_mk, fromTensor, factor₂]
    ext <;> simp +contextual [coeff_freeMonic, apply_dite, MonicDegreeEq.coeff_of_ge]

attribute [-instance] leftModule in
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite R 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Module.Finite _ _ := MvPolynomial.finite_universalFactorizationMap R n m k hn
  inferInstanceAs (Module.Finite R (R ⊗[_] _))

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] leftModule in
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.FinitePresentation R 𝓡 :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  letI : Algebra.FinitePresentation _ _ :=
    MvPolynomial.finitePresentation_universalFactorizationMap R n m k hn
  inferInstanceAs (Algebra.FinitePresentation R (R ⊗[_] _))

/-- The presentation of `UniversalFactorizationRing`.
Its jacobian is the resultant of the two factors (up to sign). -/
/-
**Polynomial.UniversalFactorizationRing.presentation** 是 Mathlib 中的一个定义，位于命名空间 `
Polynomial.UniversalFactorizationRing`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {n : ℕ} →       (m k : ℕ) →  
       (hn : n = m + k) →           (p : Polynomial.MonicDegreeEq R n) →        
     Algebra.PreSubmersivePresentation R (Polynomial.UniversalFactorizationRing 
m k hn p) (Fin m ⊕ Fin k) (Fin n)
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomial.UniversalF
actorizationRing m k hn p；Fin m ⊕ Fin k；Fin n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The presentation of `UniversalFactorizationRing`.
Its jacobian is the resultant of the two factors (up to sign).
-/
def UniversalFactorizationRing.presentation :
    Algebra.PreSubmersivePresentation R 𝓡 (Fin m ⊕ Fin k) (Fin n) :=
  letI := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  letI := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  (MvPolynomial.universalFactorizationMapPresentation R n m k hn).baseChange _

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.UniversalFactorizationRing.jacobian_resentation** 是 Mathlib 中的一个定理，
位于命名空间 `Polynomial.UniversalFactorizationRing`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} (m k : ℕ) (hn : n = m + k) (p
 : Polynomial.MonicDegreeEq R n),   (Polynomial.UniversalFactorizationRing.prese
ntation m k hn p).jacobian =     (-1) ^ n *       (↑(Polynomial.UniversalFactori
zationRing.factor₁ m k hn p)).resultant         ↑(Polynomial.UniversalFactorizat
ionRing.factor₂ m k hn p)
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomial.UniversalF
actorizationRing.presentation m k hn p；-1；↑(Polynomial.UniversalFactorizationRin
g.factor₁ m k hn p)；Polynomial.UniversalFactorizationRing.factor₂ m k hn p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `Algebra.PreSubmersivePresentation.baseChange_jacobian`：baseChange_jacobi
an [Finite σ] : (P.baseChange T).jacobian = 1 otimesₜ P.jacobian
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPolynomial.universalFactorizationMapPresentation_jacobian`：universalFa
ctorizationMapPresentation_jacobian : letI
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
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
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.coe_toRingHom`：coe_toRingHom (f : A ->ₐ[R] B) : ⇑(f : A ->+* B) =
 f
· 使用引理 `Polynomial.resultant_map_map`：resultant_map_map (φ : R ->+* S) : resulta
nt (f.map φ) (g.map φ) m n = φ (resultant f g m n)
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Monic.natDegree_map`：∀ {R : Type u} {S : Type v} [inst : Semi
ring R] [inst_1 : Semiring S] [Nontrivial S] {P : Polynomial R},   P.Monic → ∀ (
f : R →+* S), (Polyn…
· 使用引理 `Polynomial.monic_freeMonic`：monic_freeMonic : (freeMonic R n).Monic
· 使用定理 `Polynomial.MonicDegreeEq.natDegree`：∀ {R : Type u} {n : ℕ} [inst : Semir
ing R] [Nontrivial R] (p : Polynomial.MonicDegreeEq R n), (↑p).natDegree = n
（共 31 条，此处仅展示前 30 条）
-/
lemma UniversalFactorizationRing.jacobian_resentation :
    (presentation m k hn p).jacobian =
      (-1) ^ n * (factor₁ m k hn p).1.resultant (factor₂ m k hn p).1 := by
  cases subsingleton_or_nontrivial 𝓡
  · exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial ((MvPolynomial (Fin m) R ⊗[R] MvPolynomial (Fin k) R))
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  cases subsingleton_or_nontrivial R
  · dsimp [UniversalFactorizationRing]; exact Subsingleton.elim _ _
  let := (MvPolynomial.universalFactorizationMap R n m k hn).toAlgebra
  let := ((MvPolynomial.mapEquivMonic R _ n).symm p).toAlgebra
  refine (Algebra.PreSubmersivePresentation.baseChange_jacobian _ _).trans ?_
  change fromTensor _ _ _ _ _ = _
  rw [MvPolynomial.universalFactorizationMapPresentation_jacobian]
  rw [map_mul, map_pow, map_neg, map_one, ← AlgHom.coe_toRingHom, ← Polynomial.resultant_map_map,
    Polynomial.map_map, Polynomial.map_map, (monic_freeMonic R k).natDegree_map,
    (monic_freeMonic R m).natDegree_map, MonicDegreeEq.natDegree,
    MonicDegreeEq.natDegree, natDegree_freeMonic, natDegree_freeMonic]
  rfl

open UniversalFactorizationRing in
/-- The universal coprime factorization ring of a monic polynomial `p` of degree `n`.
This is the representing object of the functor
`S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`.
See `UniversalCoprimeFactorizationRing.homEquiv`. -/
/-
**Polynomial.UniversalCoprimeFactorizationRing** 是 Mathlib 中的一个缩写定义，位于命名空间 `Poly
nomial`。
形式化陈述：UniversalCoprimeFactorizationRing : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal coprime factorization ring of a monic polynomial `p` of degree `n`
.
This is the representing object of the functor
`S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`.
See `UniversalCoprimeFactorizationRing.homEquiv`.
-/
abbrev UniversalCoprimeFactorizationRing : Type _ :=
  Localization.Away (M := 𝓡) (presentation m k hn p).jacobian

local notation "𝓡'" => UniversalCoprimeFactorizationRing m k hn p

/-- The first factor of `p` in the universal coprime factorization ring of `p`. -/
/-
**Polynomial.UniversalCoprimeFactorizationRing.factor** 是 Mathlib 中的一个定义，位于命名空间 
`Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first factor of `p` in the universal coprime factorization ring of `p`.
-/
def UniversalCoprimeFactorizationRing.factor₁ : MonicDegreeEq 𝓡' m :=
  (UniversalFactorizationRing.factor₁ m k hn p).map (algebraMap _ _)

/-- The second factor of `p` in the universal coprime factorization ring of `p`. -/
/-
**Polynomial.UniversalCoprimeFactorizationRing.factor** 是 Mathlib 中的一个定义，位于命名空间 
`Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second factor of `p` in the universal coprime factorization ring of `p`.
-/
def UniversalCoprimeFactorizationRing.factor₂ : MonicDegreeEq 𝓡' k :=
  (UniversalFactorizationRing.factor₂ m k hn p).map (algebraMap _ _)
/-
**Polynomial.UniversalCoprimeFactorizationRing.factor** 是 Mathlib 中的一个引理，位于命名空间 
`Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniversalCoprimeFactorizationRing.factor₁_mul_factor₂ :
    (factor₁ m k hn p).1 * (factor₂ m k hn p).1 = p.map (algebraMap R 𝓡') := by
  simp [factor₁, factor₂, ← Polynomial.map_mul, UniversalFactorizationRing.factor₁_mul_factor₂,
    Polynomial.map_map, ← IsScalarTower.algebraMap_eq]
/-
**Polynomial.UniversalCoprimeFactorizationRing.isCoprime_factor** 是 Mathlib 中的一个
引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UniversalCoprimeFactorizationRing.isCoprime_factor₁_factor₂ :
    IsCoprime (factor₁ m k hn p).1 (factor₂ m k hn p).1 := by
  cases subsingleton_or_nontrivial 𝓡'
  · rw [Subsingleton.elim (Subtype.val _) 1]; exact isCoprime_one_left
  rw [← Polynomial.isUnit_resultant_iff_isCoprime (factor₁ m k hn p).monic, factor₁,
    factor₂, MonicDegreeEq.map_coe, MonicDegreeEq.map_coe, Polynomial.resultant_map_map,
    (UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map,
    (UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map]
  refine ((IsUnit.mul_iff (x := algebraMap 𝓡 𝓡' ((-1) ^ n))).mp ?_).2
  rw [← map_mul, ← UniversalFactorizationRing.jacobian_resentation m k hn p]
  exact IsLocalization.Away.algebraMap_isUnit _

open UniversalFactorizationRing in
/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra.Etale R 𝓡' := by
  let Δ : 𝓡 := (presentation m k hn p).jacobian
  have hΔ : IsUnit (algebraMap 𝓡 (Localization.Away Δ) Δ) :=
    IsLocalization.Away.algebraMap_isUnit _
  let P : Algebra.SubmersivePresentation R (Localization.Away Δ) _ _ :=
    { toPreSubmersivePresentation :=
        .comp (.localizationAway (Localization.Away Δ) Δ) (presentation m k hn p),
      jacobian_isUnit := by simpa [Algebra.smul_def, -isUnit_map_iff, hΔ] }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 R (Localization.Away Δ) :=
    ⟨_, _, _, inferInstance, P, by
      simp only [Algebra.PreSubmersivePresentation.dimension_comp_eq_dimension_add_dimension, P]
      simp [Algebra.Presentation.dimension, hn]⟩
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- The universal factorization ring represents
`S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`. -/
/-
**Polynomial.UniversalCoprimeFactorizationRing.homEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `Polynomial.UniversalCoprimeFactorizationRing`。
形式化陈述：{R : Type u_1} →   (S : Type u_2) →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           {n : ℕ} →          
   (m k : ℕ) →               (hn : n = m + k) →                 (p : Polynomial.
MonicDegreeEq R n) →                   (Polynomial.UniversalCoprimeFactorization
Ring m k hn p →ₐ[R] S) ≃                     { q // ↑q.1 * ↑q.2 = Polynomial.map
 (algebraMap R S) ↑p ∧ IsCoprime ↑q.1 ↑q.2 }
参数：S : Type u_2；m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；Polynomi
al.UniversalCoprimeFactorizationRing m k hn p →ₐ[R] S；algebraMap R S。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The universal factorization ring represents
`S ↦ "factorizations of p into coprime (monic deg m) * (monic deg k) in S"`.
-/
def UniversalCoprimeFactorizationRing.homEquiv :
    (𝓡' →ₐ[R] S) ≃ { q : MonicDegreeEq S m × MonicDegreeEq S k //
      q.1.1 * q.2.1 = p.1.map (algebraMap R S) ∧ IsCoprime q.1.1 q.2.1 } where
  toFun f :=
    letI q := UniversalFactorizationRing.homEquiv S m k hn p (f.comp (IsScalarTower.toAlgHom _ _ _))
    ⟨q.1, q.2, by
      convert! (isCoprime_factor₁_factor₂ m k hn p).map (Polynomial.mapRingHom f.toRingHom) <;>
        simp [q, UniversalFactorizationRing.homEquiv,
          AlgHom.comp_toRingHom, ← Polynomial.map_map] <;> rfl⟩
  invFun q := by
    letI f := (UniversalFactorizationRing.homEquiv S m k hn p).symm ⟨q.1, q.2.1⟩
    apply IsLocalization.Away.liftAlgHom (f := f)
      (UniversalFactorizationRing.presentation m k hn p).jacobian
    nontriviality S
    rw [← AlgHom.coe_toRingHom, UniversalFactorizationRing.jacobian_resentation, map_mul,
      ← Polynomial.resultant_map_map, IsUnit.mul_iff]
    refine ⟨by cases n <;> simp, ?_⟩
    rw [← (UniversalFactorizationRing.factor₁ m k hn p).monic.natDegree_map f.toRingHom,
      ← (UniversalFactorizationRing.factor₂ m k hn p).monic.natDegree_map f.toRingHom,
      AlgHom.toRingHom_eq_coe, Polynomial.isUnit_resultant_iff_isCoprime
        ((UniversalFactorizationRing.factor₁ m k hn p).monic.map _)]
    change IsCoprime (UniversalFactorizationRing.homEquiv S m k hn p f).1.1.1
      (UniversalFactorizationRing.homEquiv S m k hn p f).1.2.1
    simpa [f] using q.2.2
  left_inv f := by
    apply IsLocalization.algHom_ext
      (.powers (UniversalFactorizationRing.presentation m k hn p).jacobian)
    ext; simp [Algebra.algHom]
  right_inv q := by
    apply Subtype.ext
    convert! congr($((UniversalFactorizationRing.homEquiv S m k hn p).apply_symm_apply
      ⟨_, q.2.1⟩).1) using 1
    dsimp
    congr 2
    ext
    simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_fst** 是 Mathlib 中的一
个定理，位于命名空间 `Polynomial.UniversalCoprimeFactorizationRing`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {n : ℕ} (m k : ℕ)   (hn : n = m + k) (p : Polynomial.Moni
cDegreeEq R n) {T : Type u_4} [inst_3 : CommRing T] [inst_4 : Algebra R T]   (f 
: Polynomial.UniversalCoprimeFactorizationRing m k hn p →ₐ[R] S) (g : S →ₐ[R] T)
,   (↑((Polynomial.UniversalCoprimeFactorizationRing.homEquiv T m k hn p) (g.com
p f))).1 =     (↑((Polynomial.UniversalCoprimeFactorizationRing.homEquiv S m k h
n p) f)).1.map ↑g
参数：S : Type u_2；m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；f : Poly
nomial.UniversalCoprimeFactorizationRing m k hn p →ₐ[R] S；g : S →ₐ[R] T；↑((Polyn
omial.UniversalCoprimeFactorizationRing.homEquiv T m k hn p) (g.comp f))；↑((Poly
nomial.UniversalCoprimeFactorizationRing.homEquiv S m k hn p) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.MonicDegreeEq.map_coe`：∀ {R : Type u} {S : Type v} {n : ℕ} [i
nst : Semiring R] [inst_1 : Semiring S] (p : Polynomial.MonicDegreeEq R n)   (f 
: R →+* S), ↑(p.map f)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
-/
lemma UniversalCoprimeFactorizationRing.homEquiv_comp_fst {T : Type*} [CommRing T] [Algebra R T]
    (f : 𝓡' →ₐ[R] S) (g : S →ₐ[R] T) :
    (homEquiv T m k hn p (g.comp f)).1.1 = (homEquiv S m k hn p f).1.1.map g := by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**Polynomial.UniversalCoprimeFactorizationRing.homEquiv_comp_snd** 是 Mathlib 中的一
个定理，位于命名空间 `Polynomial.UniversalCoprimeFactorizationRing`。
形式化陈述：∀ {R : Type u_1} (S : Type u_2) [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {n : ℕ} (m k : ℕ)   (hn : n = m + k) (p : Polynomial.Moni
cDegreeEq R n) {T : Type u_4} [inst_3 : CommRing T] [inst_4 : Algebra R T]   (f 
: Polynomial.UniversalCoprimeFactorizationRing m k hn p →ₐ[R] S) (g : S →ₐ[R] T)
,   (↑((Polynomial.UniversalCoprimeFactorizationRing.homEquiv T m k hn p) (g.com
p f))).2 =     (↑((Polynomial.UniversalCoprimeFactorizationRing.homEquiv S m k h
n p) f)).2.map ↑g
参数：S : Type u_2；m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；f : Poly
nomial.UniversalCoprimeFactorizationRing m k hn p →ₐ[R] S；g : S →ₐ[R] T；↑((Polyn
omial.UniversalCoprimeFactorizationRing.homEquiv T m k hn p) (g.comp f))；↑((Poly
nomial.UniversalCoprimeFactorizationRing.homEquiv S m k hn p) f)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.MonicDegreeEq.map_coe`：∀ {R : Type u} {S : Type v} {n : ℕ} [i
nst : Semiring R] [inst_1 : Semiring S] (p : Polynomial.MonicDegreeEq R n)   (f 
: R →+* S), ↑(p.map f)…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
-/
lemma UniversalCoprimeFactorizationRing.homEquiv_comp_snd {T : Type*} [CommRing T] [Algebra R T]
    (f : 𝓡' →ₐ[R] S) (g : S →ₐ[R] T) :
    (homEquiv T m k hn p (g.comp f)).1.2 = (homEquiv S m k hn p f).1.2.map g := by
  ext1
  simp [homEquiv, UniversalFactorizationRing.homEquiv, Polynomial.map_map]
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists `Q : Spec R_univ` in the universal coprime factorization ring lying over `P`,
such that `κ(P) = κ(Q)` and `f` and `g` are the image of the universal factors. -/
/-
**Polynomial.UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_b
ijective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.UniversalCoprimeFactorizationRing
`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {n : ℕ} (m k : ℕ) (hn : n = m + k) (p
 : Polynomial.MonicDegreeEq R n) (P : Ideal R)   [inst_1 : P.IsPrime] (f : Polyn
omial.MonicDegreeEq P.ResidueField m) (g : Polynomial.MonicDegreeEq P.ResidueFie
ld k),   Polynomial.map (algebraMap R P.ResidueField) ↑p = ↑f * ↑g →     IsCopri
me ↑f ↑g →       ∃ Q,         ∃ (x : Q.IsPrime) (x_1 : Q.LiesOver P),           
Function.Bijective               ⇑(Ideal.ResidueField.mapₐ P Q (Algebra.ofId R (
Polynomial.UniversalCoprimeFactorizationRing m k hn p))                   ⋯) ∧  
           f.map                   (Ideal.ResidueField.mapₐ P Q (Algebra.ofId R 
(Polynomial.UniversalCoprimeFactorizationRing m k hn p))                       ⋯
).toRingHom =                 (Polynomial.UniversalCoprimeFactorizationRing.fact
or₁ m k hn p).map                   (algebraMap (Polynomial.UniversalCoprimeFact
orizationRing m k hn p) Q.ResidueField) ∧               g.map                   
(Ideal.ResidueField.mapₐ P Q (Algebra.ofId R (Polynomial.UniversalCoprimeFactori
zationRing m k hn p))                       ⋯).toRingHom =                 (Poly
nomial.UniversalCoprimeFactorizationRing.factor₂ m k hn p).map                  
 (algebraMap (Polynomial.UniversalCoprimeFactorizationRing m k hn p) Q.ResidueFi
eld)
参数：m k : ℕ；hn : n = m + k；p : Polynomial.MonicDegreeEq R n；P : Ideal R；f : Polyn
omial.MonicDegreeEq P.ResidueField m；g : Polynomial.MonicDegreeEq P.ResidueField
 k；algebraMap R P.ResidueField；x : Q.IsPrime；x_1 : Q.LiesOver P；Ideal.ResidueFie
ld.mapₐ P Q (Algebra.ofId R (Polynomial.UniversalCoprimeFactorizationRing m k hn
 p))                   ⋯；Ideal.ResidueField.mapₐ P Q (Algebra.ofId R (Polynomial
.UniversalCoprimeFactorizationRing m k hn p))                       ⋯；Polynomial
.UniversalCoprimeFactorizationRing.factor₁ m k hn p；algebraMap (Polynomial.Unive
rsalCoprimeFactorizationRing m k hn p) Q.ResidueField；Ideal.ResidueField.mapₐ P 
Q (Algebra.ofId R (Polynomial.UniversalCoprimeFactorizationRing m k hn p))      
                 ⋯；Polynomial.UniversalCoprimeFactorizationRing.factor₂ m k hn p
；algebraMap (Polynomial.UniversalCoprimeFactorizationRing m k hn p) Q.ResidueFie
ld。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.ker_isPrime`：ker_isPrime {F : Type*} [Semiring R] [Semiring S] [
IsDomain S] [FunLike F R S] [RingHomClass F R S] (f : F) : (ker f).IsPrime
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.under.eq_1`：∀ (A : Type u_2) [inst : CommSemiring A] {B : Type u_3
} [inst_1 : Semiring B] [inst_2 : Algebra A B] (P : Ideal B),   Ideal.under A P 
= Idea…
· 使用定理 `RingHom.comap_ker`：comap_ker (f : S ->+* R) (g : T ->+* S) : (ker f).com
ap g = ker (f.comp g)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用引理 `Ideal.ker_algebraMap_residueField`：Ideal.ker_algebraMap_residueField : R
ingHom.ker (algebraMap R I.ResidueField) = I
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `Ideal.ResidueField.algHom_ext`：Ideal.ResidueField.algHom_ext {I : Ideal 
A} [I.IsPrime] {f g : I.ResidueField ->ₐ[R] B} (H : f.comp (IsScalarTower.toAlgH
om R A _) = g.comp …
· 使用定理 `Algebra.ext_id`：ext_id (f g : R ->ₐ[R] A) : f = g
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If a monic polynomial `p : R[X]` factors into a product of coprime monic polynom
ials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists `Q : Spec R_univ` in the universal coprime factorization ring 
lying over `P`,
such that `κ(P) = κ(Q)` and `f` and `g` are the image of the universal factors.
-/
lemma UniversalCoprimeFactorizationRing.exists_liesOver_residueFieldMap_bijective
    (P : Ideal R) [P.IsPrime]
    (f : MonicDegreeEq P.ResidueField m) (g : MonicDegreeEq P.ResidueField k)
    (H : p.1.map (algebraMap R _) = f.1 * g.1) (Hpq : IsCoprime f.1 g.1) :
    ∃ (Q : Ideal 𝓡') (_ : Q.IsPrime) (_ : Q.LiesOver P),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₁ m k hn p).map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      (factor₂ m k hn p).map (algebraMap _ _) := by
  let φ : 𝓡' →ₐ[R] P.ResidueField :=
    (UniversalCoprimeFactorizationRing.homEquiv _ m k hn p).symm ⟨(f, g), H.symm, Hpq⟩
  let Q := RingHom.ker φ.toRingHom
  have : Q.IsPrime := RingHom.ker_isPrime _
  have : Q.LiesOver P := ⟨by rw [Ideal.under, RingHom.comap_ker, AlgHom.toRingHom_eq_coe,
      φ.comp_algebraMap, Ideal.ker_algebraMap_residueField]⟩
  let φ' : Q.ResidueField →ₐ[R] P.ResidueField := Ideal.ResidueField.liftₐ _ φ le_rfl (by
    simp [SetLike.le_def, IsUnit.mem_submonoid_iff, Q])
  let φi : P.ResidueField →ₐ[R] Q.ResidueField :=
    Ideal.ResidueField.mapₐ _ _ (Algebra.ofId _ _) (Ideal.over_def _ _)
  let e : P.ResidueField ≃ₐ[R] Q.ResidueField :=
    .ofAlgHom φi φ' (AlgHom.ext fun x ↦ φ'.injective <|
      show (φ'.comp φi) (φ' x) = AlgHom.id R _ (φ' x) by congr; ext) (by ext)
  have H : φi.comp φ = (IsScalarTower.toAlgHom _ _ _) :=
    AlgHom.ext fun x ↦ e.eq_symm_apply.mp (by simp [e, φ'])
  refine ⟨Q, ‹_›, ‹_›, e.bijective, ?_, ?_⟩
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.1
    · simp [homEquiv_comp_fst, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₁,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl
  · trans ((homEquiv Q.ResidueField m k hn p) (φi.comp φ)).1.2
    · simp [homEquiv_comp_snd, φ, φi]
    · rw [H]
      simp [homEquiv, UniversalFactorizationRing.homEquiv, factor₂,
        MonicDegreeEq.map, Polynomial.map_map]
      rfl

open UniversalCoprimeFactorizationRing in
/-- If a monic polynomial `p : R[X]` factors into a product of coprime monic polynomials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists an etale algebra `R'` of `R` and a prime `Q` of `R'` lying over `P`,
such that `κ(P) = κ(Q)` and that the factorization lifts to `R'`. -/
@[stacks 00UH]
/-
**Polynomial._root_.Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mu
l_and_isCoprime.** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a monic polynomial `p : R[X]` factors into a product of coprime monic polynom
ials `p = f * g`
in the residue field `κ(P)` of some `P : Spec R`,
then there exists an etale algebra `R'` of `R` and a prime `Q` of `R'` lying ove
r `P`,
such that `κ(P) = κ(Q)` and that the factorization lifts to `R'`.
-/
lemma _root_.Algebra.exists_etale_bijective_residueFieldMap_and_map_eq_mul_and_isCoprime.{u}
    {R : Type u} [CommRing R]
    (P : Ideal R) [P.IsPrime] (p : R[X])
    (f g : P.ResidueField[X]) (hp : p.Monic) (hf : f.Monic) (hg : g.Monic)
    (H : p.map (algebraMap R _) = f * g) (Hpq : IsCoprime f g) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra R R') (_ : Algebra.Etale R R')
      (Q : Ideal R') (_ : Q.IsPrime) (_ : Q.LiesOver P) (f' g' : R'[X]),
    Function.Bijective (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)) ∧
    f'.Monic ∧ g'.Monic ∧ p.map (algebraMap R R') = f' * g' ∧ IsCoprime f' g' ∧
    f.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      f'.map (algebraMap _ _) ∧
    g.map (Ideal.ResidueField.mapₐ P Q (Algebra.ofId _ _) (Ideal.over_def Q P)).toRingHom =
      g'.map (algebraMap _ _) := by
  obtain ⟨Q, _, _, h₁, h₂, h₃⟩ :=
    exists_liesOver_residueFieldMap_bijective f.natDegree g.natDegree
    (by simpa [hf.natDegree_mul hg, hp.natDegree_map] using congr(($H).natDegree)) (.mk p hp rfl)
    P (.mk f hf rfl) (.mk g hg rfl) H Hpq
  exact ⟨_, _, _, inferInstance, Q, ‹_›, ‹_›, (factor₁ ..).1, (factor₂ ..).1, h₁,
    (factor₁ ..).monic, (factor₂ ..).monic, (factor₁_mul_factor₂ ..).symm,
    isCoprime_factor₁_factor₂ .., congr(($h₂).1), congr(($h₃).1)⟩

end Polynomial

