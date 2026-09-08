/-
Copyright (c) 2023 Sidharth Hariharan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Sidharth Hariharan, Aaron Liu
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.RingTheory.Coprime.Lemmas

/-!

# Partial fractions

For `f, g : R[X]`, if `g` is expressed as a product `g₁ ^ n₁ * g₂ ^ n₂ * ... * gₙ ^ nₙ`,
where the `gᵢ` are monic and pairwise coprime, then there is a quotient `q` and
for each `i` from 1 to n and for each `0 ≤ j < nᵢ` there is a remainder `rᵢⱼ`
with degree less than the degree of `gᵢ`, such that the fraction `f / g`
decomposes as `q + ∑ i j, rᵢⱼ / gᵢ ^ (j + 1)`.

Since polynomials do not have a division, the main theorem
`mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` is stated in an `R[X]`-algebra `K`
containing inverses `giᵢ` for each polynomial `gᵢ` occurring in the denominator.


These results were formalised by the Xena Project, at the suggestion
of Patrick Massot.


## Main results

* `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denominator is a product of powers of
  monic pairwise coprime polynomials. Division is done in an `R[X]`-algebra `K`
  containing inverses `gi i` for each `g i` occurring in the denominator.
* `eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denominator is a product of powers of
  monic pairwise coprime polynomials. The denominators are multiplied out on both sides
  and formally cancelled.
* `eq_quo_mul_prod_add_sum_rem_mul_prod`: Partial fraction decomposition for
  polynomials over a commutative ring `R`, the denominator is a product of monic
  pairwise coprime polynomials. The denominators are multiplied out on both sides
  and formally cancelled.
* `div_prod_eq_quo_add_sum_rem_div`: Partial fraction decomposition for polynomials over an
  integral domain `R`, the denominator is a product of monic pairwise coprime polynomials.
  Division is done in a field `K` containing `R[X]`.
* `div_eq_quo_add_rem_div_add_rem_div`: Partial fraction decomposition for polynomials over an
  integral domain `R`, the denominator is a product of two monic coprime polynomials.
  Division is done in a field `K` containing `R[X]`.

## Naming

The lemmas in this file proving existence of partial fraction decomposition all have
conclusions of the form `∃ q r, degree r < degree g ∧ f / g = q + ∑ r / g`.
The names of these lemmas depict only the final equality `f / g = q + ∑ r / g`.
They are named structurally, except the bound variable `q` is called `quo` (for quotient)
and the bound variable `r` is called `rem` (for remainder), since they are the quotient
and remainder of the division `f / g`.
For example, `div_prod_eq_quo_add_sum_rem_div` has the conclusion
```
∃ q r, (∀ i ∈ s, (r i).degree < (g i).degree) ∧
  ↑f / ∏ i ∈ s, ↑(g i) = ↑q + ∑ i ∈ s, ↑(r i) / ↑(g i)
```
The name of the lemma only shows the final equality, and in order we have
`/` (`div`), `∏` (`prod`), `=` (`eq`), `q` (`quo`),
`+` (`add`), `∑` (`sum`), `r i` (`rem`), `/` (`div`).

The lemmas in this file proving uniqueness of partial fraction decomposition all have
conclusions of the form `q₁ + ∑ r₁ / g = q₂ + ∑ r₂ / g → q₁ = q₂ ∧ r₁ = r₂`.
The names of these lemmas show a side of the equality hypothesis `q₁ + ∑ r₁ / g = q₂ + ∑ r₂ / g`,
and are suffixed by `_unique`.
In analogy with the existence lemmas, the variables `qᵢ` are called quotients
and referred to as `quo` in the name of the lemma and the variables `rᵢ` are called remainders
and referred to as `rem` in the name of the lemma.
For example, `quo_add_sum_rem_div_unique` has the conclusion
```
↑q₁ + ∑ i ∈ s, ↑(r₁ i) / ↑(g i) = ↑q₂ + ∑ i ∈ s, ↑(r₂ i) / ↑(g i)) →
  q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i
```
The name of the lemmas shows one side of the equality hypothesis (the other is the same),
and in order we have
`q` (`quo`), `+` (`add`), `∑` (`sum`), `r i` (`rem`), `/` (`div`).

-/

public section


variable {R : Type*} [CommRing R]

namespace Polynomial

section Mul

section OneDenominator

/-- Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g ^ n * (q + ∑ i : Fin n, r i / g ^ (i + 1))`, where
`degree (r i) < degree g` and the denominator cancels formally.
See `quo_mul_pow_add_sum_rem_mul_pow_unique` for the uniqueness of this representation. -/
/-
**Polynomial.eq_quo_mul_pow_add_sum_rem_mul_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：eq_quo_mul_pow_add_sum_rem_mul_pow [Nontrivial R] (f : R[X]) {g : R[X]} (h
g : g.Monic) (n : Nat) : exists (q : R[X]) (r : Fin n -> R[X]), (forall i, (r i)
.degree < g.degree) ∧ f = q * g ^ n + ∑ i, r i * g ^ i.1
参数：f : R[X]；hg : g.Monic；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `add_rotate'`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G), a
 + (b + c) = b + (c + a)
· 使用定理 `Fin.val_last`：∀ (n : ℕ), ↑(Fin.last n) = n
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.modByMonic_add_div`：modByMonic_add_div (p q : R[X]) : p %ₘ q 
+ q * (p /ₘ q) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g ^ n * (q + ∑ i : Fin n, r i / g ^ (i + 1)
)`, where
`degree (r i) < degree g` and the denominator cancels formally.
See `quo_mul_pow_add_sum_rem_mul_pow_unique` for the uniqueness of this represen
tation.
-/
theorem eq_quo_mul_pow_add_sum_rem_mul_pow [Nontrivial R] (f : R[X]) {g : R[X]} (hg : g.Monic)
    (n : ℕ) : ∃ (q : R[X]) (r : Fin n → R[X]), (∀ i, (r i).degree < g.degree) ∧
      f = q * g ^ n + ∑ i, r i * g ^ i.1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨q, r, hr, hf⟩ := ih
    refine ⟨q /ₘ g, Fin.snoc r (q %ₘ g), fun i => ?_, hf.trans ?_⟩
    · cases i using Fin.lastCases with
      | cast i => simpa using hr i
      | last => simpa using degree_modByMonic_lt q hg
    · rw [Fin.sum_univ_castSucc, ← add_rotate', Fin.snoc_last, Fin.val_last,
        ← add_assoc, pow_succ', ← mul_assoc, ← add_mul, mul_comm (q /ₘ g) g,
        modByMonic_add_div q]
      simp

/-- Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g ^ n * (q + ∑ i : Fin n, r i / g ^ (i + 1))`
in at most one way, where `degree (r i) < degree g` and the denominator cancels formally.
See `eq_quo_mul_pow_add_sum_rem_mul_pow` for the existence of such a representation. -/
/-
**Polynomial.quo_mul_pow_add_sum_rem_mul_pow_unique** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：quo_mul_pow_add_sum_rem_mul_pow_unique {g : R[X]} (hg : g.Monic) {n : Nat}
 {q₁ q₂ : R[X]} {r₁ r₂ : Fin n -> R[X]} (hr₁ : forall i, (r₁ i).degree < g.degre
e) (hr₂ : forall i, (r₂ i).degree < g.degree) (hf : q₁ * g ^ n + ∑ i, r₁ i * g ^
 i.1 = q₂ * g ^ n + ∑ i, r₂ i * g ^ i.1) : q₁ = q₂ ∧ r₁ = r₂
参数：hg : g.Monic；hr₁ : forall i, (r₁ i).degree < g.degree；hr₂ : forall i, (r₂ i).
degree < g.degree；hf : q₁ * g ^ n + ∑ i, r₁ i * g ^ i.1 = q₂ * g ^ n + ∑ i, r₂ i
 * g ^ i.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `add_rotate'`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G), a
 + (b + c) = b + (c + a)
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
· 使用定理 `Polynomial.div_modByMonic_unique`：div_modByMonic_unique {f g} (q r : R[X
]) (hg : Monic g) (h : r + g * q = f ∧ degree r < degree g) : f /ₘ g = q ∧ f %ₘ 
g = r
· 使用定理 `congrArg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → γ
) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'

--- 原说明 ---
Let `R` be a commutative ring and `f g : R[X]`. Let `n` be a natural number.
Then `f` can be written in the form `g ^ n * (q + ∑ i : Fin n, r i / g ^ (i + 1)
)`
in at most one way, where `degree (r i) < degree g` and the denominator cancels 
formally.
See `eq_quo_mul_pow_add_sum_rem_mul_pow` for the existence of such a representat
ion.
-/
theorem quo_mul_pow_add_sum_rem_mul_pow_unique {g : R[X]} (hg : g.Monic) {n : ℕ}
    {q₁ q₂ : R[X]} {r₁ r₂ : Fin n → R[X]}
    (hr₁ : ∀ i, (r₁ i).degree < g.degree) (hr₂ : ∀ i, (r₂ i).degree < g.degree)
    (hf : q₁ * g ^ n + ∑ i, r₁ i * g ^ i.1 = q₂ * g ^ n + ∑ i, r₂ i * g ^ i.1) :
    q₁ = q₂ ∧ r₁ = r₂ := by
  induction n generalizing q₁ q₂ with
  | zero => exact ⟨by simpa using hf, funext Fin.rec0⟩
  | succ n ih =>
    cases r₁ using Fin.snocCases with | snoc rs₁ r₁
    cases r₂ using Fin.snocCases with | snoc rs₂ r₂
    simp only [Fin.sum_univ_castSucc, Fin.snoc_castSucc,
      Fin.val_castSucc, Fin.snoc_last, Fin.val_last] at hf
    rw [← add_rotate' (r₁ * g ^ n), ← add_rotate' (r₂ * g ^ n), pow_succ', ← mul_assoc, ← mul_assoc,
      ← add_assoc, ← add_assoc, ← add_mul, ← add_mul, ← mul_comm g, ← mul_comm g] at hf
    obtain ⟨hqr, hrs⟩ := ih
      (fun i => by simpa using hr₁ i.castSucc)
      (fun i => by simpa using hr₂ i.castSucc) hf
    obtain ⟨hq₁, hrr₁⟩ := div_modByMonic_unique q₁ r₁ hg ⟨rfl, by simpa using hr₁ (Fin.last n)⟩
    obtain ⟨hq₂, hrr₂⟩ := div_modByMonic_unique q₂ r₂ hg ⟨rfl, by simpa using hr₂ (Fin.last n)⟩
    exact ⟨hq₁.symm.trans (hqr ▸ hq₂), congrArg₂ Fin.snoc hrs (hrr₁.symm.trans (hqr ▸ hrr₂))⟩

end OneDenominator

section ManyDenominators

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`, where
`degree (r i) < degree (g i)` and the denominator cancels formally.
See `quo_mul_prod_add_sum_rem_mul_prod_unique` for the uniqueness of this representation. -/
/-
**Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：eq_quo_mul_prod_add_sum_rem_mul_prod [Nontrivial R] {ι : Type*} [Decidable
Eq ι] {s : Finset ι} (f : R[X]) {g : ι -> R[X]} (hg : forall i in s, (g i).Monic
) (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) : exists (q : R[X]) (r
 : ι -> R[X]), (forall i in s, (r i).degree < (g i).degree) ∧ f = q * (∏ i in s,
 g i) + ∑ i in s, r i * ∏ k in s.erase i, g k
参数：f : R[X]；hg : forall i in s, (g i).Monic；hgg : Set.Pairwise s fun i j => IsCo
prime (g i) (g j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.forall_mem_cons`：forall_mem_cons (h : a ∉ s) (p : α -> Prop) : (f
orall x, x in cons a s h -> p x) ↔ p a ∧ forall x, x in s -> p x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.pairwise_insert`：pairwise_insert : (insert a s).Pairwise r ↔ s.Pairw
ise r ∧ forall b in s, a != b -> r a b ∧ r b a
· 使用定理 `Finset.coe_cons`：coe_cons {a s h} : (@cons α a s h : Set α) = insert a (
s : Set α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Polynomial.degree_modByMonic_lt`：degree_modByMonic_lt [Nontrivial R] : f
orall (p : R[X]) {q : R[X]} (_hq : Monic q), degree (p %ₘ q) < degree q | p, q, 
hq => letI
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `
s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`,
 where
`degree (r i) < degree (g i)` and the denominator cancels formally.
See `quo_mul_prod_add_sum_rem_mul_prod_unique` for the uniqueness of this repres
entation.
-/
theorem eq_quo_mul_prod_add_sum_rem_mul_prod [Nontrivial R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
      f = q * (∏ i ∈ s, g i) + ∑ i ∈ s, r i * ∏ k ∈ s.erase i, g k := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hg
    rw [Finset.coe_cons, Set.pairwise_insert] at hgg
    obtain ⟨q, r, -, hf⟩ := ih hg.2 hgg.1
    have hjs {j : ι} (hj : j ∈ s) : i ≠ j := fun hij => hi (hij ▸ hj)
    have hc (j : ι) : ∃ a b, j ∈ s → a * g i + b * g j = 1 :=
      if h : j ∈ s ∧ i ≠ j then
        (hgg.2 j h.1 h.2).1.elim fun a h => h.elim fun b h => ⟨a, b, fun _ => h⟩
      else
        ⟨0, 0, fun hj => (h ⟨hj, hjs hj⟩).elim⟩
    choose a b hab using hc
    refine ⟨(q + ∑ j ∈ s, r j * b j %ₘ g i) /ₘ g i + ∑ j ∈ s, (r j * b j /ₘ g i + r j * a j /ₘ g j),
      Function.update (fun j => r j * a j %ₘ g j) i ((q + ∑ j ∈ s, r j * b j %ₘ g i) %ₘ g i),
      ?_, hf.trans ?_⟩
    · rw [Finset.forall_mem_cons, Function.update_self]
      refine ⟨degree_modByMonic_lt _ hg.1, fun j hj => ?_⟩
      rw [Function.update_of_ne (hjs hj).symm]
      exact degree_modByMonic_lt _ (hg.2 j hj)
    · rw [Finset.prod_cons, Finset.sum_cons, Function.update_self, Finset.erase_cons, add_mul,
        add_add_add_comm, ← mul_assoc, ← add_mul, add_comm (_ * g i), ← mul_comm (g i),
        modByMonic_add_div, add_mul, add_assoc, add_right_inj, Finset.sum_mul,
        Finset.sum_mul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_of_ne (hjs hj).symm, Finset.erase_cons_of_ne _ (hjs hj),
        Finset.prod_cons, ← Finset.mul_prod_erase s g hj]
      simp_rw [← mul_assoc, ← add_mul]
      refine congrArg (· * _) ?_
      rw [add_mul, add_mul, ← add_assoc, ← add_assoc, ← add_mul, ← mul_comm (g i),
        modByMonic_add_div, add_assoc, mul_right_comm (_ /ₘ g j),
        ← add_mul, add_comm (_ * g j) (_ %ₘ g j), mul_comm (_ /ₘ g j),
        modByMonic_add_div, mul_assoc, mul_assoc, ← mul_add,
        add_comm, hab j hj, mul_one]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`
in at most one way, where `degree (r i) < degree (g i)` and the denominator cancels formally.
See `eq_quo_mul_prod_add_sum_rem_mul_prod` for the existence of such a representation. -/
/-
**Polynomial.quo_mul_prod_add_sum_rem_mul_prod_unique** 是 Mathlib 中的一个定理，位于命名空间 
`Polynomial`。
形式化陈述：quo_mul_prod_add_sum_rem_mul_prod_unique {ι : Type*} [DecidableEq ι] {s : 
Finset ι} {g : ι -> R[X]} (hg : forall i in s, (g i).Monic) (hgg : Set.Pairwise 
s fun i j => IsCoprime (g i) (g j)) {q₁ q₂ : R[X]} {r₁ r₂ : ι -> R[X]} (hr₁ : fo
rall i in s, (r₁ i).degree < (g i).degree) (hr₂ : forall i in s, (r₂ i).degree <
 (g i).degree) (hf : q₁ * (∏ i in s, g i) + ∑ i in s, r₁ i * (∏ k in s.erase i, 
g k) = q₂ * (∏ i in s, g i) + ∑ i in s, r₂ i * (∏ k in s.erase i, g k)) : q₁ = q
₂ ∧ forall i in s, r₁ i = 
参数：hg : forall i in s, (g i).Monic；hgg : Set.Pairwise s fun i j => IsCoprime (g 
i) (g j)；hr₁ : forall i in s, (r₁ i).degree < (g i).degree；hr₂ : forall i in s, 
(r₂ i).degree < (g i).degree；hf : q₁ * (∏ i in s, g i) + ∑ i in s, r₁ i * (∏ k i
n s.erase i, g k) = q₂ * (∏ i in s, g i) + ∑ i in s, r₂ i * (∏ k in s.erase i, g
 k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.erase_eq_of_notMem`：erase_eq_of_notMem {a : α} {s : Finset α} (h 
: a ∉ s) : erase s a = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.prod_cons`：prod_cons (h : a ∉ s) : ∏ x in cons a s h, f x = f a *
 ∏ x in s, f x
· 使用定理 `IsCoprime.mul_right_iff`：IsCoprime.mul_right_iff : IsCoprime x (y * z) ↔
 IsCoprime x y ∧ IsCoprime x z
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.cons.congr_simp`：∀ {α : Type u_1} (a a_1 : α) (e_a : a = a_1) (s 
s_1 : Finset α) (e_s : s = s_1) (h : a ∉ s),   Finset.cons a s h = Finset.cons a
_1 s_1 ⋯
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Finset.mem_cons_of_mem`：mem_cons_of_mem {a b : α} {s : Finset α} {hb : b
 ∉ s} (ha : a in s) : a in cons b s hb
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
（共 90 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `
s`.
Then `f` can be written in the form `(∏ i ∈ s, g i) * (q + ∑ i ∈ s, r i / g i)`
in at most one way, where `degree (r i) < degree (g i)` and the denominator canc
els formally.
See `eq_quo_mul_prod_add_sum_rem_mul_prod` for the existence of such a represent
ation.
-/
theorem quo_mul_prod_add_sum_rem_mul_prod_unique {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    {q₁ q₂ : R[X]} {r₁ r₂ : ι → R[X]}
    (hr₁ : ∀ i ∈ s, (r₁ i).degree < (g i).degree) (hr₂ : ∀ i ∈ s, (r₂ i).degree < (g i).degree)
    (hf : q₁ * (∏ i ∈ s, g i) + ∑ i ∈ s, r₁ i * (∏ k ∈ s.erase i, g k) =
      q₂ * (∏ i ∈ s, g i) + ∑ i ∈ s, r₂ i * (∏ k ∈ s.erase i, g k)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  induction s using Finset.cons_induction with
  | empty => simpa using hf
  | cons i s hi ih =>
    rw [Finset.forall_mem_cons] at hg hr₁ hr₂
    have cop : IsCoprime (g i) (∏ i ∈ s, g i) := by
      clear *-hgg
      induction s using Finset.cons_induction with
      | empty => simp [isCoprime_one_right]
      | cons j s hj ih =>
        rw [Finset.prod_cons, IsCoprime.mul_right_iff]
        refine ⟨hgg (by simp) (by simp) fun hij => hi (by simp [hij]), ih ?_ ?_⟩
        · exact mt Finset.mem_cons_of_mem hi
        · exact hgg.mono (SetLike.coe_mono (Finset.cons_subset_cons.2 (Finset.subset_cons hj)))
    rw [Finset.prod_cons, Finset.sum_cons, Finset.sum_cons, Finset.erase_cons] at hf
    have hjs {j : ι} (hj : j ∈ s) : i ≠ j := fun hij => hi (hij ▸ hj)
    simp +contextual only [Finset.erase_cons_of_ne hi (hjs _),
      Finset.prod_cons, ← mul_left_comm (g i), ← Finset.mul_sum] at hf
    rw [add_left_comm, ← mul_add, add_left_comm, ← mul_add] at hf
    rw [← sub_eq_zero, add_sub_add_comm, ← sub_mul, ← mul_sub,
      ← neg_sub, neg_mul, neg_add_eq_sub, sub_eq_zero] at hf
    have hgid : g i ∣ r₂ i - r₁ i := cop.dvd_of_dvd_mul_right (hf ▸ dvd_mul_right _ _)
    rw [add_sub_add_comm, ← sub_mul, mul_add, ← mul_assoc,
      ← eq_sub_iff_add_eq', ← sub_mul, ← Finset.sum_sub_distrib] at hf
    simp only [← sub_mul] at hf
    have hpgd : ∏ i ∈ s, g i ∣ _ := cop.symm.dvd_of_dvd_mul_left (hf.symm ▸ dvd_mul_left _ _)
    have hdr : (r₂ i - r₁ i).degree < (g i).degree :=
      (degree_sub_le (r₂ i) (r₁ i)).trans_lt (max_lt hr₂.1 hr₁.1)
    have hr0 : r₂ i - r₁ i = 0 := (hg.1.not_dvd_of_degree_lt · hdr).mtr hgid
    have hpm : (∏ i ∈ s, g i).Monic := monic_prod_of_monic s g hg.2
    have hdp : (∑ i ∈ s, (r₁ i - r₂ i) * ∏ k ∈ s.erase i, g k).degree < (∏ i ∈ s, g i).degree := by
      refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 ?_)
      · rw [bot_lt_iff_ne_bot, degree_ne_bot]
        exact hpm.ne_zero_of_polynomial_ne fun h : r₂ i - r₁ i = g i => lt_irrefl _ (h ▸ hdr)
      · intro j hj
        rw [← Finset.mul_prod_erase s g hj, mul_comm (g j), (hg.2 j hj).degree_mul]
        refine (degree_mul_le (r₁ j - r₂ j) (∏ k ∈ s.erase j, g k)).trans_lt ?_
        have dnb : (∏ k ∈ s.erase j, g k).degree ≠ ⊥ := by
          rw [degree_ne_bot]
          exact (monic_prod_of_monic _ g
            fun j hj => hg.2 j (Finset.mem_of_mem_erase hj)).ne_zero_of_polynomial_ne
            fun h : r₂ i - r₁ i = g i => lt_irrefl _ (h ▸ hdr)
        rw [add_comm, WithBot.add_lt_add_iff_left dnb]
        exact (degree_sub_le (r₁ j) (r₂ j)).trans_lt (max_lt (hr₁.2 j hj) (hr₂.2 j hj))
    have hp0 : ∑ i ∈ s, (r₁ i - r₂ i) * ∏ k ∈ s.erase i, g k = 0 :=
      (hpm.not_dvd_of_degree_lt · hdp).mtr hpgd
    rw [hr0, hp0, mul_zero, zero_sub, neg_mul, eq_comm, neg_eq_zero,
      ← mul_rotate, (hpm.mul hg.1).mul_right_eq_zero_iff] at hf
    simp only [sub_mul, Finset.sum_sub_distrib] at hp0
    rw [sub_eq_zero] at hf hr0 hp0
    obtain ⟨-, hrr⟩ := ih hg.2 (hgg.mono (SetLike.coe_mono (Finset.subset_cons hi)))
      hr₁.2 hr₂.2 congr($hf * ∏ i ∈ s, g i + $hp0)
    exact ⟨hf, (Finset.forall_mem_cons hi (fun j => r₁ j = r₂ j)).2 ⟨hr0.symm, hrr⟩⟩

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`, where
`degree (r i j) < degree (g i)` and the denominator cancels formally.
See `quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique` for the uniqueness of this representation. -/
/-
**Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow** 是 Mathlib 中的一个定理，位于命
名空间 `Polynomial`。
形式化陈述：eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow [Nontrivial R] {ι : Type*} [D
ecidableEq ι] {s : Finset ι} (f : R[X]) {g : ι -> R[X]} (hg : forall i in s, (g 
i).Monic) (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) (n : ι -> Nat)
 : exists (q : R[X]) (r : (i : ι) -> Fin (n i) -> R[X]), (forall i in s, forall 
j, (r i j).degree < (g i).degree) ∧ f = q * (∏ i in s, g i ^ n i) + ∑ i in s, ∑ 
j, r i j * g i ^ j.1 * ∏ k in s.erase i, g k ^ n k
参数：f : R[X]；hg : forall i in s, (g i).Monic；hgg : Set.Pairwise s fun i j => IsCo
prime (g i) (g j)；n : ι -> Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_quo_mul_prod_add_sum_rem_mul_prod`：eq_quo_mul_prod_add_sum
_rem_mul_prod [Nontrivial R] {ι : Type*} [DecidableEq ι] {s : Finset ι} (f : R[X
]) {g : ι -> R[X]} (hg : forall i in …
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Set.Pairwise.mono'`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, r
 ≤ p → s.Pairwise r → s.Pairwise p
· 使用定理 `IsCoprime.pow`：IsCoprime.pow (H : IsCoprime x y) : IsCoprime (x ^ m) (y 
^ n)
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Polynomial.eq_quo_mul_pow_add_sum_rem_mul_pow`：eq_quo_mul_pow_add_sum_re
m_mul_pow [Nontrivial R] (f : R[X]) {g : R[X]} (hg : g.Monic) (n : Nat) : exists
 (q : R[X]) (r : Fin n -> R[X]), (f…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `
s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the
 form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`, 
where
`degree (r i j) < degree (g i)` and the denominator cancels formally.
See `quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique` for the uniqueness of thi
s representation.
-/
theorem eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow [Nontrivial R] {ι : Type*} [DecidableEq ι]
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) (n : ι → ℕ) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      f = q * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k := by
  obtain ⟨q, r, -, hf⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod f
    (fun i hi => (hg i hi).pow (n i))
    (hgg.mono' fun i j hij => hij.pow)
  have hc (i : ι) : ∃ (q' : R[X]) (r' : Fin (n i) → R[X]), i ∈ s →
      (∀ j, (r' j).degree < (g i).degree) ∧
      r i = q' * g i ^ (n i) + ∑ j, r' j * g i ^ j.1 :=
    if hi : i ∈ s then
      (eq_quo_mul_pow_add_sum_rem_mul_pow (r i) (hg i hi) (n i)).elim
        fun q' h => h.elim fun r' h => ⟨q', r', fun _ => h⟩
    else
      ⟨0, fun _ => 0, hi.elim⟩
  choose q' r' hr' hr using hc
  refine ⟨q + ∑ i ∈ s, q' i, r', hr', hf.trans ?_⟩
  rw [add_mul, add_assoc, add_right_inj, Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [← Finset.mul_prod_erase s _ hi, hr i hi, add_mul, Finset.sum_mul, mul_assoc]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`
in at most one way, where `degree (r i j) < degree (g i)` and the denominator cancels formally.
See `eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow` for the existence of such a representation. -/
/-
**Polynomial.quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique** 是 Mathlib 中的一个定理
，位于命名空间 `Polynomial`。
形式化陈述：quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique {ι : Type*} [DecidableEq 
ι] {s : Finset ι} {g : ι -> R[X]} (hg : forall i in s, (g i).Monic) (hgg : Set.P
airwise s fun i j => IsCoprime (g i) (g j)) {n : ι -> Nat} {q₁ q₂ : R[X]} {r₁ r₂
 : (i : ι) -> Fin (n i) -> R[X]} (hr₁ : forall i in s, forall j, (r₁ i j).degree
 < (g i).degree) (hr₂ : forall i in s, forall j, (r₂ i j).degree < (g i).degree)
 (hf : q₁ * (∏ i in s, g i ^ n i) + ∑ i in s, ∑ j, r₁ i j * g i ^ j.1 * ∏ k in s
.erase i, g k ^ n k = q₂ *
参数：hg : forall i in s, (g i).Monic；hgg : Set.Pairwise s fun i j => IsCoprime (g 
i) (g j)；i : ι；n i；hr₁ : forall i in s, forall j, (r₁ i j).degree < (g i).degree
；hr₂ : forall i in s, forall j, (r₂ i j).degree < (g i).degree。
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
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Polynomial.degree_ne_bot`：degree_ne_bot : degree p != ⊥ ↔ p != 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.Monic.natDegree_pow`：natDegree_pow (hp : p.Monic) (n : Nat) :
 (p ^ n).natDegree = n * p.natDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
· 使用引理 `Fin.neZero`：neZero {n : Nat} (i : Fin n) : NeZero n
· 使用定理 `Nat.add_one_mul`：∀ (n m : ℕ), (n + 1) * m = n * m + m
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `
s`,
and for each `g i` let `n i` be a natural number. Then `f` can be written in the
 form
`(∏ i ∈ s, g i ^ n i) * (q + ∑ i ∈ s, ∑ j : Fin (n i), r i j / g i ^ (j + 1))`
in at most one way, where `degree (r i j) < degree (g i)` and the denominator ca
ncels formally.
See `eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow` for the existence of such a r
epresentation.
-/
theorem quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) {n : ι → ℕ}
    {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) → Fin (n i) → R[X]}
    (hr₁ : ∀ i ∈ s, ∀ j, (r₁ i j).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, ∀ j, (r₂ i j).degree < (g i).degree)
    (hf : q₁ * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r₁ i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k =
      q₂ * (∏ i ∈ s, g i ^ n i) +
        ∑ i ∈ s, ∑ j, r₂ i j * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  nontriviality R
  simp only [← Finset.sum_mul] at hf
  have hrd {r : (i : ι) → Fin (n i) → R[X]} (hr : ∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree)
      (i : ι) (hi : i ∈ s) : (∑ j, r i j * g i ^ j.1).degree < (g i ^ n i).degree := by
    refine (degree_sum_le _ _).trans_lt ((Finset.sup_lt_iff ?_).2 fun j _ => ?_)
    · rw [bot_lt_iff_ne_bot, degree_ne_bot]
      exact ((hg i hi).pow (n i)).ne_zero
    · refine (degree_mul_le _ _).trans_lt ?_
      rw [degree_eq_natDegree ((hg i hi).pow j.1).ne_zero, (hg i hi).natDegree_pow,
        degree_eq_natDegree ((hg i hi).pow (n i)).ne_zero, (hg i hi).natDegree_pow]
      conv_rhs => rw [← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 j.neZero.ne)]
      rw [Nat.add_one_mul, Nat.add_comm, Nat.cast_add, ← degree_eq_natDegree (hg i hi).ne_zero]
      refine WithBot.add_lt_add_of_lt_of_le (WithBot.natCast_ne_bot _) (hr i hi j) ?_
      exact Nat.cast_le.2 (Nat.mul_le_mul_right _ (Nat.le_sub_one_of_lt j.isLt))
  obtain ⟨hq, hr⟩ := quo_mul_prod_add_sum_rem_mul_prod_unique
    (fun i hi => (hg i hi).pow (n i)) (hgg.imp fun i j hij => hij.pow) (hrd hr₁) (hrd hr₂) hf
  refine ⟨hq, fun i hi => ?_⟩
  exact (quo_mul_pow_add_sum_rem_mul_pow_unique (hg i hi) (hr₁ i hi) (hr₂ i hi)
    (congrArg (0 * g i ^ n i + ·) (hr i hi))).2

end ManyDenominators

end Mul

section Div
variable {K : Type*} [CommRing K] [Algebra R[X] K]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`, where `degree (r i j) < degree (g i)`.
See `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` for the
uniqueness of this representation. -/
/-
**Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse** 是 Mathlib
 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse [Nontrivial R] {ι 
: Type*} {s : Finset ι} (f : R[X]) {g : ι -> R[X]} (hg : forall i in s, (g i).Mo
nic) (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j)) (n : ι -> Nat) {gi 
: ι -> K} (hgi : forall i in s, gi i * algebraMap R[X] K (g i) = 1) : exists (q 
: R[X]) (r : (i : ι) -> Fin (n i) -> R[X]), (forall i in s, forall j, (r i j).de
gree < (g i).degree) ∧ algebraMap R[X] K f * ∏ i in s, gi i ^ n i = algebraMap R
[X] K q + ∑ i in s, ∑ j, a
参数：f : R[X]；hg : forall i in s, (g i).Monic；hgg : Set.Pairwise s fun i j => IsCo
prime (g i) (g j)；n : ι -> Nat；hgi : forall i in s, gi i * algebraMap R[X] K (g 
i) = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow`：eq_quo_mul_prod
_pow_add_sum_rem_mul_prod_pow [Nontrivial R] {ι : Type*} [DecidableEq ι] {s : Fi
nset ι} (f : R[X]) {g : ι -> R[X]} (hg : fora…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `
s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`, where `degree (r i j) < 
degree (g i)`.
See `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` for the
uniqueness of this representation.
-/
theorem mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse [Nontrivial R] {ι : Type*}
    {s : Finset ι} (f : R[X]) {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    (n : ι → ℕ) {gi : ι → K} (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1) :
    ∃ (q : R[X]) (r : (i : ι) → Fin (n i) → R[X]),
      (∀ i ∈ s, ∀ j, (r i j).degree < (g i).degree) ∧
      algebraMap R[X] K f * ∏ i ∈ s, gi i ^ n i =
        algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
          algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1) := by
  classical
  obtain ⟨q, r, hr, hf⟩ := eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow f hg hgg n
  refine ⟨q, fun i j => r i j.rev, fun i hi j => hr i hi j.rev, ?_⟩
  rw [hf, map_add, map_mul, map_prod, add_mul, mul_assoc, ← Finset.prod_mul_distrib]
  have hc (x : ι) (hx : x ∈ s) : (algebraMap R[X] K) (g x ^ n x) * gi x ^ n x = 1 := by
    rw [map_pow, ← mul_pow, mul_comm, hgi x hx, one_pow]
  rw [Finset.prod_congr rfl hc, Finset.prod_const_one,
    mul_one, add_right_inj, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [map_sum, Finset.sum_mul, ← Equiv.sum_comp Fin.revPerm]
  refine Fintype.sum_congr _ _ fun j => ?_
  rw [Fin.revPerm_apply, map_mul, map_prod, ← Finset.prod_erase_mul s _ hi,
    ← mul_rotate', mul_assoc, ← Finset.prod_mul_distrib,
    Finset.prod_congr rfl fun x hx => hc x (Finset.mem_of_mem_erase hx),
    Finset.prod_const_one, mul_one, map_mul, map_pow, mul_left_comm]
  refine congrArg (_ * ·) ?_
  rw [← mul_one (gi i ^ (j.1 + 1)), ← @one_pow K _ j.rev, ← hgi i hi,
    mul_pow, ← mul_assoc, ← pow_add, Fin.val_rev, Nat.add_sub_cancel' (by lia)]

/-- Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`
in at most one way, where `degree (r i j) < degree (g i)`.
See `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` for the
existence of such a representation. -/
/-
**Polynomial.quo_add_sum_rem_mul_pow_inverse_unique** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：quo_add_sum_rem_mul_pow_inverse_unique [FaithfulSMul R[X] K] {ι : Type*} {
s : Finset ι} {g : ι -> R[X]} (hg : forall i in s, (g i).Monic) (hgg : Set.Pairw
ise s fun i j => IsCoprime (g i) (g j)) {n : ι -> Nat} {gi : ι -> K} (hgi : fora
ll i in s, gi i * algebraMap R[X] K (g i) = 1) {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) -
> Fin (n i) -> R[X]} (hr₁ : forall i in s, forall j, (r₁ i j).degree < (g i).deg
ree) (hr₂ : forall i in s, forall j, (r₂ i j).degree < (g i).degree) (hf : algeb
raMap R[X] K q₁ + ∑ i in s
参数：hg : forall i in s, (g i).Monic；hgg : Set.Pairwise s fun i j => IsCoprime (g 
i) (g j)；hgi : forall i in s, gi i * algebraMap R[X] K (g i) = 1；i : ι；n i；hr₁ :
 forall i in s, forall j, (r₁ i j).degree < (g i).degree；hr₂ : forall i in s, fo
rall j, (r₂ i j).degree < (g i).degree。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Fintype.sum_congr`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α] [i
nst_1 : AddCommMonoid M] (f g : α → M),   (∀ (a : α), f a = g a) → ∑ a, f a = ∑ 
a, g a
· 使用定理 `Fin.revPerm_apply`：∀ {n : ℕ} (i : Fin n), Fin.revPerm i = i.rev
· 使用定理 `Finset.mul_prod_erase`：mul_prod_erase [DecidableEq ι] (s : Finset ι) (f 
: ι -> M) {a : ι} (h : a in s) : (f a * ∏ x in s.erase a, f x) = ∏ x in s, f x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
Let `R` be a commutative ring and `f : R[X]`. Let `s` be a finite index set.
Let `g i` be a collection of monic and pairwise coprime polynomials indexed by `
s`,
and for each `g i` let `n i` be a natural number.
Let `K` be an algebra over `R[X]` containing inverses `gi i` for each `g i`.
Then a fraction of the form `f * ∏ i ∈ s, gi i ^ n i` can be rewritten as
`q + ∑ i ∈ s, ∑ j : Fin (n i), r i j * gi i ^ (j + 1)`
in at most one way, where `degree (r i j) < degree (g i)`.
See `mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse` for the
existence of such a representation.
-/
theorem quo_add_sum_rem_mul_pow_inverse_unique [FaithfulSMul R[X] K] {ι : Type*}
    {s : Finset ι} {g : ι → R[X]} (hg : ∀ i ∈ s, (g i).Monic)
    (hgg : Set.Pairwise s fun i j => IsCoprime (g i) (g j))
    {n : ι → ℕ} {gi : ι → K} (hgi : ∀ i ∈ s, gi i * algebraMap R[X] K (g i) = 1)
    {q₁ q₂ : R[X]} {r₁ r₂ : (i : ι) → Fin (n i) → R[X]}
    (hr₁ : ∀ i ∈ s, ∀ j, (r₁ i j).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, ∀ j, (r₂ i j).degree < (g i).degree)
    (hf : algebraMap R[X] K q₁ + ∑ i ∈ s, ∑ j, algebraMap R[X] K (r₁ i j) * gi i ^ (j.1 + 1) =
      algebraMap R[X] K q₂ + ∑ i ∈ s, ∑ j, algebraMap R[X] K (r₂ i j) * gi i ^ (j.1 + 1)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  classical
  suffices hff : ∀ {q : R[X]} {r : (i : ι) → Fin (n i) → R[X]},
      (algebraMap R[X] K q + ∑ i ∈ s, ∑ j,
        algebraMap R[X] K (r i j) * gi i ^ (j.1 + 1)) * ∏ i ∈ s, algebraMap R[X] K (g i) ^ n i =
      algebraMap R[X] K (q * ∏ i ∈ s, g i ^ n i + ∑ i ∈ s,
        ∑ j : Fin (n i), r i j.rev * g i ^ j.1 * ∏ k ∈ s.erase i, g k ^ n k) by
    apply_fun (· * ∏ i ∈ s, algebraMap R[X] K (g i) ^ n i) at hf
    rw [hff, hff, (FaithfulSMul.algebraMap_injective R[X] K).eq_iff] at hf
    obtain ⟨hq, hr⟩ := quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique hg hgg
      (fun i hi j => hr₁ i hi j.rev) (fun i hi j => hr₂ i hi j.rev) hf
    exact ⟨hq, fun i hi => funext fun j => j.rev_rev ▸ congrFun (hr i hi) j.rev⟩
  intro q r
  simp_rw [add_mul, Finset.sum_mul, map_add, map_sum, map_mul, map_prod, map_pow]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i hi => ?_)
  refine (Equiv.sum_comp Fin.revPerm _).symm.trans (Fintype.sum_congr _ _ fun j => ?_)
  rw [Fin.revPerm_apply, ← Finset.mul_prod_erase s _ hi, ← mul_assoc,
    mul_assoc (algebraMap R[X] K (r i j.rev))]
  refine congrArg (algebraMap R[X] K (r i j.rev) * · * _) ?_
  rw [← mul_one (gi i ^ (j.rev.1 + 1)), ← @one_pow K _ j, ← hgi i hi,
    mul_pow, ← mul_assoc, ← pow_add, Fin.val_rev, Nat.add_right_comm, Nat.add_assoc,
    Nat.sub_add_cancel (by lia), mul_right_comm, ← mul_pow, hgi i hi, one_pow, one_mul]

end Div

section Field

variable (K : Type*) [Field K] [Algebra R[X] K] [FaithfulSMul R[X] K]

section NDenominators

open algebraMap

/-- Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containing `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i`, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise coprime.
See `quo_add_sum_rem_div_unique` for the uniqueness of this representation. -/
/-
**Polynomial.div_prod_eq_quo_add_sum_rem_div** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：div_prod_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι -> R[X]} {s 
: Finset ι} (hg : forall i in s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j =>
 IsCoprime (g i) (g j)) : exists (q : R[X]) (r : ι -> R[X]), (forall i in s, (r 
i).degree < (g i).degree) ∧ ((↑f : K) / ∏ i in s, ↑(g i)) = ↑q + ∑ i in s, (r i 
: K) / (g i : K)
参数：f : R[X]；hg : forall i in s, (g i).Monic；hcop : Set.Pairwise ↑s fun i j => Is
Coprime (g i) (g j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse`：mul_
prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse [Nontrivial R] {ι : Type*} {
s : Finset ι} (f : R[X]) {g : ι -> R[X]} (hg : forall i …
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_inv_distrib`：prod_inv_distrib (f : ι -> G) : (∏ x in s, (f x
)⁻¹) = (∏ x in s, f x)⁻¹
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0

--- 原说明 ---
Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containi
ng `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i`, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise co
prime.
See `quo_add_sum_rem_div_unique` for the uniqueness of this representation.
-/
theorem div_prod_eq_quo_add_sum_rem_div (f : R[X]) {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j)) :
    ∃ (q : R[X]) (r : ι → R[X]),
      (∀ i ∈ s, (r i).degree < (g i).degree) ∧
        ((↑f : K) / ∏ i ∈ s, ↑(g i)) = ↑q + ∑ i ∈ s, (r i : K) / (g i : K) := by
  have : Nontrivial R :=
    have : Nontrivial R[X] := Module.nontrivial R[X] K
    Module.nontrivial R R[X]
  have hgi (i : ι) (hi : i ∈ s) : (algebraMap R[X] K (g i))⁻¹ * algebraMap R[X] K (g i) = 1 :=
    inv_mul_cancel₀ (by simpa using (hg i hi).ne_zero)
  obtain ⟨q, r, hr, hf⟩ := mul_prod_pow_inverse_eq_quo_add_sum_rem_mul_pow_inverse
    f hg hcop (fun _ => 1) hgi
  refine ⟨q, fun i => r i 0, fun i hi => hr i hi 0, ?_⟩
  simp_rw [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one, Finset.prod_inv_distrib] at hf
  simp_rw [Algebra.cast, div_eq_mul_inv]
  exact hf

@[deprecated (since := "2026-02-08")]
alias _root_.div_eq_quo_add_sum_rem_div := div_prod_eq_quo_add_sum_rem_div

/-- Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containing `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i` in at most one way, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise coprime.
See `div_prod_eq_quo_add_sum_rem_div` for the existence of such a representation. -/
/-
**Polynomial.quo_add_sum_rem_div_unique** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：quo_add_sum_rem_div_unique {ι : Type*} {g : ι -> R[X]} {s : Finset ι} (hg 
: forall i in s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i)
 (g j)) {q₁ q₂ : R[X]} {r₁ r₂ : ι -> R[X]} (hr₁ : forall i in s, (r₁ i).degree <
 (g i).degree) (hr₂ : forall i in s, (r₂ i).degree < (g i).degree) (hf : ↑q₁ + ∑
 i in s, (r₁ i : K) / (g i : K) = ↑q₂ + ∑ i in s, (r₂ i : K) / (g i : K)) : q₁ =
 q₂ ∧ forall i in s, r₁ i = r₂ i
参数：hg : forall i in s, (g i).Monic；hcop : Set.Pairwise ↑s fun i j => IsCoprime (
g i) (g j)；hr₁ : forall i in s, (r₁ i).degree < (g i).degree；hr₂ : forall i in s
, (r₂ i).degree < (g i).degree；hf : ↑q₁ + ∑ i in s, (r₁ i : K) / (g i : K) = ↑q₂
 + ∑ i in s, (r₂ i : K) / (g i : K)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZer
o R] [Nontrivial M] [inst_2 : Zero M] [MulActionWithZero R M],   Nontrivial R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.quo_add_sum_rem_mul_pow_inverse_unique`：quo_add_sum_rem_mul_p
ow_inverse_unique [FaithfulSMul R[X] K] {ι : Type*} {s : Finset ι} {g : ι -> R[X
]} (hg : forall i in s, (g i).Monic) (h…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Fin.sum_univ_one`：∀ {M : Type u_2} [inst : AddCommMonoid M] (f : Fin 1 →
 M), ∑ i, f i = f 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a

--- 原说明 ---
Let `R` be an integral domain and `f : R[X]`. Let `s` be a finite index set.
Then a fraction of the form `f / ∏ i ∈ s, g i` evaluated in a field `K` containi
ng `R[X]`
can be rewritten as `q + ∑ i ∈ s, r i / g i` in at most one way, where
`degree (r i) < degree (g i)`, provided that the `g i` are monic and pairwise co
prime.
See `div_prod_eq_quo_add_sum_rem_div` for the existence of such a representation
.
-/
theorem quo_add_sum_rem_div_unique {ι : Type*} {g : ι → R[X]} {s : Finset ι}
    (hg : ∀ i ∈ s, (g i).Monic) (hcop : Set.Pairwise ↑s fun i j => IsCoprime (g i) (g j))
    {q₁ q₂ : R[X]} {r₁ r₂ : ι → R[X]}
    (hr₁ : ∀ i ∈ s, (r₁ i).degree < (g i).degree)
    (hr₂ : ∀ i ∈ s, (r₂ i).degree < (g i).degree)
    (hf : ↑q₁ + ∑ i ∈ s, (r₁ i : K) / (g i : K) = ↑q₂ + ∑ i ∈ s, (r₂ i : K) / (g i : K)) :
    q₁ = q₂ ∧ ∀ i ∈ s, r₁ i = r₂ i := by
  have : Nontrivial R :=
    have : Nontrivial R[X] := Module.nontrivial R[X] K
    Module.nontrivial R R[X]
  have hgi (i : ι) (hi : i ∈ s) : (algebraMap R[X] K (g i))⁻¹ * algebraMap R[X] K (g i) = 1 :=
    inv_mul_cancel₀ (by simpa using (hg i hi).ne_zero)
  refine (quo_add_sum_rem_mul_pow_inverse_unique (n := fun _ => 1)
      hg hcop hgi (fun i hi _ => hr₁ i hi) (fun i hi _ => hr₂ i hi) ?_).imp_right
      fun h i hi => congrFun (h i hi) 0
  simp_rw [Fin.sum_univ_one, Fin.val_zero, zero_add, pow_one, ← div_eq_mul_inv]
  exact hf

end NDenominators

section TwoDenominators

open scoped algebraMap

/-- Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic and coprime.
Then `∃ q, r₁, r₂ : R[X]` such that `f / (g₁ * g₂) = q + r₁ / g₁ + r₂ / g₂` and
`degree rᵢ < degree gᵢ`, where the equality is taken in a field `K` containing `R[X]`.
See `quo_add_rem_div_add_rem_div_unique` for the uniqueness of this representation. -/
/-
**Polynomial.div_eq_quo_add_rem_div_add_rem_div** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]} (hg₁ : g₁.Mon
ic) (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂) : exists q r₁ r₂ : R[X], r₁.de
gree < g₁.degree ∧ r₂.degree < g₂.degree ∧ (f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g
₁ + ↑r₂ / ↑g₂
参数：f : R[X]；hg₁ : g₁.Monic；hg₂ : g₂.Monic；hcoprime : IsCoprime g₁ g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.true_eq`：∀ (b : Bool), (true = b) = (b = true)
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Polynomial.div_prod_eq_quo_add_sum_rem_div`：div_prod_eq_quo_add_sum_rem_
div (f : R[X]) {ι : Type*} {g : ι -> R[X]} {s : Finset ι} (hg : forall i in s, (
g i).Monic) (hcop : Set.Pairwise…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.prod_singleton`：prod_singleton (f : ι -> M) (a : ι) : ∏ x in sing
leton a, f x = f a
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a

--- 原说明 ---
Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic
 and coprime.
Then `∃ q, r₁, r₂ : R[X]` such that `f / (g₁ * g₂) = q + r₁ / g₁ + r₂ / g₂` and
`degree rᵢ < degree gᵢ`, where the equality is taken in a field `K` containing `
R[X]`.
See `quo_add_rem_div_add_rem_div_unique` for the uniqueness of this representati
on.
-/
theorem div_eq_quo_add_rem_div_add_rem_div (f : R[X]) {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂) :
    ∃ q r₁ r₂ : R[X],
      r₁.degree < g₁.degree ∧
        r₂.degree < g₂.degree ∧ (f : K) / (↑g₁ * ↑g₂) = ↑q + ↑r₁ / ↑g₁ + ↑r₂ / ↑g₂ := by
  let g : Bool → R[X] := Bool.rec g₂ g₁
  have hg (i : Bool) (_ : i ∈ Finset.univ) : (g i).Monic := Bool.rec hg₂ hg₁ i
  have hcoprime : Set.Pairwise (Finset.univ : Finset Bool) fun i j => IsCoprime (g i) (g j) := by
    simp [g, Set.pairwise_insert, hcoprime, hcoprime.symm]
  obtain ⟨q, r, hr, hf⟩ := div_prod_eq_quo_add_sum_rem_div K f hg hcoprime
  refine ⟨q, r true, r false, hr true (Finset.mem_univ true), hr false (Finset.mem_univ false), ?_⟩
  simpa [g, add_assoc] using hf

@[deprecated (since := "2026-02-08")]
alias _root_.div_eq_quo_add_rem_div_add_rem_div := div_eq_quo_add_rem_div_add_rem_div

/-- Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic and coprime.
Then the representation of `f / (g₁ * g₂)` as `q + r₁ / g₁ + r₂ / g₂` for `q r₁ r₂ : R[X]` and
`degree rᵢ < degree gᵢ` is unique, where the equality is taken in a field `K` containing `R[X]`.
See `div_eq_quo_add_rem_div_add_rem_div` for the existence of such a representation. -/
/-
**Polynomial.quo_add_rem_div_add_rem_div_unique** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：quo_add_rem_div_add_rem_div_unique {g₁ g₂ : R[X]} (hg₁ : g₁.Monic) (hg₂ : 
g₂.Monic) (hcoprime : IsCoprime g₁ g₂) {q₁ q₂ r₁₁ r₁₂ r₂₁ r₂₂ : R[X]} (hr₁₁ : r₁
₁.degree < g₁.degree) (hr₁₂ : r₁₂.degree < g₁.degree) (hr₂₁ : r₂₁.degree < g₂.de
gree) (hr₂₂ : r₂₂.degree < g₂.degree) (hf : (↑q₁ + ↑r₁₁ / ↑g₁ + ↑r₂₁ / ↑g₂ : K) 
= ↑q₂ + ↑r₁₂ / ↑g₁ + ↑r₂₂ / ↑g₂) : q₁ = q₂ ∧ r₁₁ = r₁₂ ∧ r₂₁ = r₂₂
参数：hg₁ : g₁.Monic；hg₂ : g₂.Monic；hcoprime : IsCoprime g₁ g₂；hr₁₁ : r₁₁.degree < 
g₁.degree；hr₁₂ : r₁₂.degree < g₁.degree；hr₂₁ : r₂₁.degree < g₂.degree；hr₂₂ : r₂₂
.degree < g₂.degree；hf : (↑q₁ + ↑r₁₁ / ↑g₁ + ↑r₂₁ / ↑g₂ : K) = ↑q₂ + ↑r₁₂ / ↑g₁ 
+ ↑r₂₂ / ↑g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Bool.true_eq`：∀ (b : Bool), (true = b) = (b = true)
· 使用定理 `Bool.not_eq_true`：∀ (b : Bool), (¬b = true) = (b = false)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsCoprime.symm`：IsCoprime.symm (H : IsCoprime x y) : IsCoprime y x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Polynomial.quo_add_sum_rem_div_unique`：quo_add_sum_rem_div_unique {ι : T
ype*} {g : ι -> R[X]} {s : Finset ι} (hg : forall i in s, (g i).Monic) (hcop : S
et.Pairwise ↑s fun i j => I…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Bool.true_eq_false`：(true = false) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)

--- 原说明 ---
Let `R` be an integral domain and `f, g₁, g₂ : R[X]`. Let `g₁` and `g₂` be monic
 and coprime.
Then the representation of `f / (g₁ * g₂)` as `q + r₁ / g₁ + r₂ / g₂` for `q r₁ 
r₂ : R[X]` and
`degree rᵢ < degree gᵢ` is unique, where the equality is taken in a field `K` co
ntaining `R[X]`.
See `div_eq_quo_add_rem_div_add_rem_div` for the existence of such a representat
ion.
-/
theorem quo_add_rem_div_add_rem_div_unique {g₁ g₂ : R[X]} (hg₁ : g₁.Monic)
    (hg₂ : g₂.Monic) (hcoprime : IsCoprime g₁ g₂)
    {q₁ q₂ r₁₁ r₁₂ r₂₁ r₂₂ : R[X]}
    (hr₁₁ : r₁₁.degree < g₁.degree) (hr₁₂ : r₁₂.degree < g₁.degree)
    (hr₂₁ : r₂₁.degree < g₂.degree) (hr₂₂ : r₂₂.degree < g₂.degree)
    (hf : (↑q₁ + ↑r₁₁ / ↑g₁ + ↑r₂₁ / ↑g₂ : K) = ↑q₂ + ↑r₁₂ / ↑g₁ + ↑r₂₂ / ↑g₂) :
    q₁ = q₂ ∧ r₁₁ = r₁₂ ∧ r₂₁ = r₂₂ := by
  let g : Bool → R[X] := Bool.rec g₂ g₁
  let r₁ : Bool → R[X] := Bool.rec r₂₁ r₁₁
  let r₂ : Bool → R[X] := Bool.rec r₂₂ r₁₂
  have hg (i : Bool) (_ : i ∈ Finset.univ) : (g i).Monic := Bool.rec hg₂ hg₁ i
  have hcoprime : Set.Pairwise (Finset.univ : Finset Bool) fun i j => IsCoprime (g i) (g j) := by
    simp [g, Set.pairwise_insert, hcoprime, hcoprime.symm]
  have hr₁ (i : Bool) (_ : i ∈ Finset.univ) : (r₁ i).degree < (g i).degree := Bool.rec hr₂₁ hr₁₁ i
  have hr₂ (i : Bool) (_ : i ∈ Finset.univ) : (r₂ i).degree < (g i).degree := Bool.rec hr₂₂ hr₁₂ i
  refine (quo_add_sum_rem_div_unique K hg hcoprime hr₁ hr₂ ?_).imp_right fun h =>
    ⟨h true (Finset.mem_univ true), h false (Finset.mem_univ false)⟩
  simpa [g, r₁, r₂, add_assoc] using hf

end TwoDenominators

end Field

end Polynomial

