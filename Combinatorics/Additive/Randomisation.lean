/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Combinatorics.Additive.Dissociation

/-!
# Randomising by a function of dissociated support

This file proves that a function from a finite abelian group can be randomised by a function of
dissociated support.

Precisely, for `G` a finite abelian group and two functions `c : AddChar G ℂ → ℝ` and
`d : AddChar G ℂ → ℝ` such that `{ψ | d ψ ≠ 0}` is dissociated, the product of the `c ψ` over `ψ` is
the same as the average over `a` of the product of the `c ψ + Re (d ψ * ψ a)`.
-/

public section

open Finset
open scoped BigOperators ComplexConjugate

variable {G : Type*} [Fintype G] [AddCommGroup G] {p : ℕ}

/-- One can randomise by a function of dissociated support. -/
/-
**AddDissociated.randomisation** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AddDissociated.randomisation (c : AddChar G Complex -> Real) (d : AddChar 
G Complex -> Complex) (hcd : AddDissociated {ψ | d ψ != 0}) : 𝔼 a, ∏ ψ, (c ψ + (
d ψ * ψ a).re) = ∏ ψ, c ψ
参数：c : AddChar G Complex -> Real；d : AddChar G Complex -> Complex；hcd : AddDisso
ciated {ψ | d ψ != 0}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.ofReal_injective`：ofReal_injective : Function.Injective ((↑) : R
eal -> Complex)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `Complex.ofReal_expect`：ofReal_expect (f : α -> Real) : (𝔼 i in s, f i : 
Real) = 𝔼 i in s, (f i : Complex)
· 使用引理 `Finset.expect_congr`：expect_congr {t : Finset ι} (hst : s = t) (h : fora
ll i in t, f i = g i) : 𝔼 i in s, f i = 𝔼 i in t, g i
· 使用定理 `Complex.ofReal_prod`：ofReal_prod (f : α -> Real) : ((∏ i in s, f i : Rea
l) : Complex) = ∏ i in s, (f i : Complex)
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Complex.ofReal_add`：ofReal_add (r s : Real) : ((r + s : Real) : Complex)
 = r + s
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `Finset.expect_mul`：expect_mul [IsScalarTower Rat>=0 M M] (s : Finset ι) 
(f : ι -> M) (a : M) : (𝔼 i in s, f i) * a = 𝔼 i in s, f i * a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.re_eq_add_conj`：re_eq_add_conj (z : Complex) : (z.re : Complex) 
= (z + conj z) / 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fintype.sum_eq_single`：∀ {α : Type u_1} {M : Type u_4} [inst : Fintype α
] [inst_1 : AddCommMonoid M] {f : α → M} (a : α),   (∀ (x : α), x ≠ a → f x = 0)
 → ∑ x, f x…
· 使用定理 `mul_eq_zero_of_left`：mul_eq_zero_of_left {a : M₀} (h : a = 0) (b : M₀) :
 a * b = 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Finset.prod_div_distrib`：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x
 / g x = (∏ x in s, f x) / ∏ x in s, g x
· 使用定理 `Finset.prod_add`：prod_add (f g : ι -> R) (s : Finset ι) : ∏ i in s, (f i
 + g i) = ∑ t in s.powerset, (∏ i in t, f i) * ∏ i in s \ t, g i
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
（共 66 条，此处仅展示前 30 条）

--- 原说明 ---
One can randomise by a function of dissociated support.
-/
lemma AddDissociated.randomisation (c : AddChar G ℂ → ℝ) (d : AddChar G ℂ → ℂ)
    (hcd : AddDissociated {ψ | d ψ ≠ 0}) : 𝔼 a, ∏ ψ, (c ψ + (d ψ * ψ a).re) = ∏ ψ, c ψ := by
  refine Complex.ofReal_injective ?_
  push_cast
  calc
    _ = ∑ t, (𝔼 a, ∏ ψ ∈ t, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ ∈ tᶜ, (c ψ : ℂ) := by
        simp_rw [expect_mul, ← expect_sum_comm, ← Fintype.prod_add, add_comm,
          Complex.re_eq_add_conj]
    _ = (𝔼 a, ∏ ψ ∈ ∅, ((d ψ * ψ a) + conj (d ψ * ψ a)) / 2) * ∏ ψ ∈ ∅ᶜ, (c ψ : ℂ) :=
        Fintype.sum_eq_single ∅ fun t ht ↦ mul_eq_zero_of_left ?_ _
    _ = ∏ ψ, (c ψ : ℂ) := by simp
  simp only [map_mul, prod_div_distrib, prod_add, prod_const, ← expect_div, expect_sum_comm,
    div_eq_zero_iff, pow_eq_zero_iff', OfNat.ofNat_ne_zero, ne_eq, card_eq_zero,
    false_and, or_false]
  refine sum_eq_zero fun u _ ↦ ?_
  calc
    𝔼 a, (∏ ψ ∈ u, d ψ * ψ a) * ∏ ψ ∈ t \ u, conj (d ψ) * conj (ψ a)
      = ((∏ ψ ∈ u, d ψ) * ∏ ψ ∈ t \ u, conj (d ψ)) * 𝔼 a, (∑ ψ ∈ u, ψ - ∑ ψ ∈ t \ u, ψ) a := by
        simp_rw [mul_expect, AddChar.sub_apply, AddChar.sum_apply, mul_mul_mul_comm,
          ← prod_mul_distrib, AddChar.map_neg_eq_conj]
    _ = 0 := ?_
  rw [mul_eq_zero, AddChar.expect_eq_zero_iff_ne_zero, sub_ne_zero, or_iff_not_imp_left, ← Ne,
    mul_ne_zero_iff, prod_ne_zero_iff, prod_ne_zero_iff]
  exact fun h ↦ hcd.ne h.1 (by simpa only [map_ne_zero] using! h.2)
    (sdiff_ne_right.2 <| .inl ht).symm
