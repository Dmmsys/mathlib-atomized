/-
Copyright (c) 2022 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.Polynomial.UnitTrinomial
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Irreducibility of unit trinomials

## TODO

Develop more theory (e.g., it suffices to check that `aeval z p ≠ 0` for `z = 0` and `z` a root of
unity).
-/

public section

namespace Polynomial.IsUnitTrinomial
variable {p : ℤ[X]}

/-- A unit trinomial is irreducible if it has no complex roots in common with its mirror. -/
/-
**Polynomial.IsUnitTrinomial.irreducible_of_coprime'** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial.IsUnitTrinomial`。
形式化陈述：irreducible_of_coprime' (hp : IsUnitTrinomial p) (h : forall z : Complex, 
¬(aeval z p = 0 ∧ aeval z (mirror p) = 0)) : Irreducible p
参数：hp : IsUnitTrinomial p；h : forall z : Complex, ¬(aeval z p = 0 ∧ aeval z (mir
ror p) = 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsUnitTrinomial.irreducible_of_coprime`：irreducible_of_coprim
e (hp : p.IsUnitTrinomial) (h : IsRelPrime p p.mirror) : Irreducible p
· 使用定理 `Complex.exists_root`：exists_root {f : Complex[X]} (hf : 0 < degree f) : 
exists z : Complex, IsRoot f z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_map_eq_of_injective`：degree_map_eq_of_injective {f : R
 ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).degree = p.d
egree
· 使用定理 `RingHom.injective_int`：RingHom.injective_int {α : Type*} [NonAssocRing α
] (f : Int ->+* α) [CharZero α] : Function.Injective f
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.IsUnitTrinomial.leadingCoeff_isUnit`：leadingCoeff_isUnit (hp 
: p.IsUnitTrinomial) : IsUnit p.leadingCoeff
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x

--- 原说明 ---
A unit trinomial is irreducible if it has no complex roots in common with its mi
rror.
-/
theorem irreducible_of_coprime' (hp : IsUnitTrinomial p)
    (h : ∀ z : ℂ, ¬(aeval z p = 0 ∧ aeval z (mirror p) = 0)) : Irreducible p := by
  refine hp.irreducible_of_coprime fun q hq hq' => ?_
  suffices ¬0 < q.natDegree by
    rcases hq with ⟨p, rfl⟩
    replace hp := hp.leadingCoeff_isUnit
    rw [leadingCoeff_mul] at hp
    replace hp := isUnit_of_mul_isUnit_left hp
    rw [not_lt, Nat.le_zero] at this
    rwa [eq_C_of_natDegree_eq_zero this, isUnit_C, ← this]
  intro hq''
  rw [natDegree_pos_iff_degree_pos] at hq''
  rw [← degree_map_eq_of_injective (algebraMap ℤ ℂ).injective_int] at hq''
  obtain ⟨z, hz⟩ := Complex.exists_root hq''
  rw [IsRoot, eval_map_algebraMap] at hz
  refine h z ⟨?_, ?_⟩
  · obtain ⟨g', hg'⟩ := hq
    rw [hg', aeval_mul, hz, zero_mul]
  · obtain ⟨g', hg'⟩ := hq'
    rw [hg', aeval_mul, hz, zero_mul]

end Polynomial.IsUnitTrinomial

