/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Prime.Defs

/-!
# Mapping irreducible polynomials

## Main results

* `Monic.irreducible_of_irreducible_map`: we can prove a monic polynomial is irreducible
  by mapping it to another integral domain and checking for irreducibility there.
-/

public section

noncomputable section

open Finset AddMonoidAlgebra

open Polynomial

namespace Polynomial

universe u v w y

variable {R : Type u} {S : Type v} {T : Type w} {ι : Type y} {a b : R} {m n : ℕ}

section
variable [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] (φ : R →+* S)

/-- A polynomial over an integral domain `R` is irreducible if it is monic and
irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
/-
**Polynomial.Monic.irreducible_of_irreducible_map** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial.Monic`。
形式化陈述：∀ {R : Type u} {S : Type v} [inst : CommRing R] [IsDomain R] [inst_2 : Com
mRing S] [IsDomain S] (φ : R →+* S)   (f : Polynomial R), f.Monic → Irreducible 
(Polynomial.map φ f) → Irreducible f
参数：φ : R →+* S；f : Polynomial R；Polynomial.map φ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用引理 `Polynomial.isUnit_of_isUnit_leadingCoeff_of_isUnit_map`：isUnit_of_isUnit
_leadingCoeff_of_isUnit_map (hf : IsUnit f.leadingCoeff) (H : IsUnit (map φ f)) 
: IsUnit f
· 使用定理 `IsUnit.of_mul_eq_one`：IsUnit.of_mul_eq_one [Monoid M] [IsDedekindFiniteM
onoid M] {a : M} (b : M) (h : a * b = 1) : IsUnit a
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.map_mul`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p q
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   Polynomial.map f (p * q)
 = Polyn…

--- 原说明 ---
A polynomial over an integral domain `R` is irreducible if it is monic and
irreducible after mapping into an integral domain `S`.

A special case of this lemma is that a polynomial over `ℤ` is irreducible if
it is monic and irreducible over `ℤ/pℤ` for some prime `p`.
-/
lemma Monic.irreducible_of_irreducible_map (f : R[X]) (h_mon : Monic f)
    (h_irr : Irreducible (f.map φ)) : Irreducible f := by
  refine ⟨h_irr.not_isUnit ∘ IsUnit.map (mapRingHom φ), fun a b h => ?_⟩
  dsimp [Monic] at h_mon
  have q := (leadingCoeff_mul a b).symm
  rw [← h, h_mon] at q
  refine (h_irr.isUnit_or_isUnit <|
    (congr_arg (Polynomial.map φ) h).trans (Polynomial.map_mul φ)).imp ?_ ?_ <;>
      apply isUnit_of_isUnit_leadingCoeff_of_isUnit_map <;>
    apply IsUnit.of_mul_eq_one
  · exact q
  · rw [mul_comm]
    exact q

end
end Polynomial

