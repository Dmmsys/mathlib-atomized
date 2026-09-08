/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.RingTheory.Polynomial.Nilpotent

/-!

# Polynomials over an irreducible ring

This file contains results about the polynomials over an irreducible ring (i.e. a ring with only
one minimal prime ideal, equivalently, whose spectrum is an irreducible topological space).

## Main results

- `Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical`: a monic polynomial over
  an irreducible ring is irreducible if it is irreducible after mapping into an integral domain.
  A generalization to `Polynomial.Monic.irreducible_of_irreducible_map`.

## Tags

polynomial, irreducible ring, nilradical, prime ideal

-/

public section

open Polynomial

noncomputable section

/-- A polynomial over an irreducible ring `R` is irreducible if it is monic and irreducible after
mapping into an integral domain `S` (https://math.stackexchange.com/a/4843432/235999).
A generalization to `Polynomial.Monic.irreducible_of_irreducible_map`. -/
/-
**Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical** 是 Math
lib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical {R S
 : Type*} [CommRing R] [(nilradical R).IsPrime] [CommRing S] [IsDomain S] (φ : R
 ->+* S) (f : R[X]) (hm : f.Monic) (hi : Irreducible (f.map φ)) : Irreducible f
参数：nilradical R；φ : R ->+* S；f : R[X]；hm : f.Monic；hi : Irreducible (f.map φ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `nilradical_le_prime`：nilradical_le_prime (J : Ideal R) [H : J.IsPrime] :
 nilradical R <= J
· 使用定理 `RingHom.ker_isPrime`：ker_isPrime {F : Type*} [Semiring R] [Semiring S] [
IsDomain S] [FunLike F R S] [RingHomClass F R S] (f : F) : (ker f).IsPrime
· 使用定理 `Polynomial.Monic.irreducible_of_irreducible_map`：∀ {R : Type u} {S : Typ
e v} [inst : CommRing R] [IsDomain R] [inst_2 : CommRing S] [IsDomain S] (φ : R 
→+* S)   (f : Polynomial R), f.Monic …
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isUnit_iff`：isUnit_iff : IsUnit p ↔ exists r : R, IsUnit r ∧ 
C r = p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `Polynomial.isUnit_of_coeff_isUnit_isNilpotent`：isUnit_of_coeff_isUnit_is
Nilpotent (hunit : IsUnit (P.coeff 0)) (hnil : forall i, i != 0 -> IsNilpotent (
P.coeff i)) : IsUnit P
· 使用定理 `isUnit_of_mul_isUnit_right`：isUnit_of_mul_isUnit_right [Monoid M] [IsDed
ekindFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit y
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `IsUnit.neg_iff`：IsUnit.neg_iff [Monoid α] [HasDistribNeg α] (a : α) : Is
Unit (-a) ↔ IsUnit a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
A polynomial over an irreducible ring `R` is irreducible if it is monic and irre
ducible after
mapping into an integral domain `S` (https://math.stackexchange.com/a/4843432/23
5999).
A generalization to `Polynomial.Monic.irreducible_of_irreducible_map`.
-/
theorem Polynomial.Monic.irreducible_of_irreducible_map_of_isPrime_nilradical
    {R S : Type*} [CommRing R] [(nilradical R).IsPrime] [CommRing S] [IsDomain S]
    (φ : R →+* S) (f : R[X]) (hm : f.Monic) (hi : Irreducible (f.map φ)) : Irreducible f := by
  let R' := R ⧸ nilradical R
  let ψ : R' →+* S := Ideal.Quotient.lift (nilradical R) φ
    (haveI := RingHom.ker_isPrime φ; nilradical_le_prime (RingHom.ker φ))
  let ι := algebraMap R R'
  rw [show φ = ψ.comp ι from rfl, ← map_map] at hi
  replace hi := hm.map ι |>.irreducible_of_irreducible_map _ _ hi
  refine ⟨fun h ↦ hi.1 <| (mapRingHom ι).isUnit_map h, fun a b h ↦ ?_⟩
  wlog hb : IsUnit (b.map ι) generalizing a b
  · exact (this b a (mul_comm a b ▸ h)
      (hi.2 (by rw [h, Polynomial.map_mul]) |>.resolve_right hb)).symm
  have hn (i : ℕ) (hi : i ≠ 0) : IsNilpotent (b.coeff i) := by
    obtain ⟨_, _, h⟩ := Polynomial.isUnit_iff.1 hb
    simpa only [coeff_map, coeff_C, hi, ite_false, ← RingHom.mem_ker,
      show RingHom.ker ι = nilradical R from Ideal.mk_ker] using! congr(coeff $(h.symm) i)
  refine .inr <| isUnit_of_coeff_isUnit_isNilpotent (isUnit_of_mul_isUnit_right
    (x := a.coeff f.natDegree) <| (IsUnit.neg_iff _).1 ?_) hn
  have hc : f.leadingCoeff = _ := congr(coeff $h f.natDegree)
  rw [hm, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun i j ↦ a.coeff i * b.coeff j,
    Finset.sum_range_succ, ← sub_eq_iff_eq_add, Nat.sub_self] at hc
  rw [← add_sub_cancel_left 1 (-(_ * _)), ← sub_eq_add_neg, hc]
  exact IsNilpotent.isUnit_sub_one <| show _ ∈ nilradical R from sum_mem fun i hi ↦
    Ideal.mul_mem_left _ _ <| hn _ <| Nat.sub_ne_zero_of_lt (List.mem_range.1 hi)
