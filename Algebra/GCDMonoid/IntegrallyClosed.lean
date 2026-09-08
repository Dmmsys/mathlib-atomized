/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.GCDMonoid.Basic
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic

/-!

# GCD domains are integrally closed

-/

public section


open scoped Polynomial

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

/-
**IsLocalization.surj_of_gcd_domain** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsLocalization.surj_of_gcd_domain [GCDMonoid R] (M : Submonoid R) [IsLocal
ization M A] (z : A) : exists a b : R, IsUnit (gcd a b) ∧ z * algebraMap R A b =
 algebraMap R A a
参数：M : Submonoid R；z : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `extract_gcd`：extract_gcd {α : Type*} [CommMonoidWithZero α] [GCDMonoid α
] (x y : α) : exists x' y', x = gcd x y * x' ∧ y = gcd x y * y' ∧ IsUnit (gcd x'
 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsLocalization.mul_mk'_eq_mk'_of_mul`：∀ {R : Type u_1} [inst : CommSemir
ing R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Al
gebra R S] [inst_3 : IsLoc…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalization.mk'_mul_cancel_left`：∀ {R : Type u_1} [inst : CommSemirin
g R] {M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Alge
bra R S] [inst_3 : IsLoc…
-/
theorem IsLocalization.surj_of_gcd_domain [GCDMonoid R] (M : Submonoid R) [IsLocalization M A]
    (z : A) : ∃ a b : R, IsUnit (gcd a b) ∧ z * algebraMap R A b = algebraMap R A a := by
  obtain ⟨x, ⟨y, hy⟩, rfl⟩ := IsLocalization.exists_mk'_eq M z
  obtain ⟨x', y', hx', hy', hu⟩ := extract_gcd x y
  use x', y', hu
  rw [mul_comm, IsLocalization.mul_mk'_eq_mk'_of_mul]
  convert! IsLocalization.mk'_mul_cancel_left (M := M) (S := A) _ _ using 2
  grind
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) GCDMonoid.toIsIntegrallyClosed
    [h : IsGCDMonoid R] : IsIntegrallyClosed R :=
  (isIntegrallyClosed_iff (FractionRing R)).mpr fun {X} ⟨p, hp₁, hp₂⟩ => by
    cases h
    obtain ⟨x, y, hg, he⟩ := IsLocalization.surj_of_gcd_domain (nonZeroDivisors R) X
    have :=
      Polynomial.dvd_pow_natDegree_of_eval₂_eq_zero (IsFractionRing.injective R <| FractionRing R)
        hp₁ y x _ hp₂ (by rw [mul_comm, he])
    have : IsUnit y := by
      rw [isUnit_iff_dvd_one, ← one_pow]
      exact
        (dvd_gcd this <| dvd_refl y).trans
          (gcd_pow_left_dvd_pow_gcd.trans <| pow_dvd_pow_of_dvd (isUnit_iff_dvd_one.1 hg) _)
    use x * (this.unit⁻¹ :)
    rw [map_mul]
    have coe_map_inv :=
      Units.coe_map_inv ((algebraMap R (FractionRing R) : R →* FractionRing R)) this.unit
    simp only [MonoidHom.coe_coe] at coe_map_inv
    rw [← coe_map_inv, eq_comm, Units.eq_mul_inv_iff_mul_eq]
    exact he
