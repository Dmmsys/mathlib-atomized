/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
public import Mathlib.RingTheory.UniqueFactorizationDomain.GCDMonoid

/-!
# Unique factorization for univariate and multivariate polynomials

## Main results
* `Polynomial.wfDvdMonoid`:
  If an integral domain is a `WFDvdMonoid`, then so is its polynomial ring.
* `Polynomial.uniqueFactorizationMonoid`, `MvPolynomial.uniqueFactorizationMonoid`:
  If an integral domain is a `UniqueFactorizationMonoid`, then so is its polynomial ring (of any
  number of variables).
-/

@[expose] public section

noncomputable section

open Polynomial

universe u v

namespace Polynomial

variable {R : Type*} [CommSemiring R] [NoZeroDivisors R] [WfDvdMonoid R] {f : R[X]}

/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) wfDvdMonoid : WfDvdMonoid R[X] where
  wf := by
    classical
      refine
        RelHomClass.wellFounded
          (⟨fun p : R[X] =>
              ((if p = 0 then ⊤ else ↑p.degree : WithTop (WithBot ℕ)), p.leadingCoeff), ?_⟩ :
            DvdNotUnit →r Prod.Lex (· < ·) DvdNotUnit)
          (wellFounded_lt.prod_lex ‹WfDvdMonoid R›.wf)
      rintro a b ⟨ane0, ⟨c, ⟨not_unit_c, rfl⟩⟩⟩
      rw [Polynomial.degree_mul, if_neg ane0]
      split_ifs with hac
      · rw [hac, Polynomial.leadingCoeff_zero]
        apply Prod.Lex.left
        exact WithTop.coe_lt_top _
      have cne0 : c ≠ 0 := right_ne_zero_of_mul hac
      simp only [Polynomial.leadingCoeff_mul]
      by_cases hdeg : c.degree = (0 : ℕ)
      · simp only [hdeg, Nat.cast_zero, add_zero]
        refine Prod.Lex.right _ ⟨?_, ⟨c.leadingCoeff, fun unit_c => not_unit_c ?_, rfl⟩⟩
        · rwa [Ne, Polynomial.leadingCoeff_eq_zero]
        rw [Polynomial.isUnit_iff, Polynomial.eq_C_of_degree_eq_zero hdeg]
        use c.leadingCoeff, unit_c
        rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some hdeg]
      · apply Prod.Lex.left
        rw [Polynomial.degree_eq_natDegree cne0] at *
        simp only [Nat.cast_inj] at hdeg
        rw [WithTop.coe_lt_coe, Polynomial.degree_eq_natDegree ane0, ← Nat.cast_add, Nat.cast_lt]
        exact lt_add_of_pos_right _ (Nat.pos_of_ne_zero hdeg)

variable [Nontrivial R]
/-
**Polynomial.exists_irreducible_of_degree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：exists_irreducible_of_degree_pos (hf : 0 < f.degree) : exists g, Irreducib
le g ∧ g ∣ f
参数：hf : 0 < f.degree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `Polynomial.wfDvdMonoid`：∀ {R : Type u_1} [inst : CommSemiring R] [NoZero
Divisors R] [WfDvdMonoid R], WfDvdMonoid (Polynomial R)
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `Polynomial.degree_eq_zero_of_isUnit`：degree_eq_zero_of_isUnit [Nontrivia
l R] (h : IsUnit p) : degree p = 0
· 使用定理 `not_lt_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 < a
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
-/
theorem exists_irreducible_of_degree_pos (hf : 0 < f.degree) : ∃ g, Irreducible g ∧ g ∣ f :=
  WfDvdMonoid.exists_irreducible_factor (fun huf => ne_of_gt hf <| degree_eq_zero_of_isUnit huf)
    fun hf0 => not_lt_of_gt hf <| hf0.symm ▸ (@degree_zero R _).symm ▸ WithBot.bot_lt_coe _
/-
**Polynomial.exists_irreducible_of_natDegree_pos** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：exists_irreducible_of_natDegree_pos (hf : 0 < f.natDegree) : exists g, Irr
educible g ∧ g ∣ f
参数：hf : 0 < f.natDegree。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_irreducible_of_degree_pos`：exists_irreducible_of_degre
e_pos (hf : 0 < f.degree) : exists g, Irreducible g ∧ g ∣ f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
-/
theorem exists_irreducible_of_natDegree_pos (hf : 0 < f.natDegree) : ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_degree_pos <| by
    contrapose! hf
    exact natDegree_le_of_degree_le hf
/-
**Polynomial.exists_irreducible_of_natDegree_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：exists_irreducible_of_natDegree_ne_zero (hf : f.natDegree != 0) : exists g
, Irreducible g ∧ g ∣ f
参数：hf : f.natDegree != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_irreducible_of_natDegree_pos`：exists_irreducible_of_na
tDegree_pos (hf : 0 < f.natDegree) : exists g, Irreducible g ∧ g ∣ f
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem exists_irreducible_of_natDegree_ne_zero (hf : f.natDegree ≠ 0) :
    ∃ g, Irreducible g ∧ g ∣ f :=
  exists_irreducible_of_natDegree_pos <| Nat.pos_of_ne_zero hf

end Polynomial

section UniqueFactorizationDomain

variable (σ : Type v) {D : Type u} [CommRing D] [UniqueFactorizationMonoid D]

open UniqueFactorizationMonoid

namespace Polynomial

/-
**Polynomial.** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) uniqueFactorizationMonoid : UniqueFactorizationMonoid D[X] := by
  let := Classical.arbitrary (NormalizedGCDMonoid D)
  exact ufm_of_decomposition_of_wfDvdMonoid

/-- If `D` is a unique factorization domain, `f` is a non-zero polynomial in `D[X]`, then `f` has
only finitely many monic factors.
(Note that its factors up to unit may be more than monic factors.)
See also `UniqueFactorizationMonoid.fintypeSubtypeDvd`. -/
@[instance_reducible]
/-
**Polynomial.fintypeSubtypeMonicDvd** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：fintypeSubtypeMonicDvd (f : D[X]) (hf : f != 0) : Fintype { g : D[X] // g.
Monic ∧ g ∣ f }
参数：f : D[X]；hf : f != 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `D` is a unique factorization domain, `f` is a non-zero polynomial in `D[X]`,
 then `f` has
only finitely many monic factors.
(Note that its factors up to unit may be more than monic factors.)
See also `UniqueFactorizationMonoid.fintypeSubtypeDvd`.
-/
noncomputable def fintypeSubtypeMonicDvd (f : D[X]) (hf : f ≠ 0) :
    Fintype { g : D[X] // g.Monic ∧ g ∣ f } := by
  set G := { g : D[X] // g.Monic ∧ g ∣ f }
  let y : Associates D[X] := Associates.mk f
  have hy : y ≠ 0 := Associates.mk_ne_zero.mpr hf
  let H := { x : Associates D[X] // x ∣ y }
  let hfin : Fintype H := UniqueFactorizationMonoid.fintypeSubtypeDvd y hy
  let i : G → H := fun x ↦ ⟨Associates.mk x.1, Associates.mk_dvd_mk.2 x.2.2⟩
  refine Fintype.ofInjective i fun x y heq ↦ ?_
  rw [Subtype.mk.injEq] at heq ⊢
  exact eq_of_monic_of_associated x.2.1 y.2.1 (Associates.mk_eq_mk_iff_associated.mp heq)

end Polynomial

namespace MvPolynomial
variable (d : ℕ)

/-
**MvPolynomial.uniqueFactorizationMonoid_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `M
vPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem uniqueFactorizationMonoid_of_fintype [Finite σ] :
    UniqueFactorizationMonoid (MvPolynomial σ D) :=
  have := Fintype.ofFinite σ
  (renameEquiv D (Fintype.equivFin σ)).toMulEquiv.symm.uniqueFactorizationMonoid <| by
    induction Fintype.card σ with
    | zero =>
      apply (isEmptyAlgEquiv D (Fin 0)).toMulEquiv.symm.uniqueFactorizationMonoid
      infer_instance
    | succ d hd =>
      apply (finSuccEquiv D d).toMulEquiv.symm.uniqueFactorizationMonoid
      exact Polynomial.uniqueFactorizationMonoid
/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) uniqueFactorizationMonoid :
    UniqueFactorizationMonoid (MvPolynomial σ D) := by
  rw [iff_exists_prime_factors]
  intro a ha; obtain ⟨s, a', rfl⟩ := exists_finset_rename a
  obtain ⟨w, h, u, hw⟩ :=
    iff_exists_prime_factors.1 (uniqueFactorizationMonoid_of_fintype s) a' fun h =>
      ha <| by simp [h]
  exact
    ⟨w.map (rename (↑)), fun b hb =>
      let ⟨b', hb', he⟩ := Multiset.mem_map.1 hb
      he ▸ (prime_rename_iff (σ := σ) ↑s).2 (h b' hb'),
      Units.map (@rename s σ D _ (↑)).toRingHom.toMonoidHom u, by
      rw [Multiset.prod_hom, Units.coe_map, AlgHom.toRingHom_eq_coe, RingHom.toMonoidHom_eq_coe,
        AlgHom.toRingHom_toMonoidHom, MonoidHom.coe_coe, ← map_mul, hw]⟩

end MvPolynomial

end UniqueFactorizationDomain

/-- A polynomial over a field which is not a unit must have a monic irreducible factor.
See also `WfDvdMonoid.exists_irreducible_factor`. -/
/-
**Polynomial.exists_monic_irreducible_factor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.exists_monic_irreducible_factor {F : Type*} [Field F] (f : F[X]
) (hu : ¬IsUnit f) : exists g : F[X], g.Monic ∧ Irreducible g ∧ g ∣ f
参数：f : F[X]；hu : ¬IsUnit f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
· 使用定理 `Polynomial.irreducible_X`：irreducible_X : Irreducible (X : R[X])
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `associated_mul_unit_right`：associated_mul_unit_right {N : Type*} [Monoid
 N] (a u : N) (hu : IsUnit u) : Associated a (a * u)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Polynomial.monic_mul_leadingCoeff_inv`：monic_mul_leadingCoeff_inv {p : K
[X]} (h : p != 0) : Monic (p * C (leadingCoeff p)⁻¹)
· 使用定理 `Associated.irreducible`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}, As
sociated p q → Irreducible p → Irreducible q
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Associated.dvd_iff_dvd_left`：Associated.dvd_iff_dvd_left [Monoid M] {a b
 c : M} (h : a ~ᵤ b) : a ∣ c ↔ b ∣ c

--- 原说明 ---
A polynomial over a field which is not a unit must have a monic irreducible fact
or.
See also `WfDvdMonoid.exists_irreducible_factor`.
-/
theorem Polynomial.exists_monic_irreducible_factor {F : Type*} [Field F] (f : F[X])
    (hu : ¬IsUnit f) : ∃ g : F[X], g.Monic ∧ Irreducible g ∧ g ∣ f := by
  by_cases hf : f = 0
  · exact ⟨X, monic_X, irreducible_X, hf ▸ dvd_zero X⟩
  obtain ⟨g, hi, hf⟩ := WfDvdMonoid.exists_irreducible_factor hu hf
  have ha : Associated g (g * C g.leadingCoeff⁻¹) := associated_mul_unit_right _ _ <|
    isUnit_C.2 (leadingCoeff_ne_zero.2 hi.ne_zero).isUnit.inv
  exact ⟨_, monic_mul_leadingCoeff_inv hi.ne_zero, ha.irreducible hi, ha.dvd_iff_dvd_left.1 hf⟩
