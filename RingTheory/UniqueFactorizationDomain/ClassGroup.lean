/-
Copyright (c) 2026 Boris Bilich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Bilich, Alexei Piskunov, Jonathan Shneyer
-/
module

public import Mathlib.RingTheory.ClassGroup.Basic

/-!
# The class group of a Unique Factorization Domain is trivial

This file proves that the ideal class group of a GCD Domain is trivial.
The main application is to Unique Factorization Domains,
which are known to be GCD Domains.

## Main result
- `IsGCDMonoid.subsingleton_classGroup` : the class group of a GCD domain is trivial.
  This includes unique factorization domains.

## References

- [stacks-project]: The Stacks project, [tag 0BCH](https://stacks.math.columbia.edu/tag/0BCH)
-/

open scoped nonZeroDivisors

open FractionalIdeal Ideal

public section

variable {R : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
namespace IsGCDMonoid

/-
**IsGCDMonoid.isPrincipal_of_exists_mul_ne_zero_isPrincipal** 是 Mathlib 中的一个引理，位
于命名空间 `IsGCDMonoid`。
形式化陈述：isPrincipal_of_exists_mul_ne_zero_isPrincipal {J : Ideal R} (hJ : exists K
 : Ideal R, J * K != 0 ∧ (J * K).IsPrincipal) : J.IsPrincipal
参数：hJ : exists K : Ideal R, J * K != 0 ∧ (J * K).IsPrincipal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instNonemptyNormalizedGCDMonoidOfIsGCDMonoid`：∀ (α : Type u_2) [inst : C
ommMonoidWithZero α] [IsGCDMonoid α], Nonempty (NormalizedGCDMonoid α)
· 使用定理 `Submodule.IsPrincipal.principal`：∀ {R : Type u_1} {M : Type u_4} {inst :
 Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   (S : Subm
odule R M) [self : S.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_span_mul_finite_of_mem_mul`：mem_span_mul_finite_of_mem_mul
 {P Q : Submodule R A} {x : A} (hx : x in P * Q) : exists T T' : Finset A, (T : 
Set A) subseteq P ∧ (T' : Set …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_eq`：span_eq : span (I : Set α) = I
· 使用定理 `Ideal.span_mul_span`：span_mul_span (S T : Set R) [(span S).IsTwoSided] :
 span S * span T = span (S * T)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.span_mono`：span_mono {s t : Set α} : s subseteq t -> span s <= spa
n t
· 使用定理 `Set.mul_subset_mul_right`：mul_subset_mul_right : s₁ subseteq s₂ -> s₁ * 
t subseteq s₂ * t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `Finset.gcd_dvd`：gcd_dvd {b : β} (hb : b in s) : s.gcd f ∣ f b
· 使用定理 `Ideal.mul_mono_right`：mul_mono_right (h : J <= K) : I * J <= I * K
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.mul_le`：mul_le : I * J <= K ↔ forall r in I, forall s in J, r * s 
in K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `Associated.dvd_iff_dvd_right`：Associated.dvd_iff_dvd_right [Monoid M] {a
 b c : M} (h : b ~ᵤ c) : a ∣ b ↔ a ∣ c
· 使用定理 `Finset.gcd_mul_left'`：∀ {α : Type u_2} {β : Type u_3} [inst : CommMonoid
WithZero α] [inst_1 : NormalizedGCDMonoid α] (s : Finset β)   (f : β → α) (a : α
), Associa…
· 使用定理 `Finset.dvd_gcd_iff`：dvd_gcd_iff {a : α} : a ∣ s.gcd f ↔ forall b in s, a
 ∣ f b
· 使用定理 `Ideal.span.eq_1`：∀ {α : Type u} [inst : Semiring α] (s : Set α), Ideal.s
pan s = Submodule.span α s
（共 43 条，此处仅展示前 30 条）
-/
lemma isPrincipal_of_exists_mul_ne_zero_isPrincipal
    {J : Ideal R} (hJ : ∃ K : Ideal R, J * K ≠ 0 ∧ (J * K).IsPrincipal) :
    J.IsPrincipal := by
  let : NormalizedGCDMonoid R := Classical.arbitrary _
  obtain ⟨K, hJK0, hK⟩ := hJ
  rcases hK.principal with ⟨x, hJK⟩
  have hxmemJK : x ∈ J * K := by simp [hJK]
  -- Shrink `K` to a finitely generated subideal `K'` witnessing `x ∈ J * K'`.
  have : ∃ T : Finset R, (T : Set R) ⊆ K ∧ x ∈ J * span T := by
    obtain ⟨S, T, hSJ, hTK, hx⟩ := Submodule.mem_span_mul_finite_of_mem_mul hxmemJK
    refine ⟨T, hTK, ?_⟩
    rw [← J.span_eq, span_mul_span]
    exact span_mono (Set.mul_subset_mul_right hSJ) hx
  obtain ⟨T, hTK, hxT⟩ := this
  set K' : Ideal R := span T
  -- Let `g` be the gcd of the chosen generators of `K'`; then `K' ≤ (g)`.
  let g : R := T.gcd id
  have hK' : K' ≤ span {g} :=
    span_le.mpr fun z hz ↦ mem_span_singleton.mpr (Finset.gcd_dvd hz)
  -- Upgrade to `x ∈ J * (g)`, hence `(x) ≤ J * (g)`.
  have hxJg : x ∈ J * span {g} := mul_mono_right hK' hxT
  have hx0 : x ≠ 0 := by
    intro hx
    apply hJK0
    simpa [hJK]
  -- From `(x) = J * (g)`, extract `y` with `x = y * g` and cancel `(g)` to show `J` is principal.
  suffices J * span {g} = span {x} by
    obtain ⟨y, hyJ, rfl⟩ := (Ideal.mem_mul_span_singleton).1 hxJg
    rw [← span_singleton_mul_span_singleton, span_singleton_mul_left_inj] at this
    · exact ⟨y, this⟩
    · contrapose hx0
      rw [hx0, mul_zero]
  -- Show `J * (g) ≤ (x)` by proving `x ∣ b * g` for all `b ∈ J`.
  refine le_antisymm
      (mul_le.mpr fun b hb z hz ↦ ?_)
      ((span_singleton_le_iff_mem _).mpr hxJg)
  obtain ⟨z, rfl⟩ := mem_span_singleton.mp hz
  rw [mem_span_singleton, ← mul_assoc]
  apply dvd_mul_of_dvd_left
  suffices x ∣ normalize b * g from this.trans ((associated_normalize b).mul_right g).dvd'
  -- Show `x ∣ b * g` by proving `x ∣ b * c` for all `b ∈ J` and `c ∈ T`.
  rw [← (Finset.gcd_mul_left' ..).dvd_iff_dvd_right, Finset.dvd_gcd_iff]
  intro c hc
  rw [← mem_span_singleton, span, ← hJK, normalize_apply]
  exact mul_mem_mul (J.mul_mem_right _ hb) (hTK hc)

/-- In a GCD domain, an integral ideal that is invertible as a fractional ideal is principal.

Public API note: see `ClassGroup.isPrincipal_of_isUnit_coeIdeal`. -/
/-
**IsGCDMonoid.isPrincipal_of_isUnit_fractionalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `I
sGCDMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a GCD domain, an integral ideal that is invertible as a fractional ideal is p
rincipal.

Public API note: see `ClassGroup.isPrincipal_of_isUnit_coeIdeal`.
-/
private theorem isPrincipal_of_isUnit_fractionalIdeal (I : Ideal R)
    (hI : IsUnit (I : FractionalIdeal R⁰ (FractionRing R))) :
    I.IsPrincipal := by
  obtain ⟨a, K, ha0, h⟩ := exists_eq_spanSingleton_mul (I : FractionalIdeal R⁰ (FractionRing R))⁻¹
  have hIK : I * K = Ideal.span ({a} : Set R) :=
    (coeIdeal_inj (K := FractionRing R)).mp <| by
      rw [coeIdeal_mul, coeIdeal_span_singleton]
      rw [← mul_inv_cancel_iff_isUnit] at hI
      have ha0' := spanSingleton_mul_inv (R₁ := R) (FractionRing R)
        (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors
          (mem_nonZeroDivisors_iff_ne_zero.mpr ha0))
      replace h :=
        congrArg
          (fun t =>
            spanSingleton R⁰ ((algebraMap R (FractionRing R)) a) * I * t)
          h.symm
      rwa [mul_mul_mul_comm, ← spanSingleton_inv, ha0', one_mul, mul_assoc, hI, mul_one] at h
  refine isPrincipal_of_exists_mul_ne_zero_isPrincipal (J := I) ?_
  refine ⟨K, ?_, ?_⟩
  · simp [hIK, ha0]
  · simpa [hIK] using (inferInstance : (Ideal.span {a}).IsPrincipal)

/-- In a GCD domain, every invertible fractional ideal is principal.

Public API note: see `ClassGroup.isPrincipal_coeSubmodule_of_isUnit`. -/
/-
**IsGCDMonoid.isPrincipal_fractionalIdeal_of_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `I
sGCDMonoid`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a GCD domain, every invertible fractional ideal is principal.

Public API note: see `ClassGroup.isPrincipal_coeSubmodule_of_isUnit`.
-/
private theorem isPrincipal_fractionalIdeal_of_isUnit
    (I : (FractionalIdeal R⁰ (FractionRing R))ˣ) :
    (I : Submodule R (FractionRing R)).IsPrincipal := by
  let J : Ideal R := (I : FractionalIdeal R⁰ (FractionRing R)).num
  have hJunit : IsUnit (J : FractionalIdeal R⁰ (FractionRing R)) :=
    FractionalIdeal.isUnit_num.mpr ⟨I, rfl⟩
  have hJprin : J.IsPrincipal := isPrincipal_of_isUnit_fractionalIdeal J hJunit
  exact isPrincipal_of_isPrincipal_num
    (I : FractionalIdeal R⁰ (FractionRing R)) hJprin

/-- The ideal class group of a GCD domain is trivial.
This includes unique factorization domains. -/
/-
**IsGCDMonoid.subsingleton_classGroup** 是 Mathlib 中的一个实例，位于命名空间 `IsGCDMonoid`。
形式化陈述：subsingleton_classGroup : Subsingleton (ClassGroup R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_forall_eq`：∀ {α : Sort u_1} (x : α), (∀ (y : α), y = x) 
→ Subsingleton α
· 使用定理 `ClassGroup.induction`：ClassGroup.induction {P : ClassGroup R -> Prop} (h
 : forall I : (FractionalIdeal R⁰ K)ˣ, P (ClassGroup.mk K I)) (x : ClassGroup R)
 : P x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClassGroup.mk_eq_one_iff`：ClassGroup.mk_eq_one_iff {I : (FractionalIdeal
 R⁰ K)ˣ} : ClassGroup.mk K I = 1 ↔ (I : Submodule R K).IsPrincipal
· 使用定理 `_private.Mathlib.RingTheory.UniqueFactorizationDomain.ClassGroup.0.IsGCD
Monoid.isPrincipal_fractionalIdeal_of_isUnit`：∀ {R : Type u_1} [inst : CommRing 
R] [IsDomain R] [IsGCDMonoid R]   (I : (FractionalIdeal (nonZeroDivisors R) (Fra
ctionRing R))ˣ), (↑↑I).IsP…

--- 原说明 ---
The ideal class group of a GCD domain is trivial.
This includes unique factorization domains.
-/
instance subsingleton_classGroup : Subsingleton (ClassGroup R) := by
  refine subsingleton_of_forall_eq 1 ?_
  intro x
  refine ClassGroup.induction (FractionRing R) ?_ x
  intro I
  exact ClassGroup.mk_eq_one_iff.mpr
    (isPrincipal_fractionalIdeal_of_isUnit I)

end IsGCDMonoid

@[deprecated (since := "2026-07-08")]
alias NormalizedGCDMonoid.isPrincipal_of_exists_mul_ne_zero_isPrincipal :=
  IsGCDMonoid.isPrincipal_of_exists_mul_ne_zero_isPrincipal

