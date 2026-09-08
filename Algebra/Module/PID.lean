/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.DedekindDomain
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Structure of finitely generated modules over a PID

## Main statements

* `Module.equiv_directSum_of_isTorsion` : A finitely generated torsion module over a PID is
  isomorphic to a direct sum of some `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
* `Module.equiv_free_prod_directSum` : A finitely generated module over a PID is isomorphic to the
  product of a free module (its torsion free part) and a direct sum of the form above (its torsion
  submodule).

## Notation

* `R` is a PID and `M` is a (finitely generated for main statements) `R`-module, with additional
  torsion hypotheses in the intermediate lemmas.
* `p` is an irreducible element of `R` or a tuple of these.

## Implementation details

We first prove (`Submodule.isInternal_prime_power_torsion_of_pid`) that a finitely generated
torsion module is the internal direct sum of its `p i ^ e i`-torsion submodules for some
(finitely many) prime powers `p i ^ e i`. This is proved in more generality for a Dedekind domain
at `Submodule.isInternal_prime_power_torsion`.

Then we treat the case of a `p ^ ∞`-torsion module (that is, a module where all elements are
cancelled by scalar multiplication by some power of `p`) and apply it to the `p i ^ e i`-torsion
submodules (that are `p i ^ ∞`-torsion) to get the result for torsion modules.

Then we get the general result using that a torsion free module is free (which has been proved at
`Module.free_of_finite_type_torsion_free'` at `LinearAlgebra.FreeModule.PID`.)

## Tags

Finitely generated module, principal ideal domain, classification, structure theorem
-/

public section

-- We shouldn't need to know about topology to prove
-- the structure theorem for finitely generated modules over a PID.
assert_not_exists TopologicalSpace

universe u v

variable {R : Type u} [CommRing R] [IsPrincipalIdealRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

open Submodule

open UniqueFactorizationMonoid

/-
**Submodule.isSemisimple_torsionBy_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isSemisimple_torsionBy_of_irreducible {a : R} (h : Irreducible a
) : IsSemisimpleModule R (torsionBy R M a)
参数：h : Irreducible a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isSemisimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) 
[inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSemisimpleModule R M
 ↔ Complemen…
· 使用定理 `OrderIso.complementedLattice`：OrderIso.complementedLattice [Complemented
Lattice α] (f : α ≃o β) : ComplementedLattice β
· 使用定理 `PrincipalIdealRing.isMaximal_of_irreducible`：isMaximal_of_irreducible [C
ommSemiring R] [IsPrincipalIdealRing R] {p : R} (hp : Irreducible p) : Ideal.IsM
aximal (span R ({p} : Set R))
-/
theorem Submodule.isSemisimple_torsionBy_of_irreducible {a : R} (h : Irreducible a) :
    IsSemisimpleModule R (torsionBy R M a) :=
  haveI := PrincipalIdealRing.isMaximal_of_irreducible h
  letI := Ideal.Quotient.field (R ∙ a)
  (isSemisimpleModule_iff ..).mpr (submodule_torsionBy_orderIso a).complementedLattice

variable [IsDomain R]

/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`. -/
/-
**Submodule.isInternal_prime_power_torsion_of_pid** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.isInternal_prime_power_torsion_of_pid [Module.Finite R M] (hM : 
Module.IsTorsion R M) : DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M
).annihilator).toFinset => torsionBy R M (IsPrincipal.generator (p : Ideal R) ^ 
(factors (⊤ : Submodule R M).annihilator).count ↑p)
参数：hM : Module.IsTorsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.torsionBySet_span_singleton_eq`：torsionBySet_span_singleton_eq
 : torsionBySet R M (R ∙ a) = torsionBy R M a
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
· 使用定理 `Submodule.isInternal_prime_power_torsion`：isInternal_prime_power_torsion
 [Module.Finite R M] (hM : Module.IsTorsion R M) : DirectSum.IsInternal fun p : 
(factors (⊤ : Submodule R M).a…

--- 原说明 ---
A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.
-/
theorem Submodule.isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBy R M
        (IsPrincipal.generator (p : Ideal R) ^
          (factors (⊤ : Submodule R M).annihilator).count ↑p) := by
  convert! isInternal_prime_power_torsion hM
  rw [← torsionBySet_span_singleton_eq, Ideal.submodule_span_eq, ← Ideal.span_singleton_pow,
    Ideal.span_singleton_generator]

/-- A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`. -/
/-
**Submodule.exists_isInternal_prime_power_torsion_of_pid** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
 (hM : Module.IsTorsion R M) : exists (ι : Type u) (_ : Fintype ι) (_ : Decidabl
eEq ι) (p : ι -> R) (_ : forall i, Irreducible <| p i) (e : ι -> Nat), DirectSum
.IsInternal fun i => torsionBy R M p i ^ e i
参数：hM : Module.IsTorsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Ideal.isPrime_of_prime`：isPrime_of_prime {P : Ideal A} (h : Prime P) : I
sPrime P
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Submodule.IsPrincipal.prime_generator_of_isPrime`：prime_generator_of_isP
rime (S : Ideal R) [S.IsPrincipal] [is_prime : S.IsPrime] (ne_bot : S != ⊥) : Pr
ime (generator S)
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Submodule.isInternal_prime_power_torsion_of_pid`：Submodule.isInternal_pr
ime_power_torsion_of_pid [Module.Finite R M] (hM : Module.IsTorsion R M) : Direc
tSum.IsInternal fun p : (factors (⊤ :…

--- 原说明 ---
A finitely generated torsion module over a PID is an internal direct sum of its
`p i ^ e i`-torsion submodules for some primes `p i` and numbers `e i`.
-/
theorem Submodule.exists_isInternal_prime_power_torsion_of_pid [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (_ : DecidableEq ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i)
        (e : ι → ℕ), DirectSum.IsInternal fun i => torsionBy R M <| p i ^ e i := by
  refine ⟨_, ?_, _, _, ?_, _, Submodule.isInternal_prime_power_torsion_of_pid hM⟩
  · exact Finset.fintypeCoeSort _
  · rintro ⟨p, hp⟩
    have hP := prime_of_factor p (Multiset.mem_toFinset.mp hp)
    have := Ideal.isPrime_of_prime hP
    exact (IsPrincipal.prime_generator_of_isPrime p hP.ne_zero).irreducible

namespace Module

section PTorsion

variable {p : R} (hp : Irreducible p) (hM : Module.IsTorsion' M (Submonoid.powers p))
variable [dec : ∀ x : M, Decidable (x = 0)]

open Ideal Submodule.IsPrincipal

include hp

/-
**Module._root_.Ideal.torsionOf_eq_span_pow_pOrder** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Ideal.torsionOf_eq_span_pow_pOrder (x : M) :
    torsionOf R M x = span {p ^ pOrder hM x} := by
  classical
  dsimp only [pOrder]
  rw [← (torsionOf R M x).span_singleton_generator, Ideal.span_singleton_eq_span_singleton, ←
    Associates.mk_eq_mk_iff_associated, Associates.mk_pow]
  have prop :
    (fun n : ℕ => p ^ n • x = 0) = fun n : ℕ =>
      (Associates.mk <| generator <| torsionOf R M x) ∣ Associates.mk p ^ n := by
    ext n; rw [← Associates.mk_pow, Associates.mk_dvd_mk, ← mem_iff_generator_dvd]; rfl
  have := (isTorsion'_powers_iff p).mp hM x; rw [prop] at this
  convert!
    Associates.eq_pow_find_of_dvd_irreducible_pow (Associates.irreducible_mk.mpr hp)
      this.choose_spec
/-
**Module.p_pow_smul_lift** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：p_pow_smul_lift {x y : M} {k : Nat} (hM' : Module.IsTorsionBy R M (p ^ pOr
der hM y)) (h : p ^ k • x in R ∙ y) : exists a : R, p ^ k • x = p ^ k • a • y
参数：hM' : Module.IsTorsionBy R M (p ^ pOrder hM y)；h : p ^ k • x in R ∙ y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Ideal.torsionOf_eq_span_pow_pOrder`：∀ {R : Type u} [inst : CommRing R] [
IsPrincipalIdealRing R] {M : Type v} [inst_2 : AddCommGroup M]   [inst_3 : _root
_.Module R M] [IsDomain …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.torsionBy_eq_span_singleton`：torsionBy_eq_span_singleton 
{R : Type w} [CommRing R] (a b : R) (ha : a in R⁰) : torsionBy R (R ⧸ R ∙ a * b)
 a = R ∙ mk (R ∙ a * b) b
· 使用定理 `mem_nonZeroDivisors_of_ne_zero`：mem_nonZeroDivisors_of_ne_zero (hx : x !
= 0) : x in M₀⁰
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Submodule.mem_torsionBy_iff`：mem_torsionBy_iff (x : M) : x in torsionBy 
R M a ↔ a • x = 0
· 使用定理 `LinearEquiv.map_smul`：map_smul (e : N₁ ≃ₗ[R₁] N₂) (c : R₁) (x : N₁) : e 
(c • x) = c • e x
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Submodule.coe_smul_of_tower`：coe_smul_of_tower [SMul S R] [SMul S M] [Is
ScalarTower S R M] (r : S) (x : p) : ((r • x : p) : M) = r • (x : M)
· 使用定理 `Submodule.coe_mk`：coe_mk (x : M) (hx : x in p) : ((⟨x, hx⟩ : p) : M) = x
· 使用定理 `Submodule.coe_zero`：coe_zero : ((0 : p) : M) = 0
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `LinearEquiv.map_zero`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M₂
 : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst_…
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Ideal.Quotient.mk_eq_mk`：mk_eq_mk (x : R) : (Submodule.Quotient.mk x : R
 ⧸ I) = mk I x
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
（共 31 条，此处仅展示前 30 条）
-/
theorem p_pow_smul_lift {x y : M} {k : ℕ} (hM' : Module.IsTorsionBy R M (p ^ pOrder hM y))
    (h : p ^ k • x ∈ R ∙ y) : ∃ a : R, p ^ k • x = p ^ k • a • y := by
  by_cases! hk : k ≤ pOrder hM y
  · let f :=
      ((R ∙ p ^ (pOrder hM y - k) * p ^ k).quotEquivOfEq _ ?_).trans
        (quotTorsionOfEquivSpanSingleton R M y)
    · have : f.symm ⟨p ^ k • x, h⟩ ∈
          R ∙ Ideal.Quotient.mk (R ∙ p ^ (pOrder hM y - k) * p ^ k) (p ^ k) := by
        rw [← Quotient.torsionBy_eq_span_singleton, mem_torsionBy_iff, ← f.symm.map_smul]
        · convert! f.symm.map_zero; ext
          rw [coe_smul_of_tower, coe_mk, coe_zero, smul_smul, ← pow_add, Nat.sub_add_cancel hk,
            @hM' x]
        · exact mem_nonZeroDivisors_of_ne_zero (pow_ne_zero _ hp.ne_zero)
      rw [Submodule.mem_span_singleton] at this; obtain ⟨a, ha⟩ := this; use a
      rw [f.eq_symm_apply, ← Ideal.Quotient.mk_eq_mk, ← Quotient.mk_smul] at ha
      dsimp only [smul_eq_mul, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
        quotTorsionOfEquivSpanSingleton_apply_mk] at ha
      rw [smul_smul, mul_comm]; exact congr_arg ((↑) : _ → M) ha.symm
    · symm; convert! Ideal.torsionOf_eq_span_pow_pOrder hp hM y
      rw [← pow_add, Nat.sub_add_cancel hk]
  · use 0
    rw [zero_smul, smul_zero, ← Nat.sub_add_cancel hk.le, pow_add, mul_smul, hM',
      smul_zero]

open Submodule.Quotient
/-
**Module.exists_smul_eq_zero_and_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：exists_smul_eq_zero_and_mk_eq {z : M} (hz : Module.IsTorsionBy R M (p ^ pO
rder hM z)) {k : Nat} (f : (R ⧸ R ∙ p ^ k) ->ₗ[R] M ⧸ R ∙ z) : exists x : M, p ^
 k • x = 0 ∧ Submodule.Quotient.mk (p
参数：hz : Module.IsTorsionBy R M (p ^ pOrder hM z)；f : (R ⧸ R ∙ p ^ k) ->ₗ[R] M ⧸ 
R ∙ z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `LinearMap.map_smul`：∀ {R : Type u_1} {M : Type u_8} {M₂ : Type u_10} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid M₂] [inst_
3 : _roo…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Module.p_pow_smul_lift`：p_pow_smul_lift {x y : M} {k : Nat} (hM' : Modul
e.IsTorsionBy R M (p ^ pOrder hM y)) (h : p ^ k • x in R ∙ y) : exists a : R, p 
^ k • x = p …
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Submodule.Quotient.mk_sub`：mk_sub : (mk (x - y) : M ⧸ p) = mk x - mk y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
-/
theorem exists_smul_eq_zero_and_mk_eq {z : M} (hz : Module.IsTorsionBy R M (p ^ pOrder hM z))
    {k : ℕ} (f : (R ⧸ R ∙ p ^ k) →ₗ[R] M ⧸ R ∙ z) :
    ∃ x : M, p ^ k • x = 0 ∧ Submodule.Quotient.mk (p := span R {z}) x = f 1 := by
  have f1 := mk_surjective (R ∙ z) (f 1)
  have : p ^ k • f1.choose ∈ R ∙ z := by
    rw [← Quotient.mk_eq_zero, mk_smul, f1.choose_spec, ← f.map_smul]
    convert! f.map_zero; change _ • Submodule.Quotient.mk _ = _
    rw [← mk_smul, Quotient.mk_eq_zero, smul_eq_mul, mul_one]
    exact Submodule.mem_span_singleton_self _
  obtain ⟨a, ha⟩ := p_pow_smul_lift hp hM hz this
  refine ⟨f1.choose - a • z, by rw [smul_sub, sub_eq_zero, ha], ?_⟩
  rw [mk_sub, mk_smul, (Quotient.mk_eq_zero _).mpr <| Submodule.mem_span_singleton_self _,
    smul_zero, sub_zero, f1.choose_spec]

open Finset Multiset

set_option backward.isDefEq.respectTransparency.types false in
omit dec in
/-- A finitely generated `p ^ ∞`-torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p ^ e i)` for some `e i`. -/
/-
**Module.torsion_by_prime_power_decomposition** 是 Mathlib 中的一个定理，位于命名空间 `Module`
。
形式化陈述：torsion_by_prime_power_decomposition (hM : Module.IsTorsion' M (Submonoid.
powers p)) [h' : Module.Finite R M] : exists (d : Nat) (k : Fin d -> Nat), Nonem
pty M ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ (k i : Nat)
参数：hM : Module.IsTorsion' M (Submonoid.powers p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Finite.exists_fin`：exists_fin [Module.Finite R M] : exists (n : N
at) (s : Fin n -> M), span R (range s) = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Submodule.exists_isTorsionBy`：exists_isTorsionBy {p : R} (hM : IsTorsion
' M <| Submonoid.powers p) (d : Nat) (hd : d != 0) (s : Fin d -> M) (hs : span R
 (Set.range s) = ⊤…
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Submodule.Quotient.mk_zero`：mk_zero : mk 0 = (0 : M ⧸ p)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Function.comp_assoc`：comp_assoc (f : φ -> δ) (g : β -> φ) (h : α -> β) :
 (f ∘ g) ∘ h = f ∘ g ∘ h
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Fin.range_succAbove`：∀ {n : ℕ} (p : Fin (n + 1)), Set.range p.succAbove 
= {p}ᶜ
· 使用定理 `Submodule.span_insert_zero`：span_insert_zero : span R (insert (0 : M) s)
 = span R s
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Set.insert_image_compl_eq_range`：insert_image_compl_eq_range (f : α -> β
) (x : α) : insert (f x) (f '' {x}ᶜ) = range f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
A finitely generated `p ^ ∞`-torsion module over a PID is isomorphic to a direct
 sum of some
  `R ⧸ R ∙ (p ^ e i)` for some `e i`.
-/
theorem torsion_by_prime_power_decomposition (hM : Module.IsTorsion' M (Submonoid.powers p))
    [h' : Module.Finite R M] :
    ∃ (d : ℕ) (k : Fin d → ℕ), Nonempty <| M ≃ₗ[R] ⨁ i : Fin d, R ⧸ R ∙ p ^ (k i : ℕ) := by
  obtain ⟨d, s, hs⟩ := @Module.Finite.exists_fin _ _ _ _ _ h'; use d; clear h'
  induction d generalizing M with
  | zero =>
    use finZeroElim
    rw [Set.range_eq_empty, Submodule.span_empty] at hs
    have : Unique M :=
      ⟨⟨0⟩, fun x => by dsimp; rw [← Submodule.mem_bot R, hs]; exact Submodule.mem_top⟩
    exact ⟨0⟩
  | succ d IH =>
    have : ∀ x : M, Decidable (x = 0) := fun _ => by classical infer_instance
    obtain ⟨j, hj⟩ := exists_isTorsionBy hM d.succ d.succ_ne_zero s hs
    let s' : Fin d → M ⧸ R ∙ s j := Submodule.Quotient.mk ∘ s ∘ j.succAbove
    -- Porting note(https://github.com/leanprover-community/mathlib4/issues/5732):
    -- `obtain` doesn't work with placeholders.
    have := IH ?_ s' ?_
    · obtain ⟨k, ⟨f⟩⟩ := this
      clear IH
      have : ∀ i : Fin d,
          ∃ x : M, p ^ k i • x = 0 ∧ f (Submodule.Quotient.mk x) = DirectSum.lof R _ _ i 1 := by
        intro i
        let fi := f.symm.toLinearMap.comp (DirectSum.lof _ _ _ i)
        obtain ⟨x, h0, h1⟩ := exists_smul_eq_zero_and_mk_eq hp hM hj fi; refine ⟨x, h0, ?_⟩; rw [h1]
        simp only [fi, LinearMap.coe_comp, f.symm.coe_toLinearMap, f.apply_symm_apply,
          Function.comp_apply]
      refine ⟨?_, ⟨?_⟩⟩
      · exact fun a => (fun i => (Option.rec (pOrder hM (s j)) k i : ℕ)) (finSuccEquiv d a)
      · refine
          (lequivProdOfRightSplitExact
            (g := f.toLinearMap.comp <| mkQ _)
            (f := (DirectSum.toModule _ _ _ fun i => (liftQSpanSingleton (p ^ k i)
                (LinearMap.toSpanSingleton _ _ _) (this i).choose_spec.left : R ⧸ _ →ₗ[R] _)))
              (R ∙ s j).injective_subtype ?_ ?_).symm ≪≫ₗ
          (((quotTorsionOfEquivSpanSingleton R M (s j)).symm ≪≫ₗ
            (quotEquivOfEq (torsionOf R M (s j)) _
              (Ideal.torsionOf_eq_span_pow_pOrder hp hM (s j)))).prodCongr (.refl _ _)) ≪≫ₗ
          (@DirectSum.lequivProdDirectSum R _ _
            (fun i => R ⧸ R ∙ p ^ @Option.rec _ (fun _ => ℕ) (pOrder hM <| s j) k i) _ _).symm ≪≫ₗ
          (DirectSum.lequivCongrLeft R (finSuccEquiv d).symm)
        · rw [range_subtype, LinearEquiv.ker_comp, ker_mkQ]
        · rw [LinearMap.comp_assoc]
          ext i : 3
          simp only [LinearMap.coe_comp, Function.comp_apply, mkQ_apply]
          rw [LinearEquiv.coe_toLinearMap, LinearMap.id_apply, DirectSum.toModule_lof,
            liftQSpanSingleton_apply, LinearMap.toSpanSingleton_apply_one, Ideal.Quotient.mk_eq_mk,
            map_one (Ideal.Quotient.mk _), (this i).choose_spec.right]
    · exact (mk_surjective _).forall.mpr fun x =>
        ⟨(@hM x).choose, by rw [← Quotient.mk_smul, (@hM x).choose_spec, Quotient.mk_zero]⟩
    · have hs' := congr_arg (Submodule.map <| mkQ <| R ∙ s j) hs
      rw [Submodule.map_span, Submodule.map_top, range_mkQ] at hs'; simp only [mkQ_apply] at hs'
      simp only [s']; rw [← Function.comp_assoc, Set.range_comp (_ ∘ s), Fin.range_succAbove]
      rw [← Set.range_comp, ← Set.insert_image_compl_eq_range _ j, Function.comp_apply,
        (Quotient.mk_eq_zero _).mpr (Submodule.mem_span_singleton_self _),
        Submodule.span_insert_zero] at hs'
      exact hs'

end PTorsion

/-- A finitely generated torsion module over a PID is isomorphic to a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers. -/
/-
**Module.equiv_directSum_of_isTorsion** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：equiv_directSum_of_isTorsion [h' : Module.Finite R M] (hM : Module.IsTorsi
on R M) : exists (ι : Type u) (_ : Fintype ι) (p : ι -> R) (_ : forall i, Irredu
cible <| p i) (e : ι -> Nat), Nonempty M ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i
参数：hM : Module.IsTorsion R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_isInternal_prime_power_torsion_of_pid`：Submodule.exists
_isInternal_prime_power_torsion_of_pid [Module.Finite R M] (hM : Module.IsTorsio
n R M) : exists (ι : Type u) (_ : Fintype ι)…
· 使用定理 `Module.torsion_by_prime_power_decomposition`：torsion_by_prime_power_deco
mposition (hM : Module.IsTorsion' M (Submonoid.powers p)) [h' : Module.Finite R 
M] : exists (d : Nat) (k : Fin d …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.isTorsion'_powers_iff`：∀ {R : Type u_1} {M : Type u_2} [inst :
 Monoid R] [inst_1 : AddCommMonoid M] [inst_2 : DistribMulAction R M] (p : R),  
 Module.IsTorsion' M …
· 使用定理 `Submodule.smul_torsionBy`：smul_torsionBy (x : torsionBy R M a) : a • x =
 0
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A finitely generated torsion module over a PID is isomorphic to a direct sum of 
some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
-/
theorem equiv_directSum_of_isTorsion [h' : Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, _, p, hp, e, h⟩ := Submodule.exists_isInternal_prime_power_torsion_of_pid hM
  have :
    ∀ i,
      ∃ (d : ℕ) (k : Fin d → ℕ),
        Nonempty <| torsionBy R M (p i ^ e i) ≃ₗ[R] ⨁ j, R ⧸ R ∙ p i ^ k j := by
    exact fun i =>
      torsion_by_prime_power_decomposition.{u, v} (hp i)
        ((isTorsion'_powers_iff <| p i).mpr fun x => ⟨e i, smul_torsionBy _ _⟩)
  refine
    ⟨Σ i, Fin (this i).choose, inferInstance, fun ⟨i, _⟩ => p i, fun ⟨i, _⟩ => hp i, fun ⟨i, j⟩ =>
      (this i).choose_spec.choose j,
      ⟨(LinearEquiv.ofBijective (DirectSum.coeLinearMap _) h).symm.trans <|
          (DFinsupp.mapRange.linearEquiv fun i => (this i).choose_spec.choose_spec.some).trans <|
            (DirectSum.sigmaLcurryEquiv R).symm.trans
              (DFinsupp.mapRange.linearEquiv fun i => quotEquivOfEq _ _ ?_)⟩⟩
  simp only

variable (R M)

/-- **Structure theorem of finitely generated modules over a PID** : A finitely generated
  module over a PID is isomorphic to the product of a free module and a direct sum of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers. -/
/-
**Module.equiv_free_prod_directSum** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：equiv_free_prod_directSum [h' : Module.Finite R M] : exists (n : Nat) (ι :
 Type u) (_ : Fintype ι) (p : ι -> R) (_ : forall i, Irreducible <| p i) (e : ι 
-> Nat), Nonempty M ≃ₗ[R] (Fin n ->₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.equiv_directSum_of_isTorsion`：equiv_directSum_of_isTorsion [h' : 
Module.Finite R M] (hM : Module.IsTorsion R M) : exists (ι : Type u) (_ : Fintyp
e ι) (p : ι -> R) (_ : fo…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsDedekindRing.toIsNoetherian`：∀ {A : Type u_2} {inst : CommRing A} [sel
f : IsDedekindRing A], IsNoetherian A A
· 使用定理 `IsDedekindDomain.toIsDedekindRing`：∀ {A : Type u_2} {inst : CommRing A} 
[self : IsDedekindDomain A], IsDedekindRing A
· 使用定理 `IsPrincipalIdealRing.isDedekindDomain`：∀ (A : Type u_2) [inst : CommRing
 A] [IsDomain A] [IsPrincipalIdealRing A], IsDedekindDomain A
· 使用定理 `Submodule.torsion_isTorsion`：torsion_isTorsion : Module.IsTorsion R (tor
sion R M)
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p

--- 原说明 ---
**Structure theorem of finitely generated modules over a PID** : A finitely gene
rated
  module over a PID is isomorphic to the product of a free module and a direct s
um of some
  `R ⧸ R ∙ (p i ^ e i)` where the `p i ^ e i` are prime powers.
-/
theorem equiv_free_prod_directSum [h' : Module.Finite R M] :
    ∃ (n : ℕ) (ι : Type u) (_ : Fintype ι) (p : ι → R) (_ : ∀ i, Irreducible <| p i) (e : ι → ℕ),
      Nonempty <| M ≃ₗ[R] (Fin n →₀ R) × ⨁ i : ι, R ⧸ R ∙ p i ^ e i := by
  obtain ⟨I, fI, p, hp, e, ⟨h⟩⟩ :=
    equiv_directSum_of_isTorsion.{u, v} (@torsion_isTorsion R M _ _ _)
  obtain ⟨n, ⟨g⟩⟩ := @Module.basisOfFiniteTypeTorsionFree' R _ (M ⧸ torsion R M) _ _ _ _ _ _
  obtain ⟨f, hf⟩ := Module.projective_lifting_property _ LinearMap.id (torsion R M).mkQ_surjective
  refine
    ⟨n, I, fI, p, hp, e,
      ⟨(lequivProdOfRightSplitExact (torsion R M).injective_subtype ?_ hf).symm.trans <|
          (h.prodCongr g).trans <| LinearEquiv.prodComm.{u, u} R _ (Fin n →₀ R) ⟩⟩
  rw [range_subtype, ker_mkQ]

set_option backward.isDefEq.respectTransparency false in
open LinearMap in
/-
**Module.exists_ker_toSpanSingleton_eq_annihilator** 是 Mathlib 中的一个定理，位于命名空间 `Mo
dule`。
形式化陈述：exists_ker_toSpanSingleton_eq_annihilator [Module.Finite R M] : exists x :
 M, ker (toSpanSingleton R _ x) = annihilator R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.equiv_free_prod_directSum`：equiv_free_prod_directSum [h' : Module
.Finite R M] : exists (n : Nat) (ι : Type u) (_ : Fintype ι) (p : ι -> R) (_ : f
orall i, Irreducible <…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `LinearEquiv.annihilator_eq`：LinearEquiv.annihilator_eq (e : M ≃ₗ[R] M') 
: Module.annihilator R M = Module.annihilator R M'
· 使用定理 `Module.annihilator_prod`：Module.annihilator_prod : annihilator R (M × M'
) = annihilator R M ⊓ annihilator R M'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.annihilator_eq_top_iff`：Module.annihilator_eq_top_iff : annihilat
or R M = ⊤ ↔ Subsingleton M
· 使用定理 `Module.annihilator_dfinsupp`：Module.annihilator_dfinsupp : annihilator R
 (Π₀ i, M i) = ⨅ i, annihilator R (M i)
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ideal.annihilator_quotient`：∀ {R : Type u_1} [inst : Ring R] {I : Ideal 
R} [I.IsTwoSided], Module.annihilator R (R ⧸ I) = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
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
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ZeroMemClass.zero_mem`：∀ {S : Type u_3} {M : outParam (Type u_4)} {inst 
: Zero M} {inst_1 : SetLike S M} [self : ZeroMemClass S M] (s : S),   0 ∈ s
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
（共 42 条，此处仅展示前 30 条）
-/
theorem exists_ker_toSpanSingleton_eq_annihilator [Module.Finite R M] :
    ∃ x : M, ker (toSpanSingleton R _ x) = annihilator R M := by
  have ⟨m, ι, _, p, irr, n, ⟨e⟩⟩ := equiv_free_prod_directSum (R := R) (M := M)
  refine ⟨e.symm (Finsupp.equivFunOnFinite.symm fun _ ↦ 1, DFinsupp.equivFunOnFintype.symm
    fun _ ↦ mkQ _ 1), le_antisymm (fun x h ↦ ?_) fun x h ↦ mem_annihilator.mp h _⟩
  rw [mem_ker, toSpanSingleton_apply, ← map_smul,
    e.symm.map_eq_zero_iff, Prod.ext_iff, Finsupp.ext_iff, DFinsupp.ext_iff] at h
  obtain _ | m := m
  · rw [← mul_one x, ← smul_eq_mul, e.annihilator_eq, annihilator_prod]
    simp_rw [annihilator_eq_top_iff.mpr inferInstance, DirectSum, annihilator_dfinsupp,
      top_inf_eq, mem_iInf, Ideal.annihilator_quotient, ← Quotient.mk_eq_zero]
    exact h.2
  · rw [show x = 0 by simpa using h.1 0]
    exact zero_mem _

end Module

