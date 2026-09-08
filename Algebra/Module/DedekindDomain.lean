/-
Copyright (c) 2022 Pierre-Alexandre Bazin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pierre-Alexandre Bazin
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Modules over a Dedekind domain

Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-torsion
submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals.
Therefore, as any finitely generated torsion module is `I`-torsion for some `I`, it is an internal
direct sum of its `p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/

public section


universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {M : Type v} [AddCommGroup M] [Module R M]

open scoped DirectSum

namespace Submodule

open UniqueFactorizationMonoid

/-- Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its `p i ^ e i`-
torsion submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in prime ideals. -/
/-
**Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal** 是 Mathlib 中的
一个定理，位于命名空间 `Submodule`。
形式化陈述：isInternal_prime_power_torsion_of_is_torsion_by_ideal {I : Ideal R} (hI : 
I != ⊥) (hM : Module.IsTorsionBySet R M I) : DirectSum.IsInternal fun p : (facto
rs I).toFinset => torsionBySet R M (p ^ (factors I).count ↑p : Ideal R)
参数：hI : I != ⊥；hM : Module.IsTorsionBySet R M I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Submodule.torsionBySet_isInternal`：torsionBySet_isInternal {p : ι -> Ide
al R} (hp : (S : Set ι).Pairwise fun i j => p i ⊔ p j = ⊤) (hM : Module.IsTorsio
nBySet R M (⨅ i in S, p…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.irreducible_pow_sup`：irreducible_pow_sup (hI : I != ⊥) (hJ : Irred
ucible J) (n : Nat) : J ^ n ⊔ I = J ^ min ((normalizedFactors I).count J) n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.zero_eq_bot`：zero_eq_bot : (0 : Ideal R) = ⊥
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `Multiset.count_eq_zero`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Mul
tiset α} {a : α}, Multiset.count a s = 0 ↔ a ∉ s
· 使用定理 `UniqueFactorizationMonoid.normalizedFactors_of_irreducible_pow`：normaliz
edFactors_of_irreducible_pow {p : α} (hp : Irreducible p) (k : Nat) : normalized
Factors (p ^ k) = Multiset.replicate k (normalize p)
· 使用定理 `Multiset.mem_replicate`：mem_replicate {a b : α} {n : Nat} : b in replica
te n a ↔ n != 0 ∧ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `normalize_eq`：normalize_eq (x : α) : normalize x = x
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `zero_min`：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Zero α] [IsB
otZeroClass α] (a : α), min 0 a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.inf_eq_iInf`：∀ {α : Type u_2} {β : Type u_3} [inst : CompleteLatt
ice β] (s : Finset α) (f : α → β), s.inf f = ⨅ a ∈ s, f a
· 使用定理 `IsDedekindDomain.inf_pow_eq_prod_of_prime`：inf_pow_eq_prod_of_prime (s :
 Finset ι) (f : ι -> Ideal R) (e : ι -> Nat) (prime : forall i in s, Prime (f i)
) (coprime : forallᵉ (i in s) (…
· 使用定理 `Finset.prod_multiset_count`：prod_multiset_count [DecidableEq M] (s : Mul
tiset M) : s.prod = ∏ m in s.toFinset, m ^ s.count m
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Over a Dedekind domain, an `I`-torsion module is the internal direct sum of its 
`p i ^ e i`-
torsion submodules, where `I = ∏ i, p i ^ e i` is its unique decomposition in pr
ime ideals.
-/
theorem isInternal_prime_power_torsion_of_is_torsion_by_ideal
    {I : Ideal R} (hI : I ≠ ⊥) (hM : Module.IsTorsionBySet R M I) :
    DirectSum.IsInternal fun p : (factors I).toFinset =>
      torsionBySet R M (p ^ (factors I).count ↑p : Ideal R) := by
  let P := factors I
  have prime_of_mem := fun p (hp : p ∈ P.toFinset) =>
    prime_of_factor p (Multiset.mem_toFinset.mp hp)
  apply torsionBySet_isInternal (p := fun p => p ^ P.count p) _
  · convert! hM
    rw [← Finset.inf_eq_iInf, IsDedekindDomain.inf_pow_eq_prod_of_prime,
      ← Finset.prod_multiset_count, ← associated_iff_eq]
    · exact factors_prod hI
    · exact prime_of_mem
    · exact fun _ _ _ _ ij => ij
  · intro p hp q hq pq
    rw [Ideal.irreducible_pow_sup]
    · suffices (normalizedFactors _).count p = 0 by rw [this, zero_min, pow_zero, Ideal.one_eq_top]
      rw [Multiset.count_eq_zero,
        normalizedFactors_of_irreducible_pow (prime_of_mem q hq).irreducible,
        Multiset.mem_replicate]
      exact fun H => pq <| H.2.trans <| normalize_eq q
    · rw [← Ideal.zero_eq_bot]; apply pow_ne_zero; exact (prime_of_mem q hq).ne_zero
    · exact (prime_of_mem p hp).irreducible

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules where `p i` are factors of `(⊤ : Submodule R M).annihilator` and
`e i` are their multiplicities. -/
/-
**Submodule.isInternal_prime_power_torsion** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`
。
形式化陈述：isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion 
R M) : DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).to
Finset => torsionBySet R M (p ^ (factors (⊤ : Submodule R M).annihilator).count 
↑p : Ideal R)
参数：hM : Module.IsTorsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.isTorsionBySet_annihilator_top`：∀ (R : Type u_1) (M : Type u_2) [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M], 
  Module.IsTorsionBySet R M…
· 使用定理 `Submodule.annihilator_top_inter_nonZeroDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Mod
ule R M]   [Module.Finite R M], Modul…
· 使用定理 `Submodule.isInternal_prime_power_torsion_of_is_torsion_by_ideal`：isInter
nal_prime_power_torsion_of_is_torsion_by_ideal {I : Ideal R} (hI : I != ⊥) (hM :
 Module.IsTorsionBySet R M I) : DirectSum.IsInternal …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `nonZeroDivisors.ne_zero`：nonZeroDivisors.ne_zero (hx : x in M₀⁰) : x != 
0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A

--- 原说明 ---
A finitely generated torsion module over a Dedekind domain is an internal direct
 sum of its
`p i ^ e i`-torsion submodules where `p i` are factors of `(⊤ : Submodule R M).a
nnihilator` and
`e i` are their multiplicities.
-/
theorem isInternal_prime_power_torsion [Module.Finite R M]
    (hM : Module.IsTorsion R M) :
    DirectSum.IsInternal fun p : (factors (⊤ : Submodule R M).annihilator).toFinset =>
      torsionBySet R M (p ^ (factors (⊤ : Submodule R M).annihilator).count ↑p : Ideal R) := by
  have hM' := Module.isTorsionBySet_annihilator_top R M
  have hI := Submodule.annihilator_top_inter_nonZeroDivisors hM
  refine isInternal_prime_power_torsion_of_is_torsion_by_ideal ?_ hM'
  rw [Submodule.ne_bot_iff]
  obtain ⟨x, H, hx⟩ := hI; exact ⟨x, H, nonZeroDivisors.ne_zero hx⟩

/-- A finitely generated torsion module over a Dedekind domain is an internal direct sum of its
`p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`. -/
/-
**Submodule.exists_isInternal_prime_power_torsion** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsT
orsion R M) : exists (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : forall p i
n P, Prime p) (e : P -> Nat), DirectSum.IsInternal fun p : P => torsionBySet R M
 (p ^ e p : Ideal R)
参数：hM : Module.IsTorsion R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `UniqueFactorizationMonoid.prime_of_factor`：prime_of_factor {a : α} (x : 
α) (hx : x in factors a) : Prime x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Multiset.mem_toFinset`：mem_toFinset {a : α} {s : Multiset α} : a in s.to
Finset ↔ a in s
· 使用定理 `Submodule.isInternal_prime_power_torsion`：isInternal_prime_power_torsion
 [Module.Finite R M] (hM : Module.IsTorsion R M) : DirectSum.IsInternal fun p : 
(factors (⊤ : Submodule R M).a…

--- 原说明 ---
A finitely generated torsion module over a Dedekind domain is an internal direct
 sum of its
`p i ^ e i`-torsion submodules for some prime ideals `p i` and numbers `e i`.
-/
theorem exists_isInternal_prime_power_torsion [Module.Finite R M] (hM : Module.IsTorsion R M) :
    ∃ (P : Finset <| Ideal R) (_ : DecidableEq P) (_ : ∀ p ∈ P, Prime p) (e : P → ℕ),
      DirectSum.IsInternal fun p : P => torsionBySet R M (p ^ e p : Ideal R) := by
  exact ⟨_, _, fun p hp => prime_of_factor p (Multiset.mem_toFinset.mp hp), _,
    isInternal_prime_power_torsion hM⟩

end Submodule

