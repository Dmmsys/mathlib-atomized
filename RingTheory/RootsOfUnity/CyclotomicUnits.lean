/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Riccardo Brasca
-/
module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Cyclotomic units.

We gather miscellaneous results about units given by sums of powers of roots of unit, the so-called
*cyclotomic units*.


## Main results

* `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime` : given an `n`-th primitive root of
  unity `ζ`, we have that `ζ - 1` and `ζ ^ j - 1` are associated for all `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime` : given an `n`-th primitive root of unity
  `ζ`, we have that `ζ ^ i - 1` and `ζ ^ j - 1` are associated for all `i` and `j` coprime with `n`.
* `IsPrimitiveRoot.associated_pow_add_sub_sub_one` : given an `n`-th primitive root of unity `ζ`,
  where `2 ≤ n`, we have that `ζ - 1` and `ζ ^ (i + j) - ζ ^ i` are associated for all and `j`
  coprime with `n` and all `i`.

## Implementation details

We sometimes state series of results of the form `a = u * b`, `IsUnit u` and `Associated a b`.
Often, `Associated a b` is everything one needs, and it is more convenient to use, we include the
other version for completeness.
-/

public section

open Polynomial Finset Nat

variable {n i j p : ℕ} {A K : Type*} {ζ : A}

variable [CommRing A] [IsDomain A] {R : Type*} [CommRing R] [Algebra R A]

/-- If `ζ ^ n = 1` and `ζ ≠ 1`, then `ζ - 1` divides `n`. This does not require `ζ` to be a
  primitive root of unity, only a root of unity different from `1`. -/
/-
**sub_one_dvd_natCast_of_pow_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_one_dvd_natCast_of_pow_eq_one (hζ : ζ ^ n = 1) (hζ1 : ζ != 1) : ζ - 1 
∣ (n : A)
参数：hζ : ζ ^ n = 1；hζ1 : ζ != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `geom_sum_mul`：geom_sum_mul (x : R) (n : Nat) : (∑ i in range n, x ^ i) *
 (x - 1) = x ^ n - 1
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.dvd_sum`：dvd_sum (h : forall i in s, a ∣ f i) : a ∣ ∑ i in s, f i
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用引理 `sub_dvd_pow_sub_pow`：sub_dvd_pow_sub_pow (x y : R) (n : Nat) : x - y ∣ x
 ^ n - y ^ n
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b

--- 原说明 ---
If `ζ ^ n = 1` and `ζ ≠ 1`, then `ζ - 1` divides `n`. This does not require `ζ` 
to be a
  primitive root of unity, only a root of unity different from `1`.
-/
theorem sub_one_dvd_natCast_of_pow_eq_one (hζ : ζ ^ n = 1) (hζ1 : ζ ≠ 1) : ζ - 1 ∣ (n : A) := by
  have key : (n : A) = ∑ i ∈ range n, (1 - ζ ^ i) := by
    have hgs : ∑ i ∈ range n, ζ ^ i = 0 := by
      have := geom_sum_mul ζ n
      rw [hζ, sub_self] at this
      exact (mul_eq_zero.1 this).resolve_right fun h ↦ hζ1 (sub_eq_zero.1 h)
    rw [Finset.sum_sub_distrib, hgs, sub_zero, Finset.sum_const, card_range, nsmul_eq_mul, mul_one]
  rw [key]
  refine Finset.dvd_sum fun i _ ↦ ?_
  have h : ζ - 1 ∣ ζ ^ i - 1 := by simpa using sub_dvd_pow_sub_pow ζ 1 i
  rwa [← dvd_neg, neg_sub] at h

namespace IsPrimitiveRoot

/-- Given an `n`-th primitive root of unity `ζ,` we have that `ζ - 1` and `ζ ^ j - 1` are associated
  for all `j` coprime with `n`.
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum` gives an explicit formula for the unit. -/
/-
**IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime** 是 Mathlib 中的一个定理，位
于命名空间 `IsPrimitiveRoot`。
形式化陈述：associated_sub_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj :
 j.Coprime n) : Associated (ζ - 1) (ζ ^ j - 1)
参数：hζ : IsPrimitiveRoot ζ n；hj : j.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `associated_of_dvd_dvd`：associated_of_dvd_dvd [MonoidWithZero M] [IsLeftC
ancelMulZero M] {a b : M} (hab : a ∣ b) (hba : b ∣ a) : a ~ᵤ b
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_geom_sum`：mul_geom_sum (x : R) (n : Nat) : ((x - 1) * ∑ i in range n
, x ^ i) = x ^ n - 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Nat.exists_mul_mod_eq_one_of_coprime`：exists_mul_mod_eq_one_of_coprime {
k n : Nat} (hkn : Coprime n k) (hk : 1 < k) : exists m < k, n * m % k = 1
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用引理 `pow_mod_orderOf`：pow_mod_orderOf (x : G) (n : Nat) : x ^ (n % orderOf x)
 = x ^ n
· 使用定理 `IsPrimitiveRoot.eq_orderOf`：eq_orderOf (h : IsPrimitiveRoot ζ k) : k = o
rderOf ζ

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ,` we have that `ζ - 1` and `ζ ^ j - 1
` are associated
  for all `j` coprime with `n`.
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum` gives an explicit formu
la for the unit.
-/
theorem associated_sub_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) :
    Associated (ζ - 1) (ζ ^ j - 1) := by
  refine associated_of_dvd_dvd ⟨∑ i ∈ range j, ζ ^ i, (mul_geom_sum _ _).symm⟩ ?_
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 =>
      obtain ⟨m, -, hm⟩ := exists_mul_mod_eq_one_of_coprime hj (by lia)
      use ∑ i ∈ range m, (ζ ^ j) ^ i
      rw [mul_geom_sum, ← pow_mul, ← pow_mod_orderOf, ← hζ.eq_orderOf, hm, pow_one]

/-- Given an `n`-th primitive root of unity `ζ`, we have that `ζ ^ j - 1` and `ζ ^ i - 1` are
  associated for all `i` and `j` coprime with `n`. -/
/-
**IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime** 是 Mathlib 中的一个定理，位于命名空
间 `IsPrimitiveRoot`。
形式化陈述：associated_pow_sub_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n) (hi : i.C
oprime n) (hj : j.Coprime n) : Associated (ζ ^ j - 1) (ζ ^ i - 1)
参数：hζ : IsPrimitiveRoot ζ n；hi : i.Coprime n；hj : j.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`：associated_su
b_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) : Ass
ociated (ζ - 1) (ζ ^ j - 1)

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ`, we have that `ζ ^ j - 1` and `ζ ^ i
 - 1` are
  associated for all `i` and `j` coprime with `n`.
-/
theorem associated_pow_sub_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n)
    (hi : i.Coprime n) (hj : j.Coprime n) : Associated (ζ ^ j - 1) (ζ ^ i - 1) := by
  suffices ∀ {j}, j.Coprime n → Associated (ζ - 1) (ζ ^ j - 1) by
    grind [Associated.trans, Associated.symm]
  exact hζ.associated_sub_one_pow_sub_one_of_coprime

/-- Given an `n`-th primitive root of unity `ζ`, we have that `ζ - 1` is associated to any of its
  conjugate. -/
/-
**IsPrimitiveRoot.associated_sub_one_map_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPr
imitiveRoot`。
形式化陈述：associated_sub_one_map_sub_one {n : Nat} [NeZero n] (hζ : IsPrimitiveRoot 
ζ n) (σ : A ≃ₐ[R] A) : Associated (ζ - 1) (σ (ζ - 1))
参数：hζ : IsPrimitiveRoot ζ n；σ : A ≃ₐ[R] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.autToPow_spec`：autToPow_spec [NeZero n] (f : S ≃ₐ[R] S) 
: μ ^ (hμ.autToPow R f : ZMod n).val = f μ
· 使用定理 `IsPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime`：associated_su
b_one_pow_sub_one_of_coprime (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) : Ass
ociated (ζ - 1) (ζ ^ j - 1)
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ`, we have that `ζ - 1` is associated 
to any of its
  conjugate.
-/
theorem associated_sub_one_map_sub_one {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (σ : A ≃ₐ[R] A) : Associated (ζ - 1) (σ (ζ - 1)) := by
  rw [map_sub, map_one, ← hζ.autToPow_spec R σ]
  apply hζ.associated_sub_one_pow_sub_one_of_coprime
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) σ)

/-- Given an `n`-th primitive root of unity `ζ`, we have that two conjugates of `ζ - 1`
  are associated. -/
/-
**IsPrimitiveRoot.associated_map_sub_one_map_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `
IsPrimitiveRoot`。
形式化陈述：associated_map_sub_one_map_sub_one {n : Nat} [NeZero n] (hζ : IsPrimitiveR
oot ζ n) (σ τ : A ≃ₐ[R] A) : Associated (σ (ζ - 1)) (τ (ζ - 1))
参数：hζ : IsPrimitiveRoot ζ n；σ τ : A ≃ₐ[R] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrimitiveRoot.autToPow_spec`：autToPow_spec [NeZero n] (f : S ≃ₐ[R] S) 
: μ ^ (hμ.autToPow R f : ZMod n).val = f μ
· 使用定理 `IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime`：associated_pow_su
b_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n) (hi : i.Coprime n) (hj : j.Copri
me n) : Associated (ζ ^ j - 1) (ζ ^ i - 1)
· 使用定理 `ZMod.val_coe_unit_coprime`：val_coe_unit_coprime {n : Nat} (u : (ZMod n)ˣ
) : Nat.Coprime (u : ZMod n).val n

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ`, we have that two conjugates of `ζ -
 1`
  are associated.
-/
theorem associated_map_sub_one_map_sub_one {n : ℕ} [NeZero n] (hζ : IsPrimitiveRoot ζ n)
    (σ τ : A ≃ₐ[R] A) : Associated (σ (ζ - 1)) (τ (ζ - 1)) := by
  rw [map_sub, map_sub, map_one, map_one, ← hζ.autToPow_spec R σ, ← hζ.autToPow_spec R τ]
  apply hζ.associated_pow_sub_one_pow_of_coprime <;>
  exact ZMod.val_coe_unit_coprime ((autToPow R hζ) _)

/-- Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `∑ i ∈ range j, ζ ^ i`
  is a unit for all `j` coprime with `n`. This is the unit given by
  `associated_pow_sub_one_pow_of_coprime` (see
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum`). -/
/-
**IsPrimitiveRoot.geom_sum_isUnit** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：geom_sum_isUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (hj : j.Coprime n
) : IsUnit (∑ i in range j, ζ ^ i)
参数：hζ : IsPrimitiveRoot ζ n；hn : 2 <= n；hj : j.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.associated_pow_sub_one_pow_of_coprime`：associated_pow_su
b_one_pow_of_coprime (hζ : IsPrimitiveRoot ζ n) (hi : i.Coprime n) (hj : j.Copri
me n) : Associated (ζ ^ j - 1) (ζ ^ i - 1)
· 使用定理 `Nat.coprime_one_left`：∀ (n : ℕ), Nat.Coprime 1 n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_right_injective₀`：mul_right_injective₀ (ha : a != 0) : Function.Inje
ctive (a * ·)
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `∑ i ∈ 
range j, ζ ^ i`
  is a unit for all `j` coprime with `n`. This is the unit given by
  `associated_pow_sub_one_pow_of_coprime` (see
  `pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum`).
-/
theorem geom_sum_isUnit (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (hj : j.Coprime n) :
    IsUnit (∑ i ∈ range j, ζ ^ i) := by
  obtain ⟨u, hu⟩ := hζ.associated_pow_sub_one_pow_of_coprime hj (coprime_one_left n)
  convert! u.isUnit
  apply mul_right_injective₀ (show 1 - ζ ≠ 0 by grind [sub_one_ne_zero])
  grind [mul_neg_geom_sum]

/-- Similar to `geom_sum_isUnit`, but instead of assuming `2 ≤ n` we assume that `j` is a unit in
  `A`. -/
/-
**IsPrimitiveRoot.geom_sum_isUnit'** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：geom_sum_isUnit' (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) (hj_Unit : 
IsUnit (j : A)) : IsUnit (∑ i in range j, ζ ^ i)
参数：hζ : IsPrimitiveRoot ζ n；hj : j.Coprime n；hj_Unit : IsUnit (j : A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `IsPrimitiveRoot.geom_sum_isUnit`：geom_sum_isUnit (hζ : IsPrimitiveRoot ζ
 n) (hn : 2 <= n) (hj : j.Coprime n) : IsUnit (∑ i in range j, ζ ^ i)
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
Similar to `geom_sum_isUnit`, but instead of assuming `2 ≤ n` we assume that `j`
 is a unit in
  `A`.
-/
theorem geom_sum_isUnit' (hζ : IsPrimitiveRoot ζ n) (hj : j.Coprime n) (hj_Unit : IsUnit (j : A)) :
    IsUnit (∑ i ∈ range j, ζ ^ i) := by
  match n with
  | 0 => simp_all
  | 1 => simp_all
  | n + 2 => exact geom_sum_isUnit hζ (by linarith) hj
/-
**IsPrimitiveRoot.pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one** 是 M
athlib 中的一个定理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one (hζ : IsPrimitive
Root ζ n) (hn : 2 <= n) (hi : i.Coprime n) (hj : j.Coprime n) : (ζ ^ j - 1) = (h
ζ.geom_sum_isUnit hn hj).unit * (hζ.geom_sum_isUnit hn hi).unit⁻¹ * (ζ ^ i - 1)
参数：hζ : IsPrimitiveRoot ζ n；hn : 2 <= n；hi : i.Coprime n；hj : j.Coprime n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one (hζ : IsPrimitiveRoot ζ n)
    (hn : 2 ≤ n) (hi : i.Coprime n) (hj : j.Coprime n) :
    (ζ ^ j - 1) =
      (hζ.geom_sum_isUnit hn hj).unit * (hζ.geom_sum_isUnit hn hi).unit⁻¹ * (ζ ^ i - 1) := by
  grind [IsUnit.mul_val_inv, pow_sub_one_mul_geom_sum_eq_pow_sub_one_mul_geom_sum, IsUnit.unit_spec]

/-- Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `ζ - 1` and
  `ζ ^ (i + j) - ζ ^ i` are associated for all and `j` coprime with `n` and all `i`. See
  `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one` for the explicit formula of the
  unit. -/
/-
**IsPrimitiveRoot.associated_pow_add_sub_sub_one** 是 Mathlib 中的一个定理，位于命名空间 `IsPr
imitiveRoot`。
形式化陈述：associated_pow_add_sub_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (i
 : Nat) (hjn : j.Coprime n) : Associated (ζ - 1) (ζ ^ (i + j) - ζ ^ i)
参数：hζ : IsPrimitiveRoot ζ n；hn : 2 <= n；i : Nat；hjn : j.Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrimitiveRoot.isUnit`：isUnit (h : IsPrimitiveRoot ζ k) (h0 : k != 0) :
 IsUnit ζ
· 使用定理 `IsPrimitiveRoot.geom_sum_isUnit`：geom_sum_isUnit (hζ : IsPrimitiveRoot ζ
 n) (hn : 2 <= n) (hj : j.Coprime n) : IsUnit (∑ i in range j, ζ ^ i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ`, where `2 ≤ n`, we have that `ζ - 1`
 and
  `ζ ^ (i + j) - ζ ^ i` are associated for all and `j` coprime with `n` and all 
`i`. See
  `pow_sub_one_eq_geom_sum_mul_geom_sum_inv_mul_pow_sub_one` for the explicit fo
rmula of the
  unit.
-/
theorem associated_pow_add_sub_sub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 ≤ n) (i : ℕ)
    (hjn : j.Coprime n) : Associated (ζ - 1) (ζ ^ (i + j) - ζ ^ i) := by
  use (hζ.isUnit (by lia)).unit ^ i * (hζ.geom_sum_isUnit hn hjn).unit
  suffices (ζ - 1) * ζ ^ i * ∑ i ∈ range j, ζ ^ i = (ζ ^ (i + j) - ζ ^ i) by
    simp [← this, mul_assoc]
  grind [mul_geom_sum]

/-- If `p` is prime and `ζ` is a `p`-th primitive root of unity, then `ζ - 1` and `η₁ - η₂` are
  associated for all distinct `p`-th roots of unity `η₁` and `η₂`. -/
/-
**IsPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime** 是 Ma
thlib 中的一个引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：nthRootsFinset_pairwise_associated_sub_one_sub_of_prime (hζ : IsPrimitiveR
oot ζ p) (hp : p.Prime) : Set.Pairwise (nthRootsFinset p (1 : A)) fun η₁ η₂ => A
ssociated (ζ - 1) (η₁ - η₂)
参数：hζ : IsPrimitiveRoot ζ p；hp : p.Prime。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `IsPrimitiveRoot.eq_pow_of_pow_eq_one`：eq_pow_of_pow_eq_one {k : Nat} [Ne
Zero k] {ζ ξ : R} (h : IsPrimitiveRoot ζ k) (hξ : ξ ^ k = 1) : exists i < k, ζ ^
 i = ξ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_nthRootsFinset`：mem_nthRootsFinset {n : Nat} (h : 0 < n) 
(a : R) {x : R} : x in nthRootsFinset n a ↔ x ^ (n : Nat) = a
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Nat.Coprime.symm`：∀ {n m : ℕ}, n.Coprime m → m.Coprime n
· 使用定理 `Nat.coprime_of_lt_prime`：coprime_of_lt_prime {n p} (ne_zero : n != 0) (h
lt : n < p) (pp : Prime p) : Coprime p n
· 使用定理 `IsPrimitiveRoot.associated_pow_add_sub_sub_one`：associated_pow_add_sub_s
ub_one (hζ : IsPrimitiveRoot ζ n) (hn : 2 <= n) (i : Nat) (hjn : j.Coprime n) : 
Associated (ζ - 1) (ζ ^ (i + j) - ζ …
· 使用定理 `Nat.Prime.two_le`：∀ {p : ℕ}, Nat.Prime p → 2 ≤ p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `associated_mul_unit_right_iff`：associated_mul_unit_right_iff {N : Type*}
 [Monoid N] {a b : N} {u : Units N} : Associated a (b * u) ↔ Associated a b
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用引理 `Associated.neg_right`：neg_right (h : Associated a b) : Associated a (-b)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If `p` is prime and `ζ` is a `p`-th primitive root of unity, then `ζ - 1` and `η
₁ - η₂` are
  associated for all distinct `p`-th roots of unity `η₁` and `η₂`.
-/
lemma nthRootsFinset_pairwise_associated_sub_one_sub_of_prime (hζ : IsPrimitiveRoot ζ p)
    (hp : p.Prime) :
    Set.Pairwise (nthRootsFinset p (1 : A)) fun η₁ η₂ ↦ Associated (ζ - 1) (η₁ - η₂) := by
  intro η₁ hη₁ η₂ hη₂ e
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i, hi, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₁)
  obtain ⟨j, hj, rfl⟩ := hζ.eq_pow_of_pow_eq_one ((Polynomial.mem_nthRootsFinset hp.pos 1).1 hη₂)
  wlog hij : j ≤ i
  · simpa using (this hζ ‹_› ‹_› _ hj ‹_› _ hi ‹_› e.symm (by lia)).neg_right
  have H : (i - j).Coprime p := (coprime_of_lt_prime (by grind) (by grind) hp).symm
  obtain ⟨u, h⟩ := hζ.associated_pow_add_sub_sub_one hp.two_le j H
  simp only [hij, add_tsub_cancel_of_le] at h
  rw [← h, associated_mul_unit_right_iff]

@[deprecated (since := "2026-06-23")]
alias ntRootsFinset_pairwise_associated_sub_one_sub_of_prime :=
  nthRootsFinset_pairwise_associated_sub_one_sub_of_prime

/-- If `p` is prime and `ζ` is a `p`-th primitive root of unity, then `ζ - 1` divides `η₁ - η₂`
for all `p`-th roots of unity `η₁` and `η₂`. -/
/-
**IsPrimitiveRoot.sub_one_dvd_sub** 是 Mathlib 中的一个引理，位于命名空间 `IsPrimitiveRoot`。
形式化陈述：sub_one_dvd_sub (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime) {η₁ : A} (hη₁ : 
η₁ in nthRootsFinset p (1 : A)) {η₂ : A} (hη₂ : η₂ in nthRootsFinset p (1 : A)) 
: ζ - 1 ∣ η₁ - η₂
参数：hζ : IsPrimitiveRoot ζ p；hp : p.Prime；hη₁ : η₁ in nthRootsFinset p (1 : A)；hη
₂ : η₂ in nthRootsFinset p (1 : A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用引理 `IsPrimitiveRoot.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime`
：nthRootsFinset_pairwise_associated_sub_one_sub_of_prime (hζ : IsPrimitiveRoot ζ
 p) (hp : p.Prime) : Set.Pairwise (nthRootsFinset p (1 : A)) …

--- 原说明 ---
If `p` is prime and `ζ` is a `p`-th primitive root of unity, then `ζ - 1` divide
s `η₁ - η₂`
for all `p`-th roots of unity `η₁` and `η₂`.
-/
lemma sub_one_dvd_sub (hζ : IsPrimitiveRoot ζ p) (hp : p.Prime)
    {η₁ : A} (hη₁ : η₁ ∈ nthRootsFinset p (1 : A))
    {η₂ : A} (hη₂ : η₂ ∈ nthRootsFinset p (1 : A)) :
    ζ - 1 ∣ η₁ - η₂ := by
  rcases eq_or_ne η₁ η₂ with rfl | h
  · simp
  · exact (hζ.nthRootsFinset_pairwise_associated_sub_one_sub_of_prime hp hη₁ hη₂ h).dvd

/-- Given an `n`-th primitive root of unity `ζ`, where `1 < n`, we have that `ζ - 1` divides `n`.
  In particular, if `ζ` is a `p`-th primitive root of unity with `p` prime, then `ζ - 1` divides
  `p`. -/
/-
**IsPrimitiveRoot.sub_one_dvd_natCast** 是 Mathlib 中的一个定理，位于命名空间 `IsPrimitiveRoot
`。
形式化陈述：sub_one_dvd_natCast (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) : ζ - 1 ∣ (n :
 A)
参数：hζ : IsPrimitiveRoot ζ n；hn : 1 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_one_dvd_natCast_of_pow_eq_one`：sub_one_dvd_natCast_of_pow_eq_one (hζ
 : ζ ^ n = 1) (hζ1 : ζ != 1) : ζ - 1 ∣ (n : A)
· 使用定理 `IsPrimitiveRoot.pow_eq_one`：∀ {M : Type u_1} [inst : CommMonoid M] {ζ : 
M} {k : ℕ}, IsPrimitiveRoot ζ k → ζ ^ k = 1
· 使用定理 `IsPrimitiveRoot.ne_one`：ne_one (h : IsPrimitiveRoot ζ k) (hk : 1 < k) : 
ζ != 1

--- 原说明 ---
Given an `n`-th primitive root of unity `ζ`, where `1 < n`, we have that `ζ - 1`
 divides `n`.
  In particular, if `ζ` is a `p`-th primitive root of unity with `p` prime, then
 `ζ - 1` divides
  `p`.
-/
theorem sub_one_dvd_natCast (hζ : IsPrimitiveRoot ζ n) (hn : 1 < n) : ζ - 1 ∣ (n : A) :=
  sub_one_dvd_natCast_of_pow_eq_one hζ.pow_eq_one (hζ.ne_one hn)

end IsPrimitiveRoot

