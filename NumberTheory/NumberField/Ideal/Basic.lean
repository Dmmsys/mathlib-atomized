/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Basic results on integral ideals of a number field

We study results about integral ideals of a number field `K`.

## Main definitions and results

* `Ideal.rootsOfUnityMapQuot` : For `I` an integral ideal of `K`, the group morphism from the
  group of roots of unity of `K` of order `n` to `(𝓞 K ⧸ I)ˣ`.

* `Ideal.rootsOfUnityMapQuot_injective`: If the ideal `I` is nontrivial and its norm is coprime
  with `n`, then the map `Ideal.rootsOfUnityMapQuot` is injective.

* `NumberField.torsionOrder_dvd_absNorm_sub_one`: If the norm of the (nonzero) prime ideal `P` is
  coprime with the order of the torsion of `K`, then the norm of `P` is congruent to `1` modulo
  `torsionOrder K`.

-/

@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

/-
**IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one [NumberField K] (hI : absNor
m I != 1) {n : Nat} {ζ : K} (hn : 2 <= n) (hζ : IsPrimitiveRoot ζ n) (h : letI _
 : NeZero n
参数：hI : absNorm I != 1；hn : 2 <= n；hζ : IsPrimitiveRoot ζ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `NeZero.of_gt`：of_gt [Preorder α] [IsBotZeroClass α] (h : a < b) : NeZero
 b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.exists_prime_and_dvd`：exists_prime_and_dvd {n : Nat} (hn : n != 1) :
 exists p, Prime p ∧ p ∣ n
· 使用定理 `Nat.Prime.not_dvd_one`：∀ {p : ℕ}, Nat.Prime p → ¬p ∣ 1
· 使用定理 `Nat.dvd_gcd`：∀ {k m n : ℕ}, k ∣ m → k ∣ n → k ∣ m.gcd n
· 使用定理 `IsPrimitiveRoot.prime_dvd_of_dvd_norm_sub_one`：prime_dvd_of_dvd_norm_sub
_one {n : Nat} (hn : 2 <= n) {K : Type*} [Field K] [NumberField K] {ζ : K} {p : 
Nat} [hF : Fact (Nat.Prime p)] (hζ …
· 使用定理 `Int.dvd_trans`：∀ {a b c : ℤ}, a ∣ b → b ∣ c → a ∣ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Int.natCast_dvd_natCast`：∀ {m n : ℕ}, ↑m ∣ ↑n ↔ m ∣ n
· 使用定理 `Ideal.absNorm_dvd_norm_of_mem`：absNorm_dvd_norm_of_mem {I : Ideal S} {x 
: S} (h : x in I) : ↑(Ideal.absNorm I) ∣ Algebra.norm Int x
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
-/
theorem IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one [NumberField K] (hI : absNorm I ≠ 1) {n : ℕ}
    {ζ : K} (hn : 2 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (h : letI _ : NeZero n := NeZero.of_gt hn; Ideal.Quotient.mk I hζ.toInteger = 1) :
    ¬ (absNorm I).Coprime n := by
  intro h₁
  rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at h
  obtain ⟨p, hp, h₂⟩ := Nat.exists_prime_and_dvd hI
  have : Fact (p.Prime) := ⟨hp⟩
  refine hp.not_dvd_one <| h₁ ▸ Nat.dvd_gcd h₂ ?_
  exact hζ.prime_dvd_of_dvd_norm_sub_one hn <|
    Int.dvd_trans (Int.natCast_dvd_natCast.mpr h₂) (absNorm_dvd_norm_of_mem h)

variable (I)

/--
For `I` an integral ideal of `K`, the group morphism from the group of roots of unity of `K`
of order `n` to `(𝓞 K ⧸ I)ˣ`.
-/
/-
**Ideal.rootsOfUnityMapQuot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.rootsOfUnityMapQuot (n : Nat) : (rootsOfUnity n (𝓞 K)) ->* ((𝓞 K) ⧸ 
I)ˣ
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `I` an integral ideal of `K`, the group morphism from the group of roots of 
unity of `K`
of order `n` to `(𝓞 K ⧸ I)ˣ`.
-/
def Ideal.rootsOfUnityMapQuot (n : ℕ) : (rootsOfUnity n (𝓞 K)) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict _

@[simp]
/-
**Ideal.rootsOfUnityMapQuot_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.rootsOfUnityMapQuot_apply (n : Nat) {x : (𝓞 K)ˣ} (hx : x in rootsOfU
nity n (𝓞 K)) : rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x
参数：n : Nat；𝓞 K；hx : x in rootsOfUnity n (𝓞 K)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ideal.rootsOfUnityMapQuot_apply (n : ℕ) {x : (𝓞 K)ˣ} (hx : x ∈ rootsOfUnity n (𝓞 K)) :
    rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

/--
For `I` an integral ideal of `K`, the group morphism from the torsion of `K` to `(𝓞 K ⧸ I)ˣ`.
-/
/-
**Ideal.torsionMapQuot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Ideal.torsionMapQuot : (Units.torsion K) ->* ((𝓞 K) ⧸ I)ˣ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `I` an integral ideal of `K`, the group morphism from the torsion of `K` to 
`(𝓞 K ⧸ I)ˣ`.
-/
def Ideal.torsionMapQuot : (Units.torsion K) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).domRestrict (torsion K)

@[simp]
/-
**Ideal.torsionMapQuot_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.torsionMapQuot_apply {x : (𝓞 K)ˣ} (hx : x in torsion K) : torsionMap
Quot I ⟨x, hx⟩ = Ideal.Quotient.mk I x
参数：𝓞 K；hx : x in torsion K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Ideal.torsionMapQuot_apply {x : (𝓞 K)ˣ} (hx : x ∈ torsion K) :
    torsionMapQuot I ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

variable {I} [NumberField K]
/-
**Ideal.rootsOfUnityMapQuot_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.rootsOfUnityMapQuot_injective (n : Nat) [NeZero n] (hI₁ : absNorm I 
!= 1) (hI₂ : (absNorm I).Coprime n) : Function.Injective (rootsOfUnityMapQuot I 
n)
参数：n : Nat；hI₁ : absNorm I != 1；hI₂ : (absNorm I).Coprime n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_one`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9}
 [inst : Group G] [inst_1 : MulOneClass H] [inst_2 : FunLike F G H]   [MonoidHom
Class F G H] (…
· 使用定理 `isPrimitiveRoot_of_mem_rootsOfUnity`：∀ {M : Type u_1} [inst : CommMonoid
 M] {u : Mˣ} {n : ℕ} [NeZero n],   u ∈ rootsOfUnity n M → ∃ d, d ≠ 0 ∧ d ∣ n ∧ I
sPrimitiveRoot u d
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsPrimitiveRoot.coe_units_iff`：coe_units_iff {ζ : Mˣ} : IsPrimitiveRoot 
(ζ : M) k ↔ IsPrimitiveRoot ζ k
· 使用引理 `NumberField.RingOfIntegers.coe_injective`：coe_injective : Function.Injec
tive (algebraMap (𝓞 K) K)
· 使用定理 `IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one`：IsPrimitiveRoot.not_copri
me_norm_of_mk_eq_one [NumberField K] (hI : absNorm I != 1) {n : Nat} {ζ : K} (hn
 : 2 <= n) (hζ : IsPrimitiveRoot ζ …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Units.val_one`：val_one : ((1 : αˣ) : α) = 1
· 使用定理 `Ideal.rootsOfUnityMapQuot_apply`：Ideal.rootsOfUnityMapQuot_apply (n : Na
t) {x : (𝓞 K)ˣ} (hx : x in rootsOfUnity n (𝓞 K)) : rootsOfUnityMapQuot I n ⟨x, h
x⟩ = Ideal.Quotient.m…
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.gcd_dvd_gcd_of_dvd_right`：∀ {m k : ℕ} (n : ℕ), m ∣ k → n.gcd m ∣ n.g
cd k
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Ideal.rootsOfUnityMapQuot_injective (n : ℕ) [NeZero n] (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime n) :
    Function.Injective (rootsOfUnityMapQuot I n) := by
  refine (injective_iff_map_eq_one _).mpr fun ⟨ζ, hζ⟩ h ↦ ?_
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity hζ
  suffices ¬ (2 ≤ t) by
    simpa [show t = 1 by grind] using hζ
  intro ht'
  let μ : K := ζ.val
  have hμ : IsPrimitiveRoot μ t :=
    (IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective RingOfIntegers.coe_injective
  rw [Units.ext_iff, rootsOfUnityMapQuot_apply, Units.val_one] at h
  refine hμ.not_coprime_norm_of_mk_eq_one hI₁ ht' h ?_
  exact Nat.dvd_one.mp (hI₂ ▸ Nat.gcd_dvd_gcd_of_dvd_right (absNorm I) ht)
/-
**IsPrimitiveRoot.idealQuotient_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrimitiveRoot.idealQuotient_mk {n : Nat} [NeZero n] {ζ : (𝓞 K)} (hζ : Is
PrimitiveRoot ζ n) (hI₁ : absNorm I != 1) (hI₂ : (absNorm I).Coprime n) : IsPrim
itiveRoot (Ideal.Quotient.mk I ζ) n
参数：𝓞 K；hζ : IsPrimitiveRoot ζ n；hI₁ : absNorm I != 1；hI₂ : (absNorm I).Coprime n
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsPrimitiveRoot.coe_submonoidClass_iff`：coe_submonoidClass_iff {M B : Ty
pe*} [CommMonoid M] [SetLike B M] [SubmonoidClass B M] {N : B} {ζ : N} : IsPrimi
tiveRoot (ζ : M) k ↔ IsPrimi…
· 使用定理 `IsPrimitiveRoot.coe_units_iff`：coe_units_iff {ζ : Mˣ} : IsPrimitiveRoot 
(ζ : M) k ↔ IsPrimitiveRoot ζ k
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsPrimitiveRoot.map_of_injective`：map_of_injective [MonoidHomClass F M N
] (h : IsPrimitiveRoot ζ k) (hf : Injective f) : IsPrimitiveRoot (f ζ) k where p
ow_eq_one
· 使用定理 `Ideal.rootsOfUnityMapQuot_injective`：Ideal.rootsOfUnityMapQuot_injective
 (n : Nat) [NeZero n] (hI₁ : absNorm I != 1) (hI₂ : (absNorm I).Coprime n) : Fun
ction.Injective (rootsOfU…
-/
theorem IsPrimitiveRoot.idealQuotient_mk {n : ℕ} [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
    (hI₁ : absNorm I ≠ 1) (hI₂ : (absNorm I).Coprime n) :
    IsPrimitiveRoot (Ideal.Quotient.mk I ζ) n := by
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp <| IsPrimitiveRoot.coe_units_iff.mp hζ
  exact IsPrimitiveRoot.coe_units_iff.mpr <|
    h.map_of_injective <| Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂
/-
**Ideal.torsionMapQuot_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Ideal.torsionMapQuot_injective (hI₁ : absNorm I != 1) (hI₂ : (absNorm I).C
oprime (torsionOrder K)) : Function.Injective (torsionMapQuot I)
参数：hI₁ : absNorm I != 1；hI₂ : (absNorm I).Coprime (torsionOrder K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.Units.rootsOfUnity_eq_torsion`：rootsOfUnity_eq_torsion : roo
tsOfUnity (torsionOrder K) (𝓞 K) = torsion K
· 使用定理 `Ideal.rootsOfUnityMapQuot_injective`：Ideal.rootsOfUnityMapQuot_injective
 (n : Nat) [NeZero n] (hI₁ : absNorm I != 1) (hI₂ : (absNorm I).Coprime n) : Fun
ction.Injective (rootsOfU…
· 使用定理 `NumberField.Units.instNeZeroNatTorsionOrder`：∀ (K : Type u_1) [inst : Fi
eld K] [NumberField K], NeZero (NumberField.Units.torsionOrder K)
-/
theorem Ideal.torsionMapQuot_injective (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) :
    Function.Injective (torsionMapQuot I) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  rw [← rootsOfUnity_eq_torsion] at hx hy
  rw [Subtype.mk_eq_mk, ← Subtype.mk_eq_mk (h := hx) (h' := hy)]
  exact rootsOfUnityMapQuot_injective (torsionOrder K) hI₁ hI₂ h

/--
If the norm of the (nonzero) prime ideal `P` is coprime with the order of the torsion of `K`, then
the norm of `P` is congruent to `1` modulo `torsionOrder K`.
-/
/-
**NumberField.torsionOrder_dvd_absNorm_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：NumberField.torsionOrder_dvd_absNorm_sub_one {P : Ideal (𝓞 K)} (hP₀ : P !=
 ⊥) (hP₁ : P.IsPrime) (hP₂ : (absNorm P).Coprime (torsionOrder K)) : torsionOrde
r K ∣ absNorm P - 1
参数：𝓞 K；hP₀ : P != ⊥；hP₁ : P.IsPrime；hP₂ : (absNorm P).Coprime (torsionOrder K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.RingOfIntegers.instIsDedekindDomain`：∀ (K : Type u_1) [inst 
: Field K] [NumberField K], IsDedekindDomain (NumberField.RingOfIntegers K)
· 使用定理 `NumberField.RingOfIntegers.instFreeInt`：∀ (K : Type u_1) [inst : Field K
] [NumberField K], Module.Free ℤ (NumberField.RingOfIntegers K)
· 使用定理 `Ring.DimensionLEOne.maximalOfPrime`：∀ {R : Type u_1} {inst : CommRing R}
 [self : Ring.DimensionLEOne R] {p : Ideal R}, p ≠ ⊥ → p.IsPrime → p.IsMaximal
· 使用定理 `Ring.HasFiniteQuotients.instDimensionLEOne`：∀ {R : Type u_1} [inst : Com
mRing R] [Ring.HasFiniteQuotients R], Ring.DimensionLEOne R
· 使用定理 `Ring.HasFiniteQuotients.instOfIsDomainOfFiniteInt`：∀ {R : Type u_1} [ins
t : CommRing R] [IsDomain R] [Module.Finite ℤ R], Ring.HasFiniteQuotients R
· 使用定理 `NumberField.instIsDomainRingOfIntegers`：∀ (K : Type u_1) [inst : Field K
], IsDomain (NumberField.RingOfIntegers K)
· 使用定理 `AddMonoid.fg_of_addGroup_fg`：∀ {G : Type u_3} [inst : AddGroup G] [AddGr
oup.FG G], AddMonoid.FG G
· 使用定理 `NumberField.RingOfIntegers.instFG`：∀ (K : Type u_1) [inst : Field K] [Nu
mberField K], AddGroup.FG (NumberField.RingOfIntegers K)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.absNorm_eq_one_iff`：absNorm_eq_one_iff {I : Ideal S} : absNorm I =
 1 ↔ I = ⊤
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Subgroup.card_dvd_of_injective`：card_dvd_of_injective (f : α ->* H) (hf 
: Function.Injective f) : Nat.card α ∣ Nat.card H
· 使用定理 `Ideal.torsionMapQuot_injective`：Ideal.torsionMapQuot_injective (hI₁ : ab
sNorm I != 1) (hI₂ : (absNorm I).Coprime (torsionOrder K)) : Function.Injective 
(torsionMapQuot I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_units`：Nat.card_units [GroupWithZero α] : Nat.card αˣ = Nat.car
d α - 1

--- 原说明 ---
If the norm of the (nonzero) prime ideal `P` is coprime with the order of the to
rsion of `K`, then
the norm of `P` is congruent to `1` modulo `torsionOrder K`.
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one {P : Ideal (𝓞 K)} (hP₀ : P ≠ ⊥)
    (hP₁ : P.IsPrime) (hP₂ : (absNorm P).Coprime (torsionOrder K)) :
    torsionOrder K ∣ absNorm P - 1 := by
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP₁
  let _ := Ideal.Quotient.field P
  have hP₃ : absNorm P ≠ 1 := absNorm_eq_one_iff.not.mpr <| IsPrime.ne_top hP₁
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective hP₃ hP₂)
  rwa [Nat.card_units] at h

end torsionMapQuot

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NumberField K] [I.IsMaximal] : Finite (𝓞 K ⧸ I) :=
  I.finiteQuotientOfFreeOfNeBot (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
