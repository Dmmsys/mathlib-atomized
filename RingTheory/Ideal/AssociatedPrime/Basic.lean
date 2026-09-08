/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.MinimalPrime.Colon
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Noetherian.Basic

/-!

# Associated primes of a module

We provide the definition and related lemmas about associated primes of modules.

## Main definition
- `IsAssociatedPrime`: `IsAssociatedPrime I M` if the prime ideal `I` is the
  radical of the annihilator of some `x : M`.
- `associatedPrimes`: The set of associated primes of a module.

## Main results
- `exists_le_isAssociatedPrime_of_isNoetherianRing`: In a Noetherian ring, any `ann(x)` is
  contained in an associated prime for `x ≠ 0`.
- `associatedPrimes.eq_singleton_of_isPrimary`: In a Noetherian ring, `I.radical` is the only
  associated prime of `R ⧸ I` when `I` is primary.

## Implementation details

The presence of the radical in the definition of `IsAssociatedPrime` is slightly nonstandard but
gives the correct characterization of the prime ideals of any minimal primary decomposition in the
non-Noetherian setting (see Theorem 4.5 in Atiyah-Macdonald). If the ring `R` is assumed to be
Noetherian, then the radical can be dropped from the definition (see `isAssociatedPrime_iff`).

See also [Stacks: Lemma 0566](https://stacks.math.columbia.edu/tag/0566) which states that a
prime `p` is minimal among primes containing an annihilator an element of `M` if and only if
`p R_p` is an associated prime of `M_p` (including the radical).

## TODO

Generalize this to a non-commutative setting once there are annihilator for non-commutative rings.

## References

* [M. F. Atiyah and I. G. Macdonald, *Introduction to commutative algebra*][atiyah-macdonald]
-/

@[expose] public section

open LinearMap Submodule

namespace Submodule

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] (N : Submodule R M)
  (I : Ideal R) (x : M)

/-- `I : Ideal R` is an associated prime of a submodule `N : Submodule R M` if `I` is prime
and `I = (colon N {x}).radical` for some `x : M`. -/
/-
**Submodule.IsAssociatedPrime** 是 Mathlib 中的一个归纳类型，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → Submodule R M → Ideal R → Pr
op
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`I : Ideal R` is an associated prime of a submodule `N : Submodule R M` if `I` i
s prime
and `I = (colon N {x}).radical` for some `x : M`.
-/
protected structure IsAssociatedPrime : Prop extends I.IsPrime where
  eq_radical_colon : ∃ x, I = (colon N {x}).radical

/-- The set of associated primes of a submodule. -/
/-
**Submodule.associatedPrimes** 是 Mathlib 中的一个定义，位于命名空间 `Submodule`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     [inst : CommSemiring R] → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → Submodule R M → Set (Ideal R
)
参数：Ideal R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of associated primes of a submodule.
-/
protected def associatedPrimes : Set (Ideal R) :=
  { I | N.IsAssociatedPrime I }

variable {N I}
/-
**Submodule.isAssociatedPrime_def** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M} {I : Ideal R}, N.IsA
ssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = (N.colon {x}).radical
参数：N.colon {x}。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsAssociatedPrime.toIsPrime`：∀ {R : Type u_1} {M : Type u_2} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {N : Submodule R M} {I : I…
· 使用定理 `Submodule.IsAssociatedPrime.eq_radical_colon`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {N : Submodule R M} {I : I…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem isAssociatedPrime_def :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = (colon N {x}).radical :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩
/-
**Submodule.isAssociatedPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M} {I : Ideal R} [IsNoe
therianRing R], N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = N.colon {x}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_eq_colon_of_mem_minimalPrimes`：exists_eq_colon_of_mem_m
inimalPrimes [IsNoetherianRing R] (hI : I in (N.colon {x}).minimalPrimes) : exis
ts x' : M, I = N.colon {x'}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.radical_minimalPrimes`：Ideal.radical_minimalPrimes : I.radical.min
imalPrimes = I.minimalPrimes
· 使用定理 `Ideal.minimalPrimes_eq_subsingleton_self`：Ideal.minimalPrimes_eq_subsing
leton_self [I.IsPrime] : I.minimalPrimes = {I}
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Ideal.IsPrime.radical`：∀ {R : Type u} [inst : CommSemiring R] {I : Ideal
 R}, I.IsPrime → I.radical = I
-/
protected theorem isAssociatedPrime_iff [IsNoetherianRing R] :
    N.IsAssociatedPrime I ↔ I.IsPrime ∧ ∃ x, I = colon N {x} := by
  constructor
  · rintro ⟨hx, x, rfl⟩
    refine ⟨hx, exists_eq_colon_of_mem_minimalPrimes (x := x) ?_⟩
    rw [← Ideal.radical_minimalPrimes, Ideal.minimalPrimes_eq_subsingleton_self,
      Set.mem_singleton_iff]
  · rintro ⟨hx, x, rfl⟩
    exact ⟨hx, x, hx.radical.symm⟩
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : N.associatedPrimes) : I.1.IsPrime := I.2.1
/-
**Submodule.AssociatePrimes.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.Associa
tePrimes`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommM
onoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M} {I : Ideal R}, I ∈ N
.associatedPrimes ↔ N.IsAssociatedPrime I
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
protected theorem AssociatePrimes.mem_iff : I ∈ N.associatedPrimes ↔ N.IsAssociatedPrime I :=
  .rfl

end Submodule

section Semiring

variable {R : Type*} [CommSemiring R] (I J : Ideal R) (M : Type*) [AddCommMonoid M] [Module R M]

/-- `IsAssociatedPrime I M` if the prime ideal `I` is the radical of the annihilator
of some `x : M`. -/
/-
**IsAssociatedPrime** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsAssociatedPrime : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`IsAssociatedPrime I M` if the prime ideal `I` is the radical of the annihilator
of some `x : M`.
-/
def IsAssociatedPrime : Prop :=
  (⊥ : Submodule R M).IsAssociatedPrime I

variable (R) in
/-- The set of associated primes of a module. -/
/-
**associatedPrimes** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：associatedPrimes : Set (Ideal R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of associated primes of a module.
-/
def associatedPrimes : Set (Ideal R) :=
  { I | IsAssociatedPrime I M }

variable {I J M} {M' : Type*} [AddCommMonoid M'] [Module R M'] (f : M →ₗ[R] M')
/-
**AssociatedPrimes.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AssociatedPrimes.mem_iff : I in associatedPrimes R M ↔ IsAssociatedPrime I
 M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem AssociatedPrimes.mem_iff : I ∈ associatedPrimes R M ↔ IsAssociatedPrime I M := Iff.rfl
/-
**IsAssociatedPrime.isPrime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime
参数：h : IsAssociatedPrime I M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsAssociatedPrime.toIsPrime`：∀ {R : Type u_1} {M : Type u_2} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {N : Submodule R M} {I : I…
-/
theorem IsAssociatedPrime.isPrime (h : IsAssociatedPrime I M) : I.IsPrime := h.1
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : associatedPrimes R M) : I.1.IsPrime := I.2.1
/-
**isAssociatedPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAssociatedPrime_iff [IsNoetherianRing R] : IsAssociatedPrime I M ↔ I.IsP
rime ∧ exists x : M, I = colon ⊥ {x}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.isAssociatedPrime_iff`：∀ {R : Type u_1} {M : Type u_2} [inst :
 CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Submodule R M} {I : I…
-/
theorem isAssociatedPrime_iff [IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ x : M, I = colon ⊥ {x} :=
  (⊥ : Submodule R M).isAssociatedPrime_iff

set_option backward.isDefEq.respectTransparency false in
/-
**IsAssociatedPrime.map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Funct
ion.Injective f) : IsAssociatedPrime I M'
参数：h : IsAssociatedPrime I M；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsAssociatedPrime.eq_radical_colon`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module
 R M]   {N : Submodule R M} {I : I…
· 使用定理 `Submodule.IsAssociatedPrime.toIsPrime`：∀ {R : Type u_1} {M : Type u_2} [
inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]  
 {N : Submodule R M} {I : I…
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsAssociatedPrime.map_of_injective (h : IsAssociatedPrime I M) (hf : Function.Injective f) :
    IsAssociatedPrime I M' := by
  obtain ⟨x, rfl⟩ := h.2
  refine ⟨h.1, ⟨f x, ?_⟩⟩
  ext r
  simp_rw [Ideal.mem_radical_iff, mem_colon_singleton, mem_bot, ← map_smul, map_eq_zero_iff f hf]
/-
**LinearEquiv.isAssociatedPrime_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') : IsAssociatedPrime I M
 ↔ IsAssociatedPrime I M'
参数：l : M ≃ₗ[R] M'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAssociatedPrime.map_of_injective`：IsAssociatedPrime.map_of_injective (
h : IsAssociatedPrime I M) (hf : Function.Injective f) : IsAssociatedPrime I M'
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem LinearEquiv.isAssociatedPrime_iff (l : M ≃ₗ[R] M') :
    IsAssociatedPrime I M ↔ IsAssociatedPrime I M' :=
  ⟨fun h => h.map_of_injective l l.injective,
    fun h => h.map_of_injective l.symm l.symm.injective⟩
/-
**not_isAssociatedPrime_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrim
e I M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem not_isAssociatedPrime_of_subsingleton [Subsingleton M] : ¬IsAssociatedPrime I M := by
  rintro ⟨hI, x, hx⟩
  apply hI.ne_top
  simp [hx, Subsingleton.elim x 0]

variable (R) in
/-
**exists_le_isAssociatedPrime_of_isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (
x : M) (hx : x != 0) : exists P : Ideal R, IsAssociatedPrime P M ∧ (⊥ : Submodul
e R M).colon {x} <= P
参数：x : M；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `set_has_maximal_iff_noetherian`：set_has_maximal_iff_noetherian : (forall
 a : Set <| Submodule R M, a.Nonempty -> exists M' in a, forall I in a, ¬M' < I)
 ↔ IsNoetherian R M
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Submodule.mem_colon_singleton`：mem_colon_singleton {x : M} {r : R} : r i
n N.colon {x} ↔ r • x in N
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `LE.le.eq_of_not_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, 
a ≤ b → ¬a < b → a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_le_isAssociatedPrime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M)
    (hx : x ≠ 0) : ∃ P : Ideal R, IsAssociatedPrime P M ∧ (⊥ : Submodule R M).colon {x} ≤ P := by
  simp only [isAssociatedPrime_iff]
  obtain ⟨P, ⟨l, h₁, y, rfl⟩, h₃⟩ :=
    set_has_maximal_iff_noetherian.mpr H
      { P | (⊥ : Submodule R M).colon {x} ≤ P ∧ P ≠ ⊤ ∧ ∃ y : M, P = (⊥ : Submodule R M).colon {y} }
      ⟨_, rfl.le, by simpa, x, rfl⟩
  refine ⟨_, ⟨⟨h₁, ?_⟩, y, rfl⟩, l⟩
  intro a b hab
  rw [or_iff_not_imp_left]
  intro ha
  rw [mem_colon_singleton] at ha hab
  have H₁ : (⊥ : Submodule R M).colon {y} ≤ (⊥ : Submodule R M).colon {a • y} := by
    intro c hc
    rw [mem_colon_singleton, mem_bot] at hc ⊢
    rw [smul_comm, hc, smul_zero]
  rwa [H₁.eq_of_not_lt (h₃ _ ⟨l.trans H₁, by simpa, _, rfl⟩),
    mem_colon_singleton, smul_comm, smul_smul]

namespace associatedPrimes

variable {f} {M'' : Type*} [AddCommMonoid M''] [Module R M''] {g : M' →ₗ[R] M''}

/-- If `M → M'` is injective, then the set of associated primes of `M` is
contained in that of `M'`. -/
@[stacks 02M3 "first part"]
/-
**associatedPrimes.subset_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `associatedPrim
es`。
形式化陈述：subset_of_injective (hf : Function.Injective f) : associatedPrimes R M sub
seteq associatedPrimes R M'
参数：hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAssociatedPrime.map_of_injective`：IsAssociatedPrime.map_of_injective (
h : IsAssociatedPrime I M) (hf : Function.Injective f) : IsAssociatedPrime I M'

--- 原说明 ---
If `M → M'` is injective, then the set of associated primes of `M` is
contained in that of `M'`.
-/
theorem subset_of_injective (hf : Function.Injective f) :
    associatedPrimes R M ⊆ associatedPrimes R M' := fun _I h => h.map_of_injective f hf

/-- If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of `M'` is
contained in the union of those of `M` and `M''`. -/
@[stacks 02M3 "second part"]
/-
**associatedPrimes.subset_union_of_exact** 是 Mathlib 中的一个定理，位于命名空间 `associatedPr
imes`。
形式化陈述：subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f 
g) : associatedPrimes R M' subseteq associatedPrimes R M union associatedPrimes 
R M''
参数：hf : Function.Injective f；hfg : Function.Exact f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_colon_singleton`：mem_colon_singleton {x : M} {r : R} : r i
n N.colon {x} ↔ r • x in N
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Submonoid.pow_mem`：∀ {M : Type u_5} [inst : Monoid M] (S : Submonoid M) 
{x : M}, x ∈ S → ∀ (n : ℕ), x ^ n ∈ S
· 使用定理 `Ideal.radical_mono`：radical_mono (H : I <= J) : radical I <= radical J
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
If `0 → M → M' → M''` is an exact sequence, then the set of associated primes of
 `M'` is
contained in the union of those of `M` and `M''`.
-/
theorem subset_union_of_exact (hf : Function.Injective f) (hfg : Function.Exact f g) :
    associatedPrimes R M' ⊆ associatedPrimes R M ∪ associatedPrimes R M'' := by
  rintro p ⟨_, x, hx⟩
  by_cases! h : ∃ a ∈ p.primeCompl, ∃ y : M, ∃ k, f y = a ^ k • x
  · obtain ⟨a, ha, y, k, h⟩ := h
    left
    refine ⟨‹_›, y, le_antisymm (fun b hb ↦ ?_) (fun b ⟨n, hb⟩ ↦ ?_)⟩
    · rw [hx] at hb
      obtain ⟨n, hb⟩ := hb
      use n
      rw [mem_colon_singleton, mem_bot] at hb ⊢
      apply_fun _ using hf
      rw [map_smul, h, smul_comm, hb, smul_zero, map_zero]
    · rw [mem_colon_singleton, mem_bot] at hb
      apply_fun f at hb
      rw [map_smul, map_zero, h, ← mul_smul, ← mem_bot R, ← mem_colon_singleton] at hb
      replace hb := hx.ge (Ideal.le_radical hb)
      contrapose hb
      exact p.primeCompl.mul_mem (p.primeCompl.pow_mem hb n) (p.primeCompl.pow_mem ha k)
  · right
    refine ⟨‹_›, g x, le_antisymm (fun b hb ↦ ?_) (fun b ⟨n, hb⟩ ↦ ?_)⟩
    · rw [hx] at hb
      refine Ideal.radical_mono (fun b hb ↦ ?_) hb
      rw [mem_colon_singleton, mem_bot] at hb ⊢
      rw [← map_smul, hb, map_zero]
    · rw [mem_colon_singleton, mem_bot, ← map_smul, ← LinearMap.mem_ker,
        hfg.linearMap_ker_eq] at hb
      obtain ⟨y, hy⟩ := hb
      by_contra H
      exact h b H y n hy

variable (R M M') in
/-- The set of associated primes of the product of two modules is equal to
the union of those of the two modules. -/
@[stacks 02M3 "third part"]
/-
**associatedPrimes.prod** 是 Mathlib 中的一个定理，位于命名空间 `associatedPrimes`。
形式化陈述：prod : associatedPrimes R (M × M') = associatedPrimes R M union associated
Primes R M'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `associatedPrimes.subset_union_of_exact`：subset_union_of_exact (hf : Func
tion.Injective f) (hfg : Function.Exact f g) : associatedPrimes R M' subseteq as
sociatedPrimes R M union ass…
· 使用定理 `LinearMap.inl_injective`：inl_injective : Function.Injective (inl R M M₂)
· 使用定理 `Function.Exact.inl_snd`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_4} [
inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [inst
_3 : _root_.…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `associatedPrimes.subset_of_injective`：subset_of_injective (hf : Function
.Injective f) : associatedPrimes R M subseteq associatedPrimes R M'
· 使用定理 `LinearMap.inr_injective`：inr_injective : Function.Injective (inr R M M₂)

--- 原说明 ---
The set of associated primes of the product of two modules is equal to
the union of those of the two modules.
-/
theorem prod : associatedPrimes R (M × M') = associatedPrimes R M ∪ associatedPrimes R M' :=
  (subset_union_of_exact LinearMap.inl_injective .inl_snd).antisymm (Set.union_subset_iff.2
    ⟨subset_of_injective LinearMap.inl_injective, subset_of_injective LinearMap.inr_injective⟩)

end associatedPrimes

/-
**LinearEquiv.AssociatedPrimes.eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') : associatedPrimes R M = 
associatedPrimes R M'
参数：l : M ≃ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `associatedPrimes.subset_of_injective`：subset_of_injective (hf : Function
.Injective f) : associatedPrimes R M subseteq associatedPrimes R M'
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem LinearEquiv.AssociatedPrimes.eq (l : M ≃ₗ[R] M') :
    associatedPrimes R M = associatedPrimes R M' :=
  le_antisymm (associatedPrimes.subset_of_injective l.injective)
    (associatedPrimes.subset_of_injective l.symm.injective)
/-
**associatedPrimes.eq_empty_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPri
mes R M = ∅
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `not_isAssociatedPrime_of_subsingleton`：not_isAssociatedPrime_of_subsingl
eton [Subsingleton M] : ¬IsAssociatedPrime I M
-/
theorem associatedPrimes.eq_empty_of_subsingleton [Subsingleton M] : associatedPrimes R M = ∅ := by
  ext; simp only [Set.mem_empty_iff_false, iff_false]
  apply not_isAssociatedPrime_of_subsingleton

variable (R M)
/-
**associatedPrimes.nonempty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] : (associate
dPrimes R M).Nonempty
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `exists_le_isAssociatedPrime_of_isNoetherianRing`：exists_le_isAssociatedP
rime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M) (hx : x != 0) : exists
 P : Ideal R, IsAssociatedPrime P M ∧…
-/
theorem associatedPrimes.nonempty [IsNoetherianRing R] [Nontrivial M] :
    (associatedPrimes R M).Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  obtain ⟨P, hP, _⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x hx
  exact ⟨P, hP⟩
/-
**biUnion_associatedPrimes_eq_zero_divisors** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：biUnion_associatedPrimes_eq_zero_divisors [IsNoetherianRing R] : ⋃ p in as
sociatedPrimes R M, p = { r : R | exists x : M, x != 0 ∧ r • x = 0 }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `exists_le_isAssociatedPrime_of_isNoetherianRing`：exists_le_isAssociatedP
rime_of_isNoetherianRing [H : IsNoetherianRing R] (x : M) (hx : x != 0) : exists
 P : Ideal R, IsAssociatedPrime P M ∧…
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `isAssociatedPrime_iff`：isAssociatedPrime_iff [IsNoetherianRing R] : IsAs
sociatedPrime I M ↔ I.IsPrime ∧ exists x : M, I = colon ⊥ {x}
· 使用定理 `Submodule.mem_colon_singleton`：mem_colon_singleton {x : M} {r : R} : r i
n N.colon {x} ↔ r • x in N
-/
theorem biUnion_associatedPrimes_eq_zero_divisors [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R M, p = { r : R | ∃ x : M, x ≠ 0 ∧ r • x = 0 } := by
  simp only [AssociatedPrimes.mem_iff, isAssociatedPrime_iff]
  refine subset_antisymm (Set.iUnion₂_subset ?_) ?_
  · rintro _ ⟨h, x, ⟨⟩⟩ r h'
    exact ⟨x, by simpa using h.ne_top, by simpa using h'⟩
  · intro r ⟨x, h, h'⟩
    obtain ⟨P, hP, hx⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R x h
    rw [isAssociatedPrime_iff] at hP
    exact Set.mem_iUnion₂_of_mem hP (hx (by rwa [mem_colon_singleton]))
/-
**biUnion_associatedPrimes_eq_compl_nonZeroDivisors** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：biUnion_associatedPrimes_eq_compl_nonZeroDivisors [IsNoetherianRing R] : ⋃
 p in associatedPrimes R R, p = (nonZeroDivisors R : Set R)ᶜ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `biUnion_associatedPrimes_eq_zero_divisors`：biUnion_associatedPrimes_eq_z
ero_divisors [IsNoetherianRing R] : ⋃ p in associatedPrimes R M, p = { r : R | e
xists x : M, x != 0 ∧ r • x = 0…
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem biUnion_associatedPrimes_eq_compl_nonZeroDivisors [IsNoetherianRing R] :
    ⋃ p ∈ associatedPrimes R R, p = (nonZeroDivisors R : Set R)ᶜ :=
  (biUnion_associatedPrimes_eq_zero_divisors R R).trans <| by
    ext; simp [← nonZeroDivisorsLeft_eq_nonZeroDivisors, and_comm]

variable {R M}
/-
**IsAssociatedPrime.annihilator_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) : (⊤ : Submod
ule R M).annihilator <= I
参数：h : IsAssociatedPrime I M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.bot_colon'`：bot_colon' : (⊥ : Submodule R M).colon S = (span R
 S).annihilator
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.annihilator_mono`：annihilator_mono (h : N <= P) : P.annihilato
r <= N.annihilator
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Ideal.le_radical`：le_radical : I <= radical I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem IsAssociatedPrime.annihilator_le (h : IsAssociatedPrime I M) :
    (⊤ : Submodule R M).annihilator ≤ I := by
  obtain ⟨hI, x, rfl⟩ := h
  rw [bot_colon']
  exact (annihilator_mono le_top).trans Ideal.le_radical

end Semiring

variable {R : Type*} [CommRing R] (I J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M]

/-
**isAssociatedPrime_iff_exists_injective_linearMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isAssociatedPrime_iff_exists_injective_linearMap [IsNoetherianRing R] : Is
AssociatedPrime I M ↔ I.IsPrime ∧ exists (f : R ⧸ I ->ₗ[R] M), Function.Injectiv
e f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isAssociatedPrime_iff`：isAssociatedPrime_iff [IsNoetherianRing R] : IsAs
sociatedPrime I M ↔ I.IsPrime ∧ exists x : M, I = colon ⊥ {x}
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearMap.toSpanSingleton_apply`：∀ (R : Type u_1) (M : Type u_4) [inst :
 Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (x : M)   (
b : R), (LinearMap.to…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.ker_liftQ_eq_bot'`：ker_liftQ_eq_bot' (f : M ->ₛₗ[τ₁₂] M₂) (h :
 p = ker f) : ker (p.liftQ f (le_of_eq h)) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.ker_comp_of_ker_eq_bot`：ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂
] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) : ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) =
 ker f
· 使用定理 `LinearMap.ker_eq_bot_of_injective`：ker_eq_bot_of_injective {f : M ->ₛₗ[τ
₁₂] M₂} (hf : Injective f) : ker f = ⊥
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
-/
theorem isAssociatedPrime_iff_exists_injective_linearMap [IsNoetherianRing R] :
    IsAssociatedPrime I M ↔ I.IsPrime ∧ ∃ (f : R ⧸ I →ₗ[R] M), Function.Injective f := by
  rw [isAssociatedPrime_iff, and_congr_right_iff]
  refine fun _ ↦ ⟨fun ⟨x, h⟩ ↦ ?_, fun ⟨f, h⟩ ↦ ⟨(f ∘ₗ mkQ I) 1, ?_⟩⟩
  · replace h : I = ker (toSpanSingleton R M x) := by simp [h, SetLike.ext_iff]
    exact ⟨liftQ _ _ h.le, ker_eq_bot.mp (ker_liftQ_eq_bot' _ _ h)⟩
  · conv_lhs => rw [← I.ker_mkQ, ← ker_comp_of_ker_eq_bot (mkQ I) (ker_eq_bot_of_injective h)]
    simp [SetLike.ext_iff, ← Ideal.Quotient.algebraMap_eq, Algebra.algebraMap_eq_smul_one]

variable {I J M}
/-
**IsAssociatedPrime.eq_radical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (
R ⧸ I)) : J = I.radical
参数：hI : I.IsPrimary；h : IsAssociatedPrime J (R ⧸ I)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.radical_top`：radical_top : (radical ⊤ : Ideal R) = ⊤
· 使用引理 `Submodule.colon_singleton_zero`：colon_singleton_zero : N.colon {0} = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mkₐ_surjective`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : 
CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst
_3 : I.IsTwoSided],…
· 使用定理 `Submodule.mem_colon_singleton`：mem_colon_singleton {x : M} {r : R} : r i
n N.colon {x} ↔ r • x in N
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Ideal.Quotient.algebraMap_eq`：∀ {R : Type u_5} [inst : CommRing R] (I : 
Ideal R), algebraMap R (R ⧸ I) = Ideal.Quotient.mk I
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.radical_le_radical_iff`：radical_le_radical_iff : radical I <= radi
cal J ↔ I <= radical J
· 使用定理 `Submodule.colon_univ`：colon_univ {I : Ideal R} [I.IsTwoSided] : I.colon 
Set.univ = I
· 使用定理 `Set.top_eq_univ`：top_eq_univ : (⊤ : Set α) = univ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Submodule.IsPrimary.mem_or_mem`：∀ {R : Type u_1} {M : Type u_2} [inst : 
CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : S
ubmodule R M}, S.IsP…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Ideal.radical_mono`：radical_mono (H : I <= J) : radical I <= radical J
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
-/
theorem IsAssociatedPrime.eq_radical (hI : I.IsPrimary) (h : IsAssociatedPrime J (R ⧸ I)) :
    J = I.radical := by
  obtain ⟨hJ, x, e⟩ := h
  have : x ≠ 0 := by
    rintro rfl
    apply hJ.1
    rwa [colon_singleton_zero, Ideal.radical_top] at e
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mkₐ_surjective R _ x
  have h {y} : y ∈ colon ⊥ {(Ideal.Quotient.mk I) x} ↔ Ideal.Quotient.mk I (y * x) = 0 := by
    rw [mem_colon_singleton, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, mem_bot]
  simp only [e, Ideal.Quotient.mkₐ_eq_mk, ne_eq, Ideal.Quotient.eq_zero_iff_mem] at this h ⊢
  refine le_antisymm (Ideal.radical_le_radical_iff.mpr fun y hy ↦ ?_)
    (Ideal.radical_mono fun y ↦ h.mpr ∘ I.mul_mem_right x)
  rw [← I.colon_univ, ← Set.top_eq_univ]
  exact (hI.mem_or_mem (h.mp hy)).resolve_left this
/-
**associatedPrimes.eq_singleton_of_isPrimary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.Is
Primary) : associatedPrimes R (R ⧸ I) = {I.radical}
参数：hI : I.IsPrimary。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `IsAssociatedPrime.eq_radical`：IsAssociatedPrime.eq_radical (hI : I.IsPri
mary) (h : IsAssociatedPrime J (R ⧸ I)) : J = I.radical
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.Quotient.eq`：∀ {R : Type u} [inst : Ring R] {I : Ideal R} {x y : R
} [inst_1 : I.IsTwoSided],   (Ideal.Quotient.mk I) x = (Ideal.Quotient.mk I) y ↔
 x - y …
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `associatedPrimes.nonempty`：associatedPrimes.nonempty [IsNoetherianRing R
] [Nontrivial M] : (associatedPrimes R M).Nonempty
-/
theorem associatedPrimes.eq_singleton_of_isPrimary [IsNoetherianRing R] (hI : I.IsPrimary) :
    associatedPrimes R (R ⧸ I) = {I.radical} := by
  ext J
  rw [Set.mem_singleton_iff]
  refine ⟨IsAssociatedPrime.eq_radical hI, ?_⟩
  rintro rfl
  have : Nontrivial (R ⧸ I) := by
    refine ⟨(Ideal.Quotient.mk I :) 1, (Ideal.Quotient.mk I :) 0, ?_⟩
    rw [Ne, Ideal.Quotient.eq, sub_zero, ← Ideal.eq_top_iff_one]
    exact hI.1
  obtain ⟨a, ha⟩ := associatedPrimes.nonempty R (R ⧸ I)
  exact ha.eq_radical hI ▸ ha
