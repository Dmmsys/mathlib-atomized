/-
Copyright (c) 2020 Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard
-/
module

public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.RingTheory.Valuation.PrimeMultiplicity
public import Mathlib.RingTheory.Valuation.ValuationRing

/-!
# Discrete valuation rings

This file defines discrete valuation rings (DVRs) and develops a basic interface
for them.

## Important definitions

There are various definitions of a DVR in the literature; we define a DVR to be a local PID
which is not a field (the first definition in Wikipedia) and prove that this is equivalent
to being a PID with a unique non-zero prime ideal (the definition in Serre's
book "Local Fields").

Let R be an integral domain, assumed to be a principal ideal ring and a local ring.

* `IsDiscreteValuationRing R` : a predicate expressing that R is a DVR.

### Definitions

* `addVal R : AddValuation R ℕ∞` : the additive valuation on a DVR.
* `toEuclideanDomain R : EuclideanDomain R` : a non-canonical structure of Euclidean domain on a
  DVR, where `x % y = 0` if `y ∣ x` and `x % y = x` otherwise. The GCD algorithm terminates in two
  steps.

## Implementation notes

It's a theorem that an element of a DVR is a uniformizer if and only if it's irreducible.
We do not hence define `Uniformizer` at all, because we can use `Irreducible` instead.

## Tags

discrete valuation ring
-/

@[expose] public section

universe u

open Ideal IsLocalRing

/-- An integral domain is a *discrete valuation ring* (DVR) if it's a local PID which
  is not a field. -/
/-
**IsDiscreteValuationRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → [inst : CommRing R] → [IsDomain R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An integral domain is a *discrete valuation ring* (DVR) if it's a local PID whic
h
  is not a field.
-/
class IsDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R] : Prop
    extends IsPrincipalIdealRing R, IsLocalRing R where
  not_a_field' : maximalIdeal R ≠ ⊥

namespace IsDiscreteValuationRing

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-
**IsDiscreteValuationRing.not_a_field** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValua
tionRing`。
形式化陈述：not_a_field : maximalIdeal R != ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.not_a_field'`：∀ {R : Type u} {inst : CommRing R}
 {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R],   IsLocalRing.maximal
Ideal R ≠ ⊥
-/
theorem not_a_field : maximalIdeal R ≠ ⊥ :=
  not_a_field'

/-- A discrete valuation ring `R` is not a field. -/
/-
**IsDiscreteValuationRing.not_isField** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValua
tionRing`。
形式化陈述：not_isField : ¬IsField R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `IsLocalRing.isField_iff_maximalIdeal_eq`：isField_iff_maximalIdeal_eq : I
sField R ↔ maximalIdeal R = ⊥
· 使用定理 `IsDiscreteValuationRing.not_a_field`：not_a_field : maximalIdeal R != ⊥

--- 原说明 ---
A discrete valuation ring `R` is not a field.
-/
theorem not_isField : ¬IsField R :=
  IsLocalRing.isField_iff_maximalIdeal_eq.not.mpr (not_a_field R)

variable {R}

open PrincipalIdealRing
/-
**IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal** 是 Mathlib 中的一个定理
，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：irreducible_of_span_eq_maximalIdeal {R : Type*} [CommSemiring R] [IsLocalR
ing R] [IsDomain R] (ϖ : R) (hϖ : ϖ != 0) (h : maximalIdeal R = Ideal.span {ϖ}) 
: Irreducible ϖ
参数：ϖ : R；hϖ : ϖ != 0；h : maximalIdeal R = Ideal.span {ϖ}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_span_singleton'`：mem_span_singleton' {x y : α} : x in span ({y
} : Set α) ↔ exists a, a * y = x
· 使用定理 `eq_zero_of_mul_eq_self_right`：eq_zero_of_mul_eq_self_right [IsLeftCancel
MulZero M₀] (h₁ : b != 1) (h₂ : a * b = a) : a = 0
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `isUnit_of_dvd_one`：isUnit_of_dvd_one {a : α} (h : a ∣ 1) : IsUnit (a : α
)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
-/
theorem irreducible_of_span_eq_maximalIdeal {R : Type*} [CommSemiring R] [IsLocalRing R]
    [IsDomain R] (ϖ : R) (hϖ : ϖ ≠ 0) (h : maximalIdeal R = Ideal.span {ϖ}) : Irreducible ϖ := by
  have h2 : ¬IsUnit ϖ := show ϖ ∈ maximalIdeal R from h.symm ▸ Submodule.mem_span_singleton_self ϖ
  refine ⟨h2, ?_⟩
  intro a b hab
  by_contra! ⟨ha : a ∈ maximalIdeal R, hb : b ∈ maximalIdeal R⟩
  rw [h, mem_span_singleton'] at ha hb
  rcases ha with ⟨a, rfl⟩
  rcases hb with ⟨b, rfl⟩
  rw [show a * ϖ * (b * ϖ) = ϖ * (ϖ * (a * b)) by ring] at hab
  apply hϖ
  apply eq_zero_of_mul_eq_self_right _ hab.symm
  exact fun hh => h2 (isUnit_of_dvd_one ⟨_, hh.symm⟩)

/-- An element of a DVR is irreducible iff it is a uniformizer, that is, generates the
  maximal ideal of `R`. -/
/-
**IsDiscreteValuationRing.irreducible_iff_uniformizer** 是 Mathlib 中的一个定理，位于命名空间 
`IsDiscreteValuationRing`。
形式化陈述：irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ide
al.span {ϖ}
参数：ϖ : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.eq_maximalIdeal`：eq_maximalIdeal {I : Ideal R} (hI : I.IsMax
imal) : I = maximalIdeal R
· 使用定理 `PrincipalIdealRing.isMaximal_of_irreducible`：isMaximal_of_irreducible [C
ommSemiring R] [IsPrincipalIdealRing R] {p : R} (hp : Irreducible p) : Ideal.IsM
aximal (span R ({p} : Set R))
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `IsDiscreteValuationRing.irreducible_of_span_eq_maximalIdeal`：irreducible
_of_span_eq_maximalIdeal {R : Type*} [CommSemiring R] [IsLocalRing R] [IsDomain 
R] (ϖ : R) (hϖ : ϖ != 0) (h : maximalIdeal R = Id…
· 使用定理 `IsDiscreteValuationRing.not_a_field`：not_a_field : maximalIdeal R != ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.span_singleton_eq_bot`：span_singleton_eq_bot {x} : span ({x} : Set
 α) = ⊥ ↔ x = 0

--- 原说明 ---
An element of a DVR is irreducible iff it is a uniformizer, that is, generates t
he
  maximal ideal of `R`.
-/
theorem irreducible_iff_uniformizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ} :=
  ⟨fun hϖ => (eq_maximalIdeal (isMaximal_of_irreducible hϖ)).symm,
    fun h => irreducible_of_span_eq_maximalIdeal ϖ
      (fun e => not_a_field R <| by rwa [h, span_singleton_eq_bot]) h⟩
/-
**IsDiscreteValuationRing._root_.Irreducible.maximalIdeal_eq** 是 Mathlib 中的一个定理，
位于命名空间 `IsDiscreteValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Irreducible.maximalIdeal_eq {ϖ : R} (h : Irreducible ϖ) :
    maximalIdeal R = Ideal.span {ϖ} :=
  (irreducible_iff_uniformizer _).mp h

variable (R)

/-- Uniformizers exist in a DVR. -/
/-
**IsDiscreteValuationRing.exists_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscre
teValuationRing`。
形式化陈述：exists_irreducible : exists ϖ : R, Irreducible ϖ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.IsPrincipal.principal`：∀ {R : Type u_1} {M : Type u_4} {inst :
 Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   (S : Subm
odule R M) [self : S.…
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R

--- 原说明 ---
Uniformizers exist in a DVR.
-/
theorem exists_irreducible : ∃ ϖ : R, Irreducible ϖ := by
  simp_rw [irreducible_iff_uniformizer]
  exact (IsPrincipalIdealRing.principal <| maximalIdeal R).principal

/-- Uniformizers exist in a DVR. -/
/-
**IsDiscreteValuationRing.exists_prime** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValu
ationRing`。
形式化陈述：exists_prime : exists ϖ : R, Prime ϖ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ

--- 原说明 ---
Uniformizers exist in a DVR.
-/
theorem exists_prime : ∃ ϖ : R, Prime ϖ :=
  (exists_irreducible R).imp fun _ => irreducible_iff_prime.1

/-- An integral domain is a DVR iff it's a PID with a unique non-zero prime ideal. -/
/-
**IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime** 是 Mathlib 中的一个定理，位于命名
空间 `IsDiscreteValuationRing`。
形式化陈述：iff_pid_with_one_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] : Is
DiscreteValuationRing R ↔ IsPrincipalIdealRing R ∧ exists! P : Ideal R, P != ⊥ ∧
 IsPrime P
参数：R : Type u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsLocalRing.maximalIdeal.isMaximal`：∀ (R : Type u_1) [inst : CommSemirin
g R] [inst_1 : IsLocalRing R], (IsLocalRing.maximalIdeal R).IsMaximal
· 使用定理 `Submodule.IsPrincipal.principal`：∀ {R : Type u_1} {M : Type u_4} {inst :
 Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   (S : Subm
odule R M) [self : S.…
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Ideal.submodule_span_eq`：submodule_span_eq {s : Set α} : Submodule.span 
α s = Ideal.span s
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsDiscreteValuationRing.irreducible_iff_uniformizer`：irreducible_iff_uni
formizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ}
· 使用定理 `IsLocalRing.of_unique_nonzero_prime`：of_unique_nonzero_prime (h : exists
! P : Ideal R, P != ⊥ ∧ Ideal.IsPrime P) : IsLocalRing R
· 使用定理 `IsLocalRing.le_maximalIdeal`：le_maximalIdeal {J : Ideal R} (hJ : J != ⊤)
 : J <= maximalIdeal R
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
An integral domain is a DVR iff it's a PID with a unique non-zero prime ideal.
-/
theorem iff_pid_with_one_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] :
    IsDiscreteValuationRing R ↔ IsPrincipalIdealRing R ∧ ∃! P : Ideal R, P ≠ ⊥ ∧ IsPrime P := by
  constructor
  · intro RDVR
    rcases id RDVR with ⟨Rlocal⟩
    constructor
    · assumption
    use IsLocalRing.maximalIdeal R
    constructor
    · exact ⟨Rlocal, inferInstance⟩
    · rintro Q ⟨hQ1, hQ2⟩
      obtain ⟨q, rfl⟩ := (IsPrincipalIdealRing.principal Q).1
      have hq : q ≠ 0 := by
        rintro rfl
        apply hQ1
        simp
      rw [submodule_span_eq, span_singleton_prime hq] at hQ2
      replace hQ2 := hQ2.irreducible
      rw [irreducible_iff_uniformizer] at hQ2
      exact hQ2.symm
  · rintro ⟨RPID, Punique⟩
    have : IsLocalRing R := IsLocalRing.of_unique_nonzero_prime Punique
    refine { not_a_field' := ?_ }
    rcases Punique with ⟨P, ⟨hP1, hP2⟩, _⟩
    have hPM : P ≤ maximalIdeal R := le_maximalIdeal hP2.1
    order
/-
**IsDiscreteValuationRing.associated_of_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `I
sDiscreteValuationRing`。
形式化陈述：associated_of_irreducible {a b : R} (ha : Irreducible a) (hb : Irreducible
 b) : Associated a b
参数：ha : Irreducible a；hb : Irreducible b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `IsDiscreteValuationRing.irreducible_iff_uniformizer`：irreducible_iff_uni
formizer (ϖ : R) : Irreducible ϖ ↔ maximalIdeal R = Ideal.span {ϖ}
-/
theorem associated_of_irreducible {a b : R} (ha : Irreducible a) (hb : Irreducible b) :
    Associated a b := by
  rw [irreducible_iff_uniformizer] at ha hb
  rw [← span_singleton_eq_span_singleton, ← ha, hb]

variable (R : Type*)

/-- Alternative characterisation of discrete valuation rings. -/
/-
**IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization** 是 Mathlib 中的一个
定义，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：HasUnitMulPowIrreducibleFactorization [CommRing R] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative characterisation of discrete valuation rings.
-/
def HasUnitMulPowIrreducibleFactorization [CommRing R] : Prop :=
  ∃ p : R, Irreducible p ∧ ∀ {x : R}, x ≠ 0 → ∃ n : ℕ, Associated (p ^ n) x

namespace HasUnitMulPowIrreducibleFactorization

variable {R} [CommRing R]

/-
**IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.unique_irreducib
le** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuationRing.HasUnitMulPowIrreducibleFa
ctorization`。
形式化陈述：unique_irreducible (hR : HasUnitMulPowIrreducibleFactorization R) ⦃p q : R
⦄ (hp : Irreducible p) (hq : Irreducible q) : Associated p q
参数：hR : HasUnitMulPowIrreducibleFactorization R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Associated.irreducible`：∀ {M : Type u_1} [inst : Monoid M] {p q : M}, As
sociated p q → Irreducible p → Irreducible q
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Nat.exists_eq_add_of_lt`：∀ {m n : ℕ}, m < n → ∃ k, n = m + k + 1
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `isUnit_of_mul_isUnit_left`：isUnit_of_mul_isUnit_left [Monoid M] [IsDedek
indFiniteMonoid M] {x y : M} (hu : IsUnit (x * y)) : IsUnit x
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Associated.trans`：∀ {M : Type u_1} [inst : Monoid M] {x y z : M}, Associ
ated x y → Associated y z → Associated x z
-/
theorem unique_irreducible (hR : HasUnitMulPowIrreducibleFactorization R)
    ⦃p q : R⦄ (hp : Irreducible p) (hq : Irreducible q) :
    Associated p q := by
  rcases hR with ⟨ϖ, hϖ, hR⟩
  suffices ∀ {p : R} (_ : Irreducible p), Associated p ϖ by
    apply Associated.trans (this hp) (this hq).symm
  clear hp hq p q
  intro p hp
  obtain ⟨n, hn⟩ := hR hp.ne_zero
  have : Irreducible (ϖ ^ n) := hn.symm.irreducible hp
  rcases lt_trichotomy n 1 with (H | rfl | H)
  · obtain rfl : n = 0 := by
      clear hn this
      revert H n
      decide
    simp [not_irreducible_one, pow_zero] at this
  · simpa only [pow_one] using hn.symm
  · obtain ⟨n, rfl⟩ : ∃ k, n = 1 + k + 1 := Nat.exists_eq_add_of_lt H
    rw [pow_succ'] at this
    rcases this.isUnit_or_isUnit rfl with (H0 | H0)
    · exact (hϖ.not_isUnit H0).elim
    · rw [add_comm, pow_succ'] at H0
      exact (hϖ.not_isUnit (isUnit_of_mul_isUnit_left H0)).elim

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique factorization domain.
See `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`. -/
/-
**IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.toUniqueFactoriz
ationMonoid** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuationRing.HasUnitMulPowIrre
ducibleFactorization`。
形式化陈述：toUniqueFactorizationMonoid [IsCancelMulZero R] (hR : HasUnitMulPowIrreduc
ibleFactorization R) : UniqueFactorizationMonoid R
参数：hR : HasUnitMulPowIrreducibleFactorization R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `UniqueFactorizationMonoid.of_exists_prime_factors`：UniqueFactorizationMo
noid.of_exists_prime_factors : UniqueFactorizationMonoid α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Units.dvd_mul_right`：dvd_mul_right : a ∣ b * u ↔ a ∣ b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Units.dvd_mul_left`：dvd_mul_left : a ∣ u * b ↔ a ∣ b
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `dvd_mul_of_dvd_left`：dvd_mul_of_dvd_left (h : a ∣ b) (c : α) : a ∣ b * c
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n

--- 原说明 ---
An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p` is a unique fact
orization domain.
See `IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization`.
-/
theorem toUniqueFactorizationMonoid [IsCancelMulZero R]
    (hR : HasUnitMulPowIrreducibleFactorization R) :
    UniqueFactorizationMonoid R :=
  let p := Classical.choose hR
  let spec := Classical.choose_spec hR
  UniqueFactorizationMonoid.of_exists_prime_factors fun x hx => by
    use Multiset.replicate (Classical.choose (spec.2 hx)) p
    constructor
    · intro q hq
      have hpq := Multiset.eq_of_mem_replicate hq
      rw [hpq]
      refine ⟨spec.1.ne_zero, spec.1.not_isUnit, ?_⟩
      intro a b h
      by_cases ha : a = 0
      · rw [ha]
        simp only [true_or, dvd_zero]
      obtain ⟨m, u, rfl⟩ := spec.2 ha
      rw [mul_assoc, mul_left_comm, Units.dvd_mul_left] at h
      rw [Units.dvd_mul_right]
      by_cases hm : m = 0
      · simp only [hm, one_mul, pow_zero] at h ⊢
        right
        exact h
      left
      obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
      rw [pow_succ']
      apply dvd_mul_of_dvd_left dvd_rfl _
    · rw [Multiset.prod_replicate]
      exact Classical.choose_spec (spec.2 hx)
/-
**IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique
_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuationRing.HasUnitMulPowIrr
educibleFactorization`。
形式化陈述：of_ufd_of_unique_irreducible [UniqueFactorizationMonoid R] (h₁ : exists p 
: R, Irreducible p) (h₂ : forall ⦃p q : R⦄, Irreducible p -> Irreducible q -> As
sociated p q) : HasUnitMulPowIrreducibleFactorization R
参数：h₁ : exists p : R, Irreducible p；h₂ : forall ⦃p q : R⦄, Irreducible p -> Irre
ducible q -> Associated p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WfDvdMonoid.exists_factors`：exists_factors (a : α) : a != 0 -> exists f 
: Multiset α, (forall b in f, Irreducible b) ∧ Associated f.prod a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
· 使用定理 `Associates.prod_mk`：prod_mk {p : Multiset M} : (p.map Associates.mk).pro
d = Associates.mk p.prod
· 使用定理 `Associates.mk_pow`：mk_pow (a : M) (n : Nat) : Associates.mk (a ^ n) = As
sociates.mk a ^ n
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem of_ufd_of_unique_irreducible [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    HasUnitMulPowIrreducibleFactorization R := by
  obtain ⟨p, hp⟩ := h₁
  refine ⟨p, hp, ?_⟩
  intro x hx
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  refine ⟨Multiset.card fx, ?_⟩
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H, ← Associates.prod_mk, Associates.mk_pow, ← Multiset.prod_replicate]
  congr 1
  symm
  rw [Multiset.eq_replicate]
  simp only [true_and, and_imp, Multiset.card_map, Multiset.mem_map, exists_imp]
  rintro _ q hq rfl
  rw [Associates.mk_eq_mk_iff_associated]
  apply h₂ (hfx.1 _ hq) hp

end HasUnitMulPowIrreducibleFactorization

/-
**IsDiscreteValuationRing.aux_pid_of_ufd_of_unique_irreducible** 是 Mathlib 中的一个定
理，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：aux_pid_of_ufd_of_unique_irreducible (R : Type u) [CommRing R] [UniqueFact
orizationMonoid R] (h₁ : exists p : R, Irreducible p) (h₂ : forall ⦃p q : R⦄, Ir
reducible p -> Irreducible q -> Associated p q) : IsPrincipalIdealRing R
参数：R : Type u；h₁ : exists p : R, Irreducible p；h₂ : forall ⦃p q : R⦄, Irreducibl
e p -> Irreducible q -> Associated p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_zero`：span_zero : span R (0 : Set M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.of_ufd_of_
unique_irreducible`：of_ufd_of_unique_irreducible [UniqueFactorizationMonoid R] (
h₁ : exists p : R, Irreducible p) (h₂ : forall ⦃p q : R⦄, Irreducible p -> Irred
…
· 使用定理 `Units.mul_inv_cancel_right`：mul_inv_cancel_right (a : α) (b : αˣ) : a * 
b * ↑b⁻¹ = a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `pow_dvd_pow`：pow_dvd_pow (a : α) (h : m <= n) : a ^ m ∣ a ^ n
· 使用定理 `Nat.find_min'`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n) 
{m : ℕ}, p m → Nat.find H ≤ m
· 使用定理 `Ideal.span_singleton_le_iff_mem`：span_singleton_le_iff_mem {x : α} : spa
n {x} <= I ↔ x in I
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
-/
theorem aux_pid_of_ufd_of_unique_irreducible (R : Type u) [CommRing R]
    [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    IsPrincipalIdealRing R := by
  classical
  constructor
  intro I
  by_cases I0 : I = ⊥
  · rw [I0]
    use 0
    simp only [Set.singleton_zero, Submodule.span_zero]
  obtain ⟨x, hxI, hx0⟩ : ∃ x ∈ I, x ≠ (0 : R) := I.ne_bot_iff.mp I0
  obtain ⟨p, _, H⟩ := HasUnitMulPowIrreducibleFactorization.of_ufd_of_unique_irreducible h₁ h₂
  have ex : ∃ n : ℕ, p ^ n ∈ I := by
    obtain ⟨n, u, rfl⟩ := H hx0
    refine ⟨n, ?_⟩
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hxI
  constructor
  use p ^ Nat.find ex
  change I = Ideal.span _
  apply le_antisymm
  · intro r hr
    by_cases hr0 : r = 0
    · simp only [hr0, Submodule.zero_mem]
    obtain ⟨n, u, rfl⟩ := H hr0
    simp only [mem_span_singleton, Units.isUnit, IsUnit.dvd_mul_right]
    apply pow_dvd_pow
    apply Nat.find_min'
    simpa only [Units.mul_inv_cancel_right] using I.mul_mem_right (↑u⁻¹) hr
  · rw [span_singleton_le_iff_mem]
    exact Nat.find_spec ex

/-- A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
/-
**IsDiscreteValuationRing.of_ufd_of_unique_irreducible** 是 Mathlib 中的一个定理，位于命名空间
 `IsDiscreteValuationRing`。
形式化陈述：of_ufd_of_unique_irreducible {R : Type u} [CommRing R] [IsDomain R] [Uniqu
eFactorizationMonoid R] (h₁ : exists p : R, Irreducible p) (h₂ : forall ⦃p q : R
⦄, Irreducible p -> Irreducible q -> Associated p q) : IsDiscreteValuationRing R
参数：h₁ : exists p : R, Irreducible p；h₂ : forall ⦃p q : R⦄, Irreducible p -> Irre
ducible q -> Associated p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.iff_pid_with_one_nonzero_prime`：iff_pid_with_one
_nonzero_prime (R : Type u) [CommRing R] [IsDomain R] : IsDiscreteValuationRing 
R ↔ IsPrincipalIdealRing R ∧ exists! P : Ide…
· 使用定理 `IsDiscreteValuationRing.aux_pid_of_ufd_of_unique_irreducible`：aux_pid_of
_ufd_of_unique_irreducible (R : Type u) [CommRing R] [UniqueFactorizationMonoid 
R] (h₁ : exists p : R, Irreducible p) (h₂ : forall…
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_span_singleton`：mem_span_singleton {x y : α} : x in span ({y} 
: Set α) ↔ y ∣ x
· 使用定理 `dvd_refl`：dvd_refl (a : α) : a ∣ a
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniqueFactorizationMonoid.irreducible_iff_prime`：∀ {α : Type u_2} {inst 
: CommMonoidWithZero α} [self : UniqueFactorizationMonoid α] {a : α}, Irreducibl
e a ↔ Prime a
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Submodule.IsPrincipal.span_singleton_generator`：span_singleton_generator
 (S : Submodule R M) [S.IsPrincipal] : span R {generator S} = S
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…
· 使用定理 `Submodule.span_singleton_eq_bot`：span_singleton_eq_bot : R ∙ x = ⊥ ↔ x =
 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b

--- 原说明 ---
A unique factorization domain with at least one irreducible element
in which all irreducible elements are associated
is a discrete valuation ring.
-/
theorem of_ufd_of_unique_irreducible {R : Type u} [CommRing R] [IsDomain R]
    [UniqueFactorizationMonoid R] (h₁ : ∃ p : R, Irreducible p)
    (h₂ : ∀ ⦃p q : R⦄, Irreducible p → Irreducible q → Associated p q) :
    IsDiscreteValuationRing R := by
  rw [iff_pid_with_one_nonzero_prime]
  have PID : IsPrincipalIdealRing R := aux_pid_of_ufd_of_unique_irreducible R h₁ h₂
  obtain ⟨p, hp⟩ := h₁
  refine ⟨PID, ⟨Ideal.span {p}, ⟨?_, ?_⟩, ?_⟩⟩
  · rw [Submodule.ne_bot_iff]
    exact ⟨p, Ideal.mem_span_singleton.mpr (dvd_refl p), hp.ne_zero⟩
  · rwa [Ideal.span_singleton_prime hp.ne_zero, ← UniqueFactorizationMonoid.irreducible_iff_prime]
  · intro I
    rw [← Submodule.IsPrincipal.span_singleton_generator I]
    rintro ⟨I0, hI⟩
    apply span_singleton_eq_span_singleton.mpr
    apply h₂ _ hp
    rw [Ne, Submodule.span_singleton_eq_bot] at I0
    rwa [UniqueFactorizationMonoid.irreducible_iff_prime, ← Ideal.span_singleton_prime I0]

/-- An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
/-
**IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization** 是 Mathlib 中的
一个定理，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：ofHasUnitMulPowIrreducibleFactorization {R : Type u} [CommRing R] [IsDomai
n R] (hR : HasUnitMulPowIrreducibleFactorization R) : IsDiscreteValuationRing R
参数：hR : HasUnitMulPowIrreducibleFactorization R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.toUniqueFa
ctorizationMonoid`：toUniqueFactorizationMonoid [IsCancelMulZero R] (hR : HasUnit
MulPowIrreducibleFactorization R) : UniqueFactorizationMonoid R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDiscreteValuationRing.of_ufd_of_unique_irreducible`：of_ufd_of_unique_i
rreducible {R : Type u} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R] 
(h₁ : exists p : R, Irreducible p) (h₂ : f…
· 使用定理 `IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization.unique_irr
educible`：unique_irreducible (hR : HasUnitMulPowIrreducibleFactorization R) ⦃p q
 : R⦄ (hp : Irreducible p) (hq : Irreducible q) : Associated p q

--- 原说明 ---
An integral domain in which there is an irreducible element `p`
such that every nonzero element is associated to a power of `p`
is a discrete valuation ring.
-/
theorem ofHasUnitMulPowIrreducibleFactorization {R : Type u} [CommRing R] [IsDomain R]
    (hR : HasUnitMulPowIrreducibleFactorization R) : IsDiscreteValuationRing R := by
  let : UniqueFactorizationMonoid R := hR.toUniqueFactorizationMonoid
  apply of_ufd_of_unique_irreducible _ hR.unique_irreducible
  obtain ⟨p, hp, H⟩ := hR
  exact ⟨p, hp⟩

/-- If a ring is equivalent to a DVR, it is itself a DVR. -/
/-
**IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing** 是 Mathlib 中的一
个定理，位于命名空间 `IsDiscreteValuationRing.RingEquivClass`。
形式化陈述：∀ {A : Type u_2} {B : Type u_3} {E : Type u_4} [inst : CommRing A] [inst_1
 : IsDomain A] [inst_2 : CommRing B]   [inst_3 : IsDomain B] [IsDiscreteValuatio
nRing A] [inst_5 : EquivLike E A B] [RingEquivClass E A B] (e : E),   IsDiscrete
ValuationRing B
参数：e : E。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquiv.isLocalRing`：∀ {A : Type u_4} {B : Type u_5} [inst : CommSemir
ing A] [IsLocalRing A] [inst_2 : Semiring B] (e : A ≃+* B),   IsLocalRing B
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isPrincipalIdealRing_iff`：∀ (R : Type u) [inst : Semiring R], IsPrincipa
lIdealRing R ↔ ∀ (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `IsPrincipalIdealRing.of_surjective`：IsPrincipalIdealRing.of_surjective [
IsPrincipalIdealRing R] (f : F) (hf : Function.Surjective f) : IsPrincipalIdealR
ing S
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
· 使用定理 `Submodule.nonzero_mem_of_bot_lt`：nonzero_mem_of_bot_lt {p : Submodule R 
M} (bot_lt : ⊥ < p) : exists a : p, a != 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `IsDiscreteValuationRing.not_a_field`：not_a_field : maximalIdeal R != ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `IsLocalRing.mem_maximalIdeal`：mem_maximalIdeal (x) : x in maximalIdeal R
 ↔ x in nonunits R
· 使用定理 `map_mem_nonunits_iff`：map_mem_nonunits_iff [Monoid α] [Monoid β] [FunLik
e F α β] [MonoidHomClass F α β] (f : F) [IsLocalHom f] (a) : f a in nonunits β ↔
 a in nonu…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If a ring is equivalent to a DVR, it is itself a DVR.
-/
theorem RingEquivClass.isDiscreteValuationRing {A B E : Type*} [CommRing A] [IsDomain A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing A] [EquivLike E A B] [RingEquivClass E A B]
    (e : E) : IsDiscreteValuationRing B where
  principal := (isPrincipalIdealRing_iff _).1 <|
    .of_surjective _ (EquivLike.surjective e)
  __ : IsLocalRing B := (RingEquivClass.toRingEquiv e).isLocalRing
  not_a_field' := by
    obtain ⟨a, ha⟩ := Submodule.nonzero_mem_of_bot_lt (bot_lt_iff_ne_bot.mpr
      <| IsDiscreteValuationRing.not_a_field A)
    rw [Submodule.ne_bot_iff]
    refine ⟨e a, ⟨?_, by simp only [ne_eq, EmbeddingLike.map_eq_zero_iff, ZeroMemClass.coe_eq_zero,
      ha, not_false_eq_true]⟩⟩
    rw [IsLocalRing.mem_maximalIdeal, map_mem_nonunits_iff e, ← IsLocalRing.mem_maximalIdeal]
    exact a.2

section

variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable {R}

/-
**IsDiscreteValuationRing.associated_pow_irreducible** 是 Mathlib 中的一个定理，位于命名空间 `
IsDiscreteValuationRing`。
形式化陈述：associated_pow_irreducible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducib
le ϖ) : exists n : Nat, Associated x (ϖ ^ n)
参数：hx : x != 0；hirr : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsNoetherianRing.wfDvdMonoid`：∀ {R : Type u_1} [inst : CommSemiring R] [
IsDomain R] [h : IsNoetherianRing R], WfDvdMonoid R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `WfDvdMonoid.exists_factors`：exists_factors (a : α) : a != 0 -> exists f 
: Multiset α, (forall b in f, Irreducible b) ∧ Associated f.prod a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
· 使用定理 `Associates.prod_mk`：prod_mk {p : Multiset M} : (p.map Associates.mk).pro
d = Associates.mk p.prod
· 使用定理 `Associates.mk_pow`：mk_pow (a : M) (n : Nat) : Associates.mk (a ^ n) = As
sociates.mk a ^ n
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Multiset.eq_replicate`：eq_replicate {a : α} {n} {s : Multiset α} : s = r
eplicate n a ↔ card s = n ∧ forall b in s, b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.card_map`：card_map (f : α -> β) (s) : card (map f s) = card s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `IsDiscreteValuationRing.associated_of_irreducible`：associated_of_irreduc
ible {a b : R} (ha : Irreducible a) (hb : Irreducible b) : Associated a b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem associated_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ n : ℕ, Associated x (ϖ ^ n) := by
  have : WfDvdMonoid R := IsNoetherianRing.wfDvdMonoid
  obtain ⟨fx, hfx⟩ := WfDvdMonoid.exists_factors x hx
  use Multiset.card fx
  have H := hfx.2
  rw [← Associates.mk_eq_mk_iff_associated] at H ⊢
  rw [← H, ← Associates.prod_mk, Associates.mk_pow, ← Multiset.prod_replicate]
  congr 1
  rw [Multiset.eq_replicate]
  simp only [true_and, and_imp, Multiset.card_map, Multiset.mem_map, exists_imp]
  rintro _ _ _ rfl
  rw [Associates.mk_eq_mk_iff_associated]
  refine associated_of_irreducible _ ?_ hirr
  apply hfx.1
  assumption
/-
**IsDiscreteValuationRing.eq_unit_mul_pow_irreducible** 是 Mathlib 中的一个定理，位于命名空间 
`IsDiscreteValuationRing`。
形式化陈述：eq_unit_mul_pow_irreducible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreduci
ble ϖ) : exists (n : Nat) (u : Rˣ), x = u * ϖ ^ n
参数：hx : x != 0；hirr : Irreducible ϖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.associated_pow_irreducible`：associated_pow_irred
ucible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists n : Nat, As
sociated x (ϖ ^ n)
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem eq_unit_mul_pow_irreducible {x : R} (hx : x ≠ 0) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ (n : ℕ) (u : Rˣ), x = u * ϖ ^ n := by
  obtain ⟨n, hn⟩ := associated_pow_irreducible hx hirr
  obtain ⟨u, rfl⟩ := hn.symm
  use n, u
  apply mul_comm

/--
If `K` is the fraction field of a discrete valuation ring `R`, any element `x` of `K` can be
expressed as `u • (algebraMap R K ϖ) ^ n` for some `u : Rˣ` and `n : ℤ`.
-/
/-
**IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible** 是 Mathlib 中
的一个引理，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：exists_units_eq_smul_zpow_of_irreducible {K : Type*} [Field K] [Algebra R 
K] [IsFractionRing R K] {ϖ : R} (hϖ : Irreducible ϖ) {x : K} (hx : x != 0) : exi
sts (n : Int) (u : Rˣ), x = u • algebraMap R K ϖ ^ n
参数：hϖ : Irreducible ϖ；hx : x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`：eq_unit_mul_pow_irr
educible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists (n : Nat)
 (u : Rˣ), x = u * ϖ ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `div_smul_div_comm`：div_smul_div_comm [Group G] [GroupWithZero G₀] [MulAc
tion G G₀] [IsScalarTower G G₀ G₀] [SMulCommClass G G₀ G₀] (g h : G) (a b : G₀) 
: (g / …
· 使用定理 `Units.instIsScalarTower`：∀ {M : Type u_3} {N : Type u_4} {α : Type u_5} 
[inst : Monoid M] [inst_1 : SMul M N] [inst_2 : SMul M α]   [inst_3 : SMul N α] 
[IsScalarTowe…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `K` is the fraction field of a discrete valuation ring `R`, any element `x` o
f `K` can be
expressed as `u • (algebraMap R K ϖ) ^ n` for some `u : Rˣ` and `n : ℤ`.
-/
lemma exists_units_eq_smul_zpow_of_irreducible
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {ϖ : R} (hϖ : Irreducible ϖ) {x : K} (hx : x ≠ 0) :
    ∃ (n : ℤ) (u : Rˣ), x = u • algebraMap R K ϖ ^ n := by
  obtain ⟨x, y, hy, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible (x := x) (by simp_all) hϖ
  obtain ⟨m, v, rfl⟩ := eq_unit_mul_pow_irreducible (by simpa using hy) hϖ
  have hϖ' : algebraMap R K ϖ ≠ 0 := by simpa using hϖ.ne_zero
  refine ⟨n - m, u / v, ?_⟩
  simp [hϖ', zpow_sub₀, div_smul_div_comm, Units.smul_def u, Units.smul_def v, Algebra.smul_def]

open Submodule.IsPrincipal

/-- Every nonzero ideal in a DVR is a power of the maximal ideal.
See `idealOrderIsoENat` for a precise classification of ideals in a DVR. -/
/-
**IsDiscreteValuationRing.ideal_eq_span_pow_irreducible** 是 Mathlib 中的一个定理，位于命名空
间 `IsDiscreteValuationRing`。
形式化陈述：ideal_eq_span_pow_irreducible {s : Ideal R} (hs : s != ⊥) {ϖ : R} (hirr : 
Irreducible ϖ) : exists n : Nat, s = Ideal.span {ϖ ^ n}
参数：hs : s != ⊥；hirr : Irreducible ϖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero`：eq_bot_iff_generator
_eq_zero (S : Submodule R M) [S.IsPrincipal] : S = ⊥ ↔ generator S = 0
· 使用定理 `IsDiscreteValuationRing.associated_pow_irreducible`：associated_pow_irred
ucible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists n : Nat, As
sociated x (ϖ ^ n)
· 使用定理 `Ideal.span_singleton_generator`：∀ {R : Type u} [inst : Semiring R] (I : 
Ideal R) [inst_1 : Submodule.IsPrincipal I],   Ideal.span {Submodule.IsPrincipal
.generator I} = I
· 使用定理 `Ideal.span_singleton_eq_span_singleton`：span_singleton_eq_span_singleton
 {α : Type u} [CommSemiring α] [IsDomain α] {x y : α} : span ({x} : Set α) = spa
n ({y} : Set α) ↔ Associated…

--- 原说明 ---
Every nonzero ideal in a DVR is a power of the maximal ideal.
See `idealOrderIsoENat` for a precise classification of ideals in a DVR.
-/
theorem ideal_eq_span_pow_irreducible {s : Ideal R} (hs : s ≠ ⊥) {ϖ : R} (hirr : Irreducible ϖ) :
    ∃ n : ℕ, s = Ideal.span {ϖ ^ n} := by
  have gen_ne_zero : generator s ≠ 0 := by
    rw [Ne, ← eq_bot_iff_generator_eq_zero]
    assumption
  rcases associated_pow_irreducible gen_ne_zero hirr with ⟨n, u, hnu⟩
  use n
  have : span _ = _ := Ideal.span_singleton_generator s
  rw [← this, ← hnu, span_singleton_eq_span_singleton]
  use u
/-
**IsDiscreteValuationRing.unit_mul_pow_congr_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsDi
screteValuationRing`。
形式化陈述：unit_mul_pow_congr_pow {p q : R} (hp : Irreducible p) (hq : Irreducible q)
 (u v : Rˣ) (m n : Nat) (h : ↑u * p ^ m = v * q ^ n) : m = n
参数：hp : Irreducible p；hq : Irreducible q；u v : Rˣ；m n : Nat；h : ↑u * p ^ m = v *
 q ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_replicate`：prod_replicate (n : Nat) (a : M) : (replicate n
 a).prod = a ^ n
· 使用定理 `Associated.eq_1`：∀ {M : Type u_1} [inst : Monoid M] (x y : M), Associate
d x y = ∃ u, x * ↑u = y
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Units.mul_inv`：mul_inv : (a * ↑a⁻¹ : α) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Multiset.card_eq_card_of_rel`：card_eq_card_of_rel {r : α -> β -> Prop} {
s : Multiset α} {t : Multiset β} (h : Rel r s t) : card s = card t
· 使用定理 `UniqueFactorizationMonoid.factors_unique`：factors_unique {f g : Multiset
 α} (hf : forall x in f, Irreducible x) (hg : forall x in g, Irreducible x) (h :
 f.prod ~ᵤ g.prod) : Multiset.…
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `Multiset.eq_of_mem_replicate`：eq_of_mem_replicate {a b : α} {n} : b in r
eplicate n a -> b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Multiset.card_replicate`：∀ {α : Type u_1} (n : ℕ) (a : α), (Multiset.rep
licate n a).card = n
-/
theorem unit_mul_pow_congr_pow {p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ)
    (m n : ℕ) (h : ↑u * p ^ m = v * q ^ n) : m = n := by
  have key : Associated (Multiset.replicate m p).prod (Multiset.replicate n q).prod := by
    rw [Multiset.prod_replicate, Multiset.prod_replicate, Associated]
    refine ⟨u * v⁻¹, ?_⟩
    simp only [Units.val_mul]
    rw [mul_left_comm, ← mul_assoc, h, mul_right_comm, Units.mul_inv, one_mul]
  have := by
    refine Multiset.card_eq_card_of_rel (UniqueFactorizationMonoid.factors_unique ?_ ?_ key)
    all_goals
      intro x hx
      obtain rfl := Multiset.eq_of_mem_replicate hx
      assumption
  simpa only [Multiset.card_replicate]
/-
**IsDiscreteValuationRing.unit_mul_pow_congr_unit** 是 Mathlib 中的一个定理，位于命名空间 `IsD
iscreteValuationRing`。
形式化陈述：unit_mul_pow_congr_unit {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : N
at) (h : ↑u * ϖ ^ m = v * ϖ ^ n) : u = v
参数：hirr : Irreducible ϖ；u v : Rˣ；m n : Nat；h : ↑u * ϖ ^ m = v * ϖ ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDiscreteValuationRing.unit_mul_pow_congr_pow`：unit_mul_pow_congr_pow {
p q : R} (hp : Irreducible p) (hq : Irreducible q) (u v : Rˣ) (m n : Nat) (h : ↑
u * p ^ m = v * q ^ n) : m = n
-/
theorem unit_mul_pow_congr_unit {ϖ : R} (hirr : Irreducible ϖ) (u v : Rˣ) (m n : ℕ)
    (h : ↑u * ϖ ^ m = v * ϖ ^ n) : u = v := by
  obtain rfl : m = n := unit_mul_pow_congr_pow hirr hirr u v m n h
  rw [← sub_eq_zero] at h
  rw [← sub_mul, mul_eq_zero] at h
  rcases h with h | h
  · rw [sub_eq_zero] at h
    exact mod_cast h
  · apply (hirr.ne_zero (eq_zero_of_pow_eq_zero h)).elim

/-!
## The additive valuation on a DVR
-/

/-- The `ℕ∞`-valued additive valuation on a DVR. -/
/-
**IsDiscreteValuationRing.addVal** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscreteValuationR
ing`。
形式化陈述：addVal (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] 
: AddValuation R Nat∞
参数：R : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.exists_prime`：exists_prime : exists ϖ : R, Prime
 ϖ

--- 原说明 ---
The `ℕ∞`-valued additive valuation on a DVR.
-/
noncomputable def addVal (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    AddValuation R ℕ∞ :=
  multiplicity_addValuation (Classical.choose_spec (exists_prime R))
/-
**IsDiscreteValuationRing.addVal_def** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuat
ionRing`。
形式化陈述：addVal_def (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : Nat) (hr : r
 = u * ϖ ^ n) : addVal R r = n
参数：r : R；u : Rˣ；hϖ : Irreducible ϖ；n : Nat；hr : r = u * ϖ ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.exists_prime`：exists_prime : exists ϖ : R, Prime
 ϖ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.addVal.eq_1`：∀ (R : Type u) [inst : CommRing R] 
[inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R],   IsDiscreteValuatio
nRing.addVal R = multipli…
· 使用定理 `multiplicity_addValuation_apply`：multiplicity_addValuation_apply {hp : P
rime p} {r : R} : multiplicity_addValuation hp r = emultiplicity p r
· 使用定理 `emultiplicity_eq_of_associated_left`：emultiplicity_eq_of_associated_left
 {a b c : α} (h : Associated a b) : emultiplicity b c = emultiplicity a c
· 使用定理 `IsDiscreteValuationRing.associated_of_irreducible`：associated_of_irreduc
ible {a b : R} (ha : Irreducible a) (hb : Irreducible b) : Associated a b
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `emultiplicity_eq_of_associated_right`：emultiplicity_eq_of_associated_rig
ht {a b c : α} (h : Associated b c) : emultiplicity a b = emultiplicity a c
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `emultiplicity_pow_self_of_prime`：emultiplicity_pow_self_of_prime {p : α}
 (hp : Prime p) (n : Nat) : emultiplicity p (p ^ n) = n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `irreducible_iff_prime`：irreducible_iff_prime [DecompositionMonoid M] {a 
: M} : Irreducible a ↔ Prime a
· 使用定理 `UniqueFactorizationMonoid.instDecompositionMonoid`：∀ {α : Type u_1} [ins
t : CommMonoidWithZero α] [UniqueFactorizationMonoid α], DecompositionMonoid α
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
-/
theorem addVal_def (r : R) (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) (hr : r = u * ϖ ^ n) :
    addVal R r = n := by
  rw [addVal, multiplicity_addValuation_apply, hr, emultiplicity_eq_of_associated_left
      (associated_of_irreducible R hϖ (Classical.choose_spec (exists_prime R)).irreducible),
    emultiplicity_eq_of_associated_right (Associated.symm ⟨u, mul_comm _ _⟩),
    emultiplicity_pow_self_of_prime (irreducible_iff_prime.1 hϖ)]

/-- An alternative definition of the additive valuation, taking units into account -/
/-
**IsDiscreteValuationRing.addVal_def'** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValua
tionRing`。
形式化陈述：addVal_def' (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : Nat) : addVal R ((u
 : R) * ϖ ^ n) = n
参数：u : Rˣ；hϖ : Irreducible ϖ；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.addVal_def`：addVal_def (r : R) (u : Rˣ) {ϖ : R} 
(hϖ : Irreducible ϖ) (n : Nat) (hr : r = u * ϖ ^ n) : addVal R r = n

--- 原说明 ---
An alternative definition of the additive valuation, taking units into account
-/
theorem addVal_def' (u : Rˣ) {ϖ : R} (hϖ : Irreducible ϖ) (n : ℕ) :
    addVal R ((u : R) * ϖ ^ n) = n :=
  addVal_def _ u hϖ n rfl
/-
**IsDiscreteValuationRing.addVal_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValua
tionRing`。
形式化陈述：addVal_zero : addVal R 0 = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_zero`：AddValuation.map_zero : addValuationDef (0 : Rat_
[p]) = ⊤
-/
theorem addVal_zero : addVal R 0 = ⊤ :=
  (addVal R).map_zero
/-
**IsDiscreteValuationRing.addVal_one** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuat
ionRing`。
形式化陈述：addVal_one : addVal R 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_one`：AddValuation.map_one : addValuationDef (1 : Rat_[p
]) = 0
-/
theorem addVal_one : addVal R 1 = 0 :=
  (addVal R).map_one

@[simp]
/-
**IsDiscreteValuationRing.addVal_uniformizer** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscre
teValuationRing`。
形式化陈述：addVal_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) : addVal R ϖ = 1
参数：hϖ : Irreducible ϖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsDiscreteValuationRing.addVal_def`：addVal_def (r : R) (u : Rˣ) {ϖ : R} 
(hϖ : Irreducible ϖ) (n : Nat) (hr : r = u * ϖ ^ n) : addVal R r = n
-/
theorem addVal_uniformizer {ϖ : R} (hϖ : Irreducible ϖ) : addVal R ϖ = 1 := by
  simpa only [one_mul, eq_self_iff_true, Units.val_one, pow_one, forall_true_left, Nat.cast_one]
    using addVal_def ϖ 1 hϖ 1
/-
**IsDiscreteValuationRing.addVal_mul** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuat
ionRing`。
形式化陈述：addVal_mul {a b : R} : addVal R (a * b) = addVal R a + addVal R b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_mul`：AddValuation.map_mul (x y : Rat_[p]) : addValuatio
nDef (x * y : Rat_[p]) = addValuationDef x + addValuationDef y
-/
theorem addVal_mul {a b : R} :
    addVal R (a * b) = addVal R a + addVal R b :=
  (addVal R).map_mul _ _
/-
**IsDiscreteValuationRing.addVal_pow** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuat
ionRing`。
形式化陈述：addVal_pow (a : R) (n : Nat) : addVal R (a ^ n) = n • addVal R a
参数：a : R；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_pow`：map_pow : forall (x : R) (n : Nat), v (x ^ n) = n 
• (v x)
-/
theorem addVal_pow (a : R) (n : ℕ) : addVal R (a ^ n) = n • addVal R a :=
  (addVal R).map_pow _ _

nonrec theorem _root_.Irreducible.addVal_pow {ϖ : R} (h : Irreducible ϖ) (n : ℕ) :
    addVal R (ϖ ^ n) = n := by
  rw [addVal_pow, addVal_uniformizer h, nsmul_one]
/-
**IsDiscreteValuationRing.addVal_eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscret
eValuationRing`。
形式化陈述：addVal_eq_top_iff {a : R} : addVal R a = ⊤ ↔ a = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.exists_prime`：exists_prime : exists ϖ : R, Prime
 ϖ
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `IsDiscreteValuationRing.associated_pow_irreducible`：associated_pow_irred
ucible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists n : Nat, As
sociated x (ϖ ^ n)
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsDiscreteValuationRing.addVal_def'`：addVal_def' (u : Rˣ) {ϖ : R} (hϖ : 
Irreducible ϖ) (n : Nat) : addVal R ((u : R) * ϖ ^ n) = n
· 使用定理 `IsDiscreteValuationRing.addVal_zero`：addVal_zero : addVal R 0 = ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem addVal_eq_top_iff {a : R} : addVal R a = ⊤ ↔ a = 0 := by
  have hi := (Classical.choose_spec (exists_prime R)).irreducible
  constructor
  · contrapose
    intro h
    obtain ⟨n, ha⟩ := associated_pow_irreducible h hi
    obtain ⟨u, rfl⟩ := ha.symm
    rw [mul_comm, addVal_def' u hi n]
    nofun
  · rintro rfl
    exact addVal_zero
/-
**IsDiscreteValuationRing.addVal_le_iff_dvd** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscret
eValuationRing`。
形式化陈述：addVal_le_iff_dvd {a b : R} : addVal R a <= addVal R b ↔ a ∣ b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.exists_prime`：exists_prime : exists ϖ : R, Prime
 ϖ
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.addVal_eq_top_iff`：addVal_eq_top_iff {a : R} : a
ddVal R a = ⊤ ↔ a = 0
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `IsDiscreteValuationRing.addVal_zero`：addVal_zero : addVal R 0 = ⊤
· 使用定理 `dvd_zero`：dvd_zero (a : α) : a ∣ 0
· 使用定理 `IsDiscreteValuationRing.associated_pow_irreducible`：associated_pow_irred
ucible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists n : Nat, As
sociated x (ϖ ^ n)
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `Associated.dvd`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, Associated
 a b → a ∣ b
· 使用定理 `emultiplicity_le_emultiplicity_iff`：emultiplicity_le_emultiplicity_iff {
c d : β} : emultiplicity a b <= emultiplicity c d ↔ forall n : Nat, a ^ n ∣ b ->
 c ^ n ∣ d
· 使用定理 `multiplicity_addValuation_apply`：multiplicity_addValuation_apply {hp : P
rime p} {r : R} : multiplicity_addValuation hp r = emultiplicity p r
· 使用定理 `IsDiscreteValuationRing.addVal.eq_1`：∀ (R : Type u) [inst : CommRing R] 
[inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R],   IsDiscreteValuatio
nRing.addVal R = multipli…
· 使用定理 `Associated.symm`：∀ {M : Type u_1} [inst : Monoid M] {x y : M}, Associate
d x y → Associated y x
· 使用定理 `emultiplicity_le_emultiplicity_of_dvd_right`：emultiplicity_le_emultiplic
ity_of_dvd_right {a b c : α} (h : b ∣ c) : emultiplicity a b <= emultiplicity a 
c
-/
theorem addVal_le_iff_dvd {a b : R} : addVal R a ≤ addVal R b ↔ a ∣ b := by
  have hp := Classical.choose_spec (exists_prime R)
  constructor <;> intro h
  · by_cases ha0 : a = 0
    · rw [ha0, addVal_zero, top_le_iff, addVal_eq_top_iff] at h
      rw [h]
      apply dvd_zero
    obtain ⟨n, ha⟩ := associated_pow_irreducible ha0 hp.irreducible
    rw [addVal, multiplicity_addValuation_apply, multiplicity_addValuation_apply,
      emultiplicity_le_emultiplicity_iff] at h
    exact ha.dvd.trans (h n ha.symm.dvd)
  · rw [addVal, multiplicity_addValuation_apply, multiplicity_addValuation_apply]
    exact emultiplicity_le_emultiplicity_of_dvd_right h
/-
**IsDiscreteValuationRing.addVal_add** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscreteValuat
ionRing`。
形式化陈述：addVal_add {a b : R} : min (addVal R a) (addVal R b) <= addVal R (a + b)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddValuation.map_add`：AddValuation.map_add (x y : Rat_[p]) : min (addVal
uationDef x) (addValuationDef y) <= addValuationDef (x + y : Rat_[p])
-/
theorem addVal_add {a b : R} : min (addVal R a) (addVal R b) ≤ addVal R (a + b) :=
  (addVal R).map_add _ _

@[simp]
/-
**IsDiscreteValuationRing.addVal_eq_zero_of_unit** 是 Mathlib 中的一个引理，位于命名空间 `IsDi
screteValuationRing`。
形式化陈述：addVal_eq_zero_of_unit (u : Rˣ) : addVal R u = 0
参数：u : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.addVal_def`：addVal_def (r : R) (u : Rˣ) {ϖ : R} 
(hϖ : Irreducible ϖ) (n : Nat) (hr : r = u * ϖ ^ n) : addVal R r = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
-/
lemma addVal_eq_zero_of_unit (u : Rˣ) :
    addVal R u = 0 := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [addVal_def (u : R) u hϖ 0] <;>
  simp
/-
**IsDiscreteValuationRing.addVal_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `IsDiscre
teValuationRing`。
形式化陈述：addVal_eq_zero_iff {x : R} : addVal R x = 0 ↔ IsUnit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AddValuation.map_zero`：AddValuation.map_zero : addValuationDef (0 : Rat_
[p]) = ⊤
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`：eq_unit_mul_pow_irr
educible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists (n : Nat)
 (u : Rˣ), x = u * ϖ ^ n
· 使用定理 `AddValuation.map_mul`：AddValuation.map_mul (x y : Rat_[p]) : addValuatio
nDef (x * y : Rat_[p]) = addValuationDef x + addValuationDef y
· 使用引理 `IsDiscreteValuationRing.addVal_eq_zero_of_unit`：addVal_eq_zero_of_unit (
u : Rˣ) : addVal R u = 0
· 使用定理 `AddValuation.map_pow`：map_pow : forall (x : R) (n : Nat), v (x ^ n) = n 
• (v x)
· 使用定理 `IsDiscreteValuationRing.addVal_uniformizer`：addVal_uniformizer {ϖ : R} (
hϖ : Irreducible ϖ) : addVal R ϖ = 1
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `instIsDedekindFiniteMonoid`：∀ (M : Type u_2) [inst : CommMonoid M], IsDe
dekindFiniteMonoid M
· 使用引理 `isUnit_pow_iff_of_not_isUnit`：isUnit_pow_iff_of_not_isUnit (hx : ¬ IsUni
t a) {n : Nat} : IsUnit (a ^ n) ↔ n = 0
· 使用定理 `Irreducible.not_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}, Irre
ducible p → ¬IsUnit p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
-/
lemma addVal_eq_zero_iff {x : R} :
    addVal R x = 0 ↔ IsUnit x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, rfl⟩ := eq_unit_mul_pow_irreducible hx hϖ
  simp [isUnit_pow_iff_of_not_isUnit hϖ.not_isUnit, hϖ]
/-
**IsDiscreteValuationRing.addVal_eq_iff_associated** 是 Mathlib 中的一个引理，位于命名空间 `Is
DiscreteValuationRing`。
形式化陈述：addVal_eq_iff_associated (x y : R) : addVal R x = addVal R y ↔ Associated 
x y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsDiscreteValuationRing.addVal_eq_top_iff`：addVal_eq_top_iff {a : R} : a
ddVal R a = ⊤ ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddValuation.map_zero`：AddValuation.map_zero : addValuationDef (0 : Rat_
[p]) = ⊤
· 使用定理 `Associated.refl`：∀ {M : Type u_1} [inst : Monoid M] (x : M), Associated 
x x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible`：eq_unit_mul_pow_irr
educible {x : R} (hx : x != 0) {ϖ : R} (hirr : Irreducible ϖ) : exists (n : Nat)
 (u : Rˣ), x = u * ϖ ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDiscreteValuationRing.addVal_uniformizer`：addVal_uniformizer {ϖ : R} (
hϖ : Irreducible ϖ) : addVal R ϖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddValuation.map_mul`：AddValuation.map_mul (x y : Rat_[p]) : addValuatio
nDef (x * y : Rat_[p]) = addValuationDef x + addValuationDef y
· 使用引理 `IsDiscreteValuationRing.addVal_eq_zero_of_unit`：addVal_eq_zero_of_unit (
u : Rˣ) : addVal R u = 0
· 使用定理 `AddValuation.map_pow`：map_pow : forall (x : R) (n : Nat), v (x ^ n) = n 
• (v x)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Associates.mk_eq_mk_iff_associated`：mk_eq_mk_iff_associated [Monoid M] {
a b : M} : Associates.mk a = Associates.mk b ↔ a ~ᵤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma addVal_eq_iff_associated (x y : R) :
    addVal R x = addVal R y ↔ Associated x y := by
  constructor
  · intro h
    by_cases hx : x = 0
    · simp_all only [AddValuation.map_zero]
      rw [addVal_eq_top_iff.mp h.symm]
    by_cases hy : y = 0
    · simp_all only [AddValuation.map_zero, associated_zero_iff_eq_zero]
      exact hx (addVal_eq_top_iff.mp h)
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    obtain ⟨m, α, hx'⟩ := eq_unit_mul_pow_irreducible hx hϖ
    obtain ⟨n, β, hy'⟩ := eq_unit_mul_pow_irreducible hy hϖ
    simp only [hx', AddValuation.map_mul, addVal_eq_zero_of_unit, AddValuation.map_pow,
      nsmul_eq_mul, zero_add, hy', associated_unit_mul_right_iff,
      associated_unit_mul_left_iff] at h ⊢
    simp only [addVal_uniformizer hϖ, mul_one, ENat.natCast_inj] at h
    rw [h]
    exact Associates.mk_eq_mk_iff_associated.mp rfl
  · rintro ⟨u, rfl⟩
    simp_all

variable (R)

set_option backward.isDefEq.respectTransparency.types false in
/-- The ideals of a discrete valuation ring are exactly the powers of the maximal ideal. -/
@[simps apply]
/-
**IsDiscreteValuationRing.idealOrderIsoENat** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscret
eValuationRing`。
形式化陈述：idealOrderIsoENat : Ideal R ≃o ENatᵒᵈ where toFun I
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R

--- 原说明 ---
The ideals of a discrete valuation ring are exactly the powers of the maximal id
eal.
-/
noncomputable def idealOrderIsoENat : Ideal R ≃o ENatᵒᵈ where
  toFun I := .toDual (addVal R (generator I))
  invFun n := n.ofDual.recTopCoe ⊥ (fun n ↦ maximalIdeal R ^ n)
  left_inv I := by
    let x := generator I
    suffices (addVal R x).recTopCoe ⊥ (fun n ↦ maximalIdeal R ^ n) = span {x} by
      rwa [Ideal.span_singleton_generator] at this
    by_cases hx0 : x = 0
    · simp [hx0]
    · obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
      obtain ⟨n, u, hu⟩ := eq_unit_mul_pow_irreducible hx0 hϖ
      rw [hu, addVal_def' u hϖ, span_singleton_mul_left_unit u.isUnit,
        ENat.recTopCoe_natCast, hϖ.maximalIdeal_eq, span_singleton_pow]
  right_inv n := by
    obtain ⟨k, rfl⟩ := OrderDual.toDual.surjective n
    dsimp
    induction k with
    | top => simp
    | coe k =>
      obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
      rw [OrderDual.toDual_inj, ENat.recTopCoe_natCast, hϖ.maximalIdeal_eq,
        span_singleton_pow, ← hϖ.addVal_pow k, addVal_eq_iff_associated]
      exact associated_generator_span_self (ϖ ^ k)
  map_rel_iff' {I J} := by
    simp [addVal_le_iff_dvd, ← span_singleton_le_span_singleton]

@[simp]
/-
**IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe** 是 Mathlib 中的一个定理，位于
命名空间 `IsDiscreteValuationRing`。
形式化陈述：idealOrderIsoENat_symm_apply_coe (n : Nat) : (idealOrderIsoENat R).symm n 
= maximalIdeal R ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idealOrderIsoENat_symm_apply_coe (n : ℕ) :
    (idealOrderIsoENat R).symm n = maximalIdeal R ^ n :=
  rfl

variable {R} in
/-
**IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe_of_irreducible** 是 Ma
thlib 中的一个定理，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：idealOrderIsoENat_symm_apply_coe_of_irreducible (n : Nat) {ϖ : R} (hϖ : Ir
reducible ϖ) : (idealOrderIsoENat R).symm n = Ideal.span {ϖ ^ n}
参数：n : Nat；hϖ : Irreducible ϖ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.idealOrderIsoENat_symm_apply_coe`：idealOrderIsoE
Nat_symm_apply_coe (n : Nat) : (idealOrderIsoENat R).symm n = maximalIdeal R ^ n
· 使用定理 `Irreducible.maximalIdeal_eq`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ϖ : R},   Irreducible ϖ → Is
LocalRing.maximal…
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem idealOrderIsoENat_symm_apply_coe_of_irreducible (n : ℕ) {ϖ : R} (hϖ : Irreducible ϖ) :
    (idealOrderIsoENat R).symm n = Ideal.span {ϖ ^ n} := by
  rw [idealOrderIsoENat_symm_apply_coe, hϖ.maximalIdeal_eq, span_singleton_pow]

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsDiscreteValuationRing.coheight_pow_maximalIdeal** 是 Mathlib 中的一个定理，位于命名空间 `I
sDiscreteValuationRing`。
形式化陈述：coheight_pow_maximalIdeal (n : Nat) : Order.coheight (maximalIdeal R ^ n) 
= n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Order.height_enat`：height_enat (n : Nat∞) : height n = n
· 使用引理 `Order.coheight_orderIso`：coheight_orderIso (f : α ≃o β) (x : α) : coheig
ht (f x) = coheight x
-/
theorem coheight_pow_maximalIdeal (n : ℕ) : Order.coheight (maximalIdeal R ^ n) = n := by
  simpa only [Order.coheight_toDual, Order.height_enat] using!
    Order.coheight_orderIso (idealOrderIsoENat R).symm (.toDual n)
/-
**IsDiscreteValuationRing.length_quotient_pow_maximalIdeal** 是 Mathlib 中的一个定理，位于
命名空间 `IsDiscreteValuationRing`。
形式化陈述：length_quotient_pow_maximalIdeal (n : Nat) : Module.length R (R ⧸ maximalI
deal R ^ n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.length_quotient`：Module.length_quotient {N : Submodule R M} : Mod
ule.length R (M ⧸ N) = Order.coheight N
· 使用定理 `IsDiscreteValuationRing.coheight_pow_maximalIdeal`：coheight_pow_maximalI
deal (n : Nat) : Order.coheight (maximalIdeal R ^ n) = n
-/
theorem length_quotient_pow_maximalIdeal (n : ℕ) :
    Module.length R (R ⧸ maximalIdeal R ^ n) = n := by
  rw [Module.length_quotient, coheight_pow_maximalIdeal]

end

/-
**IsDiscreteValuationRing.** 是 Mathlib 中的一个实例，位于命名空间 `IsDiscreteValuationRing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    IsHausdorff (maximalIdeal R) R where
  haus' x hx := by
    obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
    simp only [← Ideal.one_eq_top, smul_eq_mul, mul_one, SModEq.zero, hϖ.maximalIdeal_eq,
      Ideal.span_singleton_pow, Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow] at hx
    rwa [← addVal_eq_top_iff, ENat.eq_top_iff_forall_ge]

noncomputable section toEuclideanDomain
variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- A noncomputable quotient to define the Euclidean domain structure. The GCD algorithm only takes
two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` so we're done in one step;
otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to the first case. -/
/-
**IsDiscreteValuationRing.quotient** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscreteValuatio
nRing`。
形式化陈述：quotient (x y : R) : R
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A noncomputable quotient to define the Euclidean domain structure. The GCD algor
ithm only takes
two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` so we're don
e in one step;
otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to the f
irst case.
-/
def quotient (x y : R) : R :=
  open scoped Classical in if y = 0 then 0 else if h : y ∣ x then h.choose else 0

/-- A noncomputable remainder to define the Euclidean domain structure. The GCD algorithm only takes
two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` so we're done in one step;
otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to the first case. -/
/-
**IsDiscreteValuationRing.remainder** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscreteValuati
onRing`。
形式化陈述：remainder (x y : R) : R
参数：x y : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A noncomputable remainder to define the Euclidean domain structure. The GCD algo
rithm only takes
two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` so we're don
e in one step;
otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to the f
irst case.
-/
def remainder (x y : R) : R :=
  open scoped Classical in if y ∣ x then 0 else x

/-- A modification of the valuation, sending `0` to `⊥` instead of `⊤`. -/
/-
**IsDiscreteValuationRing.toWithBotNat** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscreteValu
ationRing`。
形式化陈述：toWithBotNat (x : R) : WithBot Nat
参数：x : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A modification of the valuation, sending `0` to `⊥` instead of `⊤`.
-/
def toWithBotNat (x : R) : WithBot ℕ :=
  addVal R x
/-
**IsDiscreteValuationRing.toWithBotNat_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsDiscret
eValuationRing`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R],   IsDiscreteValuationRing.toWithBotNat 0 = ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.addVal_zero`：addVal_zero : addVal R 0 = ⊤
-/
@[simp] lemma toWithBotNat_zero : toWithBotNat (R := R) 0 = ⊥ :=
  addVal_zero
/-
**IsDiscreteValuationRing.toWithBotNat_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsD
iscreteValuationRing`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] (x : R),   IsDiscreteValuationRing.toWithBotNat x = ⊥ ↔ x 
= 0
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDiscreteValuationRing.addVal_eq_top_iff`：addVal_eq_top_iff {a : R} : a
ddVal R a = ⊤ ↔ a = 0
-/
@[simp] lemma toWithBotNat_eq_bot_iff (x : R) : toWithBotNat x = ⊥ ↔ x = 0 :=
  addVal_eq_top_iff
/-
**IsDiscreteValuationRing.bot_lt_toWithBotNat_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsD
iscreteValuationRing`。
形式化陈述：∀ {R : Type u_2} [inst : CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDis
creteValuationRing R] (x : R),   ⊥ < IsDiscreteValuationRing.toWithBotNat x ↔ x 
≠ 0
参数：x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma bot_lt_toWithBotNat_iff (x : R) : ⊥ < toWithBotNat x ↔ x ≠ 0 := by
  rw [bot_lt_iff_ne_bot]; simp
/-
**IsDiscreteValuationRing.toWithBotNat_le_toWithBotNat_iff** 是 Mathlib 中的一个引理，位于
命名空间 `IsDiscreteValuationRing`。
形式化陈述：toWithBotNat_le_toWithBotNat_iff {x y : R} (hx : x != 0) (hy : y != 0) : t
oWithBotNat x <= toWithBotNat y ↔ x ∣ y
参数：hx : x != 0；hy : y != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.addVal_eq_top_iff`：addVal_eq_top_iff {a : R} : a
ddVal R a = ⊤ ↔ a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDiscreteValuationRing.addVal_le_iff_dvd`：addVal_le_iff_dvd {a b : R} :
 addVal R a <= addVal R b ↔ a ∣ b
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `WithTop.coe_le_coe`：∀ {α : Type u_1} {a b : α} [inst : LE α], ↑b ≤ ↑a ↔ 
b ≤ a
-/
lemma toWithBotNat_le_toWithBotNat_iff {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
    toWithBotNat x ≤ toWithBotNat y ↔ x ∣ y := by
  unfold toWithBotNat
  generalize hvx : addVal R x = vx
  generalize hvy : addVal R y = vy
  cases vx with
  | top => rw [addVal_eq_top_iff] at hvx; tauto
  | coe vx =>
    cases vy with
    | top => rw [addVal_eq_top_iff] at hvy; tauto
    | coe vy =>
      rw [← addVal_le_iff_dvd, hvx, hvy]
      exact WithBot.coe_le_coe.trans WithTop.coe_le_coe.symm
/-
**IsDiscreteValuationRing.dvd_of_toWithBotNat_le_toWithBotNat** 是 Mathlib 中的一个引理
，位于命名空间 `IsDiscreteValuationRing`。
形式化陈述：dvd_of_toWithBotNat_le_toWithBotNat (x y : R) (hx : x != 0) (hle : toWithB
otNat x <= toWithBotNat y) : x ∣ y
参数：x y : R；hx : x != 0；hle : toWithBotNat x <= toWithBotNat y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDiscreteValuationRing.toWithBotNat.congr_simp`：∀ {R : Type u_2} [inst 
: CommRing R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R] (x x_1 
: R),   x = x_1 → IsDiscreteValuation…
· 使用定理 `IsDiscreteValuationRing.toWithBotNat_zero`：∀ {R : Type u_2} [inst : Comm
Ring R] [inst_1 : IsDomain R] [inst_2 : IsDiscreteValuationRing R],   IsDiscrete
ValuationRing.toWithBotNat 0 = …
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsDiscreteValuationRing.toWithBotNat_le_toWithBotNat_iff`：toWithBotNat_l
e_toWithBotNat_iff {x y : R} (hx : x != 0) (hy : y != 0) : toWithBotNat x <= toW
ithBotNat y ↔ x ∣ y
-/
lemma dvd_of_toWithBotNat_le_toWithBotNat (x y : R) (hx : x ≠ 0)
    (hle : toWithBotNat x ≤ toWithBotNat y) : x ∣ y := by
  by_cases hy : y = 0
  · simp [hy, hx] at hle
  exact (toWithBotNat_le_toWithBotNat_iff hx hy).mp hle

variable (R) in
/-- A noncomputable Euclidean domain structure on a discrete valuation ring, where the GCD algorithm
only takes two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` so we're done in one
step; otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to the first case.
See `EuclideanDomain.to_principal_ideal_domain` for EuclideanDomain ⇒ PID. -/
@[instance_reducible]
/-
**IsDiscreteValuationRing.toEuclideanDomain** 是 Mathlib 中的一个定义，位于命名空间 `IsDiscret
eValuationRing`。
形式化陈述：toEuclideanDomain : EuclideanDomain R where quotient
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A noncomputable Euclidean domain structure on a discrete valuation ring, where t
he GCD algorithm
only takes two steps to terminate. Given `GCD(x,y)`, if `x ∣ y` then `y%x = 0` s
o we're done in one
step; otherwise `y%x = y` and then `GCD(x,y) = GCD(y,x)` which brings us back to
 the first case.
See `EuclideanDomain.to_principal_ideal_domain` for EuclideanDomain ⇒ PID.
-/
def toEuclideanDomain : EuclideanDomain R where
  quotient := quotient
  quotient_zero x := by simp [quotient]
  remainder := remainder
  quotient_mul_add_remainder_eq x y := by
    rw [remainder, quotient]
    split_ifs with h₁ h₂ h₂
    · rw [h₁, zero_dvd_iff] at h₂; rw [h₁, h₂]; ring
    · rw [h₁]; ring
    · rw [← h₂.choose_spec]; ring
    · ring
  r x y := toWithBotNat x < toWithBotNat y
  r_wellFounded := WellFounded.onFun wellFounded_lt
  remainder_lt x y hy := by
    rw [remainder]
    split_ifs with hyx
    · rwa [toWithBotNat_zero, bot_lt_toWithBotNat_iff]
    · exact lt_iff_not_ge.mpr (mt (dvd_of_toWithBotNat_le_toWithBotNat _ _ hy) hyx)
  mul_left_not_lt x y hy := by
    by_cases hx : x = 0
    · simp [hx]
    rw [not_lt, toWithBotNat_le_toWithBotNat_iff hx (mul_ne_zero hx hy)]
    exact dvd_mul_right _ _

end toEuclideanDomain

end IsDiscreteValuationRing


section

variable (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]

/-- A DVR is a valuation ring. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A DVR is a valuation ring.
-/
instance (priority := 100) of_isDiscreteValuationRing : ValuationRing A := inferInstance

end

namespace Valuation.Integers

variable {K Γ₀ O : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [CommRing O]
    [Algebra O K] {v : Valuation K Γ₀} (hv : v.Integers O)
include hv

/-
**Valuation.Integers.maximalIdeal_eq_setOfPred_le_v_algebraMap** 是 Mathlib 中的一个引
理，位于命名空间 `Valuation.Integers`。
形式化陈述：maximalIdeal_eq_setOfPred_le_v_algebraMap : letI : IsDomain O
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap`：coe_
span_singleton_eq_setOfPred_le_v_algebraMap (hv : Integers v O) (x : O) : (Ideal
.span {x} : Set O) = {y : O | v (algebraMap O F y) <= v …
· 使用定理 `Irreducible.maximalIdeal_eq`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ϖ : R},   Irreducible ϖ → Is
LocalRing.maximal…
-/
lemma maximalIdeal_eq_setOfPred_le_v_algebraMap :
    letI : IsDomain O := hv.hom_inj.isDomain
    ∀ [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ),
    (IsLocalRing.maximalIdeal O : Set O) =
      {y : O | v (algebraMap O K y) ≤ v (algebraMap O K ϖ)} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ _ h
  rw [← hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap, ← h.maximalIdeal_eq]

@[deprecated (since := "2026-07-09")]
alias maximalIdeal_eq_setOf_le_v_algebraMap := maximalIdeal_eq_setOfPred_le_v_algebraMap
/-
**Valuation.Integers.maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow** 是 Mathl
ib 中的一个引理，位于命名空间 `Valuation.Integers`。
形式化陈述：maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow : letI : IsDomain O
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.isDomain`：∀ {α : Type u_1} {β : Type u_2} [inst : Sem
iring α] [IsDomain α] [inst_2 : Semiring β] {F : Type u_3}   [inst_3 : FunLike F
 β α] [MonoidWith…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Valuation.Integers.hom_inj`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] {v : Valuation R Γ₀}   {O : Ty
pe w} [inst_2 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsDiscreteValuationRing.toIsLocalRing`：∀ {R : Type u} {inst : CommRing R
} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsLocalRing R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.Integers.coe_span_singleton_eq_setOfPred_le_v_algebraMap`：coe_
span_singleton_eq_setOfPred_le_v_algebraMap (hv : Integers v O) (x : O) : (Ideal
.span {x} : Set O) = {y : O | v (algebraMap O F y) <= v …
· 使用定理 `Ideal.span_singleton_pow`：span_singleton_pow (s : R) [(span {s}).IsTwoSi
ded] (n : Nat) : span {s} ^ n = (span {s ^ n} : Ideal R)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Irreducible.maximalIdeal_eq`：∀ {R : Type u} [inst : CommRing R] [inst_1 
: IsDomain R] [inst_2 : IsDiscreteValuationRing R] {ϖ : R},   Irreducible ϖ → Is
LocalRing.maximal…
-/
lemma maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow :
    letI : IsDomain O := hv.hom_inj.isDomain
    ∀ [IsDiscreteValuationRing O] {ϖ : O} (_h : Irreducible ϖ) (n : ℕ),
    ((IsLocalRing.maximalIdeal O ^ n : Ideal O) : Set O) =
      {y : O | v (algebraMap O K y) ≤ v (algebraMap O K ϖ) ^ n} := by
  let : IsDomain O := hv.hom_inj.isDomain
  intro _ ϖ h n
  have : (v (algebraMap O K ϖ)) ^ n = v (algebraMap O K (ϖ ^ n)) := by simp
  rw [this, ← hv.coe_span_singleton_eq_setOfPred_le_v_algebraMap,
      ← Ideal.span_singleton_pow, ← h.maximalIdeal_eq]

@[deprecated (since := "2026-07-09")]
alias maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow :=
  maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow

end Valuation.Integers

section Valuation.integer

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation K Γ₀)

/-
**_root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe** 是 Mathlib 中的一个引理，位于命名空
间 ``。
形式化陈述：_root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe [IsDiscreteValuation
Ring v.integer] {ϖ : v.integer} (h : Irreducible ϖ) : (IsLocalRing.maximalIdeal 
v.integer : Set v.integer) = {y : v.integer | v y <= v ϖ}
参数：h : Irreducible ϖ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe
    [IsDiscreteValuationRing v.integer] {ϖ : v.integer} (h : Irreducible ϖ) :
    (IsLocalRing.maximalIdeal v.integer : Set v.integer) = {y : v.integer | v y ≤ v ϖ} :=
  (Valuation.integer.integers v).maximalIdeal_eq_setOfPred_le_v_algebraMap h

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_eq_setOf_le_v_coe :=
  _root_.Irreducible.maximalIdeal_eq_setOfPred_le_v_coe
/-
**_root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：_root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow [IsDiscreteV
aluationRing v.integer] {ϖ : v.integer} (h : Irreducible ϖ) (n : Nat) : ((IsLoca
lRing.maximalIdeal v.integer ^ n : Ideal v.integer) : Set v.integer) = {y : v.in
teger | v y <= v (ϖ : K) ^ n}
参数：h : Irreducible ϖ；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow
    [IsDiscreteValuationRing v.integer] {ϖ : v.integer} (h : Irreducible ϖ) (n : ℕ) :
    ((IsLocalRing.maximalIdeal v.integer ^ n : Ideal v.integer) : Set v.integer) =
      {y : v.integer | v y ≤ v (ϖ : K) ^ n} :=
  (Valuation.integer.integers v).maximalIdeal_pow_eq_setOfPred_le_v_algebraMap_pow h _

@[deprecated (since := "2026-07-09")]
alias _root_.Irreducible.maximalIdeal_pow_eq_setOf_le_v_coe_pow :=
  _root_.Irreducible.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow

end Valuation.integer

