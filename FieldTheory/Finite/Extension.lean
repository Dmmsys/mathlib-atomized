/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Kevin Buzzard
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Extensions of finite fields

In this file we develop the theory of extensions of finite fields.

If `k` is a finite field (of cardinality `q = p ^ m`), then there is a unique (up to in general
non-unique isomorphism) extension `l` of `k` of any given degree `n > 0`.

This extension is Galois with cyclic Galois group of degree `n`, and the (arithmetic) Frobenius map
`x ↦ x ^ q` is a generator.


## Main definition

* `FiniteField.Extension k p n` is a non-canonically chosen extension of `k` of degree `n`
  (for `n > 0`).

## Main Results

* `FiniteField.algEquivExtension`: any other field extension `l/k` of degree `n` is (non-uniquely)
  isomorphic to our chosen `FiniteField.Extension k p n`.

-/

@[expose] public section

noncomputable section

variable (k : Type*) [Field k] [Finite k]
variable (p : ℕ) [Fact p.Prime] [CharP k p]
variable (n : ℕ) [NeZero n]

open Polynomial

namespace FiniteField

/-- Given a finite field `k` of characteristic `p`, we have a non-canonically chosen extension
of any given degree `n > 0`. -/
/-
**FiniteField.Extension** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField`。
形式化陈述：Extension : Type
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite field `k` of characteristic `p`, we have a non-canonically chosen
 extension
of any given degree `n > 0`.
-/
def Extension : Type :=
  letI := ZMod.algebra k p
  GaloisField p (Module.finrank (ZMod p) k * n)
  deriving Field, Finite, Algebra (ZMod p), FiniteDimensional (ZMod p)
/-
**FiniteField.finrank_zmod_extension** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：finrank_zmod_extension [Algebra (ZMod p) k] : Module.finrank (ZMod p) (Ext
ension k p n) = Module.finrank (ZMod p) k * n
参数：ZMod p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `ZMod.instSubsingletonAlgebra`：∀ (R : Type u_1) [inst : Ring R] (p : ℕ), 
Subsingleton (Algebra (ZMod p) R)
· 使用定理 `GaloisField.finrank`：finrank {n} (h : n != 0) : Module.finrank (ZMod p) 
(GaloisField p n) = n
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `NeZero.ne`：∀ {R : Type u_1} [inst : Zero R] (n : R) [h : NeZero n], n ≠ 
0
-/
theorem finrank_zmod_extension [Algebra (ZMod p) k] :
    Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k * n := by
  let := ZMod.algebra k p
  unfold Extension
  convert!
    GaloisField.finrank p (n := Module.finrank (ZMod p) k * n) <|
      mul_ne_zero Module.finrank_pos.ne' <| NeZero.ne n
  subsingleton
/-
**FiniteField.nonempty_algHom_extension** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：nonempty_algHom_extension [Algebra (ZMod p) k] : Nonempty (k ->ₐ[ZMod p] E
xtension k p n)
参数：ZMod p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.nonempty_algHom_of_finrank_dvd`：nonempty_algHom_of_finrank_d
vd (h : Module.finrank F K ∣ Module.finrank F L) : Nonempty (K ->ₐ[F] L)
· 使用定理 `FiniteField.instFiniteExtension`：∀ (k : Type u_1) [inst : Field k] (p : 
ℕ) [inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP k p] (n : ℕ),   Finite (FiniteF
ield.Extension k p n)
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.finrank_zmod_extension`：finrank_zmod_extension [Algebra (ZMo
d p) k] : Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k 
* n
-/
theorem nonempty_algHom_extension [Algebra (ZMod p) k] :
    Nonempty (k →ₐ[ZMod p] Extension k p n) :=
  nonempty_algHom_of_finrank_dvd (finrank_zmod_extension k p n ▸ dvd_mul_right _ _)
/-
**FiniteField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : Algebra k (Extension k p n) :=
  letI := ZMod.algebra k p
  (nonempty_algHom_extension k p n).some.toAlgebra
/-
**FiniteField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Finite k (Extension k p n) :=
  .of_finite
/-
**FiniteField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Algebra (ZMod p) k] : IsScalarTower (ZMod p) k (Extension k p n) :=
  -- there is at most one map from `𝔽_p` to any ring
  .of_algebraMap_eq' <| Subsingleton.elim _ _
/-
**FiniteField.natCard_extension** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `FiniteField.pow_finrank_eq_natCard`：pow_finrank_eq_natCard (p : Nat) [Fa
ct p.Prime] (k : Type*) [AddCommGroup k] [Finite k] [Module (ZMod p) k] : p ^ Mo
dule.finrank (ZMod p) k …
· 使用定理 `FiniteField.instFiniteExtension`：∀ (k : Type u_1) [inst : Field k] (p : 
ℕ) [inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP k p] (n : ℕ),   Finite (FiniteF
ield.Extension k p n)
· 使用定理 `FiniteField.finrank_zmod_extension`：finrank_zmod_extension [Algebra (ZMo
d p) k] : Module.finrank (ZMod p) (Extension k p n) = Module.finrank (ZMod p) k 
* n
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
-/
theorem natCard_extension : Nat.card (Extension k p n) = Nat.card k ^ n := by
  let := ZMod.algebra k p
  rw [← pow_finrank_eq_natCard p, ← pow_finrank_eq_natCard p, finrank_zmod_extension, pow_mul]
/-
**FiniteField.finrank_extension** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：finrank_extension : Module.finrank k (Extension k p n) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.pow_right_injective`：∀ {a : ℕ}, 2 ≤ a → Function.Injective fun x => 
a ^ x
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.instFiniteExtension_1`：∀ (k : Type u_1) [inst : Field k] [in
st_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] [inst_3 : CharP k p] (n :
 ℕ)   [inst_4 : NeZero …
· 使用定理 `FiniteField.natCard_extension`：natCard_extension : Nat.card (Extension k
 p n) = Nat.card k ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_extension : Module.finrank k (Extension k p n) = n := by
  refine Nat.pow_right_injective (Finite.one_lt_card : 2 ≤ Nat.card k) ?_
  simp only [← Module.natCard_eq_pow_finrank, natCard_extension]
/-
**FiniteField.** 是 Mathlib 中的一个实例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSplittingField k (Extension k p n) (X ^ Nat.card k ^ n - X) := by
  have := Fintype.ofFinite (Extension k p n)
  convert! FiniteField.isSplittingField_sub (Extension k p n) k
  · rw [Fintype.card_eq_nat_card, natCard_extension]
/-
**FiniteField.** 是 Mathlib 中的一个示例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsGalois k (Extension k p n) :=
  inferInstance
/-
**FiniteField.** 是 Mathlib 中的一个示例，位于命名空间 `FiniteField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : IsCyclic Gal(Extension k p n / k) :=
  inferInstance
/-
**FiniteField.natCard_algEquiv_extension** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`
。
形式化陈述：natCard_algEquiv_extension : Nat.card Gal(Extension k p n / k) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsGalois.card_aut_eq_finrank`：card_aut_eq_finrank [FiniteDimensional F E
] [IsGalois F E] : Nat.card Gal(E/F) = finrank F E
· 使用定理 `FiniteField.instFiniteExtension_1`：∀ (k : Type u_1) [inst : Field k] [in
st_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] [inst_3 : CharP k p] (n :
 ℕ)   [inst_4 : NeZero …
· 使用定理 `GaloisField.instIsGaloisOfFinite`：∀ {K : Type u_2} {K' : Type u_3} [inst
 : Field K] [inst_1 : Field K'] [Finite K'] [inst_3 : Algebra K K'], IsGalois K 
K'
· 使用定理 `FiniteField.instFiniteExtension`：∀ (k : Type u_1) [inst : Field k] (p : 
ℕ) [inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP k p] (n : ℕ),   Finite (FiniteF
ield.Extension k p n)
· 使用定理 `FiniteField.finrank_extension`：finrank_extension : Module.finrank k (Ext
ension k p n) = n
-/
theorem natCard_algEquiv_extension : Nat.card Gal(Extension k p n / k) = n :=
  (IsGalois.card_aut_eq_finrank _ _).trans <| finrank_extension k p n
/-
**FiniteField.card_algEquiv_extension** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`。
形式化陈述：card_algEquiv_extension : Fintype.card Gal(Extension k p n / k) = n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FiniteField.instFiniteExtension_1`：∀ (k : Type u_1) [inst : Field k] [in
st_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] [inst_3 : CharP k p] (n :
 ℕ)   [inst_4 : NeZero …
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `FiniteField.natCard_algEquiv_extension`：natCard_algEquiv_extension : Nat
.card Gal(Extension k p n / k) = n
-/
theorem card_algEquiv_extension : Fintype.card Gal(Extension k p n / k) = n :=
  Fintype.card_eq_nat_card.trans <| natCard_algEquiv_extension k p n

/-- The Frobenius automorphism `x ↦ x ^ Nat.card k` that fixes `k`. -/
/-
**FiniteField.Extension.frob** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField.Extension`。
形式化陈述：(k : Type u_1) →   [inst : Field k] →     [inst_1 : Finite k] →       (p :
 ℕ) →         [inst_2 : Fact (Nat.Prime p)] →           [inst_3 : CharP k p] → (
n : ℕ) → [inst_4 : NeZero n] → Gal(FiniteField.Extension k p n/k)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Frobenius automorphism `x ↦ x ^ Nat.card k` that fixes `k`.
-/
noncomputable def Extension.frob :
    Gal(Extension k p n / k) :=
  haveI := Fintype.ofFinite k
  FiniteField.frobeniusAlgEquivOfAlgebraic _ _
/-
**FiniteField.Extension.frob_apply** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField.Extens
ion`。
形式化陈述：∀ (k : Type u_1) [inst : Field k] [inst_1 : Finite k] (p : ℕ) [inst_2 : Fa
ct (Nat.Prime p)] [inst_3 : CharP k p] (n : ℕ)   [inst_4 : NeZero n] {x : Finite
Field.Extension k p n}, (FiniteField.Extension.frob k p n) x = x ^ Nat.card k
参数：k : Type u_1；p : ℕ；Nat.Prime p；n : ℕ；FiniteField.Extension.frob k p n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.frobeniusAlgEquivOfAlgebraic_apply`：∀ (K : Type u_1) [inst :
 Field K] [inst_1 : Fintype K] (L : Type u_3) [inst_2 : Field L] [inst_3 : Algeb
ra K L]   [inst_4 : Algebra.IsAlgebr…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma Extension.frob_apply {x : Extension k p n} :
    frob k p n x = x ^ Nat.card k := by
  simp [frob, ← Nat.card_eq_fintype_card]

@[simp]
/-
**FiniteField.Extension.frob_iterate_apply** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFiel
d.Extension`。
形式化陈述：∀ (k : Type u_1) [inst : Field k] [inst_1 : Finite k] (p : ℕ) [inst_2 : Fa
ct (Nat.Prime p)] [inst_3 : CharP k p] (n : ℕ)   [inst_4 : NeZero n] (i : ℕ) {x 
: FiniteField.Extension k p n},   (FiniteField.Extension.frob k p n ^ i) x = x ^
 Nat.card k ^ i
参数：k : Type u_1；p : ℕ；Nat.Prime p；n : ℕ；i : ℕ；FiniteField.Extension.frob k p n ^
 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `AlgEquiv.mul_apply`：mul_apply (e₁ e₂ : A₁ ≃ₐ[R] A₁) (x : A₁) : (e₁ * e₂)
 x = e₁ (e₂ x)
· 使用定理 `FiniteField.Extension.frob_apply`：∀ (k : Type u_1) [inst : Field k] [ins
t_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] [inst_3 : CharP k p] (n : 
ℕ)   [inst_4 : NeZero …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `Nat.pow_add_one'`：∀ {m n : ℕ}, m ^ (n + 1) = m * m ^ n
-/
theorem Extension.frob_iterate_apply (i : ℕ) {x : Extension k p n} :
    (frob k p n ^ i) x = x ^ (Nat.card k ^ i) := by
  induction i generalizing x with
  | zero => simp
  | succ i ih =>
      rw [pow_add, pow_one, AlgEquiv.mul_apply, ih, frob_apply, ← pow_mul, ← Nat.pow_add_one']
/-
**FiniteField.Extension.exists_frob_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `FiniteFiel
d.Extension`。
形式化陈述：∀ (k : Type u_1) [inst : Field k] [inst_1 : Finite k] (p : ℕ) [inst_2 : Fa
ct (Nat.Prime p)] [inst_3 : CharP k p] (n : ℕ)   [inst_4 : NeZero n] (g : Gal(Fi
niteField.Extension k p n/k)), ∃ i < n, FiniteField.Extension.frob k p n ^ i = g
参数：k : Type u_1；p : ℕ；Nat.Prime p；n : ℕ；g : Gal(FiniteField.Extension k p n/k)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `FiniteField.instFiniteExtension`：∀ (k : Type u_1) [inst : Field k] (p : 
ℕ) [inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP k p] (n : ℕ),   Finite (FiniteF
ield.Extension k p n)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow`：bijective_froben
iusAlgEquivOfAlgebraic_pow : Function.Bijective fun n : Fin (Module.finrank K L)
 => frobeniusAlgEquivOfAlgebraic K L ^ n.1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.finrank_extension`：finrank_extension : Module.finrank k (Ext
ension k p n) = n
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgEquiv.coe_pow`：∀ {R : Type uR} {A₁ : Type uA₁} [inst : CommSemiring R
] [inst_1 : Semiring A₁] [inst_2 : Algebra R A₁] (e : A₁ ≃ₐ[R] A₁)   (n : ℕ), ⇑(
e ^ n)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Extension.exists_frob_pow_eq (g : Gal(Extension k p n/k)) :
    ∃ i < n, Extension.frob k p n ^ i = g := by
  let := Fintype.ofFinite k
  obtain ⟨⟨i, hi⟩, rfl⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k
    (Extension k p n)).2 g
  refine ⟨i, ?_, by ext; simp [frob]⟩
  rwa [finrank_extension] at hi

/-- Given any field extension of finite fields `l/k` of degree `n`, we have a non-unique
isomorphism between `l` and our chosen `Extension k p n`. -/
/-
**FiniteField.algEquivExtension** 是 Mathlib 中的一个定义，位于命名空间 `FiniteField`。
形式化陈述：algEquivExtension (l : Type*) [Field l] [Algebra k l] (h : Module.finrank 
k l = n) : l ≃ₐ[k] Extension k p n
参数：l : Type*；h : Module.finrank k l = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given any field extension of finite fields `l/k` of degree `n`, we have a non-un
ique
isomorphism between `l` and our chosen `Extension k p n`.
-/
noncomputable def algEquivExtension (l : Type*) [Field l] [Algebra k l]
    (h : Module.finrank k l = n) : l ≃ₐ[k] Extension k p n := by
  refine Nonempty.some ?_
  have : Module.Finite k l := Module.finite_of_finrank_pos <| h ▸ NeZero.pos n
  have : Finite l := Module.finite_of_finite k
  have : Fintype l := .ofFinite _
  have : IsSplittingField k l (X ^ Nat.card k ^ n - X) := by
    rw [← h, ← Module.natCard_eq_pow_finrank, ← Fintype.card_eq_nat_card]
    exact FiniteField.isSplittingField_sub l k
  refine ⟨(IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).trans ?_⟩
  exact (IsSplittingField.algEquiv _ (X ^ (Nat.card k ^ n) - X)).symm

include p in
/-
**FiniteField.exists_forall_apply_eq_pow** 是 Mathlib 中的一个定理，位于命名空间 `FiniteField`
。
形式化陈述：exists_forall_apply_eq_pow (l : Type*) [Field l] [Algebra k l] [Finite l] 
(g : Gal(l/k)) : exists i, forall x, g x = x ^ (Nat.card k ^ i)
参数：l : Type*；g : Gal(l/k)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `FiniteField.Extension.exists_frob_pow_eq`：∀ (k : Type u_1) [inst : Field
 k] [inst_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] [inst_3 : CharP k 
p] (n : ℕ)   [inst_4 : NeZero …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgEquiv.symm_apply_apply`：symm_apply_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e.symm (e x) = x
· 使用定理 `FiniteField.Extension.frob_iterate_apply`：∀ (k : Type u_1) [inst : Field
 k] [inst_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.Prime p)] [inst_3 : CharP k 
p] (n : ℕ)   [inst_4 : NeZero …
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.congr_arg`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `AlgEquiv.congr_fun`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
theorem exists_forall_apply_eq_pow (l : Type*) [Field l] [Algebra k l] [Finite l] (g : Gal(l/k)) :
    ∃ i, ∀ x, g x = x ^ (Nat.card k ^ i) := by
  let n := Module.finrank k l
  have : NeZero n := NeZero.of_pos Module.finrank_pos
  obtain ⟨i, _, hi⟩ := Extension.exists_frob_pow_eq k p n <|
    (algEquivExtension k p n l rfl).symm.trans (g.trans (algEquivExtension k p n l rfl))
  refine ⟨i, fun x ↦ ?_⟩
  simpa using (AlgEquiv.congr_arg (f := (algEquivExtension k p n l rfl).symm) <|
    AlgEquiv.congr_fun hi (algEquivExtension k p n l rfl x)).symm

end FiniteField

namespace Irreducible

open FiniteField

variable {k}
variable {f : k[X]} (hi : Irreducible f)
include hi

omit [Finite k] in -- Junk for `Nat.card` allows us to omit the finiteness assumption here.
/-
**Irreducible.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X** 是 Mathlib 中的一个定理，位于命名空
间 `Irreducible`。
形式化陈述：natDegree_dvd_of_dvd_X_pow_card_pow_sub_X {n : Nat} (h : f ∣ X ^ (Nat.card
 k) ^ n - X) : f.natDegree ∣ n
参数：h : f ∣ X ^ (Nat.card k) ^ n - X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `CharP.char_is_prime`：char_is_prime (p : Nat) [CharP R p] : p.Prime
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiniteField.finrank_extension`：finrank_extension : Module.finrank k (Ext
ension k p n) = n
· 使用定理 `Polynomial.Irreducible.natDegree_dvd_finrank`：∀ {K : Type u} [inst : Fie
ld K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {f : Polynomial K
},   Irreducible f → (Polynomial.m…
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `Polynomial.IsSplittingField.splits`：splits (f : K[X]) [IsSplittingField 
K L f] : Splits (f.map (algebraMap K L))
· 使用定理 `FiniteField.instIsSplittingFieldExtensionHSubPolynomialHPowNatXCard`：∀ (
k : Type u_1) [inst : Field k] [inst_1 : Finite k] (p : ℕ) [inst_2 : Fact (Nat.P
rime p)] [inst_3 : CharP k p] (n : ℕ)   [inst_4 : NeZero …
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `FiniteField.X_pow_card_pow_sub_X_ne_zero`：X_pow_card_pow_sub_X_ne_zero (
hn : n != 0) (hp : 1 < p) : (X ^ p ^ n - X : K'[X]) != 0
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `Polynomial.map_dvd`：map_dvd (f : R ->+* S) {x y : R[X]} : x ∣ y -> x.map
 f ∣ y.map f
· 使用定理 `Polynomial.Splits.natDegree_eq_one_of_irreducible`：∀ {R : Type u_1} [ins
t : Field R] {f : Polynomial R}, f.Splits → Irreducible f → f.natDegree = 1
· 使用定理 `Polynomial.Splits.X_sub_C`：∀ {R : Type u_1} [inst : Ring R] (a : R), (Po
lynomial.X - Polynomial.C a).Splits
· 使用定理 `Polynomial.X_sub_C_ne_zero`：X_sub_C_ne_zero (r : R) : X - C r != 0
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `one_dvd`：one_dvd (a : α) : 1 ∣ a
-/
theorem natDegree_dvd_of_dvd_X_pow_card_pow_sub_X {n : ℕ} (h : f ∣ X ^ (Nat.card k) ^ n - X) :
    f.natDegree ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  cases finite_or_infinite k; swap
  · rw [Nat.card_eq_zero_of_infinite, zero_pow hn, pow_zero, ← dvd_neg, neg_sub] at h
    rw [((Splits.X_sub_C 1).of_dvd (X_sub_C_ne_zero 1) h).natDegree_eq_one_of_irreducible hi]
    exact one_dvd n
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  have : NeZero n := ⟨hn⟩
  rw [← finrank_extension k p n]
  apply Irreducible.natDegree_dvd_finrank hi
  refine Splits.of_dvd ?_ ?_ (map_dvd (algebraMap _ (Extension _ p n)) h)
  · apply IsSplittingField.splits
  · exact map_ne_zero (X_pow_card_pow_sub_X_ne_zero _ hn Finite.one_lt_card)
/-
**Irreducible.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X** 是 Mathlib 中的一个定理，位于命名
空间 `Irreducible`。
形式化陈述：natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X {n : Nat} : f.natDegree ∣ n ↔ f
 ∣ X ^ (Nat.card k) ^ n - X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dvd_trans`：dvd_trans : a ∣ b -> b ∣ c -> a ∣ c | ⟨d, h₁⟩, ⟨e, h₂⟩ => ⟨d 
* e, h₁ ▸ h₂.trans mul_assoc a d e⟩  alias Dvd.dvd.trans
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `Irreducible.natDegree_pos`：natDegree_pos (h : Irreducible f) : 0 < f.nat
Degree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Irreducible.dvd_iff_aeval_eq_zero`：∀ {A : Type u_1} {B : Type u_2} [inst
 : Field A] [inst_1 : Ring B] [inst_2 : Algebra A B] [Nontrivial B]   {p q : Pol
ynomial A}, Irreducible…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AdjoinRoot.aeval_eq`：aeval_eq (p : R[X]) : aeval (root f) p = mk f p
· 使用定理 `AdjoinRoot.mk_self`：mk_self : mk f f = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CharP.exists`：∀ (R : Type u_1) [inst : NonAssocSemiring R], ∃ p, CharP R
 p
· 使用定理 `CharP.char_is_prime`：char_is_prime (p : Nat) [CharP R p] : p.Prime
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `finrank_quotient_span_eq_natDegree`：∀ {K : Type u_5} [inst : Field K] {f
 : Polynomial K}, Module.finrank K (Polynomial K ⧸ Ideal.span {f}) = f.natDegree
· 使用定理 `FiniteField.instFiniteExtension`：∀ (k : Type u_1) [inst : Field k] (p : 
ℕ) [inst_1 : Fact (Nat.Prime p)] [inst_2 : CharP k p] (n : ℕ),   Finite (FiniteF
ield.Extension k p n)
· 使用定理 `FiniteField.natCard_extension`：natCard_extension : Nat.card (Extension k
 p n) = Nat.card k ^ n
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `FiniteField.pow_card`：pow_card (a : K) : a ^ q = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
（共 43 条，此处仅展示前 30 条）
-/
theorem natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X {n : ℕ} :
    f.natDegree ∣ n ↔ f ∣ X ^ (Nat.card k) ^ n - X := by
  refine ⟨fun hdvd ↦ dvd_trans ?_ (dvd_pow_pow_sub_self_of_dvd hdvd),
    hi.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X⟩
  let a := AdjoinRoot.root f
  have : NeZero f.natDegree := NeZero.of_pos (Irreducible.natDegree_pos hi)
  have : Fact <| Irreducible f := ⟨hi⟩
  rw [← hi.dvd_iff_aeval_eq_zero (b := a) (by aesop)]
  let ⟨p, hp⟩ := CharP.exists k
  have : Fact (Nat.Prime p) := ⟨CharP.char_is_prime k p⟩
  let e := FiniteField.algEquivExtension k p f.natDegree (AdjoinRoot f)
    (finrank_quotient_span_eq_natDegree (f := f))
  have hpeval : (e a) ^ (Nat.card k) ^ f.natDegree - (e a) = 0 := by
    have := Fintype.ofFinite (Extension k p f.natDegree)
    rw [← (natCard_extension k p f.natDegree), ← Fintype.card_eq_nat_card,
      pow_card (e a), sub_self]
  apply_fun e.symm at hpeval
  simpa using hpeval

end Irreducible

