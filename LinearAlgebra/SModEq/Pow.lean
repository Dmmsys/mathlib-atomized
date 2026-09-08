/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.LinearAlgebra.SModEq.Basic
public import Mathlib.RingTheory.Ideal.Operations

/-! # Lemmas about SModEq related to powers -/

public section

namespace SModEq
variable {R : Type*} [CommRing R] {I J : Ideal R} {p : ℕ} (hpI : (p : R) ∈ I)
include hpI

/-
**SModEq.pow_mul_of_le** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：pow_mul_of_le {x y : R} (h : x ≡ y [SMOD J]) (hJI : J <= I) : x ^ p ≡ y ^ 
p [SMOD J * I]
参数：h : x ≡ y [SMOD J]；hJI : J <= I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SModEq.idealQuotientMk`：idealQuotientMk {R : Type*} [CommRing R] {I : Id
eal R} {x y : R} : x ≡ y [SMOD I] ↔ Ideal.Quotient.mk I x = Ideal.Quotient.mk I 
y
· 使用定理 `SModEq.mono`：mono (HU : U₁ <= U₂) (hxy : x ≡ y [SMOD U₁]) : x ≡ y [SMOD 
U₂]
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SModEq.sub_mem`：sub_mem : x ≡ y [SMOD U] ↔ x - y in U
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Commute.mul_neg_geom_sum₂`：Commute.mul_neg_geom_sum₂ (h : Commute x y) (
n : Nat) : ((y - x) * ∑ i in range n, x ^ i * y ^ (n - 1 - i)) = y ^ n - x ^ n
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
（共 32 条，此处仅展示前 30 条）
-/
theorem pow_mul_of_le {x y : R} (h : x ≡ y [SMOD J]) (hJI : J ≤ I) :
    x ^ p ≡ y ^ p [SMOD J * I] := by
  have h₁ := idealQuotientMk.mp <| h.mono hJI
  rw [SModEq.sub_mem] at h ⊢
  rw [← Commute.mul_neg_geom_sum₂ (.all _ _)]
  refine Ideal.mul_mem_mul h ?_
  have h₂ : (p : R ⧸ I) = 0 := by simpa using Ideal.Quotient.eq_zero_iff_mem.mpr hpI
  simp only [← Ideal.Quotient.eq_zero_iff_mem, map_sum, map_mul, map_pow, h₁, ← pow_add]
  trans ∑ x ∈ Finset.range p, Ideal.Quotient.mk I y ^ (p - 1)
  · exact Finset.sum_congr rfl fun _ _ ↦ by grind
  simp [h₂]
/-
**SModEq.pow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：pow_add_one {x y : R} {m : Nat} (hm : m != 0) (h : x ≡ y [SMOD I ^ m]) : x
 ^ p ≡ y ^ p [SMOD I ^ (m + 1)]
参数：hm : m != 0；h : x ≡ y [SMOD I ^ m]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `SModEq.pow_mul_of_le`：pow_mul_of_le {x y : R} (h : x ≡ y [SMOD J]) (hJI 
: J <= I) : x ^ p ≡ y ^ p [SMOD J * I]
· 使用定理 `Ideal.pow_le_self`：pow_le_self {n : Nat} (hn : n != 0) : I ^ n <= I
-/
theorem pow_add_one {x y : R} {m : ℕ} (hm : m ≠ 0) (h : x ≡ y [SMOD I ^ m]) :
    x ^ p ≡ y ^ p [SMOD I ^ (m + 1)] := h.pow_mul_of_le hpI <| I.pow_le_self hm
/-
**SModEq.pow_pow_add_one** 是 Mathlib 中的一个定理，位于命名空间 `SModEq`。
形式化陈述：pow_pow_add_one {x y : R} (h : x ≡ y [SMOD I]) (m : Nat) : x ^ p ^ m ≡ y ^
 p ^ m [SMOD I ^ (m + 1)]
参数：h : x ≡ y [SMOD I]；m : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `SModEq.pow_add_one`：pow_add_one {x y : R} {m : Nat} (hm : m != 0) (h : x
 ≡ y [SMOD I ^ m]) : x ^ p ≡ y ^ p [SMOD I ^ (m + 1)]
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
-/
theorem pow_pow_add_one {x y : R} (h : x ≡ y [SMOD I]) (m : ℕ) :
    x ^ p ^ m ≡ y ^ p ^ m [SMOD I ^ (m + 1)] := by
  induction m with
  | zero => simpa
  | succ m ih =>
    simp_rw [pow_succ _ m, pow_mul]
    exact ih.pow_add_one hpI m.succ_ne_zero

end SModEq

