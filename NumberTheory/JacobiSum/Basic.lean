/-
Copyright (c) 2024 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.GaussSum
public import Mathlib.NumberTheory.MulChar.Lemmas
public import Mathlib.RingTheory.RootsOfUnity.Lemmas

/-!
# Jacobi Sums

This file defines the *Jacobi sum* of two multiplicative characters `χ` and `ψ` on a finite
commutative ring `R` with values in another commutative ring `R'`:

`jacobiSum χ ψ = ∑ x : R, χ x * ψ (1 - x)`

(see `jacobiSum`) and provides some basic results and API lemmas on Jacobi sums.

## References

We essentially follow
* [K. Ireland, M. Rosen, *A classical introduction to modern number theory*
  (Section 8.3)][IrelandRosen1990]

but generalize where appropriate.

This is based on Lean code written as part of the bachelor's thesis of Alexander Spahl.
-/

@[expose] public section

open Finset

/-!
### Jacobi sums: definition and first properties
-/

section Def

-- need `Fintype` instead of `Finite` to make `jacobiSum` computable.
variable {R R' : Type*} [CommRing R] [Fintype R] [CommRing R']

/-- The *Jacobi sum* of two multiplicative characters on a finite commutative ring. -/
/-
**jacobiSum** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：jacobiSum (χ ψ : MulChar R R') : R'
参数：χ ψ : MulChar R R'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *Jacobi sum* of two multiplicative characters on a finite commutative ring.
-/
def jacobiSum (χ ψ : MulChar R R') : R' :=
  ∑ x : R, χ x * ψ (1 - x)
/-
**jacobiSum_comm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ
参数：χ ψ : MulChar R R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.subLeft_apply`：∀ {G : Type u_5} [inst : AddGroup G] (a b : G), (Eq
uiv.subLeft a) b = a - b
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma jacobiSum_comm (χ ψ : MulChar R R') : jacobiSum χ ψ = jacobiSum ψ χ := by
  simp only [jacobiSum, mul_comm (χ _)]
  rw [← (Equiv.subLeft 1).sum_comp]
  simp only [Equiv.subLeft_apply, sub_sub_cancel]

/-- The Jacobi sum is compatible with ring homomorphisms. -/
/-
**jacobiSum_ringHomComp** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f
 : R' ->+* R'') : jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ
 ψ)
参数：χ ψ : MulChar R R'；f : R' ->+* R''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The Jacobi sum is compatible with ring homomorphisms.
-/
lemma jacobiSum_ringHomComp {R'' : Type*} [CommRing R''] (χ ψ : MulChar R R') (f : R' →+* R'') :
    jacobiSum (χ.ringHomComp f) (ψ.ringHomComp f) = f (jacobiSum χ ψ) := by
  simp only [jacobiSum, MulChar.ringHomComp, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum, map_mul]

end Def

/-!
### Jacobi sums over finite fields
-/

section CommRing

variable {F R : Type*} [CommRing F] [Nontrivial F] [Fintype F] [DecidableEq F] [CommRing R]

/-- The Jacobi sum of two multiplicative characters on a nontrivial finite commutative ring `F`
can be written as a sum over `F \ {0,1}`. -/
/-
**jacobiSum_eq_sum_sdiff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) : jacobiSum χ ψ = ∑ x in univ \
 {0,1}, χ x * ψ (1 - x)
参数：χ ψ : MulChar F R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Finset.sum_sdiff_eq_sub`：∀ {ι : Type u_1} {G : Type u_3} {s₁ s₂ : Finset
 ι} [inst : AddCommGroup G] [inst_1 : DecidableEq ι] {f : ι → G},   s₁ ⊆ s₂ → ∑ 
x ∈ s₂ \ s₁, …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
The Jacobi sum of two multiplicative characters on a nontrivial finite commutati
ve ring `F`
can be written as a sum over `F \ {0,1}`.
-/
lemma jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x ∈ univ \ {0,1}, χ x * ψ (1 - x) := by
  simp only [jacobiSum, subset_univ, sum_sdiff_eq_sub, sub_eq_add_neg, left_eq_add,
    neg_eq_zero]
  apply sum_eq_zero
  simp only [mem_insert, mem_singleton, forall_eq_or_imp, χ.map_zero, neg_zero, add_zero, map_one,
    mul_one, forall_eq, add_neg_cancel, ψ.map_zero, mul_zero, and_self]
/-
**jacobiSum_eq_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma jacobiSum_eq_aux (χ ψ : MulChar F R) :
    jacobiSum χ ψ = ∑ x : F, χ x + ∑ x : F, ψ x - Fintype.card F +
                      ∑ x ∈ univ \ {0, 1}, (χ x - 1) * (ψ (1 - x) - 1) := by
  rw [jacobiSum]
  conv =>
    enter [1, 2, x]
    rw [show ∀ x y : R, x * y = x + y - 1 + (x - 1) * (y - 1) by intros; ring]
  rw [sum_add_distrib, sum_sub_distrib, sum_add_distrib]
  conv => enter [1, 1, 1, 2, 2, x]; rw [← Equiv.subLeft_apply 1]
  rw [(Equiv.subLeft 1).sum_comp ψ, Fintype.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one,
    sum_sdiff_eq_sub (subset_univ _), ← sub_zero (_ - _ + _), add_sub_assoc]
  congr
  rw [sum_pair zero_ne_one, sub_zero, ψ.map_one, χ.map_one, sub_self, mul_zero, zero_mul, add_zero]

end CommRing

section FiniteField

variable {F R : Type*} [Field F] [Fintype F] [CommRing R]

/-- The Jacobi sum of twice the trivial multiplicative character on a finite field `F`
equals `#F-2`. -/
/-
**jacobiSum_trivial_trivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：jacobiSum_trivial_trivial : jacobiSum (MulChar.trivial F R) (MulChar.trivi
al F R) = Fintype.card F - 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `jacobiSum_eq_sum_sdiff`：jacobiSum_eq_sum_sdiff (χ ψ : MulChar F R) : jac
obiSum χ ψ = ∑ x in univ \ {0,1}, χ x * ψ (1 - x)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `MulChar.trivial_apply`：∀ (R : Type u_1) [inst : CommMonoid R] (R' : Type
 u_2) [inst_1 : CommMonoidWithZero R'] (x : R),   (MulChar.trivial R R') x = if 
IsUnit x th…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.cast_card`：Finset.cast_card [NonAssocSemiring R] (s : Finset α) :
 (#s : R) = ∑ _ in s, 1
· 使用定理 `Finset.card_sdiff_of_subset`：card_sdiff_of_subset (h : s subseteq t) : #
(t \ s) = #t - #s
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.card_univ`：Finset.card_univ [Fintype α] : #(univ : Finset α) = Fi
ntype.card α
· 使用定理 `Finset.card_pair`：∀ {α : Type u_1} {a b : α} [inst : DecidableEq α], a ≠
 b → {a, b}.card = 2
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Nat.add_one_le_of_lt`：∀ {n m : ℕ}, n < m → n + 1 ≤ m
· 使用定理 `Fintype.one_lt_card`：one_lt_card [h : Nontrivial α] : 1 < Fintype.card α
· 使用定理 `Nat.cast_two`：cast_two [NatCast R] : ((2 : Nat) : R) = (2 : R)

--- 原说明 ---
The Jacobi sum of twice the trivial multiplicative character on a finite field `
F`
equals `#F-2`.
-/
theorem jacobiSum_trivial_trivial :
    jacobiSum (MulChar.trivial F R) (MulChar.trivial F R) = Fintype.card F - 2 := by
  classical
  rw [jacobiSum_eq_sum_sdiff]
  have : ∀ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x) = 1 := by
    intro x hx
    rw [← map_mul, MulChar.trivial_apply, if_pos]
    simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, not_or, ← ne_eq, true_and] at hx
    simpa only [isUnit_iff_ne_zero, mul_ne_zero_iff, ne_eq, sub_eq_zero, @eq_comm _ _ x] using hx
  calc ∑ x ∈ univ \ {0, 1}, (MulChar.trivial F R) x * (MulChar.trivial F R) (1 - x)
  _ = ∑ _ ∈ univ \ {0, 1}, 1 := sum_congr rfl this
  _ = #(univ \ {0, 1}) := (cast_card _).symm
  _ = Fintype.card F - 2 := by
    rw [card_sdiff_of_subset (subset_univ _), card_univ, card_pair zero_ne_one,
      Nat.cast_sub <| Nat.add_one_le_of_lt Fintype.one_lt_card, Nat.cast_two]

/-- If `1` is the trivial multiplicative character on a finite field `F`, then `J(1,1) = #F-2`. -/
/-
**jacobiSum_one_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `jacobiSum_trivial_trivial`：jacobiSum_trivial_trivial : jacobiSum (MulCha
r.trivial F R) (MulChar.trivial F R) = Fintype.card F - 2

--- 原说明 ---
If `1` is the trivial multiplicative character on a finite field `F`, then `J(1,
1) = #F-2`.
-/
theorem jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = Fintype.card F - 2 :=
  jacobiSum_trivial_trivial

variable [IsDomain R] -- needed for `MulChar.sum_eq_zero_of_ne_one`

/-- If `χ` is a nontrivial multiplicative character on a finite field `F`, then `J(1,χ) = -1`. -/
/-
**jacobiSum_one_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：jacobiSum_one_nontrivial {χ : MulChar F R} (hχ : χ != 1) : jacobiSum 1 χ =
 -1
参数：hχ : χ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `MulChar.one_apply`：one_apply {x : R} (hx : IsUnit x) : (1 : MulChar R R'
) x = 1
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `_private.Mathlib.NumberTheory.JacobiSum.Basic.0.jacobiSum_eq_aux`：∀ {F :
 Type u_1} {R : Type u_2} [inst : CommRing F] [Nontrivial F] [inst_2 : Fintype F
] [inst_3 : DecidableEq F]   [inst_4 : CommRing R] (χ …
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `MulChar.sum_one_eq_card_units`：sum_one_eq_card_units [DecidableEq R] : (
∑ a, (1 : MulChar R R') a) = Fintype.card Rˣ
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Fintype.card_eq_card_units_add_one`：Fintype.card_eq_card_units_add_one [
GroupWithZero α] [Fintype α] [DecidableEq α] : Fintype.card α = Fintype.card αˣ 
+ 1
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `sub_add_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a - (a + b) = -b

--- 原说明 ---
If `χ` is a nontrivial multiplicative character on a finite field `F`, then `J(1
,χ) = -1`.
-/
theorem jacobiSum_one_nontrivial {χ : MulChar F R} (hχ : χ ≠ 1) : jacobiSum 1 χ = -1 := by
  classical
  have : ∑ x ∈ univ \ {0, 1}, ((1 : MulChar F R) x - 1) * (χ (1 - x) - 1) = 0 := by
    apply Finset.sum_eq_zero
    simp +contextual only [mem_sdiff, mem_univ, mem_insert, mem_singleton,
      not_or, ← isUnit_iff_ne_zero, true_and, MulChar.one_apply, sub_self, zero_mul,
      implies_true]
  simp only [jacobiSum_eq_aux, MulChar.sum_one_eq_card_units, MulChar.sum_eq_zero_of_ne_one hχ,
    add_zero, Fintype.card_eq_card_units_add_one (α := F), Nat.cast_add, Nat.cast_one,
    sub_add_cancel_left, this]

/-- If `χ` is a nontrivial multiplicative character on a finite field `F`,
then `J(χ,χ⁻¹) = -χ(-1)`. -/
/-
**jacobiSum_nontrivial_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：jacobiSum_nontrivial_inv {χ : MulChar F R} (hχ : χ != 1) : jacobiSum χ χ⁻¹
 = -χ (-1)
参数：hχ : χ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `jacobiSum.eq_1`：∀ {R : Type u_1} {R' : Type u_2} [inst : CommRing R] [in
st_1 : Fintype R] [inst_2 : CommRing R'] (χ ψ : MulChar R R'),   jacobiSum χ ψ =
 ∑ x…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulChar.inv_apply'`：inv_apply' {R : Type*} [CommGroupWithZero R] (χ : Mu
lChar R R') (a : R) : χ⁻¹ a = χ a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Finset.sum_eq_sum_sdiff_singleton_add`：∀ {ι : Type u_1} {M : Type u_3} [
inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s
 → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `MulChar.map_zero`：∀ {R' : Type u_2} [inst : CommMonoidWithZero R'] {R : 
Type u_3} [inst_1 : CommMonoidWithZero R] [Nontrivial R]   (χ : MulChar R R'), χ
 0 = 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.sum_bij'`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : 
AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} (i : (a
 : ι)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
If `χ` is a nontrivial multiplicative character on a finite field `F`,
then `J(χ,χ⁻¹) = -χ(-1)`.
-/
theorem jacobiSum_nontrivial_inv {χ : MulChar F R} (hχ : χ ≠ 1) : jacobiSum χ χ⁻¹ = -χ (-1) := by
  classical
  rw [jacobiSum]
  conv => enter [1, 2, x]; rw [MulChar.inv_apply', ← map_mul, ← div_eq_mul_inv]
  rw [sum_eq_sum_sdiff_singleton_add (mem_univ (1 : F)), sub_self, div_zero, χ.map_zero, add_zero]
  have : ∑ x ∈ univ \ {1}, χ (x / (1 - x)) = ∑ x ∈ univ \ {-1}, χ x := by
    refine sum_bij' (fun a _ ↦ a / (1 - a)) (fun b _ ↦ b / (1 + b)) (fun x hx ↦ ?_)
      (fun y hy ↦ ?_) (fun x hx ↦ ?_) (fun y hy ↦ ?_) (fun _ _ ↦ rfl)
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx ⊢
      rw [div_eq_iff <| sub_ne_zero.mpr ((ne_eq ..).symm ▸ hx).symm, mul_sub, mul_one,
        neg_one_mul, sub_neg_eq_add, right_eq_add, neg_eq_zero]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy ⊢
      rw [div_eq_iff fun h ↦ hy <| eq_neg_of_add_eq_zero_right h, one_mul, right_eq_add]
      exact one_ne_zero
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hx
      rw [eq_comm, ← sub_eq_zero] at hx
      simp [field]
    · simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at hy
      rw [eq_comm, neg_eq_iff_eq_neg, ← sub_eq_zero, sub_neg_eq_add] at hy
      simp [field]
  rw [this, ← add_eq_zero_iff_eq_neg, ← sum_eq_sum_sdiff_singleton_add (mem_univ (-1 : F))]
  exact MulChar.sum_eq_zero_of_ne_one hχ

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` such that
`χφ` is nontrivial, then `g(χφ) * J(χ,φ) = g(χ) * g(φ)`. -/
/-
**jacobiSum_mul_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：jacobiSum_mul_nontrivial {χ φ : MulChar F R} (h : χ * φ != 1) (ψ : AddChar
 F R) : gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ
参数：h : χ * φ != 1；ψ : AddChar F R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `gaussSum_mul`：gaussSum_mul {R : Type u} [CommRing R] [Fintype R] {R' : T
ype v} [CommRing R'] (χ φ : MulChar R R') (ψ : AddChar R R') : gaussSum χ ψ * ga
us…
· 使用定理 `Finset.sum_eq_sum_sdiff_singleton_add`：∀ {ι : Type u_1} {M : Type u_3} [
inst : AddCommMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s
 → ∀ (f : ι → M), ∑ x ∈ s, …
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_eq_neg_one_mul`：neg_eq_neg_one_mul (a : α) : -a = -1 * a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulCharClass.toMonoidHomClass`：∀ {F : Type u_3} {R : outParam (Type u_4)
} {R' : outParam (Type u_5)} {inst : CommMonoid R}   {inst_1 : CommMonoidWithZer
o R'} {inst_2 : Fun…
· 使用定理 `MulChar.instMulCharClass`：∀ {R : Type u_1} [inst : CommMonoid R] {R' : T
ype u_2} [inst_1 : CommMonoidWithZero R'],   MulCharClass (MulChar R R') R R'
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulChar.mul_apply`：mul_apply (χ χ' : MulChar R R') (a : R) : (χ * χ') a 
= χ a * χ' a
· 使用定理 `AddChar.map_zero_eq_one`：∀ {A : Type u_1} {M : Type u_3} [inst : AddMono
id A] [inst_1 : Monoid M] (ψ : AddChar A M), ψ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `MulChar.sum_eq_zero_of_ne_one`：sum_eq_zero_of_ne_one [IsDomain R'] {χ : 
MulChar R R'} (hχ : χ != 1) : ∑ a, χ a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `jacobiSum.eq_1`：∀ {R : Type u_1} {R' : Type u_2} [inst : CommRing R] [in
st_1 : Fintype R] [inst_2 : CommRing R'] (χ ψ : MulChar R R'),   jacobiSum χ ψ =
 ∑ x…
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
If `χ` and `φ` are multiplicative characters on a finite field `F` such that
`χφ` is nontrivial, then `g(χφ) * J(χ,φ) = g(χ) * g(φ)`.
-/
theorem jacobiSum_mul_nontrivial {χ φ : MulChar F R} (h : χ * φ ≠ 1) (ψ : AddChar F R) :
    gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ := by
  classical
  rw [gaussSum_mul _ _ ψ, sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F))]
  conv =>
    enter [2, 2, 2, x]
    rw [zero_sub, neg_eq_neg_one_mul x, map_mul, mul_left_comm (χ x) (φ (-1)),
      ← MulChar.mul_apply, ψ.map_zero_eq_one, mul_one]
  rw [← mul_sum _ _ (φ (-1)), MulChar.sum_eq_zero_of_ne_one h, mul_zero, add_zero]
  have sum_eq : ∀ t ∈ univ \ {0}, (∑ x : F, χ x * φ (t - x)) * ψ t =
      (∑ y : F, χ (t * y) * φ (t - (t * y))) * ψ t := by
    intro t ht
    simp only [mem_sdiff, mem_univ, mem_singleton, true_and] at ht
    exact congrArg (· * ψ t) (Equiv.sum_comp (Equiv.mulLeft₀ t ht) _).symm
  simp_rw [← sum_mul, sum_congr rfl sum_eq, ← mul_one_sub, map_mul, mul_assoc]
  conv => enter [2, 2, t, 1, 2, x, 2]; rw [← mul_assoc, mul_comm (χ x) (φ t)]
  simp_rw [← mul_assoc, ← MulChar.mul_apply, mul_assoc, ← mul_sum, mul_right_comm]
  rw [← jacobiSum, ← sum_mul, gaussSum, sum_eq_sum_sdiff_singleton_add (mem_univ (0 : F)),
    (χ * φ).map_zero, zero_mul, add_zero]

end FiniteField

section field_field

variable {F F' : Type*} [Fintype F] [Field F] [Field F']

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` with values
in another field `F'` and such that `χφ` is nontrivial, then `J(χ,φ) = g(χ) * g(φ) / g(χφ)`. -/
/-
**jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (h : (Fintype.card F : F')
 != 0) {χ φ : MulChar F F'} (hχφ : χ * φ != 1) {ψ : AddChar F F'} (hψ : ψ.IsPrim
itive) : jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ
参数：h : (Fintype.card F : F') != 0；hχφ : χ * φ != 1；hψ : ψ.IsPrimitive。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用引理 `gaussSum_ne_zero_of_nontrivial`：gaussSum_ne_zero_of_nontrivial (h : (Fin
type.card R : R') != 0) {χ : MulChar R R'} (hχ : χ != 1) {ψ : AddChar R R'} (hψ 
: ψ.IsPrimitive) : g…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `jacobiSum_mul_nontrivial`：jacobiSum_mul_nontrivial {χ φ : MulChar F R} (
h : χ * φ != 1) (ψ : AddChar F R) : gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSu
m χ ψ * gaussS…

--- 原说明 ---
If `χ` and `φ` are multiplicative characters on a finite field `F` with values
in another field `F'` and such that `χφ` is nontrivial, then `J(χ,φ) = g(χ) * g(
φ) / g(χφ)`.
-/
theorem jacobiSum_eq_gaussSum_mul_gaussSum_div_gaussSum (h : (Fintype.card F : F') ≠ 0)
    {χ φ : MulChar F F'} (hχφ : χ * φ ≠ 1) {ψ : AddChar F F'} (hψ : ψ.IsPrimitive) :
    jacobiSum χ φ = gaussSum χ ψ * gaussSum φ ψ / gaussSum (χ * φ) ψ := by
  rw [eq_div_iff <| gaussSum_ne_zero_of_nontrivial h hχφ hψ, mul_comm]
  exact jacobiSum_mul_nontrivial hχφ ψ

open AddChar MulChar in
/-- If `χ` and `φ` are multiplicative characters on a finite field `F` with values in another
field `F'` such that `χ`, `φ` and `χφ` are all nontrivial and `char F' ≠ char F`, then
`J(χ,φ) * J(χ⁻¹,φ⁻¹) = #F` (in `F'`). -/
/-
**jacobiSum_mul_jacobiSum_inv** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：jacobiSum_mul_jacobiSum_inv (h : ringChar F' != ringChar F) {χ φ : MulChar
 F F'} (hχ : χ != 1) (hφ : φ != 1) (hχφ : χ * φ != 1) : jacobiSum χ φ * jacobiSu
m χ⁻¹ φ⁻¹ = Fintype.card F
参数：h : ringChar F' != ringChar F；hχ : χ != 1；hφ : φ != 1；hχφ : χ * φ != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiniteField.card`：card (p : Nat) [CharP K p] : exists n : Nat+, Nat.Prim
e p ∧ q = p ^ (n : Nat)
· 使用定理 `ringChar.charP`：∀ (R : Type u_1) [inst : NonAssocSemiring R], CharP R (r
ingChar R)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `jacobiSum_ringHomComp`：jacobiSum_ringHomComp {R'' : Type*} [CommRing R''
] (χ ψ : MulChar R R') (f : R' ->+* R'') : jacobiSum (χ.ringHomComp f) (ψ.ringHo
mComp f) = …
· 使用引理 `MulChar.ringHomComp_mul`：ringHomComp_mul (χ φ : MulChar R R') (f : R' ->
+* R'') : (χ * φ).ringHomComp f = χ.ringHomComp f * φ.ringHomComp f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `MulChar.ringHomComp_ne_one_iff`：ringHomComp_ne_one_iff {f : R' ->+* R''}
 (hf : Function.Injective f) {χ : MulChar R R'} : χ.ringHomComp f != 1 ↔ χ != 1
· 使用定理 `mul_inv`：mul_inv : (a * b)⁻¹ = a⁻¹ * b⁻¹
· 使用定理 `inv_ne_one`：inv_ne_one : a⁻¹ != 1 ↔ a != 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Algebra.ringChar_eq`：Algebra.ringChar_eq : ringChar K = ringChar L
· 使用引理 `CharP.ringChar_of_prime_eq_zero`：ringChar_of_prime_eq_zero [Nontrivial R
] {p : Nat} (hprime : Nat.Prime p) (hp0 : (p : R) = 0) : ringChar R = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `gaussSum_mul_gaussSum_eq_card`：gaussSum_mul_gaussSum_eq_card {χ : MulCha
r R R'} (hχ : χ != 1) {ψ : AddChar R R'} (hψ : IsPrimitive ψ) : gaussSum χ ψ * g
aussSum χ⁻¹ ψ⁻¹ = F…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
If `χ` and `φ` are multiplicative characters on a finite field `F` with values i
n another
field `F'` such that `χ`, `φ` and `χφ` are all nontrivial and `char F' ≠ char F`
, then
`J(χ,φ) * J(χ⁻¹,φ⁻¹) = #F` (in `F'`).
-/
lemma jacobiSum_mul_jacobiSum_inv (h : ringChar F' ≠ ringChar F) {χ φ : MulChar F F'} (hχ : χ ≠ 1)
    (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    jacobiSum χ φ * jacobiSum χ⁻¹ φ⁻¹ = Fintype.card F := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- Obtain primitive additive character `ψ : F → FF'`.
  let ψ := FiniteField.primitiveChar F F' h
  -- the target field of `ψ`
  let FF' := CyclotomicField ψ.n F'
  -- Consider `χ` and `φ` as characters `F → FF'`.
  let χ' := χ.ringHomComp (algebraMap F' FF')
  let φ' := φ.ringHomComp (algebraMap F' FF')
  have hinj := (algebraMap F' FF').injective
  apply hinj
  rw [map_mul, ← jacobiSum_ringHomComp, ← jacobiSum_ringHomComp]
  have Hχφ : χ' * φ' ≠ 1 := by
    rw [← ringHomComp_mul]
    exact (MulChar.ringHomComp_ne_one_iff hinj).mpr hχφ
  have Hχφ' : χ'⁻¹ * φ'⁻¹ ≠ 1 := by
    rwa [← mul_inv, inv_ne_one]
  have Hχ : χ' ≠ 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hχ
  have Hφ : φ' ≠ 1 := (MulChar.ringHomComp_ne_one_iff hinj).mpr hφ
  have Hcard : (Fintype.card F : FF') ≠ 0 := by
    intro H
    simp only [hc, Nat.cast_pow, ne_eq, PNat.ne_zero, not_false_eq_true, pow_eq_zero_iff] at H
    exact h <| (Algebra.ringChar_eq F' FF').trans <| CharP.ringChar_of_prime_eq_zero hp H
  have H := (gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim).trans_ne Hcard
  apply_fun (gaussSum (χ' * φ') ψ.char * gaussSum (χ' * φ')⁻¹ ψ.char⁻¹ * ·)
    using mul_right_injective₀ H
  simp only
  rw [mul_mul_mul_comm, jacobiSum_mul_nontrivial Hχφ, mul_inv, ← ringHomComp_inv,
    ← ringHomComp_inv, jacobiSum_mul_nontrivial Hχφ', map_natCast, ← mul_mul_mul_comm,
    gaussSum_mul_gaussSum_eq_card Hχ ψ.prim, gaussSum_mul_gaussSum_eq_card Hφ ψ.prim,
    ← mul_inv, gaussSum_mul_gaussSum_eq_card Hχφ ψ.prim]

end field_field

section image

variable {F R : Type*} [Field F] [CommRing R] [IsDomain R]

open Algebra

section finite

variable [Finite F]

private
/-
**MulChar.exists_apply_sub_one_eq_mul_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulChar.exists_apply_sub_one_eq_mul_sub_one {n : Nat} [NeZero n] {χ : MulC
har F R} {μ : R} (hχ : χ ^ n = 1) (hμ : IsPrimitiveRoot μ n) {x : F} (hx : x != 
0) : exists z in Int[μ], χ x - 1 = z * (μ - 1)
参数：hχ : χ ^ n = 1；hμ : IsPrimitiveRoot μ n；hx : x != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulChar.exists_apply_sub_one_eq_mul_sub_one {n : ℕ} [NeZero n] {χ : MulChar F R} {μ : R}
    (hχ : χ ^ n = 1) (hμ : IsPrimitiveRoot μ n) {x : F} (hx : x ≠ 0) :
    ∃ z ∈ ℤ[μ], χ x - 1 = z * (μ - 1) := by
  obtain ⟨k, _, hk⟩ := exists_apply_eq_pow hχ hμ hx
  refine hk ▸ ⟨(Finset.range k).sum (μ ^ ·), ?_, (geom_sum_mul μ k).symm⟩
  exact Subalgebra.sum_mem _ fun m _ ↦ Subalgebra.pow_mem _ (self_mem_adjoin_singleton _ μ) _

private
/-
**MulChar.exists_apply_sub_one_mul_apply_sub_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MulChar.exists_apply_sub_one_mul_apply_sub_one {n : Nat} [NeZero n] {χ ψ :
 MulChar F R} {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hμ : IsPrimitiveRoot μ 
n) (x : F) : exists z in Int[μ], (χ x - 1) * (ψ (1 - x) - 1) = z * (μ - 1) ^ 2
参数：hχ : χ ^ n = 1；hψ : ψ ^ n = 1；hμ : IsPrimitiveRoot μ n；x : F。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulChar.exists_apply_sub_one_mul_apply_sub_one {n : ℕ} [NeZero n] {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hμ : IsPrimitiveRoot μ n) (x : F) :
    ∃ z ∈ ℤ[μ], (χ x - 1) * (ψ (1 - x) - 1) = z * (μ - 1) ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx₀
  · exact ⟨0, Subalgebra.zero_mem _, by rw [sub_zero, ψ.map_one, sub_self, mul_zero, zero_mul]⟩
  rcases eq_or_ne x 1 with rfl | hx₁
  · exact ⟨0, Subalgebra.zero_mem _, by rw [χ.map_one, sub_self, zero_mul, zero_mul]⟩
  obtain ⟨z₁, hz₁, Hz₁⟩ := MulChar.exists_apply_sub_one_eq_mul_sub_one hχ hμ hx₀
  obtain ⟨z₂, hz₂, Hz₂⟩ :=
    MulChar.exists_apply_sub_one_eq_mul_sub_one hψ hμ (sub_ne_zero_of_ne hx₁.symm)
  rewrite [Hz₁, Hz₂, sq]
  exact ⟨z₁ * z₂, Subalgebra.mul_mem _ hz₁ hz₂, mul_mul_mul_comm ..⟩

end finite

variable [Fintype F]

/-- If `χ` and `φ` are multiplicative characters on a finite field `F` satisfying `χ^n = φ^n = 1`
and with values in an integral domain `R`, and `μ` is a primitive `n`th root of unity in `R`,
then the Jacobi sum `J(χ,φ)` is in `ℤ[μ] ⊆ R`. -/
/-
**jacobiSum_mem_algebraAdjoin_of_pow_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：jacobiSum_mem_algebraAdjoin_of_pow_eq_one {n : Nat} [NeZero n] {χ φ : MulC
har F R} (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) : 
jacobiSum χ φ in Int[μ]
参数：hχ : χ ^ n = 1；hφ : φ ^ n = 1；hμ : IsPrimitiveRoot μ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.sum_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {ι : Type w}
 {t : Fi…
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用引理 `MulChar.apply_mem_algebraAdjoin_of_pow_eq_one`：apply_mem_algebraAdjoin_o
f_pow_eq_one {χ : MulChar F R} {n : Nat} [NeZero n] (hχ : χ ^ n = 1) {μ : R} (hμ
 : IsPrimitiveRoot μ n) (a : F) : χ…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `χ` and `φ` are multiplicative characters on a finite field `F` satisfying `χ
^n = φ^n = 1`
and with values in an integral domain `R`, and `μ` is a primitive `n`th root of 
unity in `R`,
then the Jacobi sum `J(χ,φ)` is in `ℤ[μ] ⊆ R`.
-/
lemma jacobiSum_mem_algebraAdjoin_of_pow_eq_one {n : ℕ} [NeZero n] {χ φ : MulChar F R}
    (hχ : χ ^ n = 1) (hφ : φ ^ n = 1) {μ : R} (hμ : IsPrimitiveRoot μ n) :
    jacobiSum χ φ ∈ ℤ[μ] :=
  Subalgebra.sum_mem _ fun _ _ ↦ Subalgebra.mul_mem _
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hχ hμ _)
    (MulChar.apply_mem_algebraAdjoin_of_pow_eq_one hφ hμ _)

/-- If `χ` and `ψ` are multiplicative characters of order dividing `n` on a finite field `F`
with values in an integral domain `R` and `μ` is a primitive `n`th root of unity in `R`,
then `J(χ,ψ) = -1 + z*(μ - 1)^2` for some `z ∈ ℤ[μ] ⊆ R`. (We assume that `#F ≡ 1 mod n`.)
Note that we do not state this as a divisibility in `R`, as this would give a weaker statement. -/
/-
**exists_jacobiSum_eq_neg_one_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_jacobiSum_eq_neg_one_add {n : Nat} (hn : 2 < n) {χ ψ : MulChar F R}
 {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hn' : n ∣ Fintype.card F - 1) (hμ : 
IsPrimitiveRoot μ n) : exists z in Int[μ], jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2
参数：hn : 2 < n；hχ : χ ^ n = 1；hψ : ψ ^ n = 1；hn' : n ∣ Fintype.card F - 1；hμ : Is
PrimitiveRoot μ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsPrimitiveRoot.self_sub_one_pow_dvd_order`：self_sub_one_pow_dvd_order {
k n : Nat} (hn : k < n) {μ : R} (hμ : IsPrimitiveRoot μ n) : exists z in Int[μ],
 n = z * (μ - 1) ^ k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `jacobiSum_one_one`：jacobiSum_one_one : jacobiSum (1 : MulChar F R) 1 = F
intype.card F - 2
· 使用定理 `Subalgebra.mul_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x y : A}, x
 ∈ S → y…
· 使用定理 `Subalgebra.natCast_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring
 R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   (n : ℕ),
 ↑n ∈ S
· 使用定理 `Nat.sub_eq_iff_eq_add`：∀ {b a c : ℕ}, b ≤ a → (a - b = c ↔ a = c + b)
· 使用定理 `NeZero.one_le`：one_le {n : Nat} [NeZero n] : 1 <= n
· 使用定理 `Fintype.instNeZeroNatCardOfNonempty`：∀ {α : Type u_1} [inst : Fintype α]
 [Nonempty α], NeZero (Fintype.card α)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
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
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
If `χ` and `ψ` are multiplicative characters of order dividing `n` on a finite f
ield `F`
with values in an integral domain `R` and `μ` is a primitive `n`th root of unity
 in `R`,
then `J(χ,ψ) = -1 + z*(μ - 1)^2` for some `z ∈ ℤ[μ] ⊆ R`. (We assume that `#F ≡ 
1 mod n`.)
Note that we do not state this as a divisibility in `R`, as this would give a we
aker statement.
-/
lemma exists_jacobiSum_eq_neg_one_add {n : ℕ} (hn : 2 < n) {χ ψ : MulChar F R}
    {μ : R} (hχ : χ ^ n = 1) (hψ : ψ ^ n = 1) (hn' : n ∣ Fintype.card F - 1)
    (hμ : IsPrimitiveRoot μ n) :
    ∃ z ∈ ℤ[μ], jacobiSum χ ψ = -1 + z * (μ - 1) ^ 2 := by
  obtain ⟨q, hq⟩ := hn'
  rw [Nat.sub_eq_iff_eq_add NeZero.one_le] at hq
  obtain ⟨z₁, hz₁, Hz₁⟩ := hμ.self_sub_one_pow_dvd_order hn
  by_cases hχ₀ : χ = 1 <;> by_cases hψ₀ : ψ = 1
  · rw [hχ₀, hψ₀, jacobiSum_one_one]
    refine ⟨q * z₁, Subalgebra.mul_mem _ (Subalgebra.natCast_mem _ q) hz₁, ?_⟩
    rw [hq, Nat.cast_add, Nat.cast_mul, Hz₁]
    ring
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [hχ₀, jacobiSum_one_nontrivial hψ₀, zero_mul, add_zero]
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [jacobiSum_comm, hψ₀, jacobiSum_one_nontrivial hχ₀, zero_mul, add_zero]
  · classical
    rw [jacobiSum_eq_aux, MulChar.sum_eq_zero_of_ne_one hχ₀, MulChar.sum_eq_zero_of_ne_one hψ₀, hq]
    have : NeZero n := ⟨by lia⟩
    have H := MulChar.exists_apply_sub_one_mul_apply_sub_one hχ hψ hμ
    have Hcs x := (H x).choose_spec
    refine ⟨-q * z₁ + ∑ x ∈ (univ \ {0, 1} : Finset F), (H x).choose, ?_, ?_⟩
    · refine Subalgebra.add_mem _ (Subalgebra.mul_mem _ (Subalgebra.neg_mem _ ?_) hz₁) ?_
      · exact Subalgebra.natCast_mem ..
      · exact Subalgebra.sum_mem _ fun x _ ↦ (Hcs x).1
    · conv => enter [1, 2, 2, x]; rw [(Hcs x).2]
      rw [← Finset.sum_mul, Nat.cast_add, Nat.cast_mul, Hz₁]
      ring

end image

section GaussSum

variable {F R : Type*} [Fintype F] [Field F] [CommRing R] [IsDomain R]

/-
**gaussSum_pow_eq_prod_jacobiSum_aux** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：gaussSum_pow_eq_prod_jacobiSum_aux (χ : MulChar F R) (ψ : AddChar F R) {n 
: Nat} (hn₁ : 0 < n) (hn₂ : n < orderOf χ) : gaussSum χ ψ ^ n = gaussSum (χ ^ n)
 ψ * ∏ j in Ico 1 n, jacobiSum χ (χ ^ j)
参数：χ : MulChar F R；ψ : AddChar F R；hn₁ : 0 < n；hn₂ : n < orderOf χ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.Ico_eq_empty_of_le`：Ico_eq_empty_of_le (h : b <= a) : Ico a b = ∅
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_ne_one_of_lt_orderOf`：pow_ne_one_of_lt_orderOf (n0 : n != 0) (h : n 
< orderOf x) : x ^ n != 1
· 使用定理 `Nat.add_one_ne_zero`：∀ (n : ℕ), n + 1 ≠ 0
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `jacobiSum_mul_nontrivial`：jacobiSum_mul_nontrivial {χ φ : MulChar F R} (
h : χ * φ != 1) (ψ : AddChar F R) : gaussSum (χ * φ) ψ * jacobiSum χ φ = gaussSu
m χ ψ * gaussS…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `Nat.lt_succ_self`：∀ (n : ℕ), n < n.succ
· 使用定理 `Finset.prod_Ico_succ_top`：prod_Ico_succ_top {a b : Nat} (hab : a <= b) (
f : Nat -> M) : (∏ k in Ico a (b + 1), f k) = (∏ k in Ico a b, f k) * f b
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
lemma gaussSum_pow_eq_prod_jacobiSum_aux (χ : MulChar F R) (ψ : AddChar F R) {n : ℕ}
    (hn₁ : 0 < n) (hn₂ : n < orderOf χ) :
    gaussSum χ ψ ^ n = gaussSum (χ ^ n) ψ * ∏ j ∈ Ico 1 n, jacobiSum χ (χ ^ j) := by
  induction n, hn₁ using Nat.le_induction with
  | base => simp only [pow_one, le_refl, Ico_eq_empty_of_le, prod_empty, mul_one]
  | succ n hn ih =>
      specialize ih <| lt_trans (Nat.lt_succ_self n) hn₂
      have gauss_rw : gaussSum (χ ^ n) ψ * gaussSum χ ψ =
            jacobiSum χ (χ ^ n) * gaussSum (χ ^ (n + 1)) ψ := by
        have hχn : χ * (χ ^ n) ≠ 1 :=
          pow_succ' χ n ▸ pow_ne_one_of_lt_orderOf n.add_one_ne_zero hn₂
        rw [mul_comm, ← jacobiSum_mul_nontrivial hχn, mul_comm, ← pow_succ']
      apply_fun (· * gaussSum χ ψ) at ih
      rw [mul_right_comm, ← pow_succ, gauss_rw] at ih
      rw [ih, Finset.prod_Ico_succ_top hn, mul_rotate, mul_assoc]

/-- If `χ` is a multiplicative character of order `n ≥ 2` on a finite field `F`,
then `g(χ)^n = χ(-1) * #F * J(χ,χ) * J(χ,χ²) * ... * J(χ,χⁿ⁻²)`. -/
/-
**gaussSum_pow_eq_prod_jacobiSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaussSum_pow_eq_prod_jacobiSum {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2
 <= orderOf χ) (hψ : ψ.IsPrimitive) : gaussSum χ ψ ^ orderOf χ = χ (-1) * Fintyp
e.card F * ∏ i in Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i)
参数：hχ : 2 <= orderOf χ；hψ : ψ.IsPrimitive。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `gaussSum_pow_eq_prod_jacobiSum_aux`：gaussSum_pow_eq_prod_jacobiSum_aux (
χ : MulChar F R) (ψ : AddChar F R) {n : Nat} (hn₁ : 0 < n) (hn₂ : n < orderOf χ)
 : gaussSum χ ψ ^ n = ga…
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `orderOf_one`：orderOf_one : orderOf (1 : G) = 1
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.sub_one_add_one_eq_of_pos`：∀ {n : ℕ}, 0 < n → n - 1 + 1 = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `gaussSum_mul_gaussSum_pow_orderOf_sub_one`：gaussSum_mul_gaussSum_pow_ord
erOf_sub_one {χ : MulChar R R'} {ψ : AddChar R R'} (hχ : χ != 1) (hψ : ψ.IsPrimi
tive) : gaussSum χ ψ * gaussSum…

--- 原说明 ---
If `χ` is a multiplicative character of order `n ≥ 2` on a finite field `F`,
then `g(χ)^n = χ(-1) * #F * J(χ,χ) * J(χ,χ²) * ... * J(χ,χⁿ⁻²)`.
-/
theorem gaussSum_pow_eq_prod_jacobiSum {χ : MulChar F R} {ψ : AddChar F R} (hχ : 2 ≤ orderOf χ)
    (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ ^ orderOf χ =
      χ (-1) * Fintype.card F * ∏ i ∈ Ico 1 (orderOf χ - 1), jacobiSum χ (χ ^ i) := by
  have := gaussSum_pow_eq_prod_jacobiSum_aux χ ψ (n := orderOf χ - 1) (by lia) (by lia)
  apply_fun (gaussSum χ ψ * ·) at this
  rw [← pow_succ', Nat.sub_one_add_one_eq_of_pos (by lia)] at this
  have hχ₁ : χ ≠ 1 :=
    fun h ↦ ((orderOf_one (G := MulChar F R) ▸ h ▸ hχ).trans_lt Nat.one_lt_two).false
  rw [this, ← mul_assoc, gaussSum_mul_gaussSum_pow_orderOf_sub_one hχ₁ hψ]

end GaussSum

