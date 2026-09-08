/-
Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Norm.Defs

/-!
# Irreducibility of X ^ p - a

## Main result
- `X_pow_sub_C_irreducible_iff_of_prime`: For `p` prime, `X ^ p - C a` is irreducible iff `a` is not
  a `p`-power. This is not true for composite `n`. For example, `x^4+4=(x^2-2x+2)(x^2+2x+2)` but
  `-4` is not a 4th power.

-/

public section
universe u

variable {K : Type u} [Field K]

open Polynomial AdjoinRoot

section Splits

/-
**root_X_pow_sub_C_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：root_X_pow_sub_C_pow (n : Nat) (a : K) : (AdjoinRoot.root (X ^ n - C a)) ^
 n = AdjoinRoot.of _ a
参数：n : Nat；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `AdjoinRoot.eval₂_root`：eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) =
 0
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `Polynomial.eval₂_pow`：eval₂_pow (n : Nat) : (p ^ n).eval₂ f x = p.eval₂ 
f x ^ n
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
-/
lemma root_X_pow_sub_C_pow (n : ℕ) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ^ n = AdjoinRoot.of _ a := by
  rw [← sub_eq_zero, ← AdjoinRoot.eval₂_root, eval₂_sub, eval₂_C, eval₂_pow, eval₂_X]
/-
**root_X_pow_sub_C_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：root_X_pow_sub_C_ne_zero {n : Nat} (hn : 1 < n) (a : K) : (AdjoinRoot.root
 (X ^ n - C a)) != 0
参数：hn : 1 < n；a : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AdjoinRoot.mk_ne_zero_of_natDegree_lt`：mk_ne_zero_of_natDegree_lt (hf : 
Monic f) {g : R[X]} (h0 : g != 0) (hd : natDegree g < natDegree f) : mk f g != 0
· 使用定理 `Polynomial.monic_X_pow_sub_C`：monic_X_pow_sub_C {R : Type u} [Ring R] (a
 : R) {n : Nat} (h : n != 0) : (X ^ n - C a).Monic
· 使用定理 `Nat.ne_zero_of_lt`：∀ {b a : ℕ}, b < a → a ≠ 0
· 使用定理 `Polynomial.X_ne_zero`：X_ne_zero [Nontrivial R] : (X : R[X]) != 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_X_pow_sub_C`：natDegree_X_pow_sub_C {n : Nat} {r : R
} : (X ^ n - C r).natDegree = n
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
-/
lemma root_X_pow_sub_C_ne_zero {n : ℕ} (hn : 1 < n) (a : K) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 :=
  mk_ne_zero_of_natDegree_lt (monic_X_pow_sub_C _ (Nat.ne_zero_of_lt hn))
    X_ne_zero <| by rwa [natDegree_X_pow_sub_C, natDegree_X]
/-
**root_X_pow_sub_C_ne_zero'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：root_X_pow_sub_C_ne_zero' {n : Nat} {a : K} (hn : 0 < n) (ha : a != 0) : (
AdjoinRoot.root (X ^ n - C a)) != 0
参数：hn : 0 < n；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `AdjoinRoot.mk_ne_zero_of_natDegree_lt`：mk_ne_zero_of_natDegree_lt (hf : 
Monic f) {g : R[X]} (h0 : g != 0) (hd : natDegree g < natDegree f) : mk f g != 0
· 使用定理 `Polynomial.monic_X_sub_C`：monic_X_sub_C (x : R) : Monic (X - C x)
· 使用定理 `Polynomial.C_ne_zero`：C_ne_zero : C a != 0 ↔ a != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Polynomial.natDegree_sub_C`：natDegree_sub_C {a : R} : natDegree (p - C a
) = natDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `AdjoinRoot.mk_self`：mk_self : mk f f = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AdjoinRoot.mk_X`：mk_X : mk f X = root f
· 使用引理 `root_X_pow_sub_C_ne_zero`：root_X_pow_sub_C_ne_zero {n : Nat} (hn : 1 < n
) (a : K) : (AdjoinRoot.root (X ^ n - C a)) != 0
-/
lemma root_X_pow_sub_C_ne_zero' {n : ℕ} {a : K} (hn : 0 < n) (ha : a ≠ 0) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 := by
  obtain (rfl | hn) := (Nat.succ_le_iff.mpr hn).eq_or_lt
  · rw [pow_one]
    intro e
    refine mk_ne_zero_of_natDegree_lt (monic_X_sub_C a) (C_ne_zero.mpr ha) (by simp) ?_
    trans AdjoinRoot.mk (X - C a) (X - (X - C a))
    · rw [sub_sub_cancel]
    · rw [map_sub, mk_self, sub_zero, mk_X, e]
  · exact root_X_pow_sub_C_ne_zero hn a

end Splits

section Irreducible

/-
**ne_zero_of_irreducible_X_pow_sub_C** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_zero_of_irreducible_X_pow_sub_C {n : Nat} {a : K} (H : Irreducible (X ^
 n - C a)) : n != 0
参数：H : Irreducible (X ^ n - C a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.not_irreducible_C`：not_irreducible_C (x : R) : ¬Irreducible (
C x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
-/
lemma ne_zero_of_irreducible_X_pow_sub_C {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    n ≠ 0 := by
  rintro rfl
  rw [pow_zero, ← C.map_one, ← map_sub] at H
  exact not_irreducible_C _ H
/-
**ne_zero_of_irreducible_X_pow_sub_C'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ne_zero_of_irreducible_X_pow_sub_C' {n : Nat} (hn : n != 1) {a : K} (H : I
rreducible (X ^ n - C a)) : a != 0
参数：hn : n != 1；H : Irreducible (X ^ n - C a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `not_irreducible_pow`：not_irreducible_pow : forall {n : Nat}, n != 1 -> ¬
 Irreducible (x ^ n) | 0, _ => by simp | n + 2, _ => by intro ⟨h₁, h₂⟩ have
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma ne_zero_of_irreducible_X_pow_sub_C' {n : ℕ} (hn : n ≠ 1) {a : K}
    (H : Irreducible (X ^ n - C a)) : a ≠ 0 := by
  rintro rfl
  rw [map_zero, sub_zero] at H
  exact not_irreducible_pow hn H
/-
**root_X_pow_sub_C_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：root_X_pow_sub_C_eq_zero_iff {n : Nat} {a : K} (H : Irreducible (X ^ n - C
 a)) : (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a = 0
参数：H : Irreducible (X ^ n - C a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.pos_iff_ne_zero`：∀ {n : ℕ}, 0 < n ↔ n ≠ 0
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C`：ne_zero_of_irreducible_X_pow_sub_C {
n : Nat} {a : K} (H : Irreducible (X ^ n - C a)) : n != 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_imp_not`：not_imp_not : ¬a -> ¬b ↔ b -> a
· 使用引理 `root_X_pow_sub_C_ne_zero'`：root_X_pow_sub_C_ne_zero' {n : Nat} {a : K} (
hn : 0 < n) (ha : a != 0) : (AdjoinRoot.root (X ^ n - C a)) != 0
· 使用引理 `ne_zero_of_irreducible_X_pow_sub_C'`：ne_zero_of_irreducible_X_pow_sub_C'
 {n : Nat} (hn : n != 1) {a : K} (H : Irreducible (X ^ n - C a)) : a != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AdjoinRoot.mk_X`：mk_X : mk f X = root f
· 使用定理 `AdjoinRoot.mk_self`：mk_self : mk f f = 0
-/
lemma root_X_pow_sub_C_eq_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a = 0 := by
  have hn := Nat.pos_iff_ne_zero.mpr (ne_zero_of_irreducible_X_pow_sub_C H)
  refine ⟨not_imp_not.mp (root_X_pow_sub_C_ne_zero' hn), ?_⟩
  rintro rfl
  have := not_imp_not.mp (fun hn ↦ ne_zero_of_irreducible_X_pow_sub_C' hn H) rfl
  rw [this, pow_one, map_zero, sub_zero, ← mk_X, mk_self]
/-
**root_X_pow_sub_C_ne_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：root_X_pow_sub_C_ne_zero_iff {n : Nat} {a : K} (H : Irreducible (X ^ n - C
 a)) : (AdjoinRoot.root (X ^ n - C a)) != 0 ↔ a != 0
参数：H : Irreducible (X ^ n - C a)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `root_X_pow_sub_C_eq_zero_iff`：root_X_pow_sub_C_eq_zero_iff {n : Nat} {a 
: K} (H : Irreducible (X ^ n - C a)) : (AdjoinRoot.root (X ^ n - C a)) = 0 ↔ a =
 0
-/
lemma root_X_pow_sub_C_ne_zero_iff {n : ℕ} {a : K} (H : Irreducible (X ^ n - C a)) :
    (AdjoinRoot.root (X ^ n - C a)) ≠ 0 ↔ a ≠ 0 :=
  (root_X_pow_sub_C_eq_zero_iff H).not
/-
**pow_ne_of_irreducible_X_pow_sub_C** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_ne_of_irreducible_X_pow_sub_C {n : Nat} {a : K} (H : Irreducible (X ^ 
n - C a)) {m : Nat} (hm : m ∣ n) (hm' : m != 1) (b : K) : b ^ m != a
参数：H : Irreducible (X ^ n - C a)；hm : m ∣ n；hm' : m != 1；b : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.not_irreducible_C`：not_irreducible_C (x : R) : ¬Irreducible (
C x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用引理 `sub_dvd_pow_sub_pow`：sub_dvd_pow_sub_pow (x y : R) (n : Nat) : x - y ∣ x
 ^ n - y ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_ne_zero_iff`：mul_ne_zero_iff : a * b != 0 ↔ a != 0 ∧ b != 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Irreducible.isUnit_or_isUnit`：∀ {M : Type u_1} [inst : Monoid M] {p : M}
, Irreducible p → ∀ ⦃a b : M⦄, p = a * b → IsUnit a ∨ IsUnit b
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_eq_right₀`：mul_eq_right₀ [IsRightCancelMulZero M₀] (hb : b != 0) : a
 * b = b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 38 条，此处仅展示前 30 条）
-/
theorem pow_ne_of_irreducible_X_pow_sub_C {n : ℕ} {a : K}
    (H : Irreducible (X ^ n - C a)) {m : ℕ} (hm : m ∣ n) (hm' : m ≠ 1) (b : K) : b ^ m ≠ a := by
  have hn : n ≠ 0 := fun e ↦ not_irreducible_C
    (1 - a) (by simpa only [e, pow_zero, ← C.map_one, ← map_sub] using H)
  obtain ⟨k, rfl⟩ := hm
  rintro rfl
  obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow (X ^ k) (C b) m
  rw [mul_comm, pow_mul, map_pow, hq] at H
  have : degree q = 0 := by
    simpa [isUnit_iff_degree_eq_zero, degree_X_pow_sub_C,
      Nat.pos_iff_ne_zero, (mul_ne_zero_iff.mp hn).2] using H.2 rfl
  apply_fun degree at hq
  simp only [this, ← pow_mul, mul_comm k m, degree_X_pow_sub_C, Nat.pos_iff_ne_zero.mpr hn,
    Nat.pos_iff_ne_zero.mpr (mul_ne_zero_iff.mp hn).2, degree_mul, ← map_pow, add_zero,
    Nat.cast_injective.eq_iff] at hq
  exact hm' ((mul_eq_right₀ (mul_ne_zero_iff.mp hn).2).mp hq)

/-- Let `p` be a prime number. Let `K` be a field.
Let `t ∈ K` be an element which does not have a `p`th root in `K`.
Then the polynomial `x ^ p - t` is irreducible over `K`. -/
@[stacks 09HF "We proved the result without the condition that `K` is char p in 09HF."]
/-
**X_pow_sub_C_irreducible_of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_of_prime {p : Nat} (hp : p.Prime) {a : K} (ha : fo
rall b : K, b ^ p != a) : Irreducible (X ^ p - C a)
参数：hp : p.Prime；ha : forall b : K, b ^ p != a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.isUnit_iff_degree_eq_zero`：isUnit_iff_degree_eq_zero : IsUnit
 p ↔ degree p = 0
· 使用定理 `Polynomial.degree_X_pow_sub_C`：degree_X_pow_sub_C {n : Nat} (hn : 0 < n)
 (a : R) : degree ((X : R[X]) ^ n - C a) = n
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
· 使用定理 `WfDvdMonoid.exists_irreducible_factor`：exists_irreducible_factor {a : α}
 (ha : ¬IsUnit a) (ha0 : a != 0) : exists i, Irreducible i ∧ i ∣ a
· 使用定理 `UniqueFactorizationMonoid.toIsWellFounded`：∀ {α : Type u_2} {inst : Comm
MonoidWithZero α} [self : UniqueFactorizationMonoid α], IsWellFounded α DvdNotUn
it
· 使用定理 `Polynomial.uniqueFactorizationMonoid`：∀ {D : Type u} [inst : CommRing D]
 [UniqueFactorizationMonoid D], UniqueFactorizationMonoid (Polynomial D)
· 使用定理 `PrincipalIdealRing.to_uniqueFactorizationMonoid`：∀ {R : Type u} [inst : 
CommRing R] [IsDomain R] [IsPrincipalIdealRing R], UniqueFactorizationMonoid R
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Polynomial.X_pow_sub_C_ne_zero`：X_pow_sub_C_ne_zero {n : Nat} (hn : 0 < 
n) (a : R) : (X : R[X]) ^ n - C a != 0
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero`：eval₂_eq_zero_of_dvd_o
f_eval₂_eq_zero (h : p ∣ q) (h0 : eval₂ f x p = 0) : eval₂ f x q = 0
· 使用定理 `AdjoinRoot.eval₂_root`：eval₂_root (f : R[X]) : f.eval₂ (of f) (root f) =
 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Polynomial.eval₂_X`：eval₂_X : X.eval₂ f x = x
· 使用定理 `Polynomial.eval₂_C`：eval₂_C : (C a).eval₂ f x = f a
· 使用定理 `Polynomial.eval₂_pow`：eval₂_pow (n : Nat) : (p ^ n).eval₂ f x = p.eval₂ 
f x ^ n
· 使用定理 `Polynomial.eval₂_sub`：eval₂_sub {S} [Ring S] (f : R ->+* S) {x : S} : (p
 - q).eval₂ f x = p.eval₂ f x - q.eval₂ f x
· 使用定理 `AdjoinRoot.algebraMap_eq`：algebraMap_eq : algebraMap R (AdjoinRoot f) = 
of f
· 使用定理 `Algebra.norm_algebraMap`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRin
g R] [inst_1 : Ring S] [inst_2 : Algebra R S] [Module.Free R S] (x : R),   (Alge
bra.norm R) (…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `PowerBasis.finrank`：finrank [StrongRankCondition R] (pb : PowerBasis R S
) : Module.finrank R S = pb.dim
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Let `p` be a prime number. Let `K` be a field.
Let `t ∈ K` be an element which does not have a `p`th root in `K`.
Then the polynomial `x ^ p - t` is irreducible over `K`.
-/
theorem X_pow_sub_C_irreducible_of_prime {p : ℕ} (hp : p.Prime) {a : K} (ha : ∀ b : K, b ^ p ≠ a) :
    Irreducible (X ^ p - C a) := by
  -- First of all, We may find an irreducible factor `g` of `X ^ p - C a`.
  have : ¬ IsUnit (X ^ p - C a) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_X_pow_sub_C hp.pos, Nat.cast_eq_zero]
    exact hp.ne_zero
  have ⟨g, hg, hg'⟩ := WfDvdMonoid.exists_irreducible_factor this (X_pow_sub_C_ne_zero hp.pos a)
  -- It suffices to show that `deg g = p`.
  suffices natDegree g = p from (associated_of_dvd_of_natDegree_le hg'
    (X_pow_sub_C_ne_zero hp.pos a) (this.trans natDegree_X_pow_sub_C.symm).ge).irreducible hg
  -- Suppose `deg g ≠ p`.
  by_contra h
  -- Let `r` be a root of `g`, then `N_K(r) ^ p = N_K(r ^ p) = N_K(a) = a ^ (deg g)`.
  have key : (Algebra.norm K (AdjoinRoot.root g)) ^ p = a ^ g.natDegree := by
    have := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero _ _ hg' (AdjoinRoot.eval₂_root g)
    rw [eval₂_sub, eval₂_pow, eval₂_C, eval₂_X, sub_eq_zero] at this
    rw [← map_pow, this, ← AdjoinRoot.algebraMap_eq, Algebra.norm_algebraMap,
      (powerBasis hg.ne_zero).finrank, powerBasis_dim hg.ne_zero]
  -- Since `a ^ (deg g)` is a `p`-power, and `p` is coprime to `deg g`, we conclude that `a` is
  -- also a `p`-power, contradicting the hypothesis
  have : p.Coprime (natDegree g) := hp.coprime_iff_not_dvd.mpr (fun e ↦ h (((natDegree_le_of_dvd hg'
    (X_pow_sub_C_ne_zero hp.pos a)).trans_eq natDegree_X_pow_sub_C).antisymm (Nat.le_of_dvd
      (natDegree_pos_iff_degree_pos.mpr <| Polynomial.degree_pos_of_irreducible hg) e)))
  exact ha _ ((pow_mem_range_pow_of_coprime this.symm a).mp ⟨_, key⟩).choose_spec
/-
**X_pow_sub_C_irreducible_iff_of_prime** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：X_pow_sub_C_irreducible_iff_of_prime {p : Nat} (hp : p.Prime) {a : K} : Ir
reducible (X ^ p - C a) ↔ forall b, b ^ p != a
参数：hp : p.Prime。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_ne_of_irreducible_X_pow_sub_C`：pow_ne_of_irreducible_X_pow_sub_C {n 
: Nat} {a : K} (H : Irreducible (X ^ n - C a)) {m : Nat} (hm : m ∣ n) (hm' : m !
= 1) (b : K) : b ^ m !=…
· 使用定理 `dvd_rfl`：dvd_rfl : forall {a : α}, a ∣ a
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `X_pow_sub_C_irreducible_of_prime`：X_pow_sub_C_irreducible_of_prime {p : 
Nat} (hp : p.Prime) {a : K} (ha : forall b : K, b ^ p != a) : Irreducible (X ^ p
 - C a)
-/
theorem X_pow_sub_C_irreducible_iff_of_prime {p : ℕ} (hp : p.Prime) {a : K} :
    Irreducible (X ^ p - C a) ↔ ∀ b, b ^ p ≠ a :=
  ⟨(pow_ne_of_irreducible_X_pow_sub_C · dvd_rfl hp.ne_one), X_pow_sub_C_irreducible_of_prime hp⟩

end Irreducible

