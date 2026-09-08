/-
Copyright (c) 2025 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Algebra.Polynomial.Monic

/-!
# Monic polynomials of given degree

This file defines the predicate `Polynomial.IsMonicOfDegree p n` that states that
the polynomial `p` is monic and has degree `n` (i.e., `p.natDegree = n`.)

We also provide some basic API.
-/

public section

namespace Polynomial

variable {R : Type*}

section Semiring

variable [Semiring R]

/-- This says that `p` has `natDegree` `n` and is monic. -/
@[mk_iff isMonicOfDegree_iff']
/-
**Polynomial.IsMonicOfDegree** 是 Mathlib 中的一个归纳类型，位于命名空间 `Polynomial`。
形式化陈述：{R : Type u_1} → [inst : Semiring R] → Polynomial R → ℕ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This says that `p` has `natDegree` `n` and is monic.
-/
structure IsMonicOfDegree (p : R[X]) (n : ℕ) : Prop where
  natDegree_eq : p.natDegree = n
  monic : p.Monic

@[simp]
/-
**Polynomial.isMonicOfDegree_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_zero_iff {p : R[X]} : IsMonicOfDegree p 0 ↔ p = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eq_one_of_monic_natDegree_zero`：eq_one_of_monic_natDegree_zer
o (hf : p.Monic) (hfd : p.natDegree = 0) : p = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isMonicOfDegree_zero_iff {p : R[X]} : IsMonicOfDegree p 0 ↔ p = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ ↦ eq_one_of_monic_natDegree_zero H₂ H₁, fun H ↦ ?_⟩
  subst H
  simp
/-
**Polynomial.IsMonicOfDegree.leadingCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al.IsMonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : Polynomial R} {n : ℕ}, p.IsMonic
OfDegree n → p.leadingCoeff = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.Monic.def`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic ↔ p.leadingCoeff = 1
· 使用定理 `Polynomial.IsMonicOfDegree.monic`：∀ {R : Type u_1} [inst : Semiring R] {
p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.Monic
-/
lemma IsMonicOfDegree.leadingCoeff_eq {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) :
    p.leadingCoeff = 1 :=
  Monic.def.mp hp.monic

@[simp]
/-
**Polynomial.isMonicOfDegree_iff_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `Poly
nomial`。
形式化陈述：isMonicOfDegree_iff_of_subsingleton [Subsingleton R] {p : R[X]} {n : Nat} 
: IsMonicOfDegree p n ↔ n = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.eq_one`：Subsingleton.eq_one [One α] [Subsingleton α] (a : α
) : a = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.natDegree_one`：natDegree_one : natDegree (1 : R[X]) = 0
· 使用引理 `Polynomial.isMonicOfDegree_zero_iff`：isMonicOfDegree_zero_iff {p : R[X]}
 : IsMonicOfDegree p 0 ↔ p = 1
-/
lemma isMonicOfDegree_iff_of_subsingleton [Subsingleton R] {p : R[X]} {n : ℕ} :
    IsMonicOfDegree p n ↔ n = 0 := by
  rw [Subsingleton.eq_one p]
  refine ⟨fun ⟨H, _⟩ ↦ ?_, fun H ↦ ?_⟩
  · rwa [natDegree_one, eq_comm] at H
  · rw [H, isMonicOfDegree_zero_iff]
/-
**Polynomial.isMonicOfDegree_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_iff [Nontrivial R] (p : R[X]) (n : Nat) : IsMonicOfDegree 
p n ↔ p.natDegree <= n ∧ p.coeff n = 1
参数：p : R[X]；n : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.Monic.coeff_natDegree`：∀ {R : Type u} [inst : Semiring R] {p 
: Polynomial R}, p.Monic → p.coeff p.natDegree = 1
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.monic_of_natDegree_le_of_coeff_eq_one`：monic_of_natDegree_le_
of_coeff_eq_one (n : Nat) (pn : p.natDegree <= n) (p1 : p.coeff n = 1) : Monic p
-/
lemma isMonicOfDegree_iff [Nontrivial R] (p : R[X]) (n : ℕ) :
    IsMonicOfDegree p n ↔ p.natDegree ≤ n ∧ p.coeff n = 1 := by
  simp only [isMonicOfDegree_iff']
  refine ⟨fun ⟨H₁, H₂⟩ ↦ ⟨H₁.le, H₁ ▸ Monic.coeff_natDegree H₂⟩, fun ⟨H₁, H₂⟩ ↦ ⟨?_, ?_⟩⟩
  · exact natDegree_eq_of_le_of_coeff_ne_zero H₁ <| H₂ ▸ one_ne_zero
  · exact monic_of_natDegree_le_of_coeff_eq_one n H₁ H₂
/-
**Polynomial.IsMonicOfDegree.exists_natDegree_lt** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.IsMonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : Polynomial R} {n : ℕ},   n ≠ 0 →
 p.IsMonicOfDegree n → ∃ q, p = Polynomial.X ^ n + q ∧ q.natDegree < n
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.eraseLead_add_C_mul_X_pow`：eraseLead_add_C_mul_X_pow (f : R[X
]) : f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_eq`：∀ {R : Type u_1} [inst : Semiri
ng R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.natDegree = n
· 使用定理 `Polynomial.IsMonicOfDegree.leadingCoeff_eq`：∀ {R : Type u_1} [inst : Sem
iring R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.leadingCoeff = 1
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
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.eraseLead_natDegree_le`：eraseLead_natDegree_le (f : R[X]) : (
eraseLead f).natDegree <= f.natDegree - 1
-/
lemma IsMonicOfDegree.exists_natDegree_lt {p : R[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : IsMonicOfDegree p n) :
    ∃ q : R[X], p = X ^ n + q ∧ q.natDegree < n := by
  refine ⟨p.eraseLead, ?_, ?_⟩
  · nth_rewrite 1 [← p.eraseLead_add_C_mul_X_pow]
    rw [add_comm, hp.natDegree_eq, hp.leadingCoeff_eq, map_one, one_mul]
  · refine p.eraseLead_natDegree_le.trans_lt ?_
    rw [hp.natDegree_eq]
    lia
/-
**Polynomial.IsMonicOfDegree.mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMonicOf
Degree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {m n : ℕ},   p.I
sMonicOfDegree m → q.IsMonicOfDegree n → (p * q).IsMonicOfDegree (m + n)
参数：p * q；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsMonicOfDegree.leadingCoeff_eq`：∀ {R : Type u_1} [inst : Sem
iring R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_eq`：∀ {R : Type u_1} [inst : Semiri
ng R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.natDegree = n
· 使用定理 `Polynomial.Monic.mul`：∀ {R : Type u} [inst : Semiring R] {p q : Polynomi
al R}, p.Monic → q.Monic → (p * q).Monic
· 使用定理 `Polynomial.IsMonicOfDegree.monic`：∀ {R : Type u_1} [inst : Semiring R] {
p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.Monic
-/
lemma IsMonicOfDegree.mul {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p * q) (m + n) := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hp hq ⊢
    exact ⟨hp, hq⟩
  refine ⟨?_, hp.monic.mul hq.monic⟩
  have : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' this, hp.natDegree_eq, hq.natDegree_eq]
/-
**Polynomial.IsMonicOfDegree.pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMonicOf
Degree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p : Polynomial R} {m : ℕ},   p.IsMon
icOfDegree m → ∀ (n : ℕ), (p ^ n).IsMonicOfDegree (m * n)
参数：n : ℕ；p ^ n；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.IsMonicOfDegree.mul`：∀ {R : Type u_1} [inst : Semiring R] {p 
q : Polynomial R} {m n : ℕ},   p.IsMonicOfDegree m → q.IsMonicOfDegree n → (p * 
q).IsMonicOfDegree (…
-/
lemma IsMonicOfDegree.pow {p : R[X]} {m : ℕ} (hp : IsMonicOfDegree p m) (n : ℕ) :
    IsMonicOfDegree (p ^ n) (m * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, mul_add, mul_one]
    exact ih.mul hp
/-
**Polynomial.IsMonicOfDegree.coeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMo
nicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {n : ℕ},   p.IsM
onicOfDegree n → q.IsMonicOfDegree n → ∀ {m : ℕ}, n ≤ m → p.coeff m = q.coeff m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Polynomial.isMonicOfDegree_iff`：isMonicOfDegree_iff [Nontrivial R] (p : 
R[X]) (n : Nat) : IsMonicOfDegree p n ↔ p.natDegree <= n ∧ p.coeff n = 1
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
-/
lemma IsMonicOfDegree.coeff_eq {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) {m : ℕ} (hm : n ≤ m) :
    p.coeff m = q.coeff m := by
  nontriviality R
  rw [isMonicOfDegree_iff] at hp hq
  rcases eq_or_lt_of_le hm with rfl | hm
  · rw [hp.2, hq.2]
  · replace hp : p.natDegree < m := hp.1.trans_lt hm
    replace hq : q.natDegree < m := hq.1.trans_lt hm
    rw [coeff_eq_zero_of_natDegree_lt hp, coeff_eq_zero_of_natDegree_lt hq]
/-
**Polynomial.IsMonicOfDegree.of_mul_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.I
sMonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {m n : ℕ},   p.I
sMonicOfDegree m → (p * q).IsMonicOfDegree (m + n) → q.IsMonicOfDegree n
参数：p * q；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Monic.of_mul_monic_left`：∀ {R : Type u} [inst : Semiring R] {
p q : Polynomial R}, p.Monic → (p * q).Monic → q.Monic
· 使用定理 `Polynomial.IsMonicOfDegree.monic`：∀ {R : Type u_1} [inst : Semiring R] {
p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.Monic
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_eq`：∀ {R : Type u_1} [inst : Semiri
ng R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.natDegree = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.IsMonicOfDegree.leadingCoeff_eq`：∀ {R : Type u_1} [inst : Sem
iring R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.leadingCoeff = 1
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_left_cancel`：∀ {n m k : ℕ}, n + m = n + k → m = k
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
-/
lemma IsMonicOfDegree.of_mul_left {p q : R[X]} {m n : ℕ} (hp : IsMonicOfDegree p m)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree q n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.2
  have h₂ : q.Monic := hp.monic.of_mul_monic_left hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [hp.leadingCoeff_eq, h₂.leadingCoeff, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hp.natDegree_eq] at this
  exact (Nat.add_left_cancel this.symm).symm
/-
**Polynomial.IsMonicOfDegree.of_mul_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.
IsMonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {m n : ℕ},   q.I
sMonicOfDegree n → (p * q).IsMonicOfDegree (m + n) → p.IsMonicOfDegree m
参数：p * q；m + n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Monic.of_mul_monic_right`：∀ {R : Type u} [inst : Semiring R] 
{p q : Polynomial R}, q.Monic → (p * q).Monic → p.Monic
· 使用定理 `Polynomial.IsMonicOfDegree.monic`：∀ {R : Type u_1} [inst : Semiring R] {
p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.Monic
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_eq`：∀ {R : Type u_1} [inst : Semiri
ng R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.natDegree = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.IsMonicOfDegree.leadingCoeff_eq`：∀ {R : Type u_1} [inst : Sem
iring R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.leadingCoeff = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_right_cancel`：∀ {n m k : ℕ}, n + m = k + m → n = k
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
-/
lemma IsMonicOfDegree.of_mul_right {p q : R[X]} {m n : ℕ} (hq : IsMonicOfDegree q n)
    (hpq : IsMonicOfDegree (p * q) (m + n)) :
    IsMonicOfDegree p m := by
  rcases subsingleton_or_nontrivial R with H | H
  · simp only [isMonicOfDegree_iff_of_subsingleton, Nat.add_eq_zero_iff] at hpq ⊢
    exact hpq.1
  have h₂ : p.Monic := hq.monic.of_mul_monic_right hpq.monic
  refine ⟨?_, h₂⟩
  have := hpq.natDegree_eq
  have h : p.leadingCoeff * q.leadingCoeff ≠ 0 := by
    rw [h₂.leadingCoeff, hq.leadingCoeff_eq, one_mul]
    exact one_ne_zero
  rw [natDegree_mul' h, hq.natDegree_eq] at this
  exact (Nat.add_right_cancel this.symm).symm
/-
**Polynomial.IsMonicOfDegree.add_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsM
onicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {n : ℕ},   p.IsM
onicOfDegree n → q.natDegree < n → (p + q).IsMonicOfDegree n
参数：p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.isMonicOfDegree_iff`：isMonicOfDegree_iff [Nontrivial R] (p : 
R[X]) (n : Nat) : IsMonicOfDegree p n ↔ p.natDegree <= n ∧ p.coeff n = 1
· 使用定理 `Polynomial.natDegree_add_le_of_degree_le`：natDegree_add_le_of_degree_le 
{p q : R[X]} {n : Nat} (hp : natDegree p <= n) (hq : natDegree q <= n) : natDegr
ee (p + q) <= n
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_eq`：∀ {R : Type u_1} [inst : Semiri
ng R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.natDegree = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add_eq_left_of_lt`：coeff_add_eq_left_of_lt (qn : q.natD
egree < n) : (p + q).coeff n = p.coeff n
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
lemma IsMonicOfDegree.add_right {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n)
    (hq : q.natDegree < n) :
    IsMonicOfDegree (p + q) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  refine (isMonicOfDegree_iff ..).mpr ⟨?_, ?_⟩
  · exact natDegree_add_le_of_degree_le hp.natDegree_eq.le hq.le
  · rw [coeff_add_eq_left_of_lt hq]
    exact ((isMonicOfDegree_iff p n).mp hp).2
/-
**Polynomial.IsMonicOfDegree.add_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMo
nicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {n : ℕ},   p.nat
Degree < n → q.IsMonicOfDegree n → (p + q).IsMonicOfDegree n
参数：p + q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.IsMonicOfDegree.add_right`：∀ {R : Type u_1} [inst : Semiring 
R] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p + 
q).IsMonicOfDegree n
-/
lemma IsMonicOfDegree.add_left {p q : R[X]} {n : ℕ} (hp : p.natDegree < n)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p + q) n := by
  rw [add_comm]
  exact hq.add_right hp
/-
**Polynomial.IsMonicOfDegree.comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMonicO
fDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] {p q : Polynomial R} {m n : ℕ},   n ≠
 0 → p.IsMonicOfDegree m → q.IsMonicOfDegree n → (p.comp q).IsMonicOfDegree (m *
 n)
参数：p.comp q；m * n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_eq`：∀ {R : Type u_1} [inst : Semiri
ng R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.natDegree = n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.isMonicOfDegree_iff`：isMonicOfDegree_iff [Nontrivial R] (p : 
R[X]) (n : Nat) : IsMonicOfDegree p n ↔ p.natDegree <= n ∧ p.coeff n = 1
· 使用定理 `Polynomial.natDegree_comp_le`：natDegree_comp_le : natDegree (p.comp q) <
= natDegree p * natDegree q
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
· 使用定理 `Polynomial.IsMonicOfDegree.leadingCoeff_eq`：∀ {R : Type u_1} [inst : Sem
iring R] {p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.leadingCoeff = 1
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
lemma IsMonicOfDegree.comp {p q : R[X]} {m n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p m)
    (hq : IsMonicOfDegree q n) :
    IsMonicOfDegree (p.comp q) (m * n) := by
  rcases subsingleton_or_nontrivial R with h | h
  · simp only [isMonicOfDegree_iff_of_subsingleton, mul_eq_zero] at hp ⊢
    exact .inl hp
  rw [← hp.natDegree_eq, ← hq.natDegree_eq]
  refine (isMonicOfDegree_iff ..).mpr ⟨natDegree_comp_le, ?_⟩
  rw [coeff_comp_degree_mul_degree (hq.natDegree_eq ▸ hn), hp.leadingCoeff_eq, hq.leadingCoeff_eq,
    one_pow, one_mul]

variable [Nontrivial R]
/-
**Polynomial.IsMonicOfDegree.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMon
icOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Semiring R] [Nontrivial R] {p : Polynomial R} {n 
: ℕ}, p.IsMonicOfDegree n → p ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `Polynomial.IsMonicOfDegree.monic`：∀ {R : Type u_1} [inst : Semiring R] {
p : Polynomial R} {n : ℕ}, p.IsMonicOfDegree n → p.Monic
-/
lemma IsMonicOfDegree.ne_zero {p : R[X]} {n : ℕ} (h : IsMonicOfDegree p n) : p ≠ 0 :=
  h.monic.ne_zero

variable (R) in
/-
**Polynomial.isMonicOfDegree_X** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_X : IsMonicOfDegree (X : R[X]) 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.isMonicOfDegree_iff`：isMonicOfDegree_iff [Nontrivial R] (p : 
R[X]) (n : Nat) : IsMonicOfDegree p n ↔ p.natDegree <= n ∧ p.coeff n = 1
· 使用定理 `Polynomial.natDegree_X_le`：natDegree_X_le : (X : R[X]).natDegree <= 1
· 使用定理 `Polynomial.coeff_X_one`：coeff_X_one : coeff (X : R[X]) 1 = 1
-/
lemma isMonicOfDegree_X : IsMonicOfDegree (X : R[X]) 1 :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_le, coeff_X_one⟩

variable (R) in
/-
**Polynomial.isMonicOfDegree_X_pow** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_X_pow (n : Nat) : IsMonicOfDegree ((X : R[X]) ^ n) n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Polynomial.isMonicOfDegree_iff`：isMonicOfDegree_iff [Nontrivial R] (p : 
R[X]) (n : Nat) : IsMonicOfDegree p n ↔ p.natDegree <= n ∧ p.coeff n = 1
· 使用定理 `Polynomial.natDegree_X_pow_le`：natDegree_X_pow_le {R : Type*} [Semiring 
R] (n : Nat) : (X ^ n : R[X]).natDegree <= n
· 使用定理 `Polynomial.coeff_X_pow_self`：coeff_X_pow_self (n : Nat) : coeff (X ^ n :
 R[X]) n = 1
-/
lemma isMonicOfDegree_X_pow (n : ℕ) : IsMonicOfDegree ((X : R[X]) ^ n) n :=
  (isMonicOfDegree_iff ..).mpr ⟨natDegree_X_pow_le n, coeff_X_pow_self n⟩
/-
**Polynomial.isMonicOfDegree_monomial_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`
。
形式化陈述：isMonicOfDegree_monomial_one (n : Nat) : IsMonicOfDegree (monomial n (1 : 
R)) n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_one_right_eq_X_pow`：monomial_one_right_eq_X_pow (n :
 Nat) : monomial n (1 : R) = X ^ n
· 使用引理 `Polynomial.isMonicOfDegree_X_pow`：isMonicOfDegree_X_pow (n : Nat) : IsMo
nicOfDegree ((X : R[X]) ^ n) n
-/
lemma isMonicOfDegree_monomial_one (n : ℕ) : IsMonicOfDegree (monomial n (1 : R)) n := by
  simpa only [monomial_one_right_eq_X_pow] using isMonicOfDegree_X_pow R n
/-
**Polynomial.isMonicOfDegree_X_add_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_X_add_one (r : R) : IsMonicOfDegree (X + C r) 1
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsMonicOfDegree.add_right`：∀ {R : Type u_1} [inst : Semiring 
R] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p + 
q).IsMonicOfDegree n
· 使用引理 `Polynomial.isMonicOfDegree_X`：isMonicOfDegree_X : IsMonicOfDegree (X : R
[X]) 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma isMonicOfDegree_X_add_one (r : R) : IsMonicOfDegree (X + C r) 1 :=
  (isMonicOfDegree_X R).add_right (by rw [natDegree_C]; exact zero_lt_one)
/-
**Polynomial.isMonicOfDegree_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_one_iff {f : R[X]} : IsMonicOfDegree f 1 ↔ exists r : R, f
 = X + C r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsMonicOfDegree.coeff_eq`：∀ {R : Type u_1} [inst : Semiring R
] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.IsMonicOfDegree n → ∀ 
{m : ℕ}, n ≤ m → p.coeff …
· 使用引理 `Polynomial.isMonicOfDegree_X_add_one`：isMonicOfDegree_X_add_one (r : R) 
: IsMonicOfDegree (X + C r) 1
-/
lemma isMonicOfDegree_one_iff {f : R[X]} : IsMonicOfDegree f 1 ↔ ∃ r : R, f = X + C r := by
  refine ⟨fun H ↦ ?_, fun ⟨r, H⟩ ↦ H ▸ isMonicOfDegree_X_add_one r⟩
  refine ⟨f.coeff 0, ?_⟩
  ext1 n
  rcases n.eq_zero_or_pos with rfl | hn
  · simp
  · exact H.coeff_eq (isMonicOfDegree_X_add_one _) (by lia)
/-
**Polynomial.isMonicOfDegree_add_add_two** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_add_add_two (a b : R) : IsMonicOfDegree (X ^ 2 + C a * X +
 C b) 2
参数：a b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Polynomial.IsMonicOfDegree.add_right`：∀ {R : Type u_1} [inst : Semiring 
R] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p + 
q).IsMonicOfDegree n
· 使用引理 `Polynomial.isMonicOfDegree_X_pow`：isMonicOfDegree_X_pow (n : Nat) : IsMo
nicOfDegree ((X : R[X]) ^ n) n
· 使用定理 `Polynomial.natDegree_add_le`：natDegree_add_le (p q : R[X]) : natDegree (
p + q) <= max (natDegree p) (natDegree q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `Polynomial.natDegree_X_le`：natDegree_X_le : (X : R[X]).natDegree <= 1
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma isMonicOfDegree_add_add_two (a b : R) : IsMonicOfDegree (X ^ 2 + C a * X + C b) 2 := by
  rw [add_assoc]
  exact (isMonicOfDegree_X_pow R 2).add_right <|
    calc
    _ ≤ max (C a * X).natDegree (C b).natDegree := natDegree_add_le ..
    _ = (C a * X).natDegree := by simp
    _ < 2 := natDegree_C_mul_le .. |>.trans natDegree_X_le |>.trans_lt one_lt_two
/-
**Polynomial.isMonicOfDegree_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_two_iff {f : R[X]} : IsMonicOfDegree f 2 ↔ exists a b : R,
 f = X ^ 2 + C a * X + C b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_X_pow`：coeff_X_pow (k n : Nat) : coeff (X ^ k : R[X]) n
 = if n = k then 1 else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `Polynomial.IsMonicOfDegree.coeff_eq`：∀ {R : Type u_1} [inst : Semiring R
] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.IsMonicOfDegree n → ∀ 
{m : ℕ}, n ≤ m → p.coeff …
· 使用引理 `Polynomial.isMonicOfDegree_add_add_two`：isMonicOfDegree_add_add_two (a b
 : R) : IsMonicOfDegree (X ^ 2 + C a * X + C b) 2
-/
lemma isMonicOfDegree_two_iff {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ a b : R, f = X ^ 2 + C a * X + C b := by
  refine ⟨fun H ↦ ?_, fun ⟨a, b, h⟩ ↦ h ▸ isMonicOfDegree_add_add_two a b⟩
  refine ⟨f.coeff 1, f.coeff 0, ext fun n ↦ ?_⟩
  rcases lt_trichotomy n 1 with hn | rfl | hn
  · obtain rfl : n = 0 := Nat.lt_one_iff.mp hn
    simp
  · simp
  · exact H.coeff_eq (isMonicOfDegree_add_add_two ..) (by lia)

end Semiring

section Ring

variable [Ring R]

/-
**Polynomial.IsMonicOfDegree.natDegree_sub_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial.IsMonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {p : Polynomial R} {n : ℕ},   n ≠ 0 → p.I
sMonicOfDegree n → (p - Polynomial.X ^ n).natDegree < n
参数：p - Polynomial.X ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsMonicOfDegree.exists_natDegree_lt`：∀ {R : Type u_1} [inst :
 Semiring R] {p : Polynomial R} {n : ℕ},   n ≠ 0 → p.IsMonicOfDegree n → ∃ q, p 
= Polynomial.X ^ n + q ∧ q.natDegree…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
lemma IsMonicOfDegree.natDegree_sub_X_pow {p : R[X]} {n : ℕ} (hn : n ≠ 0)
    (hp : IsMonicOfDegree p n) :
    (p - X ^ n).natDegree < n := by
  obtain ⟨q, hq₁, hq₂⟩ := hp.exists_natDegree_lt hn
  simpa [hq₁]
/-
**Polynomial.IsMonicOfDegree.natDegree_sub_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial.IsMonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {p q : Polynomial R} {n : ℕ},   n ≠ 0 → p
.IsMonicOfDegree n → q.IsMonicOfDegree n → (p - q).natDegree < n
参数：p - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_sub_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : 
G), a - c - (b - c) = a - b
· 使用定理 `Polynomial.IsMonicOfDegree.natDegree_sub_X_pow`：∀ {R : Type u_1} [inst :
 Ring R] {p : Polynomial R} {n : ℕ},   n ≠ 0 → p.IsMonicOfDegree n → (p - Polyno
mial.X ^ n).natDegree < n
· 使用定理 `Nat.le_sub_one_iff_lt`：∀ {m n : ℕ}, 0 < m → (n ≤ m - 1 ↔ n < m)
· 使用定理 `Nat.zero_lt_of_ne_zero`：∀ {a : ℕ}, a ≠ 0 → 0 < a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_sub_le_iff_left`：natDegree_sub_le_iff_left (qn : q.
natDegree <= n) : (p - q).natDegree <= n ↔ p.natDegree <= n
-/
lemma IsMonicOfDegree.natDegree_sub_lt {p q : R[X]} {n : ℕ} (hn : n ≠ 0) (hp : IsMonicOfDegree p n)
    (hq : IsMonicOfDegree q n) :
    (p - q).natDegree < n := by
  rw [← sub_sub_sub_cancel_right p q (X ^ n)]
  replace hp := hp.natDegree_sub_X_pow hn
  replace hq := hq.natDegree_sub_X_pow hn
  rw [← Nat.le_sub_one_iff_lt (Nat.zero_lt_of_ne_zero hn)] at hp hq ⊢
  exact (natDegree_sub_le_iff_left hq).mpr hp
/-
**Polynomial.IsMonicOfDegree.sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsMonicOf
Degree`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] {p q : Polynomial R} {n : ℕ},   p.IsMonic
OfDegree n → q.natDegree < n → (p - q).IsMonicOfDegree n
参数：p - q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.IsMonicOfDegree.add_right`：∀ {R : Type u_1} [inst : Semiring 
R] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p + 
q).IsMonicOfDegree n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
-/
lemma IsMonicOfDegree.sub {p q : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (hq : q.natDegree < n) :
    IsMonicOfDegree (p - q) n := by
  rw [sub_eq_add_neg]
  exact hp.add_right <| (natDegree_neg q) ▸ hq

variable [Nontrivial R]
/-
**Polynomial.isMonicOfDegree_X_sub_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_X_sub_one (r : R) : IsMonicOfDegree (X - C r) 1
参数：r : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.IsMonicOfDegree.sub`：∀ {R : Type u_1} [inst : Ring R] {p q : 
Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p - q).IsMonic
OfDegree n
· 使用引理 `Polynomial.isMonicOfDegree_X`：isMonicOfDegree_X : IsMonicOfDegree (X : R
[X]) 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma isMonicOfDegree_X_sub_one (r : R) : IsMonicOfDegree (X - C r) 1 :=
  (isMonicOfDegree_X R).sub (by rw [natDegree_C]; exact zero_lt_one)
/-
**Polynomial.isMonicOfDegree_sub_add_two** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_sub_add_two (a b : R) : IsMonicOfDegree (X ^ 2 - C a * X +
 C b) 2
参数：a b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b + c = a - (b - c)
· 使用定理 `Polynomial.IsMonicOfDegree.add_right`：∀ {R : Type u_1} [inst : Semiring 
R] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p + 
q).IsMonicOfDegree n
· 使用引理 `Polynomial.isMonicOfDegree_X_pow`：isMonicOfDegree_X_pow (n : Nat) : IsMo
nicOfDegree ((X : R[X]) ^ n) n
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_sub_le`：natDegree_sub_le (p q : R[X]) : natDegree (
p - q) <= max (natDegree p) (natDegree q)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `Polynomial.natDegree_X_le`：natDegree_X_le : (X : R[X]).natDegree <= 1
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
lemma isMonicOfDegree_sub_add_two (a b : R) : IsMonicOfDegree (X ^ 2 - C a * X + C b) 2 := by
  rw [sub_add]
  exact (isMonicOfDegree_X_pow R 2).add_right <| by
    rw [natDegree_neg]
    calc
    _ ≤ max (C a * X).natDegree (C b).natDegree := natDegree_sub_le ..
    _ = (C a * X).natDegree := by simp
    _ < 2 := natDegree_C_mul_le .. |>.trans natDegree_X_le |>.trans_lt one_lt_two

/-- A version of `Polynomial.isMonicOfDegree_two_iff` with negated middle coefficient. -/
/-
**Polynomial.isMonicOfDegree_two_iff'** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isMonicOfDegree_two_iff' {f : R[X]} : IsMonicOfDegree f 2 ↔ exists a b : R
, f = X ^ 2 - C a * X + C b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.isMonicOfDegree_two_iff`：isMonicOfDegree_two_iff {f : R[X]} :
 IsMonicOfDegree f 2 ↔ exists a b : R, f = X ^ 2 + C a * X + C b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `Polynomial.isMonicOfDegree_sub_add_two`：isMonicOfDegree_sub_add_two (a b
 : R) : IsMonicOfDegree (X ^ 2 - C a * X + C b) 2

--- 原说明 ---
A version of `Polynomial.isMonicOfDegree_two_iff` with negated middle coefficien
t.
-/
lemma isMonicOfDegree_two_iff' {f : R[X]} :
    IsMonicOfDegree f 2 ↔ ∃ a b : R, f = X ^ 2 - C a * X + C b := by
  refine ⟨fun H ↦ ?_, fun ⟨a, b, h⟩ ↦ h ▸ isMonicOfDegree_sub_add_two a b⟩
  simp only [sub_eq_add_neg, ← neg_mul, ← map_neg]
  obtain ⟨a, b, h⟩ := isMonicOfDegree_two_iff.mp H
  exact ⟨-a, b, (neg_neg a).symm ▸ h⟩

end Ring

section CommRing

variable [CommRing R]

/-
**Polynomial.IsMonicOfDegree.of_dvd_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Is
MonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {a b r : Polynomial R} {m n : ℕ},   n
 ≤ m →     a.IsMonicOfDegree m →       b.IsMonicOfDegree n → r.natDegree < m → b
 ∣ a + r → ∃ q, q.IsMonicOfDegree (m - n) ∧ a = q * b - r
参数：m - n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_mul_left_of_dvd`：exists_eq_mul_left_of_dvd (h : a ∣ b) : exist
s c, b = c * a
· 使用定理 `Polynomial.IsMonicOfDegree.of_mul_right`：∀ {R : Type u_1} [inst : Semiri
ng R] {p q : Polynomial R} {m n : ℕ},   q.IsMonicOfDegree n → (p * q).IsMonicOfD
egree (m + n) → p.IsMonicOfDe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.IsMonicOfDegree.add_right`：∀ {R : Type u_1} [inst : Semiring 
R] {p q : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → q.natDegree < n → (p + 
q).IsMonicOfDegree n
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
-/
lemma IsMonicOfDegree.of_dvd_add {a b r : R[X]} {m n : ℕ} (hmn : n ≤ m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a + r) :
    ∃ q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b - r := by
  obtain ⟨q, hq⟩ := exists_eq_mul_left_of_dvd h
  refine ⟨q, hb.of_mul_right ?_, eq_sub_iff_add_eq.mpr hq⟩
  rw [← hq, show m - n + n = m by lia]
  exact ha.add_right hr
/-
**Polynomial.IsMonicOfDegree.of_dvd_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Is
MonicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {a b r : Polynomial R} {m n : ℕ},   n
 ≤ m →     a.IsMonicOfDegree m →       b.IsMonicOfDegree n → r.natDegree < m → b
 ∣ a - r → ∃ q, q.IsMonicOfDegree (m - n) ∧ a = q * b + r
参数：m - n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Polynomial.IsMonicOfDegree.of_dvd_add`：∀ {R : Type u_1} [inst : CommRing
 R] {a b r : Polynomial R} {m n : ℕ},   n ≤ m →     a.IsMonicOfDegree m →       
b.IsMonicOfDegree n → r.nat…
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
-/
lemma IsMonicOfDegree.of_dvd_sub {a b r : R[X]} {m n : ℕ} (hmn : n ≤ m) (ha : IsMonicOfDegree a m)
    (hb : IsMonicOfDegree b n) (hr : r.natDegree < m) (h : b ∣ a - r) :
    ∃ q : R[X], IsMonicOfDegree q (m - n) ∧ a = q * b + r := by
  convert ha.of_dvd_add hmn hb ?_ h with q
  · rw [sub_neg_eq_add]
  · rwa [natDegree_neg]
/-
**Polynomial.IsMonicOfDegree.aeval_add** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsM
onicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {p : Polynomial R} {n : ℕ},   p.IsMon
icOfDegree n → ∀ (r : R), ((Polynomial.aeval (Polynomial.X + Polynomial.C r)) p)
.IsMonicOfDegree n
参数：r : R；(Polynomial.aeval (Polynomial.X + Polynomial.C r)) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.IsMonicOfDegree.comp`：∀ {R : Type u_1} [inst : Semiring R] {p
 q : Polynomial R} {m n : ℕ},   n ≠ 0 → p.IsMonicOfDegree m → q.IsMonicOfDegree 
n → (p.comp q).IsMoni…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `Polynomial.isMonicOfDegree_X_add_one`：isMonicOfDegree_X_add_one (r : R) 
: IsMonicOfDegree (X + C r) 1
-/
lemma IsMonicOfDegree.aeval_add {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X + C r) p) n := by
  rcases subsingleton_or_nontrivial R with H | H
  · simpa using hp
  rw [← mul_one n]
  exact hp.comp one_ne_zero (isMonicOfDegree_X_add_one r)
/-
**Polynomial.IsMonicOfDegree.aeval_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.IsM
onicOfDegree`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] {p : Polynomial R} {n : ℕ},   p.IsMon
icOfDegree n → ∀ (r : R), ((Polynomial.aeval (Polynomial.X - Polynomial.C r)) p)
.IsMonicOfDegree n
参数：r : R；(Polynomial.aeval (Polynomial.X - Polynomial.C r)) p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Polynomial.IsMonicOfDegree.aeval_add`：∀ {R : Type u_1} [inst : CommRing 
R] {p : Polynomial R} {n : ℕ},   p.IsMonicOfDegree n → ∀ (r : R), ((Polynomial.a
eval (Polynomial.X + Polyn…
-/
lemma IsMonicOfDegree.aeval_sub {p : R[X]} {n : ℕ} (hp : IsMonicOfDegree p n) (r : R) :
    IsMonicOfDegree (aeval (X - C r) p) n := by
  rw [sub_eq_add_neg, ← map_neg]
  exact aeval_add hp (-r)

end CommRing

end Polynomial

