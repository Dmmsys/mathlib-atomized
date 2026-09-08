/-
Copyright (c) 2020 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Algebra.BigOperators.NatAntidiagonal
public import Mathlib.Algebra.Polynomial.Reverse

/-!
# "Mirror" of a univariate polynomial

In this file we define `Polynomial.mirror`, a variant of `Polynomial.reverse`. The difference
between `reverse` and `mirror` is that `reverse` will decrease the degree if the polynomial is
divisible by `X`.

## Main definitions

- `Polynomial.mirror`

## Main results

- `Polynomial.mirror_mul_of_domain`: `mirror` preserves multiplication.
- `Polynomial.irreducible_of_mirror`: an irreducibility criterion involving `mirror`

-/

@[expose] public section


namespace Polynomial

section Semiring

variable {R : Type*} [Semiring R] (p q : R[X])

/-- mirror of a polynomial: reverses the coefficients while preserving `Polynomial.natDegree` -/
/-
**Polynomial.mirror** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：mirror
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
mirror of a polynomial: reverses the coefficients while preserving `Polynomial.n
atDegree`
-/
noncomputable def mirror :=
  p.reverse * X ^ p.natTrailingDegree

@[simp]
/-
**Polynomial.mirror_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_zero : (0 : R[X]).mirror = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mirror_zero : (0 : R[X]).mirror = 0 := by simp [mirror]
/-
**Polynomial.mirror_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_monomial (n : Nat) (a : R) : (monomial n a).mirror = monomial n a
参数：n : Nat；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.monomial_zero_right`：monomial_zero_right (n : Nat) : monomial
 n (0 : R) = 0
· 使用定理 `Polynomial.mirror_zero`：mirror_zero : (0 : R[X]).mirror = 0
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.reverse.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (f : Polyn
omial R), f.reverse = Polynomial.reflect f.natDegree f
· 使用定理 `Polynomial.natDegree_monomial`：natDegree_monomial [DecidableEq R] (i : N
at) (r : R) : natDegree (monomial i r) = if r = 0 then 0 else i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.natTrailingDegree_monomial`：natTrailingDegree_monomial (ha : 
a != 0) : natTrailingDegree (monomial n a) = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.reflect_C_mul_X_pow`：reflect_C_mul_X_pow (N n : Nat) {c : R} 
: reflect N (C c * X ^ n) = C c * X ^ revAt N n
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem mirror_monomial (n : ℕ) (a : R) : (monomial n a).mirror = monomial n a := by
  classical
    by_cases ha : a = 0
    · rw [ha, monomial_zero_right, mirror_zero]
    · rw [mirror, reverse, natDegree_monomial n a, if_neg ha, natTrailingDegree_monomial ha, ←
        C_mul_X_pow_eq_monomial, reflect_C_mul_X_pow, revAt_le (le_refl n), tsub_self, pow_zero,
        mul_one]
/-
**Polynomial.mirror_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_C (a : R) : (C a).mirror = C a
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mirror_monomial`：mirror_monomial (n : Nat) (a : R) : (monomia
l n a).mirror = monomial n a
-/
theorem mirror_C (a : R) : (C a).mirror = C a :=
  mirror_monomial 0 a
/-
**Polynomial.mirror_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_X : X.mirror = (X : R[X])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mirror_monomial`：mirror_monomial (n : Nat) (a : R) : (monomia
l n a).mirror = monomial n a
-/
theorem mirror_X : X.mirror = (X : R[X]) :=
  mirror_monomial 1 (1 : R)
/-
**Polynomial.mirror_natDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_natDegree : p.mirror.natDegree = p.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mirror_zero`：mirror_zero : (0 : R[X]).mirror = 0
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.natDegree_mul'`：natDegree_mul' (h : leadingCoeff p * leadingC
oeff q != 0) : natDegree (p * q) = natDegree p + natDegree q
· 使用定理 `Polynomial.leadingCoeff_X_pow`：leadingCoeff_X_pow (n : Nat) : leadingCoe
ff ((X : R[X]) ^ n) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.reverse_leadingCoeff`：reverse_leadingCoeff (f : R[X]) : f.rev
erse.leadingCoeff = f.trailingCoeff
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.trailingCoeff_eq_zero`：trailingCoeff_eq_zero : trailingCoeff 
p = 0 ↔ p = 0
· 使用定理 `Polynomial.reverse_natDegree`：reverse_natDegree (f : R[X]) : f.reverse.n
atDegree = f.natDegree - f.natTrailingDegree
· 使用定理 `Polynomial.natDegree_X_pow`：natDegree_X_pow : natDegree ((X : R[X]) ^ n)
 = n
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natTrailingDegree_le_natDegree`：natTrailingDegree_le_natDegre
e (p : R[X]) : p.natTrailingDegree <= p.natDegree
-/
theorem mirror_natDegree : p.mirror.natDegree = p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  nontriviality R
  rw [mirror, natDegree_mul', reverse_natDegree, natDegree_X_pow,
    tsub_add_cancel_of_le p.natTrailingDegree_le_natDegree]
  rwa [leadingCoeff_X_pow, mul_one, reverse_leadingCoeff, Ne, trailingCoeff_eq_zero]
/-
**Polynomial.mirror_natTrailingDegree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegre
e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mirror_zero`：mirror_zero : (0 : R[X]).mirror = 0
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.natTrailingDegree_mul_X_pow`：natTrailingDegree_mul_X_pow {p :
 R[X]} (hp : p != 0) (n : Nat) : (p * X ^ n).natTrailingDegree = p.natTrailingDe
gree + n
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.reverse_eq_zero`：reverse_eq_zero : f.reverse = 0 ↔ f = 0
· 使用定理 `Polynomial.natTrailingDegree_reverse`：natTrailingDegree_reverse (f : R[X
]) : f.reverse.natTrailingDegree = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem mirror_natTrailingDegree : p.mirror.natTrailingDegree = p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, mirror_zero]
  · rw [mirror, natTrailingDegree_mul_X_pow ((mt reverse_eq_zero.mp) hp),
      natTrailingDegree_reverse, zero_add]
/-
**Polynomial.coeff_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mirror (n : Nat) : p.mirror.coeff n = p.coeff (revAt (p.natDegree + 
p.natTrailingDegree) n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `Polynomial.mirror_natDegree`：mirror_natDegree : p.mirror.natDegree = p.n
atDegree
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `Polynomial.coeff_eq_zero_of_lt_natTrailingDegree`：coeff_eq_zero_of_lt_na
tTrailingDegree {p : R[X]} {n : Nat} (h : n < p.natTrailingDegree) : p.coeff n =
 0
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.sub_lt_sub_right`：∀ {a b c : ℕ}, c ≤ a → a < b → a - c < b - c
· 使用定理 `add_lt_add_left`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] [i : Ad
dRightStrictMono α] {b c : α}, b < c → ∀ (a : α), b + a < c + a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `add_tsub_cancel_left`：add_tsub_cancel_left (a b : α) : a + b - a = b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.revAtFun_eq`：revAtFun_eq (N i : Nat) : revAtFun N i = revAt N
 i
· 使用定理 `Polynomial.revAtFun.eq_1`：∀ (N i : ℕ), Polynomial.revAtFun N i = if i ≤ 
N then N - i else i
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `tsub_add_eq_add_tsub`：tsub_add_eq_add_tsub (h : b <= a) : a - b + c = a 
+ c - b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `tsub_tsub_assoc`：tsub_tsub_assoc (h₁ : b <= a) (h₂ : c <= b) : a - (b - 
c) = a - b + c
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.coeff_mul_X_pow'`：coeff_mul_X_pow' (p : R[X]) (n d : Nat) : (
p * X ^ n).coeff d = ite (n <= d) (p.coeff (d - n)) 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
（共 37 条，此处仅展示前 30 条）
-/
theorem coeff_mirror (n : ℕ) :
    p.mirror.coeff n = p.coeff (revAt (p.natDegree + p.natTrailingDegree) n) := by
  by_cases h2 : p.natDegree < n
  · rw [coeff_eq_zero_of_natDegree_lt (by rwa [mirror_natDegree])]
    by_cases h1 : n ≤ p.natDegree + p.natTrailingDegree
    · rw [revAt_le h1, coeff_eq_zero_of_lt_natTrailingDegree]
      grw [h2, add_tsub_cancel_left]
    · rw [← revAtFun_eq, revAtFun, if_neg h1, coeff_eq_zero_of_natDegree_lt h2]
  rw [not_lt] at h2
  rw [revAt_le (h2.trans (Nat.le_add_right _ _))]
  by_cases h3 : p.natTrailingDegree ≤ n
  · rw [← tsub_add_eq_add_tsub h2, ← tsub_tsub_assoc h2 h3, mirror, coeff_mul_X_pow', if_pos h3,
      coeff_reverse, revAt_le (tsub_le_self.trans h2)]
  rw [not_le] at h3
  rw [coeff_eq_zero_of_natDegree_lt (lt_tsub_iff_right.mpr (Nat.add_lt_add_left h3 _))]
  exact coeff_eq_zero_of_lt_natTrailingDegree (by rwa [mirror_natTrailingDegree])

--TODO: Extract `Finset.sum_range_rev_at` lemma.
/-
**Polynomial.mirror_eval_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_eval_one : p.mirror.eval 1 = p.eval 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.mirror_natDegree`：mirror_natDegree : p.mirror.natDegree = p.n
atDegree
· 使用定理 `Finset.sum_bij_ne_zero`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [
inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ} {f : ι → M}   {g : κ → M} 
(i : (a : ι)…
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `tsub_le_iff_tsub_le`：tsub_le_iff_tsub_le : a - b <= c ↔ a - c <= b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mirror_natTrailingDegree`：mirror_natTrailingDegree : p.mirror
.natTrailingDegree = p.natTrailingDegree
· 使用定理 `Polynomial.natTrailingDegree_le_of_ne_zero`：natTrailingDegree_le_of_ne_z
ero (h : coeff p n != 0) : natTrailingDegree p <= n
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
· 使用定理 `Polynomial.coeff_mirror`：coeff_mirror (n : Nat) : p.mirror.coeff n = p.c
oeff (revAt (p.natDegree + p.natTrailingDegree) n)
-/
theorem mirror_eval_one : p.mirror.eval 1 = p.eval 1 := by
  simp_rw [eval_eq_sum_range, one_pow, mul_one, mirror_natDegree]
  refine Finset.sum_bij_ne_zero ?_ ?_ ?_ ?_ ?_
  · exact fun n _ _ => revAt (p.natDegree + p.natTrailingDegree) n
  · intro n hn hp
    rw [Finset.mem_range_succ_iff] at *
    rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
    rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right, ← mirror_natTrailingDegree]
    exact natTrailingDegree_le_of_ne_zero hp
  · exact fun n₁ _ _ _ _ _ h => by rw [← @revAt_invol _ n₁, h, revAt_invol]
  · intro n hn hp
    use revAt (p.natDegree + p.natTrailingDegree) n
    refine ⟨?_, ?_, revAt_invol⟩
    · rw [Finset.mem_range_succ_iff] at *
      rw [revAt_le (hn.trans (Nat.le_add_right _ _))]
      rw [tsub_le_iff_tsub_le, add_comm, add_tsub_cancel_right]
      exact natTrailingDegree_le_of_ne_zero hp
    · change p.mirror.coeff _ ≠ 0
      rwa [coeff_mirror, revAt_invol]
  · exact fun n _ _ => p.coeff_mirror n
/-
**Polynomial.mirror_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_mirror : p.mirror.mirror = p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mirror`：coeff_mirror (n : Nat) : p.mirror.coeff n = p.c
oeff (revAt (p.natDegree + p.natTrailingDegree) n)
· 使用定理 `Polynomial.mirror_natDegree`：mirror_natDegree : p.mirror.natDegree = p.n
atDegree
· 使用定理 `Polynomial.mirror_natTrailingDegree`：mirror_natTrailingDegree : p.mirror
.natTrailingDegree = p.natTrailingDegree
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
-/
theorem mirror_mirror : p.mirror.mirror = p :=
  Polynomial.ext fun n => by
    rw [coeff_mirror, coeff_mirror, mirror_natDegree, mirror_natTrailingDegree, revAt_invol]

variable {p q}
/-
**Polynomial.mirror_involutive** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_involutive : Function.Involutive (mirror : R[X] -> R[X])
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.mirror_mirror`：mirror_mirror : p.mirror.mirror = p
-/
theorem mirror_involutive : Function.Involutive (mirror : R[X] → R[X]) :=
  mirror_mirror
/-
**Polynomial.mirror_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_eq_iff : p.mirror = q ↔ p = q.mirror
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Involutive.eq_iff`：∀ {α : Sort u} {f : α → α}, Function.Involut
ive f → ∀ {x y : α}, f x = y ↔ x = f y
· 使用定理 `Polynomial.mirror_involutive`：mirror_involutive : Function.Involutive (m
irror : R[X] -> R[X])
-/
theorem mirror_eq_iff : p.mirror = q ↔ p = q.mirror :=
  mirror_involutive.eq_iff

@[simp]
/-
**Polynomial.mirror_inj** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_inj : p.mirror = q.mirror ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Involutive.injective`：∀ {α : Sort u} {f : α → α}, Function.Invo
lutive f → Function.Injective f
· 使用定理 `Polynomial.mirror_involutive`：mirror_involutive : Function.Involutive (m
irror : R[X] -> R[X])
-/
theorem mirror_inj : p.mirror = q.mirror ↔ p = q :=
  mirror_involutive.injective.eq_iff

@[simp]
/-
**Polynomial.mirror_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_eq_zero : p.mirror = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mirror_mirror`：mirror_mirror : p.mirror.mirror = p
· 使用定理 `Polynomial.mirror_zero`：mirror_zero : (0 : R[X]).mirror = 0
-/
theorem mirror_eq_zero : p.mirror = 0 ↔ p = 0 :=
  ⟨fun h => by rw [← p.mirror_mirror, h, mirror_zero], fun h => by rw [h, mirror_zero]⟩

variable (p q)

@[simp]
/-
**Polynomial.mirror_trailingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.trailingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : P
olynomial R), p.trailingCoeff = p.coeff p.natTrailingDegree
· 使用定理 `Polynomial.mirror_natTrailingDegree`：mirror_natTrailingDegree : p.mirror
.natTrailingDegree = p.natTrailingDegree
· 使用定理 `Polynomial.coeff_mirror`：coeff_mirror (n : Nat) : p.mirror.coeff n = p.c
oeff (revAt (p.natDegree + p.natTrailingDegree) n)
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem mirror_trailingCoeff : p.mirror.trailingCoeff = p.leadingCoeff := by
  rw [leadingCoeff, trailingCoeff, mirror_natTrailingDegree, coeff_mirror,
    revAt_le (Nat.le_add_left _ _), add_tsub_cancel_right]

@[simp]
/-
**Polynomial.mirror_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.mirror_mirror`：mirror_mirror : p.mirror.mirror = p
· 使用定理 `Polynomial.mirror_trailingCoeff`：mirror_trailingCoeff : p.mirror.trailin
gCoeff = p.leadingCoeff
-/
theorem mirror_leadingCoeff : p.mirror.leadingCoeff = p.trailingCoeff := by
  rw [← p.mirror_mirror, mirror_trailingCoeff, p.mirror_mirror]
/-
**Polynomial.coeff_mul_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_mul_mirror : (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree
) = p.sum fun _ => (· ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk`：∀ {M : Type u_3} [inst
 : AddCommMonoid M] (f : ℕ × ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.ant
idiagonal n, f ij = ∑ k ∈ Finset.range…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_mirror`：coeff_mirror (n : Nat) : p.mirror.coeff n = p.c
oeff (revAt (p.natDegree + p.natTrailingDegree) n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.revAt_le`：revAt_le {N i : Nat} (H : i <= N) : revAt N i = N -
 i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_range_succ_iff`：mem_range_succ_iff {a b : Nat} : a in range b
.succ ↔ a <= b
· 使用定理 `Polynomial.revAt_invol`：revAt_invol {N i : Nat} : (revAt N) (revAt N i) 
= i
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Polynomial.sum_eq_of_subset`：sum_eq_of_subset {S : Type*} [AddCommMonoid
 S] {p : R[X]} (f : Nat -> R -> S) (hf : forall i, f i 0 = 0) {s : Finset Nat} (
hs : p.support su…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
-/
theorem coeff_mul_mirror :
    (p * p.mirror).coeff (p.natDegree + p.natTrailingDegree) = p.sum fun _ => (· ^ 2) := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  refine
    (Finset.sum_congr rfl fun n hn => ?_).trans
      (p.sum_eq_of_subset (fun _ ↦ (· ^ 2)) (fun _ ↦ zero_pow two_ne_zero) fun n hn ↦
          Finset.mem_range_succ_iff.mpr
            ((le_natDegree_of_mem_supp n hn).trans (Nat.le_add_right _ _))).symm
  rw [coeff_mirror, ← revAt_le (Finset.mem_range_succ_iff.mp hn), revAt_invol, ← sq]

variable [NoZeroDivisors R]
/-
**Polynomial.natDegree_mul_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Polynomial.natDegree_mul`：natDegree_mul (hp : p != 0) (hq : q != 0) : (p
 * q).natDegree = p.natDegree + q.natDegree
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mirror_eq_zero`：mirror_eq_zero : p.mirror = 0 ↔ p = 0
· 使用定理 `Polynomial.mirror_natDegree`：mirror_natDegree : p.mirror.natDegree = p.n
atDegree
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem natDegree_mul_mirror : (p * p.mirror).natDegree = 2 * p.natDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natDegree_zero, mul_zero]
  rw [natDegree_mul hp (mt mirror_eq_zero.mp hp), mirror_natDegree, two_mul]
/-
**Polynomial.natTrailingDegree_mul_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：natTrailingDegree_mul_mirror : (p * p.mirror).natTrailingDegree = 2 * p.na
tTrailingDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.natTrailingDegree_zero`：natTrailingDegree_zero : natTrailingD
egree (0 : R[X]) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.natTrailingDegree_mul`：natTrailingDegree_mul [NoZeroDivisors 
R] (hp : p != 0) (hq : q != 0) : (p * q).natTrailingDegree = p.natTrailingDegree
 + q.natTrailingDegree
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mirror_eq_zero`：mirror_eq_zero : p.mirror = 0 ↔ p = 0
· 使用定理 `Polynomial.mirror_natTrailingDegree`：mirror_natTrailingDegree : p.mirror
.natTrailingDegree = p.natTrailingDegree
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
-/
theorem natTrailingDegree_mul_mirror :
    (p * p.mirror).natTrailingDegree = 2 * p.natTrailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, natTrailingDegree_zero, mul_zero]
  rw [natTrailingDegree_mul hp (mt mirror_eq_zero.mp hp), mirror_natTrailingDegree, two_mul]
/-
**Polynomial.mirror_mul_of_domain** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.mirror_zero`：mirror_zero : (0 : R[X]).mirror = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.reverse_mul_of_domain`：reverse_mul_of_domain {R : Type*} [Sem
iring R] [NoZeroDivisors R] (f g : R[X]) : reverse (f * g) = reverse f * reverse
 g
· 使用定理 `Polynomial.natTrailingDegree_mul`：natTrailingDegree_mul [NoZeroDivisors 
R] (hp : p != 0) (hq : q != 0) : (p * q).natTrailingDegree = p.natTrailingDegree
 + q.natTrailingDegree
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.X_pow_mul`：X_pow_mul {n : Nat} : X ^ n * p = p * X ^ n
-/
theorem mirror_mul_of_domain : (p * q).mirror = p.mirror * q.mirror := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, mirror_zero, zero_mul]
  by_cases hq : q = 0
  · rw [hq, mul_zero, mirror_zero, mul_zero]
  rw [mirror, mirror, mirror, reverse_mul_of_domain, natTrailingDegree_mul hp hq, pow_add]
  rw [mul_assoc, ← mul_assoc q.reverse, ← X_pow_mul (p := reverse q)]
  repeat' rw [mul_assoc]
/-
**Polynomial.mirror_smul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_smul (a : R) : (a • p).mirror = a • p.mirror
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Polynomial.mirror_mul_of_domain`：mirror_mul_of_domain : (p * q).mirror =
 p.mirror * q.mirror
· 使用定理 `Polynomial.mirror_C`：mirror_C (a : R) : (C a).mirror = C a
-/
theorem mirror_smul (a : R) : (a • p).mirror = a • p.mirror := by
  rw [← C_mul', ← C_mul', mirror_mul_of_domain, mirror_C]

end Semiring

section Ring

variable {R : Type*} [Ring R] (p q : R[X])

/-
**Polynomial.mirror_neg** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mirror_neg : (-p).mirror = -p.mirror
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mirror.eq_1`：∀ {R : Type u_1} [inst : Semiring R] (p : Polyno
mial R), p.mirror = p.reverse * Polynomial.X ^ p.natTrailingDegree
· 使用定理 `Polynomial.reverse_neg`：reverse_neg (f : R[X]) : reverse (-f) = -reverse
 f
· 使用定理 `Polynomial.natTrailingDegree_neg`：natTrailingDegree_neg (p : R[X]) : nat
TrailingDegree (-p) = natTrailingDegree p
· 使用定理 `neg_mul_eq_neg_mul`：neg_mul_eq_neg_mul (a b : α) : -(a * b) = -a * b
-/
theorem mirror_neg : (-p).mirror = -p.mirror := by
  rw [mirror, mirror, reverse_neg, natTrailingDegree_neg, neg_mul_eq_neg_mul]

end Ring

section CommRing

variable {R : Type*} [CommRing R] [NoZeroDivisors R] {f : R[X]}

/-
**Polynomial.irreducible_of_mirror** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：irreducible_of_mirror (h1 : ¬IsUnit f) (h2 : forall k, f * f.mirror = k * 
k.mirror -> k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror) (h3 : IsRelPrime f f.
mirror) : Irreducible f
参数：h1 : ¬IsUnit f；h2 : forall k, f * f.mirror = k * k.mirror -> k = f ∨ k = -f ∨
 k = f.mirror ∨ k = -f.mirror；h3 : IsRelPrime f f.mirror。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mirror_mul_of_domain`：mirror_mul_of_domain : (p * q).mirror =
 p.mirror * q.mirror
· 使用定理 `Polynomial.mirror_mirror`：mirror_mirror : p.mirror.mirror = p
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用定理 `Polynomial.mirror_neg`：mirror_neg : (-p).mirror = -p.mirror
· 使用定理 `dvd_neg`：dvd_neg : a ∣ -b ↔ a ∣ b
-/
theorem irreducible_of_mirror (h1 : ¬IsUnit f)
    (h2 : ∀ k, f * f.mirror = k * k.mirror → k = f ∨ k = -f ∨ k = f.mirror ∨ k = -f.mirror)
    (h3 : IsRelPrime f f.mirror) : Irreducible f := by
  constructor
  · exact h1
  · intro g h fgh
    let k := g * h.mirror
    have key : f * f.mirror = k * k.mirror := by
      rw [fgh, mirror_mul_of_domain, mirror_mul_of_domain, mirror_mirror, mul_assoc, mul_comm h,
        mul_comm g.mirror, mul_assoc, ← mul_assoc]
    have g_dvd_f : g ∣ f := by
      rw [fgh]
      exact dvd_mul_right g h
    have h_dvd_f : h ∣ f := by
      rw [fgh]
      exact dvd_mul_left h g
    have g_dvd_k : g ∣ k := dvd_mul_right g h.mirror
    have h_dvd_k_rev : h ∣ k.mirror := by
      rw [mirror_mul_of_domain, mirror_mirror]
      exact dvd_mul_left h g.mirror
    have hk := h2 k key
    rcases hk with (hk | hk | hk | hk)
    · exact Or.inr (h3 h_dvd_f (by rwa [← hk]))
    · exact Or.inr (h3 h_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, mirror_neg, dvd_neg]))
    · exact Or.inl (h3 g_dvd_f (by rwa [← hk]))
    · exact Or.inl (h3 g_dvd_f (by rwa [← neg_eq_iff_eq_neg.mpr hk, dvd_neg]))

end CommRing

end Polynomial

