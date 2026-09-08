/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Prime.Lemmas

/-!
# Theory of degrees of polynomials

Some of the main results include
- `natDegree_comp_le` : The degree of the composition is at most the product of degrees

-/

public section


noncomputable section

open Polynomial

open Finsupp Finset

namespace Polynomial

universe u v w

variable {R : Type u} {S : Type v} {ι : Type w} {a b : R} {m n : ℕ}

section Semiring

variable [Semiring R] {p q r : R[X]}

section Degree

/-
**Polynomial.natDegree_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_comp_le : natDegree (p.comp q) <= natDegree p * natDegree q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.comp_eq_sum_left`：comp_eq_sum_left : p.comp q = p.sum fun e a
 => C a * q ^ e
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `Polynomial.degree_pow_le`：∀ {R : Type u} [inst : Semiring R] (p : Polyno
mial R) (n : ℕ), (p ^ n).degree ≤ n • p.degree
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `nsmul_le_nsmul_right`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pr
eorder M] [AddLeftMono M] [AddRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), i • a
 ≤ i • b
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 35 条，此处仅展示前 30 条）
-/
theorem natDegree_comp_le : natDegree (p.comp q) ≤ natDegree p * natDegree q :=
  letI := Classical.decEq R
  if h0 : p.comp q = 0 then by rw [h0, natDegree_zero]; exact Nat.zero_le _
  else
    WithBot.coe_le_coe.1 <|
      calc
        ↑(natDegree (p.comp q)) = degree (p.comp q) := (degree_eq_natDegree h0).symm
        _ = _ := congr_arg degree comp_eq_sum_left
        _ ≤ _ := degree_sum_le _ _
        _ ≤ _ :=
          Finset.sup_le fun n hn =>
            calc
              degree (C (coeff p n) * q ^ n) ≤ degree (C (coeff p n)) + degree (q ^ n) :=
                degree_mul_le _ _
              _ ≤ natDegree (C (coeff p n)) + n • degree q :=
                (add_le_add degree_le_natDegree (degree_pow_le _ _))
              _ ≤ natDegree (C (coeff p n)) + n • ↑(natDegree q) := by grw [degree_le_natDegree]
              _ = (n * natDegree q : ℕ) := by
                rw [natDegree_C, Nat.cast_zero, zero_add, nsmul_eq_mul]
                simp
              _ ≤ (natDegree p * natDegree q : ℕ) :=
                WithBot.coe_le_coe.2 <|
                  by gcongr; exact le_natDegree_of_ne_zero (mem_support_iff.1 hn)
/-
**Polynomial.natDegree_comp_eq_of_mul_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natDegree_comp_eq_of_mul_ne_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.
natDegree != 0) : natDegree (p.comp q) = natDegree p * natDegree q
参数：h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.natDegree_comp_le`：natDegree_comp_le : natDegree (p.comp q) <
= natDegree p * natDegree q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero`：natDegree_eq_of_le_of_co
eff_ne_zero (pn : p.natDegree <= n) (p1 : p.coeff n != 0) : p.natDegree = n
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
-/
theorem natDegree_comp_eq_of_mul_ne_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree ≠ 0) :
    natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases hq : natDegree q = 0
  · exact le_antisymm natDegree_comp_le (by simp [hq])
  apply natDegree_eq_of_le_of_coeff_ne_zero natDegree_comp_le
  rwa [coeff_comp_degree_mul_degree hq]
/-
**Polynomial.degree_pos_of_root** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_pos_of_root {p : R[X]} (hp : p != 0) (h : IsRoot p a) : 0 < degree 
p
参数：hp : p != 0；h : IsRoot p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem degree_pos_of_root {p : R[X]} (hp : p ≠ 0) (h : IsRoot p a) : 0 < degree p :=
  lt_of_not_ge fun hlt => by
    have := eq_C_of_degree_le_zero hlt
    rw [IsRoot, this, eval_C] at h
    simp only [h, map_zero] at this
    exact hp this
/-
**Polynomial.natDegree_le_iff_coeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natDegree_le_iff_coeff_eq_zero : p.natDegree <= n ↔ forall N : Nat, n < N 
-> p.coeff N = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem natDegree_le_iff_coeff_eq_zero : p.natDegree ≤ n ↔ ∀ N : ℕ, n < N → p.coeff N = 0 := by
  simp_rw [natDegree_le_iff_degree_le, degree_le_iff_coeff_zero, Nat.cast_lt]
/-
**Polynomial.natDegree_add_le_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_add_le_iff_left {n : Nat} (p q : R[X]) (qn : q.natDegree <= n) :
 (p + q).natDegree <= n ↔ p.natDegree <= n
参数：p q : R[X]；qn : q.natDegree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_le_iff_coeff_eq_zero`：natDegree_le_iff_coeff_eq_zer
o : p.natDegree <= n ↔ forall N : Nat, n < N -> p.coeff N = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.natDegree_add_le_of_degree_le`：natDegree_add_le_of_degree_le 
{p q : R[X]} {n : Nat} (hp : natDegree p <= n) (hq : natDegree q <= n) : natDegr
ee (p + q) <= n
-/
theorem natDegree_add_le_iff_left {n : ℕ} (p q : R[X]) (qn : q.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  refine ⟨fun h => ?_, fun h => natDegree_add_le_of_degree_le h qn⟩
  refine natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
  convert! natDegree_le_iff_coeff_eq_zero.mp h m hm using 1
  rw [coeff_add, natDegree_le_iff_coeff_eq_zero.mp qn _ hm, add_zero]
/-
**Polynomial.natDegree_add_le_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_add_le_iff_right {n : Nat} (p q : R[X]) (pn : p.natDegree <= n) 
: (p + q).natDegree <= n ↔ q.natDegree <= n
参数：p q : R[X]；pn : p.natDegree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.natDegree_add_le_iff_left`：natDegree_add_le_iff_left {n : Nat
} (p q : R[X]) (qn : q.natDegree <= n) : (p + q).natDegree <= n ↔ p.natDegree <=
 n
-/
theorem natDegree_add_le_iff_right {n : ℕ} (p q : R[X]) (pn : p.natDegree ≤ n) :
    (p + q).natDegree ≤ n ↔ q.natDegree ≤ n := by
  rw [add_comm]
  exact natDegree_add_le_iff_left _ _ pn

-- TODO: Do we really want the following two lemmas? They are straightforward consequences of a
-- more atomic lemma
/-
**Polynomial.natDegree_C_mul_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree <= f.natDegree
参数：a : R；f : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
-/
theorem natDegree_C_mul_le (a : R) (f : R[X]) : (C a * f).natDegree ≤ f.natDegree := by
  simpa using natDegree_mul_le (p := C a)
/-
**Polynomial.natDegree_mul_C_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree <= f.natDegree
参数：f : R[X]；a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
-/
theorem natDegree_mul_C_le (f : R[X]) (a : R) : (f * C a).natDegree ≤ f.natDegree := by
  simpa using natDegree_mul_le (q := C a)
/-
**Polynomial.eq_natDegree_of_le_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：eq_natDegree_of_le_mem_support (pn : p.natDegree <= n) (ns : n in p.suppor
t) : p.natDegree = n
参数：pn : p.natDegree <= n；ns : n in p.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.le_natDegree_of_mem_supp`：le_natDegree_of_mem_supp (a : Nat) 
: a in p.support -> a <= natDegree p
-/
theorem eq_natDegree_of_le_mem_support (pn : p.natDegree ≤ n) (ns : n ∈ p.support) :
    p.natDegree = n :=
  le_antisymm pn (le_natDegree_of_mem_supp _ ns)
/-
**Polynomial.natDegree_C_mul_eq_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) : (C a * p).na
tDegree = p.natDegree
参数：au : ai * a = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem natDegree_C_mul_eq_of_mul_eq_one {ai : R} (au : ai * a = 1) :
    (C a * p).natDegree = p.natDegree :=
  le_antisymm (natDegree_C_mul_le a p)
    (calc
      p.natDegree = (1 * p).natDegree := by nth_rw 1 [← one_mul p]
      _ = (C ai * (C a * p)).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ ≤ (C a * p).natDegree := natDegree_C_mul_le ai (C a * p))
/-
**Polynomial.natDegree_mul_C_eq_of_mul_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) : (p * C a).na
tDegree = p.natDegree
参数：au : a * ai = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.natDegree_mul_C_le`：natDegree_mul_C_le (f : R[X]) (a : R) : (
f * C a).natDegree <= f.natDegree
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Polynomial.C_1`：C_1 : C (1 : R) = 1
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem natDegree_mul_C_eq_of_mul_eq_one {ai : R} (au : a * ai = 1) :
    (p * C a).natDegree = p.natDegree :=
  le_antisymm (natDegree_mul_C_le p a)
    (calc
      p.natDegree = (p * 1).natDegree := by nth_rw 1 [← mul_one p]
      _ = (p * C a * C ai).natDegree := by rw [← C_1, ← au, map_mul, ← mul_assoc]
      _ ≤ (p * C a).natDegree := natDegree_mul_C_le (p * C a) ai)

/-- Although not explicitly stated, the assumptions of lemma `natDegree_mul_C_eq_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leadingCoeff ≠ 0`.
-/
/-
**Polynomial.natDegree_mul_C_eq_of_mul_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：natDegree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a != 0) : (p * C a
).natDegree = p.natDegree
参数：h : p.leadingCoeff * a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_natDegree_of_le_mem_support`：eq_natDegree_of_le_mem_suppor
t (pn : p.natDegree <= n) (ns : n in p.support) : p.natDegree = n
· 使用定理 `Polynomial.natDegree_mul_C_le`：natDegree_mul_C_le (f : R[X]) (a : R) : (
f * C a).natDegree <= f.natDegree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a

--- 原说明 ---
Although not explicitly stated, the assumptions of lemma `natDegree_mul_C_eq_of_
mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leadingCoeff ≠ 0`.
-/
theorem natDegree_mul_C_eq_of_mul_ne_zero (h : p.leadingCoeff * a ≠ 0) :
    (p * C a).natDegree = p.natDegree := by
  refine eq_natDegree_of_le_mem_support (natDegree_mul_C_le p a) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_mul_C]

/-- Although not explicitly stated, the assumptions of lemma `natDegree_C_mul_of_mul_ne_zero`
force the polynomial `p` to be non-zero, via `p.leadingCoeff ≠ 0`.
-/
/-
**Polynomial.natDegree_C_mul_of_mul_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natDegree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff != 0) : (C a * p).n
atDegree = p.natDegree
参数：h : a * p.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.eq_natDegree_of_le_mem_support`：eq_natDegree_of_le_mem_suppor
t (pn : p.natDegree <= n) (ns : n in p.support) : p.natDegree = n
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_support_iff`：mem_support_iff : n in p.support ↔ p.coeff n
 != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n

--- 原说明 ---
Although not explicitly stated, the assumptions of lemma `natDegree_C_mul_of_mul
_ne_zero`
force the polynomial `p` to be non-zero, via `p.leadingCoeff ≠ 0`.
-/
theorem natDegree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) :
    (C a * p).natDegree = p.natDegree := by
  refine eq_natDegree_of_le_mem_support (natDegree_C_mul_le a p) ?_
  refine mem_support_iff.mpr ?_
  rwa [coeff_C_mul]
/-
**Polynomial.degree_C_mul_of_mul_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff != 0) : (C a * p).degr
ee = p.degree
参数：h : a * p.leadingCoeff != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_mul'`：degree_mul' (h : leadingCoeff p * leadingCoeff q
 != 0) : degree (p * q) = degree p + degree q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `left_ne_zero_of_mul`：left_ne_zero_of_mul : a * b != 0 -> a != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma degree_C_mul_of_mul_ne_zero (h : a * p.leadingCoeff ≠ 0) : (C a * p).degree = p.degree := by
  rw [degree_mul' (by simpa)]; simp [left_ne_zero_of_mul h]
/-
**Polynomial.natDegree_add_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_add_coeff_mul (f g : R[X]) : (f * g).coeff (f.natDegree + g.natD
egree) = f.coeff f.natDegree * g.coeff g.natDegree
参数：f g : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_mul_degree_add_degree`：coeff_mul_degree_add_degree (p q
 : R[X]) : coeff (p * q) (natDegree p + natDegree q) = leadingCoeff p * leadingC
oeff q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_add_coeff_mul (f g : R[X]) :
    (f * g).coeff (f.natDegree + g.natDegree) = f.coeff f.natDegree * g.coeff g.natDegree := by
  simp only [coeff_natDegree, coeff_mul_degree_add_degree]
/-
**Polynomial.natDegree_lt_coeff_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) : (p * q).c
oeff (m + n) = 0
参数：h : p.natDegree + q.natDegree < m + n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.natDegree_mul_le`：natDegree_mul_le {p q : R[X]} : natDegree (
p * q) <= natDegree p + natDegree q
-/
theorem natDegree_lt_coeff_mul (h : p.natDegree + q.natDegree < m + n) :
    (p * q).coeff (m + n) = 0 :=
  coeff_eq_zero_of_natDegree_lt (natDegree_mul_le.trans_lt h)
/-
**Polynomial.coeff_pow_of_natDegree_le** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_pow_of_natDegree_le (pn : p.natDegree <= n) : (p ^ m).coeff (m * n) 
= p.coeff n ^ m
参数：pn : p.natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.succ_mul`：∀ (n m : ℕ), n.succ * m = n * m + m
· 使用定理 `Polynomial.coeff_mul_add_eq_of_natDegree_le`：coeff_mul_add_eq_of_natDegr
ee_le {df dg : Nat} {f g : R[X]} (hdf : natDegree f <= df) (hdg : natDegree g <=
 dg) : (f * g).coeff (df + dg) = …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.natDegree_pow_le`：natDegree_pow_le {p : R[X]} {n : Nat} : (p 
^ n).natDegree <= n * p.natDegree
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem coeff_pow_of_natDegree_le (pn : p.natDegree ≤ n) :
    (p ^ m).coeff (m * n) = p.coeff n ^ m := by
  induction m with
  | zero => simp
  | succ m hm =>
    rw [pow_succ, pow_succ, ← hm, Nat.succ_mul, coeff_mul_add_eq_of_natDegree_le _ pn]
    refine natDegree_pow_le.trans (le_trans ?_ (le_refl _))
    gcongr
/-
**Polynomial.coeff_pow_eq_ite_of_natDegree_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：coeff_pow_eq_ite_of_natDegree_le_of_le {o : Nat} (pn : natDegree p <= n) (
mno : m * n <= o) : coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0
参数：pn : natDegree p <= n；mno : m * n <= o。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_pow_of_natDegree_le`：coeff_pow_of_natDegree_le (pn : p.
natDegree <= n) : (p ^ m).coeff (m * n) = p.coeff n ^ m
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.natDegree_pow_le_of_le`：natDegree_pow_le_of_le (n : Nat) (hp 
: natDegree p <= m) : natDegree (p ^ n) <= n * m
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem coeff_pow_eq_ite_of_natDegree_le_of_le {o : ℕ}
    (pn : natDegree p ≤ n) (mno : m * n ≤ o) :
    coeff (p ^ m) o = if o = m * n then (coeff p n) ^ m else 0 := by
  rcases eq_or_ne o (m * n) with rfl | h
  · simpa only [ite_true] using coeff_pow_of_natDegree_le pn
  · simpa only [h, ite_false] using coeff_eq_zero_of_natDegree_lt <|
      lt_of_le_of_lt (natDegree_pow_le_of_le m pn) (lt_of_le_of_ne mno h.symm)
/-
**Polynomial.coeff_add_eq_left_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff
 n
参数：qn : q.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem coeff_add_eq_left_of_lt (qn : q.natDegree < n) : (p + q).coeff n = p.coeff n :=
  (coeff_add _ _ _).trans <|
    (congr_arg _ <| coeff_eq_zero_of_natDegree_lt <| qn).trans <| add_zero _
/-
**Polynomial.coeff_add_eq_right_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coef
f n
参数：pn : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Polynomial.coeff_add_eq_left_of_lt`：coeff_add_eq_left_of_lt (qn : q.natD
egree < n) : (p + q).coeff n = p.coeff n
-/
theorem coeff_add_eq_right_of_lt (pn : p.natDegree < n) : (p + q).coeff n = q.coeff n := by
  rw [add_comm]
  exact coeff_add_eq_left_of_lt pn

open scoped Function -- required for scoped `on` notation
/-
**Polynomial.degree_sum_eq_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_sum_eq_of_disjoint (f : S -> R[X]) (s : Finset S) (h : Set.Pairwise
 { i | i in s ∧ f i != 0 } (Ne on degree ∘ f)) : degree (s.sum f) = s.sup fun i 
=> degree (f i)
参数：f : S -> R[X]；s : Finset S；h : Set.Pairwise { i | i in s ∧ f i != 0 } (Ne on 
degree ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sup_eq_right`：sup_eq_right : a ⊔ b = b ↔ a <= b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Polynomial.degree_add_eq_right_of_degree_lt`：degree_add_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p + q) = degree q
· 使用定理 `Finset.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Finset α) : s = ∅
 ∨ s.Nonempty
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `Finset.exists_mem_eq_sup`：exists_mem_eq_sup [OrderBot α] (s : Finset ι) 
(h : s.Nonempty) (f : ι -> α) : exists i, i in s ∧ s.sup f = f i
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 35 条，此处仅展示前 30 条）
-/
theorem degree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on degree ∘ f)) :
    degree (s.sum f) = s.sup fun i => degree (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx IH =>
    simp only [hx, Finset.sum_insert, not_false_iff, Finset.sup_insert]
    specialize IH (h.mono fun _ => by simp +contextual)
    rcases lt_trichotomy (degree (f x)) (degree (s.sum f)) with (H | H | H)
    · rw [← IH, sup_eq_right.mpr H.le, degree_add_eq_right_of_degree_lt H]
    · rcases s.eq_empty_or_nonempty with (rfl | hs)
      · simp
      obtain ⟨y, hy, hy'⟩ := Finset.exists_mem_eq_sup s hs fun i => degree (f i)
      rw [IH, hy'] at H
      by_cases hx0 : f x = 0
      · simp [hx0, IH]
      have hy0 : f y ≠ 0 := by
        contrapose! H
        simpa [H, degree_eq_bot] using hx0
      refine absurd H (h ?_ ?_ fun H => hx ?_)
      · simp [hx0]
      · simp [hy, hy0]
      · exact H.symm ▸ hy
    · rw [← IH, sup_eq_left.mpr H.le, degree_add_eq_left_of_degree_lt H]
/-
**Polynomial.natDegree_sum_eq_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：natDegree_sum_eq_of_disjoint (f : S -> R[X]) (s : Finset S) (h : Set.Pairw
ise { i | i in s ∧ f i != 0 } (Ne on natDegree ∘ f)) : natDegree (s.sum f) = s.s
up fun i => natDegree (f i)
参数：f : S -> R[X]；s : Finset S；h : Set.Pairwise { i | i in s ∧ f i != 0 } (Ne on 
natDegree ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq_some`：natDegree_eq_of_degree_eq_som
e {p : R[X]} {n : Nat} (h : degree p = n) : natDegree p = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_sum_eq_of_disjoint`：degree_sum_eq_of_disjoint (f : S -
> R[X]) (s : Finset S) (h : Set.Pairwise { i | i in s ∧ f i != 0 } (Ne on degree
 ∘ f)) : degree (s.sum f) …
· 使用定理 `Set.Pairwise.imp`：∀ {α : Type u_1} {r p : α → α → Prop} {s : Set α}, s.P
airwise r → (∀ ⦃a b : α⦄, r a b → p a b) → s.Pairwise p
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sup'_eq_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] [inst_1 : OrderBot α] {s : Finset β} (H : s.Nonempty)   (f : β → α), s.sup
' H f = …
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `Finset.coe_sup'`：coe_sup' : ((s.sup' H f : α) : WithBot α) = s.sup ((↑) 
∘ f)
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finset.sup'_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeS
up α] {s : Finset β} (H : s.Nonempty) (f : β → α) {a : α},   s.sup' H f ≤ a ↔ ∀ 
b ∈ s, f…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Finset.sup_eq_bot_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : Semilatti
ceSup α] [inst_1 : OrderBot α] (f : β → α) (S : Finset β),   S.sup f = ⊥ ↔ ∀ s ∈
 S, f s = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 31 条，此处仅展示前 30 条）
-/
theorem natDegree_sum_eq_of_disjoint (f : S → R[X]) (s : Finset S)
    (h : Set.Pairwise { i | i ∈ s ∧ f i ≠ 0 } (Ne on natDegree ∘ f)) :
    natDegree (s.sum f) = s.sup fun i => natDegree (f i) := by
  by_cases! H : ∃ x ∈ s, f x ≠ 0
  · obtain ⟨x, hx, hx'⟩ := H
    have hs : s.Nonempty := ⟨x, hx⟩
    refine natDegree_eq_of_degree_eq_some ?_
    rw [degree_sum_eq_of_disjoint]
    · rw [← Finset.sup'_eq_sup hs, ← Finset.sup'_eq_sup hs,
        Nat.cast_withBot, Finset.coe_sup' hs, ←
        Finset.sup'_eq_sup hs]
      refine le_antisymm ?_ ?_
      · rw [Finset.sup'_le_iff]
        intro b hb
        by_cases hb' : f b = 0
        · simpa [hb'] using! hs
        rw [degree_eq_natDegree hb', Nat.cast_withBot]
        exact Finset.le_sup' (fun i : S => (natDegree (f i) : WithBot ℕ)) hb
      · rw [Finset.sup'_le_iff]
        intro b hb
        simp only [Finset.le_sup'_iff, Function.comp_apply]
        by_cases hb' : f b = 0
        · refine ⟨x, hx, ?_⟩
          contrapose! hx'
          simpa [← Nat.cast_withBot, hb', degree_eq_bot] using! hx'
        exact ⟨b, hb, (degree_eq_natDegree hb').ge⟩
    · exact h.imp fun x y hxy hxy' => hxy (natDegree_eq_of_degree_eq hxy')
  · rw [Finset.sum_eq_zero H, natDegree_zero, eq_comm, show 0 = ⊥ from rfl, Finset.sup_eq_bot_iff]
    intro x hx
    simp [H x hx]

variable [Semiring S]
/-
**Polynomial.natDegree_pos_of_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natDegree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < natDegree p :=
  lt_of_not_ge fun hlt => by
    have A : p = C (p.coeff 0) := eq_C_of_natDegree_le_zero hlt
    rw [A, eval₂_C] at hz
    simp only [inj (p.coeff 0) hz, map_zero] at A
    exact hp A
/-
**Polynomial.degree_pos_of_eval** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem degree_pos_of_eval₂_root {p : R[X]} (hp : p ≠ 0) (f : R →+* S) {z : S}
    (hz : eval₂ f z p = 0) (inj : ∀ x : R, f x = 0 → x = 0) : 0 < degree p :=
  natDegree_pos_iff_degree_pos.mp (natDegree_pos_of_eval₂_root hp f hz inj)

@[simp]
/-
**Polynomial.coe_lt_degree** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coe_lt_degree {p : R[X]} {n : Nat} : (n : WithBot Nat) < degree p ↔ n < na
tDegree p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem coe_lt_degree {p : R[X]} {n : ℕ} : (n : WithBot ℕ) < degree p ↔ n < natDegree p := by
  by_cases h : p = 0
  · simp [h]
  simp [degree_eq_natDegree h, Nat.cast_lt]

@[simp]
/-
**Polynomial.degree_map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_map_eq_iff {f : R ->+* S} {p : Polynomial R} : degree (map f p) = d
egree p ↔ f (leadingCoeff p) != 0 ∨ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_zero`：∀ {R : Type u} {S : Type v} [inst : Semiring R] [in
st_1 : Semiring S] (f : R →+* S), Polynomial.map f 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.degree_map_eq_of_leadingCoeff_ne_zero`：degree_map_eq_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : degree (p.map f)
 = degree p
-/
theorem degree_map_eq_iff {f : R →+* S} {p : Polynomial R} :
    degree (map f p) = degree p ↔ f (leadingCoeff p) ≠ 0 ∨ p = 0 := by
  rcases eq_or_ne p 0 with h | h
  · simp [h]
  simp only [h, or_false]
  refine ⟨fun h2 ↦ ?_, degree_map_eq_of_leadingCoeff_ne_zero f⟩
  have h3 : natDegree (map f p) = natDegree p := by simp_rw [natDegree, h2]
  have h4 : map f p ≠ 0 := by
    rwa [ne_eq, ← degree_eq_bot, h2, degree_eq_bot]
  rwa [← coeff_natDegree, ← coeff_map, ← h3, coeff_natDegree, ne_eq, leadingCoeff_eq_zero]

@[simp]
/-
**Polynomial.natDegree_map_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_map_eq_iff {f : R ->+* S} {p : Polynomial R} : natDegree (map f 
p) = natDegree p ↔ f (p.leadingCoeff) != 0 ∨ natDegree p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem natDegree_map_eq_iff {f : R →+* S} {p : Polynomial R} :
    natDegree (map f p) = natDegree p ↔ f (p.leadingCoeff) ≠ 0 ∨ natDegree p = 0 := by
  rcases eq_or_ne (natDegree p) 0 with h | h
  · simp_rw [h, ne_eq, or_true, iff_true, ← Nat.le_zero, ← h, natDegree_map_le]
  simp_all [natDegree, WithBot.unbotD_eq_unbotD_iff]
/-
**Polynomial.degree_map_eq_of_isUnit_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Pol
ynomial`。
形式化陈述：degree_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S) (hp : I
sUnit p.leadingCoeff) : (p.map f).degree = p.degree
参数：f : R ->+* S；hp : IsUnit p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.degree_map_eq_of_leadingCoeff_ne_zero`：degree_map_eq_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : degree (p.map f)
 = degree p
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
-/
theorem degree_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R →+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).degree = p.degree :=
  degree_map_eq_of_leadingCoeff_ne_zero _ <| f.isUnit_map hp |>.ne_zero
/-
**Polynomial.natDegree_map_eq_of_isUnit_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：natDegree_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S) (hp 
: IsUnit p.leadingCoeff) : (p.map f).natDegree = p.natDegree
参数：f : R ->+* S；hp : IsUnit p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Polynomial.natDegree_eq_natDegree`：natDegree_eq_natDegree {q : S[X]} (hp
q : p.degree = q.degree) : p.natDegree = q.natDegree
· 使用定理 `Polynomial.degree_map_eq_of_isUnit_leadingCoeff`：degree_map_eq_of_isUnit
_leadingCoeff [Nontrivial S] (f : R ->+* S) (hp : IsUnit p.leadingCoeff) : (p.ma
p f).degree = p.degree
-/
theorem natDegree_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R →+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).natDegree = p.natDegree :=
  natDegree_eq_natDegree <| degree_map_eq_of_isUnit_leadingCoeff _ hp
/-
**Polynomial.leadingCoeff_map_eq_of_isUnit_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空
间 `Polynomial`。
形式化陈述：leadingCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S) (
hp : IsUnit p.leadingCoeff) : (p.map f).leadingCoeff = f p.leadingCoeff
参数：f : R ->+* S；hp : IsUnit p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero`：leadingCoeff_map_of
_leadingCoeff_ne_zero (f : R ->+* S) (hf : f (leadingCoeff p) != 0) : leadingCoe
ff (p.map f) = f (leadingCoeff p)
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
-/
theorem leadingCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R →+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).leadingCoeff = f p.leadingCoeff :=
  leadingCoeff_map_of_leadingCoeff_ne_zero _ <| f.isUnit_map hp |>.ne_zero
/-
**Polynomial.nextCoeff_map_eq_of_isUnit_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：nextCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R ->+* S) (hp 
: IsUnit p.leadingCoeff) : (p.map f).nextCoeff = f p.nextCoeff
参数：f : R ->+* S；hp : IsUnit p.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.nextCoeff_map_of_leadingCoeff_ne_zero`：nextCoeff_map_of_leadi
ngCoeff_ne_zero (f : R ->+* S) (hf : f p.leadingCoeff != 0) : (p.map f).nextCoef
f = f p.nextCoeff
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `RingHom.isUnit_map`：isUnit_map (f : α ->+* β) {a : α} : IsUnit a -> IsUn
it (f a)
-/
theorem nextCoeff_map_eq_of_isUnit_leadingCoeff [Nontrivial S] (f : R →+* S)
    (hp : IsUnit p.leadingCoeff) : (p.map f).nextCoeff = f p.nextCoeff :=
  nextCoeff_map_of_leadingCoeff_ne_zero _ <| f.isUnit_map hp |>.ne_zero
/-
**Polynomial.degree_map_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_map_eq_of_injective {f : R ->+* S} (hf : Function.Injective f) (p :
 Polynomial R) : (p.map f).degree = p.degree
参数：hf : Function.Injective f；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
-/
theorem degree_map_eq_of_injective {f : R →+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).degree = p.degree := by
  simp [hf, map_ne_zero_iff, ne_or_eq]
/-
**Polynomial.natDegree_map_eq_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：natDegree_map_eq_of_injective {f : R ->+* S} (hf : Function.Injective f) (
p : Polynomial R) : (p.map f).natDegree = p.natDegree
参数：hf : Function.Injective f；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_map_eq_of_injective`：degree_map_eq_of_injective {f : R
 ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).degree = p.d
egree
-/
theorem natDegree_map_eq_of_injective {f : R →+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).natDegree = p.natDegree :=
  natDegree_eq_of_degree_eq <| degree_map_eq_of_injective hf _
/-
**Polynomial.leadingCoeff_map_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial
`。
形式化陈述：leadingCoeff_map_of_injective {f : R ->+* S} (hf : Function.Injective f) (
p : Polynomial R) : (p.map f).leadingCoeff = f p.leadingCoeff
参数：hf : Function.Injective f；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_map_eq_of_injective`：natDegree_map_eq_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).natDeg
ree = p.natDegree
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem leadingCoeff_map_of_injective {f : R →+* S} (hf : Function.Injective f)
    (p : Polynomial R) : (p.map f).leadingCoeff = f p.leadingCoeff := by
  simp only [leadingCoeff, natDegree_map_eq_of_injective hf, coeff_map]
/-
**Polynomial.nextCoeff_map** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_map {f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R
) : (p.map f).nextCoeff = f p.nextCoeff
参数：hf : Function.Injective f；p : Polynomial R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.natDegree_map_eq_of_injective`：natDegree_map_eq_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).natDeg
ree = p.natDegree
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
-/
theorem nextCoeff_map {f : R →+* S} (hf : Function.Injective f) (p : Polynomial R) :
    (p.map f).nextCoeff = f p.nextCoeff := by
  simp only [hf, nextCoeff, natDegree_map_eq_of_injective]
  split_ifs <;> simp
/-
**Polynomial.natDegree_pos_of_nextCoeff_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：natDegree_pos_of_nextCoeff_ne_zero (h : p.nextCoeff != 0) : 0 < p.natDegre
e
参数：h : p.nextCoeff != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natDegree_pos_of_nextCoeff_ne_zero (h : p.nextCoeff ≠ 0) : 0 < p.natDegree := by
  grind [nextCoeff]

end Degree

end Semiring

section Ring

variable [Ring R] {p q : R[X]}

/-
**Polynomial.natDegree_sub** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub : (p - q).natDegree = (q - p).natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
theorem natDegree_sub : (p - q).natDegree = (q - p).natDegree := by rw [← natDegree_neg, neg_sub]
/-
**Polynomial.natDegree_sub_le_iff_left** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub_le_iff_left (qn : q.natDegree <= n) : (p - q).natDegree <= n
 ↔ p.natDegree <= n
参数：qn : q.natDegree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.natDegree_add_le_iff_left`：natDegree_add_le_iff_left {n : Nat
} (p q : R[X]) (qn : q.natDegree <= n) : (p + q).natDegree <= n ↔ p.natDegree <=
 n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natDegree_sub_le_iff_left (qn : q.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ p.natDegree ≤ n := by
  rw [← natDegree_neg] at qn
  rw [sub_eq_add_neg, natDegree_add_le_iff_left _ _ qn]
/-
**Polynomial.natDegree_sub_le_iff_right** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_sub_le_iff_right (pn : p.natDegree <= n) : (p - q).natDegree <= 
n ↔ q.natDegree <= n
参数：pn : p.natDegree <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_sub`：natDegree_sub : (p - q).natDegree = (q - p).na
tDegree
· 使用定理 `Polynomial.natDegree_sub_le_iff_left`：natDegree_sub_le_iff_left (qn : q.
natDegree <= n) : (p - q).natDegree <= n ↔ p.natDegree <= n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem natDegree_sub_le_iff_right (pn : p.natDegree ≤ n) :
    (p - q).natDegree ≤ n ↔ q.natDegree ≤ n := by rwa [natDegree_sub, natDegree_sub_le_iff_left]
/-
**Polynomial.coeff_sub_eq_left_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff
 n
参数：dg : q.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.coeff_add_eq_left_of_lt`：coeff_add_eq_left_of_lt (qn : q.natD
egree < n) : (p + q).coeff n = p.coeff n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
-/
theorem coeff_sub_eq_left_of_lt (dg : q.natDegree < n) : (p - q).coeff n = p.coeff n := by
  rw [← natDegree_neg] at dg
  rw [sub_eq_add_neg, coeff_add_eq_left_of_lt dg]
/-
**Polynomial.coeff_sub_eq_neg_right_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q
.coeff n
参数：df : p.natDegree < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Polynomial.coeff_add_eq_right_of_lt`：coeff_add_eq_right_of_lt (pn : p.na
tDegree < n) : (p + q).coeff n = q.coeff n
· 使用定理 `Polynomial.coeff_neg`：coeff_neg (p : R[X]) (n : Nat) : coeff (-p) n = -c
oeff p n
-/
theorem coeff_sub_eq_neg_right_of_lt (df : p.natDegree < n) : (p - q).coeff n = -q.coeff n := by
  rwa [sub_eq_add_neg, coeff_add_eq_right_of_lt, coeff_neg]

end Ring

section NoZeroDivisors

variable [Semiring R] {p q : R[X]} {a : R}

@[simp]
/-
**Polynomial.nextCoeff_C_mul_X_add_C** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_C_mul_X_add_C (ha : a != 0) (c : R) : nextCoeff (C a * X + C c) 
= c
参数：ha : a != 0；c : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.nextCoeff_of_natDegree_pos`：nextCoeff_of_natDegree_pos (hp : 
0 < p.natDegree) : nextCoeff p = p.coeff (p.natDegree - 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.natDegree_add_C`：∀ {R : Type u} [inst : Semiring R] {p : Poly
nomial R} {a : R}, (p + Polynomial.C a).natDegree = p.natDegree
· 使用定理 `Polynomial.natDegree_C_mul_X`：natDegree_C_mul_X (a : R) (ha : a != 0) : 
natDegree (C a * X) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma nextCoeff_C_mul_X_add_C (ha : a ≠ 0) (c : R) : nextCoeff (C a * X + C c) = c := by
  rw [nextCoeff_of_natDegree_pos] <;> simp [ha]
/-
**Polynomial.natDegree_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_eq_one : p.natDegree = 1 ↔ exists a != 0, exists b, C a * X + C 
b = p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.mul_coeff_zero`：mul_coeff_zero (p q : R[X]) : coeff (p * q) 0
 = coeff p 0 * coeff q 0
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `Polynomial.coeff_X_zero`：coeff_X_zero : coeff (X : R[X]) 0 = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.coeff_mul_X`：coeff_mul_X (p : R[X]) (n : Nat) : coeff (p * X)
 (n + 1) = coeff p n
· 使用引理 `Polynomial.coeff_C_succ`：coeff_C_succ {r : R} {n : Nat} : coeff (C r) (n
 + 1) = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Polynomial.coeff_eq_zero_of_natDegree_lt`：coeff_eq_zero_of_natDegree_lt 
{p : R[X]} {n : Nat} (h : p.natDegree < n) : p.coeff n = 0
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
（共 34 条，此处仅展示前 30 条）
-/
lemma natDegree_eq_one : p.natDegree = 1 ↔ ∃ a ≠ 0, ∃ b, C a * X + C b = p := by
  refine ⟨fun hp ↦ ⟨p.coeff 1, fun h ↦ ?_, p.coeff 0, ?_⟩, ?_⟩
  · rw [← hp, coeff_natDegree, leadingCoeff_eq_zero] at h
    simp_all
  · ext n
    obtain _ | _ | n := n
    · simp
    · simp
    · simp only [coeff_add, coeff_mul_X, coeff_C_succ, add_zero]
      rw [coeff_eq_zero_of_natDegree_lt]
      simp [hp]
  · rintro ⟨a, ha, b, rfl⟩
    simp [ha]
/-
**Polynomial.subsingleton_isRoot_of_natDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `
Polynomial`。
形式化陈述：subsingleton_isRoot_of_natDegree_eq_one [IsLeftCancelMulZero R] (h : p.nat
Degree = 1) : { x | IsRoot p x }.Subsingleton
参数：h : p.natDegree = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.natDegree_eq_one`：natDegree_eq_one : p.natDegree = 1 ↔ exists
 a != 0, exists b, C a * X + C b = p
· 使用定理 `mul_left_cancel₀`：mul_left_cancel₀ (ha : a != 0) (h : a * b = a * c) : b
 = c
-/
theorem subsingleton_isRoot_of_natDegree_eq_one [IsLeftCancelMulZero R]
    (h : p.natDegree = 1) : { x | IsRoot p x }.Subsingleton := by
  intro r₁
  obtain ⟨r₂, hr₂, r₃, rfl⟩ : ∃ a, a ≠ 0 ∧ ∃ b, C a * X + C b = p := by rwa [natDegree_eq_one] at h
  have (x y : R) := mul_left_cancel₀ hr₂ (b := x) (c := y)
  grind [IsRoot, eval_add, eval_mul_X, eval_C]

variable [NoZeroDivisors R]
/-
**Polynomial.degree_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_C (a0 : a != 0) : (p * C a).degree = p.degree
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem degree_mul_C (a0 : a ≠ 0) : (p * C a).degree = p.degree := by
  rw [degree_mul, degree_C a0, add_zero]
/-
**Polynomial.degree_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_C_mul (a0 : a != 0) : (C a * p).degree = p.degree
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem degree_C_mul (a0 : a ≠ 0) : (C a * p).degree = p.degree := by
  rw [degree_mul, degree_C a0, zero_add]
/-
**Polynomial.natDegree_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_mul_C (a0 : a != 0) : (p * C a).natDegree = p.natDegree
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_mul_C`：degree_mul_C (a0 : a != 0) : (p * C a).degree =
 p.degree
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_mul_C (a0 : a ≠ 0) : (p * C a).natDegree = p.natDegree := by
  simp only [natDegree, degree_mul_C a0]
/-
**Polynomial.natDegree_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_C_mul (a0 : a != 0) : (C a * p).natDegree = p.natDegree
参数：a0 : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_C_mul`：degree_C_mul (a0 : a != 0) : (C a * p).degree =
 p.degree
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_C_mul (a0 : a ≠ 0) : (C a * p).natDegree = p.natDegree := by
  simp only [natDegree, degree_C_mul a0]
/-
**Polynomial.natDegree_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.degree_le_zero_iff`：degree_le_zero_iff : degree p <= 0 ↔ p = 
C (coeff p 0)
· 使用定理 `Polynomial.natDegree_eq_zero_iff_degree_le_zero`：natDegree_eq_zero_iff_d
egree_le_zero : p.natDegree = 0 ↔ p.degree <= 0
· 使用定理 `Polynomial.comp_C`：comp_C : p.comp (C a) = C (p.eval a)
· 使用定理 `Polynomial.natDegree_C`：natDegree_C (a : R) : natDegree (C a) = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.natDegree_comp_eq_of_mul_ne_zero`：natDegree_comp_eq_of_mul_ne
_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0) : natDegree (p.co
mp q) = natDegree p * natDegree q
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `Polynomial.ne_zero_of_natDegree_gt`：ne_zero_of_natDegree_gt {n : Nat} (h
 : n < natDegree p) : p != 0
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
theorem natDegree_comp : natDegree (p.comp q) = natDegree p * natDegree q := by
  by_cases q0 : q.natDegree = 0
  · rw [degree_le_zero_iff.mp (natDegree_eq_zero_iff_degree_le_zero.mp q0), comp_C, natDegree_C,
      natDegree_C, mul_zero]
  · by_cases p0 : p = 0
    · simp only [p0, zero_comp, natDegree_zero, zero_mul]
    · simp only [Ne, mul_eq_zero, leadingCoeff_eq_zero, p0, natDegree_comp_eq_of_mul_ne_zero,
        ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero q0), not_false_eq_true, pow_ne_zero, or_self]

@[simp]
/-
**Polynomial.natDegree_iterate_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_iterate_comp (k : Nat) : (p.comp^[k] q).natDegree = p.natDegree 
^ k * q.natDegree
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
theorem natDegree_iterate_comp (k : ℕ) :
    (p.comp^[k] q).natDegree = p.natDegree ^ k * q.natDegree := by
  induction k with
  | zero => simp
  | succ k IH => rw [Function.iterate_succ_apply', natDegree_comp, IH, pow_succ', mul_assoc]
/-
**Polynomial.leadingCoeff_comp** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：leadingCoeff_comp (hq : natDegree q != 0) : leadingCoeff (p.comp q) = lead
ingCoeff p * leadingCoeff q ^ natDegree p
参数：hq : natDegree q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
-/
theorem leadingCoeff_comp (hq : natDegree q ≠ 0) :
    leadingCoeff (p.comp q) = leadingCoeff p * leadingCoeff q ^ natDegree p := by
  rw [← coeff_comp_degree_mul_degree hq, ← natDegree_comp, coeff_natDegree]

@[simp]
/-
**Polynomial.nextCoeff_C_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_C_mul : (C a * p).nextCoeff = a * p.nextCoeff
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Polynomial.natDegree_C_mul`：natDegree_C_mul (a0 : a != 0) : (C a * p).na
tDegree = p.natDegree
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
-/
theorem nextCoeff_C_mul : (C a * p).nextCoeff = a * p.nextCoeff := by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_C_mul]

@[simp]
/-
**Polynomial.nextCoeff_mul_C** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：nextCoeff_mul_C : (p * C a).nextCoeff = p.nextCoeff * a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Polynomial.natDegree_mul_C`：natDegree_mul_C (a0 : a != 0) : (p * C a).na
tDegree = p.natDegree
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.coeff_mul_C`：coeff_mul_C (p : R[X]) (n : Nat) (a : R) : coeff
 (p * C a) n = coeff p n * a
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
theorem nextCoeff_mul_C : (p * C a).nextCoeff = p.nextCoeff * a := by
  by_cases h₀ : a = 0 <;> simp [h₀, nextCoeff, natDegree_mul_C]

end NoZeroDivisors

/-
**Polynomial.comp_neg_X_leadingCoeff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Ring R] (p : Polynomial R),   (p.comp (-Polynomial.
X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff
参数：p : Polynomial R；p.comp (-Polynomial.X)；-1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.natDegree_of_subsingleton`：natDegree_of_subsingleton [Subsing
leton R] : natDegree p = 0
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree_comp_eq_of_mul_ne_zero`：natDegree_comp_eq_of_mul_ne
_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0) : natDegree (p.co
mp q) = natDegree p * natDegree q
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Polynomial.coeff_comp_degree_mul_degree`：coeff_comp_degree_mul_degree (h
qd0 : natDegree q != 0) : coeff (p.comp q) (natDegree p * natDegree q) = leading
Coeff p * leadingCoeff q ^ na…
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `Commute.neg_one_left`：neg_one_left (a : R) : Commute (-1) a
-/
@[simp] lemma comp_neg_X_leadingCoeff_eq [Ring R] (p : R[X]) :
    (p.comp (-X)).leadingCoeff = (-1) ^ p.natDegree * p.leadingCoeff := by
  nontriviality R
  by_cases h : p = 0
  · simp [h]
  rw [Polynomial.leadingCoeff, natDegree_comp_eq_of_mul_ne_zero, coeff_comp_degree_mul_degree] <;>
  simp [((Commute.neg_one_left _).pow_left _).eq, h]

@[simp]
/-
**Polynomial.comp_neg_X_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：comp_neg_X_eq_zero_iff [Ring R] {p : R[X]} : p.comp (-X) = 0 ↔ p = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.comp_neg_X_leadingCoeff_eq`：∀ {R : Type u} [inst : Ring R] (p
 : Polynomial R),   (p.comp (-Polynomial.X)).leadingCoeff = (-1) ^ p.natDegree *
 p.leadingCoeff
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_neg_X_eq_zero_iff [Ring R] {p : R[X]} : p.comp (-X) = 0 ↔ p = 0 := by
  simp [← leadingCoeff_eq_zero]
/-
**Polynomial.comp_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：comp_eq_zero_iff [Semiring R] [NoZeroDivisors R] {p q : R[X]} : p.comp q =
 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `Polynomial.natDegree_zero`：natDegree_zero : natDegree (0 : R[X]) = 0
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `Polynomial.eq_C_of_natDegree_eq_zero`：eq_C_of_natDegree_eq_zero (h : nat
Degree p = 0) : p = C (coeff p 0)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.C_comp`：C_comp : (C a).comp p = C a
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `Polynomial.comp_C`：comp_C : p.comp (C a) = C (p.eval a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
-/
lemma comp_eq_zero_iff [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
    p.comp q = 0 ↔ p = 0 ∨ p.eval (q.coeff 0) = 0 ∧ q = C (q.coeff 0) := by
  refine ⟨fun h ↦ ?_, Or.rec (fun h ↦ by simp [h]) fun h ↦ by rw [h.2, comp_C, h.1, C_0]⟩
  have key : p.natDegree = 0 ∨ q.natDegree = 0 := by
    rw [← mul_eq_zero, ← natDegree_comp, h, natDegree_zero]
  obtain key | key := Or.imp eq_C_of_natDegree_eq_zero eq_C_of_natDegree_eq_zero key
  · rw [key, C_comp] at h
    exact Or.inl (key.trans h)
  · rw [key, comp_C, C_eq_zero] at h
    exact Or.inr ⟨h, key⟩
/-
**Polynomial.degree_comp** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_comp [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hq : 0 < q.degre
e) : (p.comp q).degree = p.degree * q.degree
参数：hq : 0 < q.degree。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `WithBot.bot_mul'`：∀ {α : Type u_1} [inst : DecidableEq α] [inst_1 : MulZ
eroClass α] (b : WithBot α), ⊥ * b = if b = 0 then 0 else ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma degree_comp [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hq : 0 < q.degree) :
    (p.comp q).degree = p.degree * q.degree := by
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp, degree_zero, WithBot.bot_mul']
    simp [hq.ne']
  rw [degree_eq_natDegree hp, degree_eq_natDegree (ne_zero_of_degree_gt hq), ← Nat.cast_mul,
    ← natDegree_comp]
  apply degree_eq_natDegree
  simp_rw [Ne, comp_eq_zero_iff, hp, false_or, not_and_or, ← degree_le_zero_iff]
  simp [hq]
/-
**Polynomial.degree_comp_neg_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {p : Polynomial R}, (p.comp (-Polynomial.X)
).degree = p.degree
参数：p.comp (-Polynomial.X)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_of_subsingleton`：degree_of_subsingleton [Subsingleton 
R] : degree p = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Polynomial.natDegree_comp_eq_of_mul_ne_zero`：natDegree_comp_eq_of_mul_ne
_zero (h : p.leadingCoeff * q.leadingCoeff ^ p.natDegree != 0) : natDegree (p.co
mp q) = natDegree p * natDegree q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.leadingCoeff_neg`：leadingCoeff_neg (p : R[X]) : (-p).leadingC
oeff = -p.leadingCoeff
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `Polynomial.natDegree_neg`：natDegree_neg (p : R[X]) : natDegree (-p) = na
tDegree p
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
@[simp] lemma degree_comp_neg_X [Ring R] {p : R[X]} : (p.comp (-X)).degree = p.degree := by
  nontriviality R
  rcases eq_or_ne p 0 with rfl | hp
  · rw [zero_comp]
  rw [degree_eq_natDegree (by simp [hp]), degree_eq_natDegree hp, Nat.cast_inj,
    natDegree_comp_eq_of_mul_ne_zero (by simp [hp]), natDegree_neg, natDegree_X, mul_one]

section DivisionRing

variable {K : Type*} [DivisionRing K]

/-! Useful lemmas for the "monicization" of a nonzero polynomial `p`. -/
@[simp]
/-
**Polynomial.irreducible_mul_leadingCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：irreducible_mul_leadingCoeff_inv {p : K[X]} : Irreducible (p * C (leadingC
oeff p)⁻¹) ↔ Irreducible p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `irreducible_mul_isUnit`：irreducible_mul_isUnit (h : IsUnit x) : Irreduci
ble (y * x) ↔ Irreducible y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.isUnit_C`：isUnit_C {x : R} : IsUnit (C x) ↔ IsUnit x
· 使用定理 `IsUnit.mk0`：IsUnit.mk0 (x : G₀) (hx : x != 0) : IsUnit x
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0

--- 原说明 ---
Useful lemmas for the "monicization" of a nonzero polynomial `p`.
-/
theorem irreducible_mul_leadingCoeff_inv {p : K[X]} :
    Irreducible (p * C (leadingCoeff p)⁻¹) ↔ Irreducible p := by
  by_cases hp0 : p = 0
  · simp [hp0]
  exact irreducible_mul_isUnit
    (isUnit_C.mpr (IsUnit.mk0 _ (inv_ne_zero (leadingCoeff_ne_zero.mpr hp0))))
/-
**Polynomial.dvd_mul_leadingCoeff_inv** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：dvd_mul_leadingCoeff_inv {p q : K[X]} (hp0 : p != 0) : q ∣ p * C (leadingC
oeff p)⁻¹ ↔ q ∣ p
参数：hp0 : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `instIsLocalHomOfMonoidWithZeroHomClassOfNontrivial`：∀ {M₀ : Type u_2} {G
₀ : Type u_3} {F : Type u_6} [inst : MonoidWithZero M₀] [inst_1 : GroupWithZero 
G₀]   [inst_2 : FunLike F G₀ M₀] [Monoid…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dvd_mul_leadingCoeff_inv {p q : K[X]} (hp0 : p ≠ 0) :
    q ∣ p * C (leadingCoeff p)⁻¹ ↔ q ∣ p := by
  simp [hp0]
/-
**Polynomial.monic_mul_leadingCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_mul_leadingCoeff_inv {p : K[X]} (h : p != 0) : Monic (p * C (leading
Coeff p)⁻¹)
参数：h : p != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.Monic.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomia
l R), p.Monic = (p.leadingCoeff = 1)
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
-/
theorem monic_mul_leadingCoeff_inv {p : K[X]} (h : p ≠ 0) : Monic (p * C (leadingCoeff p)⁻¹) := by
  rw [Monic, leadingCoeff_mul, leadingCoeff_C,
    mul_inv_cancel₀ (show leadingCoeff p ≠ 0 from mt leadingCoeff_eq_zero.1 h)]

-- `simp` normal form of `degree_mul_leadingCoeff_inv`
/-
**Polynomial.degree_leadingCoeff_inv** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：degree_leadingCoeff_inv {p : K[X]} (hp0 : p != 0) : degree (C (leadingCoef
f p)⁻¹) = 0
参数：hp0 : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_C`：degree_C (ha : a != 0) : degree (C a) = (0 : WithBo
t Nat)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma degree_leadingCoeff_inv {p : K[X]} (hp0 : p ≠ 0) :
    degree (C (leadingCoeff p)⁻¹) = 0 := by
  simp [hp0]
/-
**Polynomial.degree_mul_leadingCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q != 0) : degree (p
 * C (leadingCoeff q)⁻¹) = degree p
参数：p : K[X]；h : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_ne_zero`：inv_ne_zero (h : a != 0) : a⁻¹ != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.leadingCoeff_eq_zero`：leadingCoeff_eq_zero : leadingCoeff p =
 0 ↔ p = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_mul_C`：degree_mul_C (a0 : a != 0) : (p * C a).degree =
 p.degree
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
-/
theorem degree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q ≠ 0) :
    degree (p * C (leadingCoeff q)⁻¹) = degree p := by
  have h₁ : (leadingCoeff q)⁻¹ ≠ 0 := inv_ne_zero (mt leadingCoeff_eq_zero.1 h)
  rw [degree_mul_C h₁]
/-
**Polynomial.natDegree_mul_leadingCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：natDegree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q != 0) : natDeg
ree (p * C (leadingCoeff q)⁻¹) = natDegree p
参数：p : K[X]；h : q != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
-/
theorem natDegree_mul_leadingCoeff_inv (p : K[X]) {q : K[X]} (h : q ≠ 0) :
    natDegree (p * C (leadingCoeff q)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_inv _ h)
/-
**Polynomial.degree_mul_leadingCoeff_self_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：degree_mul_leadingCoeff_self_inv (p : K[X]) : degree (p * C (leadingCoeff 
p)⁻¹) = degree p
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_zero`：∀ {G₀ : Type u} [inst : GroupWithZero G₀], 0⁻¹ = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.degree_mul_leadingCoeff_inv`：degree_mul_leadingCoeff_inv (p :
 K[X]) {q : K[X]} (h : q != 0) : degree (p * C (leadingCoeff q)⁻¹) = degree p
-/
theorem degree_mul_leadingCoeff_self_inv (p : K[X]) :
    degree (p * C (leadingCoeff p)⁻¹) = degree p := by
  by_cases hp : p = 0
  · simp [hp]
  exact degree_mul_leadingCoeff_inv _ hp
/-
**Polynomial.natDegree_mul_leadingCoeff_self_inv** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：natDegree_mul_leadingCoeff_self_inv (p : K[X]) : natDegree (p * C (leading
Coeff p)⁻¹) = natDegree p
参数：p : K[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.natDegree_eq_of_degree_eq`：natDegree_eq_of_degree_eq [Semirin
g S] {q : S[X]} (h : degree p = degree q) : natDegree p = natDegree q
· 使用定理 `Polynomial.degree_mul_leadingCoeff_self_inv`：degree_mul_leadingCoeff_sel
f_inv (p : K[X]) : degree (p * C (leadingCoeff p)⁻¹) = degree p
-/
theorem natDegree_mul_leadingCoeff_self_inv (p : K[X]) :
    natDegree (p * C (leadingCoeff p)⁻¹) = natDegree p :=
  natDegree_eq_of_degree_eq (degree_mul_leadingCoeff_self_inv _)

-- `simp` normal form of `degree_mul_leadingCoeff_self_inv`
/-
**Polynomial.degree_add_degree_leadingCoeff_inv** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：∀ {K : Type u_1} [inst : DivisionRing K] (p : Polynomial K),   p.degree + 
(Polynomial.C p.leadingCoeff⁻¹).degree = p.degree
参数：p : Polynomial K；Polynomial.C p.leadingCoeff⁻¹。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Polynomial.degree_mul`：degree_mul : degree (p * q) = degree p + degree q
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `Polynomial.degree_mul_leadingCoeff_self_inv`：degree_mul_leadingCoeff_sel
f_inv (p : K[X]) : degree (p * C (leadingCoeff p)⁻¹) = degree p
-/
@[simp] lemma degree_add_degree_leadingCoeff_inv (p : K[X]) :
    degree p + degree (C (leadingCoeff p)⁻¹) = degree p := by
  rw [← degree_mul, degree_mul_leadingCoeff_self_inv]

end DivisionRing

end Polynomial

