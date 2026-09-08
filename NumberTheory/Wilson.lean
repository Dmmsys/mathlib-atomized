/-
Copyright (c) 2022 John Nicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Nicol
-/
module

public import Mathlib.FieldTheory.Finite.Basic

/-!
# Wilson's theorem.

This file contains a proof of Wilson's theorem.

The heavy lifting is mostly done by the previous `wilsons_lemma`,
but here we also prove the other logical direction.

This could be generalized to similar results about finite abelian groups.

## References

* [Wilson's Theorem](https://en.wikipedia.org/wiki/Wilson%27s_theorem)

## TODO

* Give `wilsons_lemma` a descriptive name.
-/

public section

assert_not_exists legendreSym.quadratic_reciprocity

open Finset Nat FiniteField ZMod

open scoped Nat

namespace ZMod

variable (p : ℕ) [Fact p.Prime]

/-- **Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`. -/
@[simp]
/-
**ZMod.wilsons_lemma** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：wilsons_lemma : ((p - 1)! : ZMod p) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.prod_Ico_id_eq_factorial`：∀ (n : ℕ), ∏ x ∈ Finset.Ico 1 (n + 1), 
x = n.factorial
· 使用定理 `Finset.prod_natCast`：prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i 
in s, f i : Nat) = ∏ i in s, (f i : R)
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Finset.prod_bij`：prod_bij (i : forall a in s, κ) (hi : forall a ha, i a 
ha in t) (i_inj : forall a₁ ha₁ a₂ ha₂, i a₁ ha₁ = i a₂ ha₂ -> a₁ = a₂) (i_surj 
: for…
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `Nat.succ_sub`：∀ {m n : ℕ}, n ≤ m → m.succ - n = (m - n).succ
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `ZMod.val_injective`：val_injective (n : Nat) [NeZero n] : Function.Inject
ive (val : ZMod n -> Nat)
· 使用定理 `ZMod.val_lt`：val_lt {n : Nat} [NeZero n] (a : ZMod n) : a.val < n
· 使用定理 `Units.ext_iff`：∀ {α : Type u} [inst : Monoid α] {u v : αˣ}, u = v ↔ ↑u =
 ↑v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `pos_iff_ne_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_
1 : Zero α] [IsBotZeroClass α], 0 < a ↔ a ≠ 0
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ZMod.val_cast_of_lt`：val_cast_of_lt {n : Nat} {a : Nat} (h : a < n) : (a
 : ZMod n).val = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Wilson's Lemma**: the product of `1`, ..., `p-1` is `-1` modulo `p`.
-/
theorem wilsons_lemma : ((p - 1)! : ZMod p) = -1 := by
  refine
    calc
      ((p - 1)! : ZMod p) = ∏ x ∈ Ico 1 (succ (p - 1)), (x : ZMod p) := by
        rw [← Finset.prod_Ico_id_eq_factorial, prod_natCast]
      _ = ∏ x : (ZMod p)ˣ, (x : ZMod p) := ?_
      _ = -1 := by
        simp_rw [← Units.coeHom_apply, ← map_prod (Units.coeHom (ZMod p)),
          prod_univ_units_id_eq_neg_one, Units.coeHom_apply, Units.val_neg, Units.val_one]
  have hp : 0 < p := (Fact.out (p := p.Prime)).pos
  symm
  refine prod_bij (fun a _ => (a : ZMod p).val) ?_ ?_ ?_ ?_
  · intro a ha
    rw [mem_Ico, ← Nat.succ_sub hp, Nat.add_one_sub_one]
    constructor
    · apply Nat.pos_of_ne_zero; rw [← @val_zero p]
      intro h; apply Units.ne_zero a (val_injective p h)
    · exact val_lt _
  · intro _ _ _ _ h; rw [Units.ext_iff]; exact val_injective p h
  · intro b hb
    rw [mem_Ico, Nat.succ_le_iff, ← succ_sub hp, Nat.add_one_sub_one, pos_iff_ne_zero] at hb
    refine ⟨Units.mk0 b ?_, Finset.mem_univ _, ?_⟩
    · intro h; apply hb.1; apply_fun val at h
      simpa only [val_cast_of_lt hb.right, val_zero] using h
    · simp only [val_cast_of_lt hb.right, Units.val_mk0]
  · rintro a -; simp only [cast_id, natCast_val]

@[simp]
/-
**ZMod.prod_Ico_one_prime** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：prod_Ico_one_prime : ∏ x in Ico 1 p, (x : ZMod p) = -1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_one_sub_one`：∀ (n : ℕ), n + 1 - 1 = n
· 使用定理 `Nat.succ_sub`：∀ {m n : ℕ}, n ≤ m → m.succ - n = (m - n).succ
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Finset.prod_natCast`：prod_natCast (s : Finset ι) (f : ι -> Nat) : ↑(∏ i 
in s, f i : Nat) = ∏ i in s, (f i : R)
· 使用定理 `Finset.prod_Ico_id_eq_factorial`：∀ (n : ℕ), ∏ x ∈ Finset.Ico 1 (n + 1), 
x = n.factorial
· 使用定理 `ZMod.wilsons_lemma`：wilsons_lemma : ((p - 1)! : ZMod p) = -1
-/
theorem prod_Ico_one_prime : ∏ x ∈ Ico 1 p, (x : ZMod p) = -1 := by
  -- Porting note: was `conv in Ico 1 p =>`
  conv =>
    congr
    congr
    rw [← Nat.add_one_sub_one p, succ_sub (Fact.out (p := p.Prime)).pos]
  rw [← prod_natCast, Finset.prod_Ico_id_eq_factorial, wilsons_lemma]

end ZMod

namespace Nat

variable {n : ℕ}

/-- For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime. -/
/-
**Nat.prime_of_fac_equiv_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n != 1) : 
Prime n
参数：h : ((n - 1)! : ZMod n) = -1；h1 : n != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_natSub`：∀ {a b a' b' c : ℕ},   Mathlib.Meta.N
ormNum.IsNat a a' →     Mathlib.Meta.NormNum.IsNat b b' → a'.sub b' = c → Mathli
b.Meta.NormNum.IsNat (a…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Mathlib.Meta.NormNum.isInt_eq_false`：∀ {α : Type u_1} [inst : Ring α] [C
harZero α] {a b : α} {a' b' : ℤ},   Mathlib.Meta.NormNum.IsInt a a' → Mathlib.Me
ta.NormNum.IsInt b b' → d…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.two_le_iff`：∀ (n : ℕ), 2 ≤ n ↔ n ≠ 0 ∧ n ≠ 1
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Nat.exists_dvd_of_not_prime2`：exists_dvd_of_not_prime2 {n : Nat} (n2 : 2
 <= n) (np : ¬Prime n) : exists m, m ∣ n ∧ 2 <= m ∧ m < n
· 使用定理 `Nat.dvd_factorial`：∀ {m n : ℕ}, 0 < m → m ≤ n → m ∣ n.factorial
· 使用定理 `pos_of_gt`：∀ {α : Type u_1} {a b : α} [inst : Preorder α] [inst_1 : Zero
 α] [IsBotZeroClass α], a < b → 0 < b
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.le_pred_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m.pred
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.dvd_one`：∀ {n : ℕ}, n ∣ 1 ↔ n = 1
· 使用定理 `Nat.dvd_add_right`：∀ {a b c : ℕ}, a ∣ b → (a ∣ b + c ↔ a ∣ c)
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `ZMod.natCast_eq_zero_iff`：natCast_eq_zero_iff (a b : Nat) : (a : ZMod b)
 = 0 ↔ b ∣ a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0

--- 原说明 ---
For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` only if n is prime.
-/
theorem prime_of_fac_equiv_neg_one (h : ((n - 1)! : ZMod n) = -1) (h1 : n ≠ 1) : Prime n := by
  rcases eq_or_ne n 0 with (rfl | h0)
  · norm_num at h
  replace h1 : 1 < n := n.two_le_iff.mpr ⟨h0, h1⟩
  by_contra h2
  obtain ⟨m, hm1, hm2 : 1 < m, hm3⟩ := exists_dvd_of_not_prime2 h1 h2
  have hm : m ∣ (n - 1)! := Nat.dvd_factorial (pos_of_gt hm2) (le_pred_of_lt hm3)
  refine hm2.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hm).mp (hm1.trans ?_)))
  rw [← ZMod.natCast_eq_zero_iff, cast_add, cast_one, h, neg_add_cancel]

/-- **Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff n is prime. -/
/-
**Nat.prime_iff_fac_equiv_neg_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：prime_iff_fac_equiv_neg_one (h : n != 1) : Prime n ↔ ((n - 1)! : ZMod n) =
 -1
参数：h : n != 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ZMod.wilsons_lemma`：wilsons_lemma : ((p - 1)! : ZMod p) = -1
· 使用定理 `Nat.prime_of_fac_equiv_neg_one`：prime_of_fac_equiv_neg_one (h : ((n - 1)
! : ZMod n) = -1) (h1 : n != 1) : Prime n

--- 原说明 ---
**Wilson's Theorem**: For `n ≠ 1`, `(n-1)!` is congruent to `-1` modulo `n` iff 
n is prime.
-/
theorem prime_iff_fac_equiv_neg_one (h : n ≠ 1) : Prime n ↔ ((n - 1)! : ZMod n) = -1 := by
  refine ⟨fun h1 => ?_, fun h2 => prime_of_fac_equiv_neg_one h2 h⟩
  have := Fact.mk h1
  exact ZMod.wilsons_lemma n

end Nat

