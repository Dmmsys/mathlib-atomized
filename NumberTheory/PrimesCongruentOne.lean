/-
Copyright (c) 2020 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval

/-!
# Primes congruent to one

We prove that, for any positive `k : ℕ`, there are infinitely many primes `p` such that
`p ≡ 1 [MOD k]`.
-/

public section


namespace Nat

open Polynomial Nat Filter

open scoped Nat

/-- For any positive `k : ℕ` there exists an arbitrarily large prime `p` such that
`p ≡ 1 [MOD k]`. -/
/-
**Nat.exists_prime_gt_modEq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：exists_prime_gt_modEq_one {k : Nat} (n : Nat) (hk0 : k != 0) : exists p : 
Nat, Nat.Prime p ∧ n < p ∧ p ≡ 1 [MOD k]
参数：n : Nat；hk0 : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `Nat.exists_infinite_primes`：exists_infinite_primes (n : Nat) : exists p,
 n <= p ∧ Prime p
· 使用引理 `Nat.modEq_one`：modEq_one : a ≡ b [MOD 1]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_iff_exists_add'`：∀ {α : Type u} [inst : AddCommMagma α] [inst_1 : Pre
order α] [CanonicallyOrderedAdd α] {a b : α}, a ≤ b ↔ ∃ c, b = c + a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_mul_of_le_of_one_le`：le_mul_of_le_of_one_le [MulLeftMono α] {a b c : 
α} (hbc : b <= c) (ha : 1 <= a) : b <= c * a
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.sub_one_lt_natAbs_cyclotomic_eval`：sub_one_lt_natAbs_cyclotom
ic_eval {n : Nat} {q : Nat} (hn' : 1 < n) (hq : q != 1) : q - 1 < ((cyclotomic n
 Int).eval ↑q).natAbs
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.succ_le_iff`：∀ {m n : ℕ}, m.succ ≤ n ↔ m < n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Polynomial.IsRoot.def`：∀ {R : Type u} {a : R} [inst : Semiring R] {p : P
olynomial R}, p.IsRoot a ↔ Polynomial.eval a p = 0
（共 58 条，此处仅展示前 30 条）

--- 原说明 ---
For any positive `k : ℕ` there exists an arbitrarily large prime `p` such that
`p ≡ 1 [MOD k]`.
-/
theorem exists_prime_gt_modEq_one {k : ℕ} (n : ℕ) (hk0 : k ≠ 0) :
    ∃ p : ℕ, Nat.Prime p ∧ n < p ∧ p ≡ 1 [MOD k] := by
  rcases (one_le_iff_ne_zero.2 hk0).eq_or_lt with (rfl | hk1)
  · rcases exists_infinite_primes (n + 1) with ⟨p, hnp, hp⟩
    exact ⟨p, hp, hnp, modEq_one⟩
  let b := k * (n !)
  have hgt : 1 < (eval (↑b) (cyclotomic k ℤ)).natAbs := by
    rcases le_iff_exists_add'.1 hk1.le with ⟨k, rfl⟩
    have hb : 2 ≤ b := le_mul_of_le_of_one_le hk1 n.factorial_pos
    calc
      1 ≤ b - 1 := le_tsub_of_add_le_left hb
      _ < (eval (b : ℤ) (cyclotomic (k + 1) ℤ)).natAbs :=
        sub_one_lt_natAbs_cyclotomic_eval hk1 (succ_le_iff.1 hb).ne'
  let p := minFac (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hprime : Fact p.Prime := ⟨minFac_prime (ne_of_lt hgt).symm⟩
  have hroot : IsRoot (cyclotomic k (ZMod p)) (castRingHom (ZMod p) b) := by
    have : ((b : ℤ) : ZMod p) = ↑(Int.castRingHom (ZMod p) b) := by simp
    rw [IsRoot.def, ← map_cyclotomic_int k (ZMod p), eval_map, coe_castRingHom,
      ← Int.cast_natCast, this, eval₂_hom, Int.coe_castRingHom, ZMod.intCast_zmod_eq_zero_iff_dvd]
    apply Int.dvd_natAbs.1
    exact mod_cast minFac_dvd (eval (↑b) (cyclotomic k ℤ)).natAbs
  have hpb : ¬p ∣ b :=
    hprime.1.coprime_iff_not_dvd.1 (coprime_of_root_cyclotomic hk0.bot_lt hroot).symm
  refine ⟨p, hprime.1, not_le.1 fun habs => ?_, ?_⟩
  · exact hpb (dvd_mul_of_dvd_right (dvd_factorial (minFac_pos _) habs) _)
  · have hdiv : orderOf (b : ZMod p) ∣ p - 1 :=
      ZMod.orderOf_dvd_card_sub_one (mt (CharP.cast_eq_zero_iff _ _ _).1 hpb)
    have : NeZero (k : ZMod p) :=
      NeZero.of_not_dvd (ZMod p) fun hpk => hpb (dvd_mul_of_dvd_left hpk _)
    have : k = orderOf (b : ZMod p) := (isRoot_cyclotomic_iff.mp hroot).eq_orderOf
    rw [← this] at hdiv
    exact ((modEq_iff_dvd' hprime.1.pos).2 hdiv).symm
/-
**Nat.frequently_atTop_modEq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：frequently_atTop_modEq_one {k : Nat} (hk0 : k != 0) : existsᶠ p in atTop, 
Nat.Prime p ∧ p ≡ 1 [MOD k]
参数：hk0 : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.exists_prime_gt_modEq_one`：exists_prime_gt_modEq_one {k : Nat} (n : 
Nat) (hk0 : k != 0) : exists p : Nat, Nat.Prime p ∧ n < p ∧ p ≡ 1 [MOD k]
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem frequently_atTop_modEq_one {k : ℕ} (hk0 : k ≠ 0) :
    ∃ᶠ p in atTop, Nat.Prime p ∧ p ≡ 1 [MOD k] := by
  refine frequently_atTop.2 fun n => ?_
  obtain ⟨p, hp⟩ := exists_prime_gt_modEq_one n hk0
  exact ⟨p, ⟨hp.2.1.le, hp.1, hp.2.2⟩⟩

/-- For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [MOD k]`. -/
/-
**Nat.infinite_setOfPred_prime_modEq_one** 是 Mathlib 中的一个定理，位于命名空间 `Nat`。
形式化陈述：infinite_setOfPred_prime_modEq_one {k : Nat} (hk0 : k != 0) : Set.Infinite
 {p : Nat | Nat.Prime p ∧ p ≡ 1 [MOD k]}
参数：hk0 : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.frequently_atTop_iff_infinite`：Nat.frequently_atTop_iff_infinite {p 
: Nat -> Prop} : (existsᶠ n in atTop, p n) ↔ Set.Infinite { n | p n }
· 使用定理 `Nat.frequently_atTop_modEq_one`：frequently_atTop_modEq_one {k : Nat} (hk
0 : k != 0) : existsᶠ p in atTop, Nat.Prime p ∧ p ≡ 1 [MOD k]

--- 原说明 ---
For any positive `k : ℕ` there are infinitely many primes `p` such that `p ≡ 1 [
MOD k]`.
-/
theorem infinite_setOfPred_prime_modEq_one {k : ℕ} (hk0 : k ≠ 0) :
    Set.Infinite {p : ℕ | Nat.Prime p ∧ p ≡ 1 [MOD k]} :=
  frequently_atTop_iff_infinite.1 (frequently_atTop_modEq_one hk0)

@[deprecated (since := "2026-07-09")]
alias infinite_setOf_prime_modEq_one := infinite_setOfPred_prime_modEq_one

end Nat

