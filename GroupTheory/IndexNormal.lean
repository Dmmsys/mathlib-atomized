/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Data.Finite.Perm
public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.GroupTheory.Index

/-! # Subgroups of small index are normal

* `Subgroup.normal_of_index_eq_smallest_prime_factor`: in a finite group `G`,
  a subgroup of index equal to the smallest prime factor of `Nat.card G` is normal.

* `Subgroup.normal_of_index_two`: in a group `G`, a subgroup of index 2 is normal
  (This does not require `G` to be finite.)

-/

public section

assert_not_exists Field

open MulAction MonoidHom Nat

variable {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}

namespace Subgroup

/-- A subgroup of index 1 is normal (does not require finiteness of G) -/
/-
**Subgroup.normal_of_index_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_of_index_eq_one (hH : H.index = 1) : H.Normal
参数：hH : H.index = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subgroup.index_eq_one`：index_eq_one : H.index = 1 ↔ H = ⊤

--- 原说明 ---
A subgroup of index 1 is normal (does not require finiteness of G)
-/
theorem normal_of_index_eq_one (hH : H.index = 1) : H.Normal := by
  rw [index_eq_one] at hH
  rw [hH]
  infer_instance

/-- A subgroup of index 2 is normal (does not require finiteness of G) -/
/-
**Subgroup.normal_of_index_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_of_index_eq_two (hH : H.index = 2) : H.Normal where conj_mem x hxH 
g
参数：hH : H.index = 2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subgroup.mul_mem_iff_of_index_two`：mul_mem_iff_of_index_two (h : H.index
 = 2) {a b : G} : a * b in H ↔ (a in H ↔ b in H)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubgroupClass.toInvMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4)} 
{inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   Inv
MemClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A subgroup of index 2 is normal (does not require finiteness of G)
-/
theorem normal_of_index_eq_two (hH : H.index = 2) : H.Normal where
  conj_mem x hxH g := by simp_rw [mul_mem_iff_of_index_two hH, hxH, iff_true, inv_mem_iff]

/-- A subgroup of a finite group whose index is the smallest prime factor is normal.

Note : if `G` is infinite, then `Nat.card G = 0` and `(Nat.card G).minFac = 2` -/
/-
**Subgroup.normal_of_index_eq_minFac_card** 是 Mathlib 中的一个定理，位于命名空间 `Subgroup`。
形式化陈述：normal_of_index_eq_minFac_card (hHp : H.index = (Nat.card G).minFac) : H.N
ormal
参数：hHp : H.index = (Nat.card G).minFac。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.normal_of_index_eq_two`：normal_of_index_eq_two (hH : H.index = 
2) : H.Normal where conj_mem x hxH g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.minFac_zero`：minFac_zero : minFac 0 = 2
· 使用定理 `Subgroup.normal_of_index_eq_one`：normal_of_index_eq_one (hH : H.index = 
1) : H.Normal
· 使用定理 `Nat.minFac_one`：minFac_one : minFac 1 = 1
· 使用定理 `Nat.finite_of_card_ne_zero`：finite_of_card_ne_zero (h : Nat.card α != 0)
 : Finite α
· 使用定理 `Subgroup.index_ne_zero_of_finite`：index_ne_zero_of_finite [hH : Finite (
G ⧸ H)] : H.index != 0
· 使用定理 `Subgroup.finiteIndex_of_finite`：∀ {G : Type u_1} [inst : Group G] {H : S
ubgroup G} [Finite G], H.FiniteIndex
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subgroup.relIndex_mul_index`：relIndex_mul_index (h : H <= K) : H.relInde
x K * K.index = H.index
· 使用定理 `Subgroup.normalCore_le`：normalCore_le (H : Subgroup G) : H.normalCore <=
 H
· 使用定理 `Nat.minFac_prime`：minFac_prime {n : Nat} (n1 : n != 1) : Prime (minFac n
)
· 使用定理 `Subgroup.normalCore_eq_ker`：normalCore_eq_ker : H.normalCore = (MulActio
n.toPermHom G (G ⧸ H)).ker
· 使用定理 `Subgroup.index_ker`：index_ker (f : G ->* G') : f.ker.index = Nat.card f.
range
· 使用定理 `Subgroup.index_eq_card`：index_eq_card : H.index = Nat.card (G ⧸ H)
· 使用定理 `Nat.card_perm`：card_perm : Nat.card (Perm α) = (Nat.card α)!
· 使用定理 `Subgroup.card_subgroup_dvd_card`：card_subgroup_dvd_card (s : Subgroup α)
 : Nat.card s ∣ Nat.card α
· 使用定理 `dvd_antisymm`：dvd_antisymm : a ∣ b -> b ∣ a -> a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Nat.Coprime.dvd_mul_right`：∀ {m n k : ℕ}, k.Coprime n → (k ∣ m * n ↔ k ∣
 m)
· 使用定理 `Nat.Prime.ne_one`：∀ {p : ℕ}, Nat.Prime p → p ≠ 1
· 使用定理 `Nat.eq_one_of_dvd_one`：∀ {n : ℕ}, n ∣ 1 → n = 1
· 使用定理 `Subgroup.index_dvd_of_le`：index_dvd_of_le (h : H <= K) : K.index ∣ H.ind
ex
· 使用定理 `Nat.coprime_factorial_iff`：coprime_factorial_iff {m n : Nat} (hm : m != 
1) : m.Coprime n ! ↔ n < m.minFac
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Nat.sub_one_lt`：∀ {n : ℕ}, n ≠ 0 → n - 1 < n
· 使用定理 `Nat.Prime.ne_zero`：∀ {n : ℕ}, Nat.Prime n → n ≠ 0
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
A subgroup of a finite group whose index is the smallest prime factor is normal.

Note : if `G` is infinite, then `Nat.card G = 0` and `(Nat.card G).minFac = 2`
-/
theorem normal_of_index_eq_minFac_card (hHp : H.index = (Nat.card G).minFac) :
    H.Normal := by
  by_cases hG0 : Nat.card G = 0
  · rw [hG0, minFac_zero] at hHp
    exact normal_of_index_eq_two hHp
  by_cases hG1 : Nat.card G = 1
  · rw [hG1, minFac_one] at hHp
    exact normal_of_index_eq_one hHp
  suffices H.normalCore.relIndex H = 1 by
    convert! H.normalCore_normal
    exact le_antisymm (relIndex_eq_one.mp this) (normalCore_le H)
  have : Finite G := finite_of_card_ne_zero hG0
  have index_ne_zero : H.index ≠ 0 := index_ne_zero_of_finite
  rw [← mul_left_inj' index_ne_zero, one_mul, relIndex_mul_index H.normalCore_le]
  have hp : Nat.Prime H.index := hHp ▸ minFac_prime hG1
  have h : H.normalCore.index ∣ H.index ! := by
    rw [normalCore_eq_ker, index_ker, index_eq_card, ← Nat.card_perm]
    exact card_subgroup_dvd_card (toPermHom G (G ⧸ H)).range
  apply dvd_antisymm _ (index_dvd_of_le H.normalCore_le)
  rwa [← Coprime.dvd_mul_right, mul_factorial_pred hp.ne_zero]
  have hr1 : H.normalCore.index ≠ 1 := fun hr1 ↦ hp.ne_one <|
    Nat.eq_one_of_dvd_one (hr1 ▸ H.normalCore.index_dvd_of_le H.normalCore_le)
  rw [Nat.coprime_factorial_iff hr1]
  exact lt_of_lt_of_le (Nat.sub_one_lt hp.ne_zero) <|
    hHp ▸ minFac_le_of_dvd (Nat.minFac_prime hr1).two_le
      (dvd_trans (minFac_dvd H.normalCore.index) (H.normalCore.index_dvd_card))

end Subgroup

