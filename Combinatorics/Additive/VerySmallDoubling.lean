/-
Copyright (c) 2024 Yaël Dillies, Patrick Luo, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo, Bhavik Mehta
-/
module

public import Mathlib.Algebra.Pointwise.Stabilizer
public import Mathlib.Combinatorics.Additive.Convolution
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Qify

/-!
# Sets with very small doubling

For a finset `A` in a group, its *doubling* is `#(A * A) / #A`. This file characterises sets with
* no doubling as the sets which are either empty or translates of a subgroup.
  For the converse, use the existing facts from the pointwise API: `∅ ^ 2 = ∅` (`Finset.empty_pow`),
  `(a • H) ^ 2 = a ^ 2 • H ^ 2 = a ^ 2 • H` (`smul_pow`, `coe_set_pow`).
* doubling strictly less than `3 / 2` as the sets that are contained in a coset of a subgroup of
  size strictly less than `3 / 2 * #A`.
* doubling strictly less than `φ` as the set `A` such that `A * A⁻¹` is covered by at most some
  constant (depending only on the doubling) number of cosets of a finite subgroup of `G`.

## TODO

* Do we need versions stated using the doubling constant (`Finset.mulConst`)?
* Add characterisation of sets with doubling ≤ 2 - ε. See
  https://terrytao.wordpress.com/2011/03/12/hamidounes-freiman-kneser-theorem-for-nonabelian-groups.

## References

* [*An elementary non-commutative Freiman theorem*, Terence Tao](https://terrytao.wordpress.com/2009/11/10/an-elementary-non-commutative-freiman-theorem)
* [*Introduction to approximate groups*, Matthew Tointon][tointon2020]
-/

@[expose] public section

open MulOpposite MulAction
open scoped Pointwise RightActions

namespace Finset
variable {G : Type*} [Group G] [DecidableEq G] {K : ℝ} {A B S : Finset G} {a b c d x y : G}

/-! ### Doubling exactly `1` -/

@[to_additive]
/-
**Finset.smul_stabilizer_of_no_doubling_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Doubling exactly `1`
-/
private lemma smul_stabilizer_of_no_doubling_aux (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A ∧ (stabilizer G A : Set G) <• a = A := by
  have smul_A {a} (ha : a ∈ A) : a •> A = A * A :=
    eq_of_subset_of_card_le (smul_finset_subset_mul ha) (by simpa)
  have A_smul {a} (ha : a ∈ A) : A <• a = A * A :=
    eq_of_subset_of_card_le (op_smul_finset_subset_mul ha) (by simpa)
  have smul_A_eq_A_smul {a} (ha : a ∈ A) : a •> A = A <• a := by rw [smul_A ha, A_smul ha]
  have mul_mem_A_comm {x a} (ha : a ∈ A) : x * a ∈ A ↔ a * x ∈ A := by
    rw [← smul_mem_smul_finset_iff a, smul_A_eq_A_smul ha, ← op_smul_eq_mul, smul_comm,
      smul_mem_smul_finset_iff, smul_eq_mul]
  let H := stabilizer G A
  have inv_smul_A {a} (ha : a ∈ A) : a⁻¹ • (A : Set G) = H := by
    ext x
    rw [Set.mem_inv_smul_set_iff, smul_eq_mul]
    refine ⟨fun hx ↦ ?_, fun hx ↦ ?_⟩
    · simpa [← smul_A ha, mul_smul] using! smul_A hx
    · norm_cast
      rwa [← mul_mem_A_comm ha, ← smul_eq_mul, ← mem_inv_smul_finset_iff, inv_mem hx]
  refine ⟨?_, ?_⟩
  · rw [← inv_smul_A ha, smul_inv_smul]
  · rw [← inv_smul_A ha, smul_comm]
    norm_cast
    rw [← smul_A_eq_A_smul ha, inv_smul_smul]

/-- A non-empty set with no doubling is the left translate of its stabilizer. -/
@[to_additive /-- A non-empty set with no doubling is the left-translate of its stabilizer. -/]
/-
**Finset.smul_stabilizer_of_no_doubling** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_stabilizer_of_no_doubling (hA : #(A * A) <= #A) (ha : a in A) : a •> 
(stabilizer G A : Set G) = A
参数：hA : #(A * A) <= #A；ha : a in A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.smul_
stabilizer_of_no_doubling_aux`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decid
ableEq G] {A : Finset G} {a : G},   (A * A).card ≤ A.card →     a ∈ A → a • ↑(Mu
lAction.sta…

--- 原说明 ---
A non-empty set with no doubling is the left translate of its stabilizer.
-/
lemma smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    a •> (stabilizer G A : Set G) = A := (smul_stabilizer_of_no_doubling_aux hA ha).1

/-- A non-empty set with no doubling is the right translate of its stabilizer. -/
@[to_additive /-- A non-empty set with no doubling is the right translate of its stabilizer. -/]
/-
**Finset.op_smul_stabilizer_of_no_doubling** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：op_smul_stabilizer_of_no_doubling (hA : #(A * A) <= #A) (ha : a in A) : (s
tabilizer G A : Set G) <• a = A
参数：hA : #(A * A) <= #A；ha : a in A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.smul_
stabilizer_of_no_doubling_aux`：∀ {G : Type u_1} [inst : Group G] [inst_1 : Decid
ableEq G] {A : Finset G} {a : G},   (A * A).card ≤ A.card →     a ∈ A → a • ↑(Mu
lAction.sta…

--- 原说明 ---
A non-empty set with no doubling is the right translate of its stabilizer.
-/
lemma op_smul_stabilizer_of_no_doubling (hA : #(A * A) ≤ #A) (ha : a ∈ A) :
    (stabilizer G A : Set G) <• a = A := (smul_stabilizer_of_no_doubling_aux hA ha).2

/-! ### Doubling strictly less than `3 / 2` -/

/-
**Finset.big_intersection** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Doubling strictly less than `3 / 2`
-/
private lemma big_intersection (ha : a ∈ B) (hb : b ∈ B) :
    2 * #A ≤ #((a • A) ∩ (b • A)) + #(B * A) := by
  have : #((a • A) ∪ (b • A)) ≤ #(B * A) := by
    gcongr
    rw [union_subset_iff]
    exact ⟨smul_finset_subset_mul ha, smul_finset_subset_mul hb⟩
  grw [← this, card_inter_add_card_union]
  simp [card_smul_finset, two_mul]
/-
**Finset.le_card_smul_inter_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le_card_smul_inter_smul (hA : #(B * A) ≤ K * #A) (ha : a ∈ B) (hb : b ∈ B) :
    (2 - K) * #A ≤ #((a • A) ∩ (b • A)) := by
  have : 2 * (#A : ℝ) ≤ #(a •> A ∩ b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith
/-
**Finset.lt_card_smul_inter_smul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lt_card_smul_inter_smul (hA : #(B * A) < K * #A) (ha : a ∈ B) (hb : b ∈ B) :
    (2 - K) * #A < #((a • A) ∩ (b • A)) := by
  have : 2 * (#A : ℝ) ≤ #(a •> A ∩ b •> A) + #(B * A) := mod_cast big_intersection ha hb; linarith
/-
**Finset.le_card_mul_inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma le_card_mul_inv_eq (hA : #(B * A) ≤ K * #A) (hx : x ∈ B⁻¹ * B) :
    (2 - K) * #A ≤ #{ab ∈ A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using le_card_smul_inter_smul hA ha hb
/-
**Finset.lt_card_mul_inv_eq** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lt_card_mul_inv_eq (hA : #(B * A) < K * #A) (hx : x ∈ B⁻¹ * B) :
    (2 - K) * #A < #{ab ∈ A ×ˢ A | ab.1 * ab.2⁻¹ = x} := by
  simp only [mem_mul, mem_inv, exists_exists_and_eq_and] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  rw [card_mul_inv_eq_convolution_inv]
  simpa [card_smul_inter_smul] using lt_card_smul_inter_smul hA ha hb
/-
**Finset.mul_inv_eq_inv_mul_of_doubling_lt_two_aux** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mul_inv_eq_inv_mul_of_doubling_lt_two_aux (h : #(A * A) < 2 * #A) :
    A⁻¹ * A ⊆ A * A⁻¹ := by
  intro z
  simp only [mem_mul, forall_exists_index, and_imp, mem_inv,
    exists_exists_and_eq_and]
  rintro x hx y hy rfl
  have ⟨t, ht⟩ : (x • A ∩ y • A).Nonempty := by
    simpa using lt_card_smul_inter_smul (K := 2) (mod_cast h) hx hy
  simp only [mem_inter, mem_smul_finset, smul_eq_mul] at ht
  obtain ⟨⟨z, hz, hzxwy⟩, w, hw, rfl⟩ := ht
  refine ⟨z, hz, w, hw, ?_⟩
  rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hzxwy, inv_mul_cancel_left]

-- TODO: is there a way to get wlog to make `mul_inv_eq_inv_mul_of_doubling_lt_two_aux` a goal?
-- i.e. wlog in the target rather than hypothesis
-- (BM: third time seeing this pattern)
-- I'm thinking something like wlog_suffices, where I could write
-- wlog_suffices : A⁻¹ * A ⊆ A * A⁻¹
-- which reverts *everything* (just like wlog does) and makes the side goal A⁻¹ * A = A * A⁻¹
-- under the assumption A⁻¹ * A ⊆ A * A⁻¹
-- and changes the main goal to A⁻¹ * A ⊆ A * A⁻¹
/-- If `A` has doubling strictly less than `2`, then `A * A⁻¹ = A⁻¹ * A`. -/
/-
**Finset.mul_inv_eq_inv_mul_of_doubling_lt_two** 是 Mathlib 中的一个引理，位于命名空间 `Finset
`。
形式化陈述：mul_inv_eq_inv_mul_of_doubling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = 
A⁻¹ * A
参数：h : #(A * A) < 2 * #A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Subset.antisymm`：∀ {α : Type u_1} {s₁ s₂ : Finset α}, s₁ ⊆ s₂ → s
₂ ⊆ s₁ → s₁ = s₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.mul_i
nv_eq_inv_mul_of_doubling_lt_two_aux`：∀ {G : Type u_1} [inst : Group G] [inst_1 
: DecidableEq G] {A : Finset G}, (A * A).card < 2 * A.card → A⁻¹ * A ⊆ A * A⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_inv`：card_inv (s : Finset α) : #s⁻¹ = #s

--- 原说明 ---
If `A` has doubling strictly less than `2`, then `A * A⁻¹ = A⁻¹ * A`.
-/
lemma mul_inv_eq_inv_mul_of_doubling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = A⁻¹ * A := by
  refine Subset.antisymm ?_ (mul_inv_eq_inv_mul_of_doubling_lt_two_aux h)
  simpa using
    mul_inv_eq_inv_mul_of_doubling_lt_two_aux (A := A⁻¹) (by simpa [← mul_inv_rev] using h)
/-
**Finset.weaken_doubling** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma weaken_doubling (h : #(A * A) < (3 / 2 : ℚ) * #A) : #(A * A) < 2 * #A := by
  rw [← Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  linarith only [h]
/-
**Finset.nonempty_of_doubling** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma nonempty_of_doubling (h : #(A * A) < (3 / 2 : ℚ) * #A) : A.Nonempty := by
  by_contra! rfl
  simp at h

/-- If `A` has doubling strictly less than `3 / 2`, then `A⁻¹ * A` is a subgroup.

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and `A⁻¹ * A` isn't a subgroup. -/
/-
**Finset.invMulSubgroup** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：invMulSubgroup (A : Finset G) (h : #(A * A) < (3 / 2 : Rat) * #A) : Subgro
up G where carrier
参数：A : Finset G；h : #(A * A) < (3 / 2 : Rat) * #A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` has doubling strictly less than `3 / 2`, then `A⁻¹ * A` is a subgroup.

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and `A⁻¹ * A` 
isn't a subgroup.
-/
def invMulSubgroup (A : Finset G) (h : #(A * A) < (3 / 2 : ℚ) * #A) : Subgroup G where
  carrier := A⁻¹ * A
  one_mem' := by
    have ⟨x, hx⟩ : A.Nonempty := nonempty_of_doubling h
    exact ⟨x⁻¹, inv_mem_inv hx, x, by simp [hx]⟩
  inv_mem' := by
    intro x
    simp only [Set.mem_mul, Set.mem_inv, coe_inv, forall_exists_index, mem_coe,
      and_imp]
    rintro a ha b hb rfl
    exact ⟨b⁻¹, by simpa using hb, a⁻¹, ha, by simp⟩
  mul_mem' := by
    norm_cast
    have h₁ x (hx : x ∈ A) y (hy : y ∈ A) : (1 / 2 : ℚ) * #A < #(x • A ∩ y • A) := by
      convert! lt_card_smul_inter_smul (by simpa using Rat.cast_strictMono (K := ℝ) h) hx hy
      norm_num
      simp [← Rat.cast_lt (K := ℝ)]
    intro a c ha hc
    simp only [mem_mul, mem_inv'] at ha hc
    obtain ⟨a, ha, b, hb, rfl⟩ := ha
    obtain ⟨c, hc, d, hd, rfl⟩ := hc
    have h₂ : (1 / 2 : ℚ) * #A < #(A ∩ (a * b)⁻¹ • A) := by
      refine (h₁ b hb _ ha).trans_le ?_
      rw [← card_smul_finset b⁻¹]
      simp [smul_smul, smul_finset_inter]
    have h₃ : (1 / 2 : ℚ) * #A < #(A ∩ (c * d) • A) := by
      refine (h₁ _ hc d hd).trans_le ?_
      rw [← card_smul_finset c]
      simp [smul_smul, smul_finset_inter]
    have ⟨t, ht⟩ : ((A ∩ (c * d) • A) ∩ (A ∩ (a * b)⁻¹ • A)).Nonempty := by
      rw [← card_pos, ← Nat.cast_pos (α := ℚ)]
      have := card_inter_add_card_union (A ∩ (c * d) • A) (A ∩ (a * b)⁻¹ • A)
      rw [← Nat.cast_inj (R := ℚ), Nat.cast_add, Nat.cast_add] at this
      have : (#((A ∩ (c * d) • A) ∪ (A ∩ (a * b)⁻¹ • A)) : ℚ) ≤ #A := by
        rw [Nat.cast_le, ← inter_union_distrib_left]
        exact card_le_card inter_subset_left
      linarith
    simp only [inter_inter_inter_comm, inter_self, mem_inter, ← inv_smul_mem_iff, inv_inv,
      smul_eq_mul, mul_assoc, mul_inv_rev] at ht
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), mem_mul]
    exact ⟨a * b * t, by simp [ht, mul_assoc], ((c * d)⁻¹ * t)⁻¹, by simp [ht, mul_assoc]⟩
/-
**Finset.invMulSubgroup_eq_inv_mul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：invMulSubgroup_eq_inv_mul (A : Finset G) (h) : (invMulSubgroup A h : Set G
) = A⁻¹ * A
参数：A : Finset G；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma invMulSubgroup_eq_inv_mul (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A := rfl
/-
**Finset.invMulSubgroup_eq_mul_inv** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：invMulSubgroup_eq_mul_inv (A : Finset G) (h) : (invMulSubgroup A h : Set G
) = A * A⁻¹
参数：A : Finset G；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.invMulSubgroup_eq_inv_mul`：invMulSubgroup_eq_inv_mul (A : Finset 
G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.mul_inv_eq_inv_mul_of_doubling_lt_two`：mul_inv_eq_inv_mul_of_doub
ling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = A⁻¹ * A
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `Int.cast_mul`：cast_mul {α : Type*} [NonAssocRing α] : forall m n, ((m * 
n : Int) : α) = m * n
· 使用定理 `Int.cast_ofNat`：cast_ofNat (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : Int) 
: R) = ofNat(n)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
（共 72 条，此处仅展示前 30 条）
-/
lemma invMulSubgroup_eq_mul_inv (A : Finset G) (h) : (invMulSubgroup A h : Set G) = A * A⁻¹ := by
  rw [invMulSubgroup_eq_inv_mul, eq_comm]
  norm_cast
  exact mul_inv_eq_inv_mul_of_doubling_lt_two (by qify at h ⊢; linarith)
/-
**Finset.** 是 Mathlib 中的一个实例，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (A : Finset G) (h) : Fintype (invMulSubgroup A h) := by
  simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
    mem_coe]
  infer_instance
/-
**Finset.weak_invMulSubgroup_bound** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma weak_invMulSubgroup_bound (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) < 2 * #A := by
  have h₀ : A.Nonempty := nonempty_of_doubling h
  have h₁ a (ha : a ∈ A⁻¹ * A) : (1 / 2 : ℚ) * #A < #{xy ∈ A ×ˢ A | xy.1 * xy.2⁻¹ = a} := by
    convert! lt_card_mul_inv_eq (by simpa using Rat.cast_strictMono (K := ℝ) h) ha
    norm_num
    simp [← Rat.cast_lt (K := ℝ)]
  have h₂ : ∀ x ∈ A ×ˢ A, (fun ⟨x, y⟩ => x * y⁻¹) x ∈ A⁻¹ * A := by
    rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h)]
    simp only [mem_product, Prod.forall, mem_mul, and_imp, mem_inv]
    intro a b ha hb
    exact ⟨a, ha, b⁻¹, by simp [hb], rfl⟩
  have : ((1 / 2 : ℚ) * #A) * #(A⁻¹ * A) < (#A : ℚ) ^ 2 := by
    rw [← Nat.cast_pow, sq, ← card_product, card_eq_sum_card_fiberwise h₂, Nat.cast_sum]
    refine (sum_lt_sum_of_nonempty (by simp [h₀]) h₁).trans_eq' ?_
    simp only [sum_const, nsmul_eq_mul, mul_comm]
  rw [← Nat.cast_lt (α := ℚ), Nat.cast_mul, Nat.cast_two]
  -- passing between ℕ- and ℚ-inequalities is annoying, here and above
  nlinarith
/-
**Finset.A_subset_aH** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma A_subset_aH (a : G) (ha : a ∈ A) : A ⊆ a • (A⁻¹ * A) := by
  rw [← smul_mul_assoc]
  exact subset_mul_right _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])
/-
**Finset.subgroup_strong_bound_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma subgroup_strong_bound_left (h : #(A * A) < (3 / 2 : ℚ) * #A) (a : G) (ha : a ∈ A) :
    A * A ⊆ a • op a • (A⁻¹ * A) := by
  have h₁ : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj, coe_mul, coe_mul, ← invMulSubgroup_eq_inv_mul _ h, coe_mul_coe]
  have h₂ : a • op a • (A⁻¹ * A) = (a • (A⁻¹ * A)) * (op a • (A⁻¹ * A)) := by
    rw [mul_smul_comm, smul_mul_assoc, h₁, smul_comm]
  rw [h₂]
  refine mul_subset_mul (A_subset_aH a ha) ?_
  rw [← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), ← mul_smul_comm]
  exact subset_mul_left _ (by simp [← inv_smul_mem_iff, inv_mem_inv ha])
/-
**Finset.subgroup_strong_bound_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma subgroup_strong_bound_right (h : #(A * A) < (3 / 2 : ℚ) * #A) (a : G) (ha : a ∈ A) :
    a • op a • (A⁻¹ * A) ⊆ A * A := by
  intro z hz
  simp only [mem_smul_finset, smul_eq_mul_unop, unop_op, smul_eq_mul, mem_mul, mem_inv,
    exists_exists_and_eq_and] at hz
  obtain ⟨d, ⟨b, hb, c, hc, rfl⟩, hz⟩ := hz
  let l : Finset G := A ∩ ((z * a⁻¹) • (A⁻¹ * A))
    -- ^ set of x ∈ A st ∃ y ∈ H a with x y = z
  let r : Finset G := (a • (A⁻¹ * A)) ∩ (z • A⁻¹)
    -- ^ set of x ∈ a H st ∃ y ∈ A with x y = z
  have : (A⁻¹ * A) * (A⁻¹ * A) = A⁻¹ * A := by
    rw [← coe_inj, coe_mul, coe_mul, ← invMulSubgroup_eq_inv_mul _ h, coe_mul_coe]
  have hl : l = A := by
    rw [inter_eq_left, ← this, subset_smul_finset_iff]
    simp only [← hz, mul_inv_rev, inv_inv, ← mul_assoc]
    refine smul_finset_subset_mul ?_
    simp [mul_mem_mul, ha, hb, hc]
  have hr : r = z • A⁻¹ := by
    rw [inter_eq_right, ← this, mul_assoc _ A,
      ← mul_inv_eq_inv_mul_of_doubling_lt_two (weaken_doubling h), subset_smul_finset_iff]
    simp only [← mul_assoc, smul_smul]
    refine smul_finset_subset_mul ?_
    simp [← hz, mul_mem_mul, ha, hb, hc]
  have lr : l ∪ r ⊆ a • (A⁻¹ * A) := by
    rw [union_subset_iff, hl]
    exact ⟨A_subset_aH a ha, inter_subset_left⟩
  have : #l = #A := by rw [hl]
  have : #r = #A := by rw [hr, card_smul_finset, card_inv]
  have : #(l ∪ r) < 2 * #A := by
    refine (card_le_card lr).trans_lt ?_
    rw [card_smul_finset]
    exact weak_invMulSubgroup_bound h
  have ⟨t, ht⟩ : (l ∩ r).Nonempty := by
    rw [← card_pos]
    linarith [card_inter_add_card_union l r]
  simp only [hl, hr, mem_inter, ← inv_smul_mem_iff, smul_eq_mul, mem_inv', mul_inv_rev,
    inv_inv] at ht
  rw [mem_mul]
  exact ⟨t, ht.1, t⁻¹ * z, ht.2, by simp⟩

open scoped RightActions in
/-
**Finset.smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves** 是 Mathlib 中的一个
引理，位于命名空间 `Finset`。
形式化陈述：smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 
/ 2 : Rat) * #A) (ha : a in A) : a •> ((A⁻¹ * A) <• a) = A * A
参数：h : #(A * A) < (3 / 2 : Rat) * #A；ha : a in A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.subgr
oup_strong_bound_right`：∀ {G : Type u_1} [inst : Group G] [inst_1 : DecidableEq 
G] {A : Finset G},   ↑(A * A).card < 3 / 2 * ↑A.card → ∀ a ∈ A, a • MulOpposite.
op a…
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.subgr
oup_strong_bound_left`：∀ {G : Type u_1} [inst : Group G] [inst_1 : DecidableEq G
] {A : Finset G},   ↑(A * A).card < 3 / 2 * ↑A.card → ∀ a ∈ A, A * A ⊆ a • MulOp
pos…
-/
lemma smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A)
    (ha : a ∈ A) : a •> ((A⁻¹ * A) <• a) = A * A :=
  (subgroup_strong_bound_right h a ha).antisymm (subgroup_strong_bound_left h a ha)
/-
**Finset.card_inv_mul_of_doubling_lt_three_halves** 是 Mathlib 中的一个引理，位于命名空间 `Fin
set`。
形式化陈述：card_inv_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #
A) : #(A⁻¹ * A) = #(A * A)
参数：h : #(A * A) < (3 / 2 : Rat) * #A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.nonem
pty_of_doubling`：∀ {G : Type u_1} [inst : Group G] [inst_1 : DecidableEq G] {A :
 Finset G}, ↑(A * A).card < 3 / 2 * ↑A.card → A.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves`：smul_inv_
mul_opSMul_eq_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #A
) (ha : a in A) : a •> ((A⁻¹ * A) <• a) = A * A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.card_smul_finset`：card_smul_finset (a : α) (s : Finset β) : (a • 
s).card = s.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_inv_mul_of_doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    #(A⁻¹ * A) = #(A * A) := by
  obtain ⟨a, ha⟩ := nonempty_of_doubling h
  simp_rw [← smul_inv_mul_opSMul_eq_mul_of_doubling_lt_three_halves h ha, card_smul_finset]
/-
**Finset.smul_inv_mul_eq_inv_mul_opSMul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：smul_inv_mul_eq_inv_mul_opSMul (h : #(A * A) < (3 / 2 : Rat) * #A) (ha : a
 in A) : a •> (A⁻¹ * A) = (A⁻¹ * A) <• a
参数：h : #(A * A) < (3 / 2 : Rat) * #A；ha : a in A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_antisymm`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Pa
rtialOrder α] {a b : α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.subset_smul_finset_iff`：subset_smul_finset_iff : s subseteq a • t
 ↔ a⁻¹ • s subseteq t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulOpposite.op_inv`：∀ {α : Type u_1} [inst : Inv α] (x : α), MulOpposite
.op x⁻¹ = (MulOpposite.op x)⁻¹
· 使用定理 `Finset.op_smul_finset_subset_mul`：op_smul_finset_subset_mul : a in t -> 
op a • s subseteq s * t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `Finset.instMulLeftMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 
: Mul α], MulLeftMono (Finset α)
· 使用定理 `Finset.instMulRightMono`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1
 : Mul α], MulRightMono (Finset α)
· 使用定理 `Finset.smul_finset_subset_mul`：∀ {α : Type u_2} [inst : Mul α] [inst_1 :
 DecidableEq α] {s t : Finset α} {a : α}, a ∈ s → a • t ⊆ s * t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.coe_mul`：coe_mul (s t : Finset α) : (↑(s * t) : Set α) = ↑s * ↑t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `Finset.invMulSubgroup_eq_mul_inv`：invMulSubgroup_eq_mul_inv (A : Finset 
G) (h) : (invMulSubgroup A h : Set G) = A * A⁻¹
· 使用引理 `coe_mul_coe`：coe_mul_coe [SetLike S M] [SubmonoidClass S M] (H : S) : H 
* H = (H : Set M)
· 使用定理 `SubgroupClass.toSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : DivInvMonoid G} {inst_1 : SetLike S G} [self : SubgroupClass S G],   
SubmonoidClass S G
· 使用定理 `Subgroup.instSubgroupClass`：∀ {G : Type u_1} [inst : Group G], SubgroupC
lass (Subgroup G) G
· 使用引理 `Finset.invMulSubgroup_eq_inv_mul`：invMulSubgroup_eq_inv_mul (A : Finset 
G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A
· 使用引理 `Finset.mul_inv_eq_inv_mul_of_doubling_lt_two`：mul_inv_eq_inv_mul_of_doub
ling_lt_two (h : #(A * A) < 2 * #A) : A * A⁻¹ = A⁻¹ * A
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.weake
n_doubling`：∀ {G : Type u_1} [inst : Group G] [inst_1 : DecidableEq G] {A : Fins
et G},   ↑(A * A).card < 3 / 2 * ↑A.card → (A * A).card < 2 * A.card
-/
lemma smul_inv_mul_eq_inv_mul_opSMul (h : #(A * A) < (3 / 2 : ℚ) * #A) (ha : a ∈ A) :
    a •> (A⁻¹ * A) = (A⁻¹ * A) <• a := by
  refine subset_antisymm ?_ ?_
  · rw [subset_smul_finset_iff, ← op_inv]
    calc
      a •> (A⁻¹ * A) <• a⁻¹ ⊆ a •> (A⁻¹ * A) * A⁻¹ := op_smul_finset_subset_mul (by simpa)
      _ ⊆ A * (A⁻¹ * A) * A⁻¹ := by grw [smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        simp_rw [← coe_inj, coe_mul]
        rw [← mul_assoc, ← invMulSubgroup_eq_mul_inv _ h, mul_assoc,
          ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe, invMulSubgroup_eq_inv_mul]
  · rw [subset_smul_finset_iff]
    calc
      a⁻¹ •> ((A⁻¹ * A) <• a) ⊆ A⁻¹ * (A⁻¹ * A) <• a := smul_finset_subset_mul (by simpa)
      _ ⊆ A⁻¹ * ((A⁻¹ * A) * A) := by grw [op_smul_finset_subset_mul (by simpa)]
      _ = A⁻¹ * A := by
        rw [← mul_inv_eq_inv_mul_of_doubling_lt_two <| weaken_doubling h]
        simp_rw [← coe_inj, coe_mul]
        rw [mul_assoc, ← invMulSubgroup_eq_inv_mul _ h, ← mul_assoc,
          ← invMulSubgroup_eq_inv_mul _ h, ← invMulSubgroup_eq_mul_inv _ h, coe_mul_coe]

open scoped RightActions in
/-- If `A` has doubling strictly less than `3 / 2`, then there exists a subgroup `H` of the
normaliser of `A` of size strictly less than `3 / 2 * #A` such that `A` is a subset of a coset of
`H` (in fact a subset of `a • H` for every `a ∈ A`).

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and can't be covered by a subgroup
of size at most `2`.

This is Theorem 2.2.1 in [tointon2020]. -/
/-
**Finset.doubling_lt_three_halves** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：doubling_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #A) : exists (H :
 Subgroup G) (_ : Fintype H), Fintype.card H < (3 / 2 : Rat) * #A ∧ forall a in 
A, (A : Set G) subseteq a • H ∧ a •> (H : Set G) = H <• a
参数：h : #(A * A) < (3 / 2 : Rat) * #A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subsemigroup.mk.congr_simp`：∀ {M : Type u_3} [inst : Mul M] (carrier car
rier_1 : Set M) (e_carrier : carrier = carrier_1)   (mul_mem' : ∀ {a b : M}, a ∈
 carrier → b ∈ c…
· 使用定理 `Submonoid.mk.congr_simp`：∀ {M : Type u_3} [inst : MulOneClass M] (toSubs
emigroup toSubsemigroup_1 : Subsemigroup M)   (e_toSubsemigroup : toSubsemigroup
 = toSubsemig…
· 使用定理 `Finset.invMulSubgroup.eq_1`：∀ {G : Type u_1} [inst : Group G] [inst_1 : 
DecidableEq G] (A : Finset G) (h : ↑(A * A).card < 3 / 2 * ↑A.card),   A.invMulS
ubgroup h = { ca…
· 使用定理 `Subgroup.mk.congr_simp`：∀ {G : Type u_3} [inst : Group G] (toSubmonoid t
oSubmonoid_1 : Submonoid G)   (e_toSubmonoid : toSubmonoid = toSubmonoid_1)   (i
nv_mem' : ∀ …
· 使用引理 `Nat.card_eq_finsetCard`：card_eq_finsetCard (s : Finset α) : Nat.card s =
 s.card
· 使用引理 `Finset.card_inv_mul_of_doubling_lt_three_halves`：card_inv_mul_of_doublin
g_lt_three_halves (h : #(A * A) < (3 / 2 : Rat) * #A) : #(A⁻¹ * A) = #(A * A)
· 使用引理 `Finset.invMulSubgroup_eq_inv_mul`：invMulSubgroup_eq_inv_mul (A : Finset 
G) (h) : (invMulSubgroup A h : Set G) = A⁻¹ * A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `_private.Mathlib.Combinatorics.Additive.VerySmallDoubling.0.Finset.A_sub
set_aH`：∀ {G : Type u_1} [inst : Group G] [inst_1 : DecidableEq G] {A : Finset G
}, ∀ a ∈ A, A ⊆ a • (A⁻¹ * A)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.smul_inv_mul_eq_inv_mul_opSMul`：smul_inv_mul_eq_inv_mul_opSMul (h
 : #(A * A) < (3 / 2 : Rat) * #A) (ha : a in A) : a •> (A⁻¹ * A) = (A⁻¹ * A) <• 
a

--- 原说明 ---
If `A` has doubling strictly less than `3 / 2`, then there exists a subgroup `H`
 of the
normaliser of `A` of size strictly less than `3 / 2 * #A` such that `A` is a sub
set of a coset of
`H` (in fact a subset of `a • H` for every `a ∈ A`).

Note that this is sharp: `A = {0, 1}` in `ℤ` has doubling `3 / 2` and can't be c
overed by a subgroup
of size at most `2`.

This is Theorem 2.2.1 in [tointon2020].
-/
theorem doubling_lt_three_halves (h : #(A * A) < (3 / 2 : ℚ) * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H), Fintype.card H < (3 / 2 : ℚ) * #A ∧ ∀ a ∈ A,
      (A : Set G) ⊆ a • H ∧ a •> (H : Set G) = H <• a := by
  let H := invMulSubgroup A h
  refine ⟨H, inferInstance, ?_, fun a ha ↦ ⟨?_, ?_⟩⟩
  · simp only [invMulSubgroup, ← coe_mul, Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk,
      mem_coe, ← Nat.card_eq_fintype_card, H]
    rwa [Nat.card_eq_finsetCard, card_inv_mul_of_doubling_lt_three_halves h]
  · rw [invMulSubgroup_eq_inv_mul]
    exact_mod_cast A_subset_aH a ha
  · simpa [H, invMulSubgroup_eq_inv_mul, ← coe_inv, ← coe_mul, ← coe_smul_finset]
      using smul_inv_mul_eq_inv_mul_opSMul h ha

/-! ### Doubling strictly less than `φ` -/

omit [DecidableEq G] in
/-
**Finset.op_smul_eq_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma op_smul_eq_iff_mem {H : Subgroup G} {c : Set G} {x : G}
    (hc : c ∈ orbit Gᵐᵒᵖ (H : Set G)) : x ∈ c ↔ H <• x = c := by
  refine ⟨fun hx => ?_, fun hx =>
    by simp only [← hx, mem_rightCoset_iff, mul_inv_cancel, SetLike.mem_coe, one_mem]⟩
  obtain ⟨⟨a⟩, rfl⟩ := hc
  change _ = _ <• _
  rw [eq_comm, smul_eq_iff_eq_inv_smul, ← op_inv, op_smul_op_smul, rightCoset_mem_rightCoset]
  rwa [← op_smul_eq_mul, op_inv, ← SetLike.mem_coe, ← Set.mem_smul_set_iff_inv_smul_mem]

omit [DecidableEq G] in
/-
**Finset.op_smul_eq_op_smul_iff_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma op_smul_eq_op_smul_iff_mem {H : Subgroup G} {x y : G} :
    x ∈ (H : Set G) <• y ↔ (H : Set G) <• x = H <• y := op_smul_eq_iff_mem (mem_orbit _ _)

omit [DecidableEq G] in
/-- Given a finite subset `A` of a group `G` and a subgroup `H ≤ G`, there exists a subset `Z ⊆ A`
such that `H * Z = H * A` and the cosets `Hz` are disjoint as `z` runs over `Z`. -/
/-
**Finset.exists_subset_mul_eq_mul_injOn** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite subset `A` of a group `G` and a subgroup `H ≤ G`, there exists a 
subset `Z ⊆ A`
such that `H * Z = H * A` and the cosets `Hz` are disjoint as `z` runs over `Z`.
-/
private lemma exists_subset_mul_eq_mul_injOn (H : Subgroup G) (A : Finset G) :
    ∃ Z ⊆ A, (H : Set G) * Z = H * A ∧ (Z : Set G).InjOn ((H : Set G) <• ·) := by
  obtain ⟨Z, hZA, hZinj, hHZA⟩ :=
    ((A : Set G).surjOn_image ((H : Set G) <• ·)).exists_subset_injOn_image_eq
  lift Z to Finset G using A.finite_toSet.subset hZA
  refine ⟨Z, mod_cast hZA, ?_, hZinj⟩
  simpa [-SetLike.mem_coe, Set.iUnion_op_smul_set] using congr(Set.sUnion $hHZA)
/-
**Finset.card_mul_eq_mul_card_of_injOn_opSMul** 是 Mathlib 中的一个引理，位于命名空间 `Finset`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma card_mul_eq_mul_card_of_injOn_opSMul {H : Subgroup G} [Fintype H]
    {Z : Finset G} (hZ : (Z : Set G).InjOn ((H : Set G) <• ·)) :
    Fintype.card H * #Z = #(Set.toFinset H * Z) := by
  rw [card_mul_iff.2]
  · simp
  rintro ⟨h₁, z₁⟩ ⟨hh₁, hz₁⟩ ⟨h₂, z₂⟩ ⟨hh₂, hz₂⟩ h
  simp only [Set.coe_toFinset, SetLike.mem_coe] at *
  obtain rfl := hZ hz₁ hz₂ <| (rightCoset_eq_iff _).2 <| by
    simpa [eq_inv_mul_iff_mul_eq.2 h, mul_assoc] using mul_mem (inv_mem hh₂) hh₁
  simp_all

set_option linter.flexible false in -- simp followed by positivity
open goldenRatio in
/-- If `A` has doubling `K` strictly less than `φ`, then `A * A⁻¹` is covered by
at most a constant number of cosets of a finite subgroup of `G`. -/
/-
**Finset.doubling_lt_golden_ratio** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：doubling_lt_golden_ratio (hK₁ : 1 < K) (hKφ : K < φ) (hA₁ : #(A⁻¹ * A) <= 
K * #A) (hA₂ : #(A * A⁻¹) <= K * #A) : exists (H : Subgroup G) (_ : Fintype H) (
Z : Finset G), #Z <= (2 - K) * K / ((φ - K) * (K - ψ)) ∧ (H : Set G) * Z = A * A
⁻¹
参数：hK₁ : 1 < K；hKφ : K < φ；hA₁ : #(A⁻¹ * A) <= K * #A；hA₂ : #(A * A⁻¹) <= K * #A
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.of_raw`：∀ (α : Type u_1) [inst : DivisionSe
miring α] (n d : ℕ), ↑d ≠ 0 → Mathlib.Meta.NormNum.IsNNRat (NNRat.rawCast n d) n
 d
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.den_nz`：∀ {α : Type u_1} [inst : DivisionSe
miring α] {a : α} {n d : ℕ}, Mathlib.Meta.NormNum.IsNNRat a n d → ↑d ≠ 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 212 条，此处仅展示前 30 条）

--- 原说明 ---
If `A` has doubling `K` strictly less than `φ`, then `A * A⁻¹` is covered by
at most a constant number of cosets of a finite subgroup of `G`.
-/
theorem doubling_lt_golden_ratio (hK₁ : 1 < K) (hKφ : K < φ)
    (hA₁ : #(A⁻¹ * A) ≤ K * #A) (hA₂ : #(A * A⁻¹) ≤ K * #A) :
    ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      #Z ≤ (2 - K) * K / ((φ - K) * (K - ψ)) ∧ (H : Set G) * Z = A * A⁻¹ := by
  -- Some useful initial calculations
  have K_pos : 0 < K := by positivity
  have hK₀ : 0 < K := by positivity
  have hKφ' : 0 < φ - K := by linarith
  have hKψ' : 0 < K - ψ := by linarith [Real.goldenConj_neg]
  have hK₂' : 0 < 2 - K := by linarith [Real.goldenRatio_lt_two]
  have const_pos : 0 < K * (2 - K) / ((φ - K) * (K - ψ)) := by positivity
  -- We dispatch the trivial case `A = ∅` separately.
  obtain rfl | A_nonempty := A.eq_empty_or_nonempty
  · exact ⟨⊥, inferInstance, ∅, by simp; positivity⟩
  -- In the case where `A` is non-empty, we consider the set `S := A * A⁻¹` and its stabilizer `H`.
  let S := A * A⁻¹
  let H := stabilizer G S
  -- `S` is finite and non-empty (because `A` is), and therefore `H` is finite too.
  have S_nonempty : S.Nonempty := by simpa [S]
  have : Finite H := by simpa [H] using! stabilizer_finite (by simpa) S.finite_toSet
  cases nonempty_fintype H
  -- By definition, `H * S = S`.
  have H_mul_S : (H : Set G) * S = S := by simp [H, ← stabilizer_coe_finset]
  -- Since `H` is a subgroup, find a finite set `Z ⊆ S` such that `H * Z = S` and `|H| * |Z| = |S|`.
  obtain ⟨Z, hZ⟩ := exists_subset_mul_eq_mul_injOn H S
  have H_mul_Z : (H : Set G) * Z = S := by simp [hZ.2.1, H_mul_S]
  have H_toFinset_mul_Z : Set.toFinset H * Z = S := by simpa [← Finset.coe_inj]
  have card_H_mul_card_Z : Fintype.card H * #Z = #S := by
    simpa [card_mul_eq_mul_card_of_injOn_opSMul hZ.2.2] using! congr_arg _ H_toFinset_mul_Z
  -- It remains to show that `|Z| ≤ C(K)` for some `C(K)` depending only on `K`.
  refine ⟨H, inferInstance, Z, ?_, mod_cast H_mul_Z⟩
  -- This is equivalent to showing that `|H| ≥ c(K)|S|` for some `c(K)` depending only on `K`.
  suffices ((φ - K) * (K - ψ)) / ((2 - K) * K) * #S ≤ Fintype.card H by
    calc
          (#Z : ℝ)
      _ = (Fintype.card H / #S : ℝ)⁻¹ := by simp [← card_H_mul_card_Z]
      _ ≤ (((φ - K) * (K - ψ) / ((2 - K) * K) * #S) / #S)⁻¹ := by gcongr
      _ = (2 - K) * K / ((φ - K) * (K - ψ)) := by
        have : (#S : ℝ) ≠ 0 := by positivity
        simp [this]
  -- Write `r(z)` the number of representations of `z ∈ S` as `x * y⁻¹` for `x, y ∈ A`.
  let r z : ℕ := A.convolution A⁻¹ z
  -- `r` is invariant under inverses.
  have r_inv z : r z⁻¹ = r z := by simp [r, inv_inv]
  -- We show that every `z ∈ S` with at least `(K - 1)|A|` representations lies in `H`,
  -- and that such `z` make up a proportion of at least `(2 - K) / ((φ - K) * (K - ψ))` of `S`.
  calc
        (φ - K) * (K - ψ) / ((2 - K) * K) * #S
    _ ≤ #{z ∈ S | (K - 1) * #A < r z} := ?_
    _ ≤ #(H : Set G).toFinset := ?_
    _ = Fintype.card H := by simp
  -- First, let's show that a large proportion of all `z ∈ S` have many representations.
  · -- Let `l` be that number.
    set l : ℕ := #{z ∈ S | (K - 1) * #A < r z} with hk
    -- By upper-bounding `r(z)` by `(K - 1)|A|` for the `z` with few representations,
    -- and by `|A|` for the `z` with many representations,
    -- we get `|A|² ≤ l|A| + (|S| - l)(K - 1)|A| = ((2 - K)l + (K - 1)|S|)|A|`.
    have ineq : #A * #A ≤ ((2 - K) * l + (K - 1) * #S) * #A := by
      calc
            (#A : ℝ) * #A
        _ = #A * #A⁻¹ := by simp
        _ = #(A ×ˢ A⁻¹) := by simp
        _ = ∑ z ∈ S, ↑(r z) := by
          norm_cast
          exact card_eq_sum_card_fiberwise fun xy hxy ↦
            mul_mem_mul (mem_product.mp hxy).1 (mem_product.mp hxy).2
        _ = ∑ z ∈ S with (K - 1) * #A < r z, ↑(r z) + ∑ z ∈ S with r z ≤ (K - 1) * #A, ↑(r z) := by
          norm_cast; simp_rw [← not_lt, sum_filter_add_sum_filter_not]
        _ ≤ ∑ z ∈ S with (K - 1) * #A < r z, ↑(#A)
          + ∑ z ∈ S with r z ≤ (K - 1) * #A, (K - 1) * #A := by
          gcongr with z hz z hz
          · exact convolution_le_card_left
          · simp_all
        _ = l * #A + (#S - l) * (K - 1) * #A := by
          simp [hk, ← not_lt, mul_assoc,
            ← S.card_filter_add_card_filter_not fun z ↦ (K - 1) * #A < r z]
        _ = ((2 - K) * l + (K - 1) * #S) * #A := by ring
    -- By cancelling `|A|` on both sides, we get `|A| ≤ (2 - K)l + (K - 1)|S|`.
    -- By composing with `|S| ≤ K|A|`, we get `|S| ≤ (2 - K)Kl + (K - 1)K|S|`.
    have : 0 < #A := by positivity
    replace ineq := calc
          (#S : ℝ)
      _ ≤ K * #A := ‹_›
      _ ≤ K * ((2 - K) * l + (K - 1) * #S) := by
        gcongr; exact le_of_mul_le_mul_right ineq <| by positivity
      _ = (2 - K) * K * l + (K - 1) * K * #S := by ring
    -- Now, we are done.
    calc
          (φ - K) * (K - ψ) / ((2 - K) * K) * #S
      _ = (φ - K) * (K - ψ) * #S / ((2 - K) * K) := div_mul_eq_mul_div ..
      _ ≤ (2 - K) * K * l / ((2 - K) * K) := by
        have := Real.goldenRatio_mul_goldenConj
        have := Real.goldenRatio_add_goldenConj
        rw [show (φ - K) * (K - ψ) = 1 - (K - 1) * K by grind]
        gcongr ?_ / _
        linarith [ineq]
      _ = l := by field
  -- Second, let's show that the `z ∈ S` with many representations are in `H`.
  · gcongr
    simp only [subset_iff, mem_filter, Set.mem_toFinset, SetLike.mem_coe, and_imp]
    rintro z hz hrz
    -- It's enough to show that `z * w ∈ S` for all `w ∈ S`.
    rw [mem_stabilizer_finset']
    rintro w hw
    -- Since `w ∈ S` and `|A⁻¹ * A| ≤ K|A|`, we know that `r(w) ≥ (2 - K)|A|`.
    have hrw : (2 - K) * #A ≤ r w := by
      simpa [card_mul_inv_eq_convolution_inv] using! le_card_mul_inv_eq hA₁ (by simpa)
    -- But also `r(z⁻¹) = r(z) > (K - 1)|A|`.
    rw [← r_inv] at hrz
    simp only [r, ← card_inter_smul] at hrz hrw
    -- By inclusion-exclusion, we get that `(z⁻¹ •> A) ∩ (w •> A)` is non-empty.
    have : (0 : ℝ) < #((z⁻¹ •> A) ∩ (w •> A)) := by
      have : (#((A ∩ z⁻¹ •> A) ∩ (A ∩ w •> A)) : ℝ) ≤ #(z⁻¹ •> A ∩ w •> A) := by
        gcongr <;> exact inter_subset_right
      have : (#((A ∩ z⁻¹ •> A) ∪ (A ∩ w •> A)) : ℝ) ≤ #A := by
        gcongr; exact union_subset inter_subset_left inter_subset_left
      have :
          (#((A ∩ z⁻¹ •> A) ∩ (A ∩ w •> A)) + #((A ∩ z⁻¹ •> A) ∪ (A ∩ w •> A)) : ℝ) =
            #(A ∩ z⁻¹ •> A) + #(A ∩ w •> A) := mod_cast card_inter_add_card_union ..
      linarith
    -- This is exactly what we set out to prove.
    simpa [S, card_smul_inter_smul, Finset.Nonempty, mem_mul, mem_inv, -mem_inv', and_assoc]
      using! this

/-! ### Doubling less than `2-ε` -/

variable (ε : ℝ)

/-- Given a constant `K ∈ ℝ` (usually `0 < K ≤ 1`) and a finite subset `S ⊆ G`,
`expansion K S : Finset G → ℝ` measures the extent to which `S` extends the argument, compared
against the reference constant `K`. That is, given a finite `A ⊆ G` (possibly empty),
`expansion K S A` is defined as the value of `#(SA) - K#S`. -/
/-
**Finset.expansion** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a constant `K ∈ ℝ` (usually `0 < K ≤ 1`) and a finite subset `S ⊆ G`,
`expansion K S : Finset G → ℝ` measures the extent to which `S` extends the argu
ment, compared
against the reference constant `K`. That is, given a finite `A ⊆ G` (possibly em
pty),
`expansion K S A` is defined as the value of `#(SA) - K#S`.
-/
private def expansion (K : ℝ) (S A : Finset G) : ℝ := #(A * S) - K * #A
/-
**Finset.expansion_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma expansion_empty (K : ℝ) (S : Finset G) : expansion K S ∅ = 0 := by
  simp [expansion]
/-
**Finset.mul_card_le_expansion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma mul_card_le_expansion (hS : S.Nonempty) : (1 - K) * #A ≤ expansion K S A := by
  rw [one_sub_mul, expansion]; have := card_le_card_mul_right hS (s := A); gcongr
/-
**Finset.expansion_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma expansion_nonneg (hK : K ≤ 1) (hS : S.Nonempty) : 0 ≤ expansion K S A := by
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]
/-
**Finset.expansion_pos** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma expansion_pos (hK : K < 1) (hS : S.Nonempty) (hA : A.Nonempty) :
    0 < expansion K S A := by
  have : (0 : ℝ) < #A := by simp [hA]
  nlinarith [mul_card_le_expansion (K := K) hS (A := A)]
/-
**Finset.expansion_pos_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma expansion_pos_iff (hK : K < 1) (hS : S.Nonempty) :
    0 < expansion K S A ↔ A.Nonempty where
  mp hA := by by_contra! rfl; simp at hA
  mpr := expansion_pos hK hS
/-
**Finset.expansion_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma expansion_smul_finset (K : ℝ) (S A : Finset G) (a : G) :
    expansion K S (a • A) = expansion K S A := by simp [expansion, smul_mul_assoc]
/-
**Finset.expansion_submodularity** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma expansion_submodularity :
    expansion K S (A ∩ B) + expansion K S (A ∪ B) ≤ expansion K S A + expansion K S B := by
  have : (#(A ∩ B) + #(A ∪ B) : ℝ) = #A + #B := mod_cast card_inter_add_card_union A B
  have : K * #(A ∩ B) + K * #(A ∪ B) = K * #A + K * #B := by simp only [← mul_add, this]
  have : (#(A * S ∩ (B * S)) + #(A * S ∪ B * S) : ℝ) = #(A * S) + #(B * S) :=
    mod_cast card_inter_add_card_union (A * S) (B * S)
  have : (#((A ∩ B) * S) : ℝ) ≤ #(A * S ∩ (B * S)) := by grw [inter_mul_subset]
  simp_rw [expansion, union_mul]
  nlinarith
/-
**Finset.bddBelow_expansion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma bddBelow_expansion (hK : K ≤ 1) (hS : S.Nonempty) :
    BddBelow (Set.range fun A : {A : Finset G // A.Nonempty} ↦ expansion K S A) :=
  ⟨0, by simp [lowerBounds, *]⟩

/-- Given `K ∈ ℝ` and a finite `S ⊆ G`, the connectivity `κ` of `G` with respect to `K` and `S` is
the infimum of `expansion K S A` over all finite nonempty `A ⊆ G`. Note that when `K ≤ 1`,
`expansion K S A` is nonnegative for all `A`, so the infimum exists. -/
/-
**Finset.connectivity** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K ∈ ℝ` and a finite `S ⊆ G`, the connectivity `κ` of `G` with respect to 
`K` and `S` is
the infimum of `expansion K S A` over all finite nonempty `A ⊆ G`. Note that whe
n `K ≤ 1`,
`expansion K S A` is nonnegative for all `A`, so the infimum exists.
-/
private noncomputable def connectivity (K : ℝ) (S : Finset G) : ℝ :=
  ⨅ A : {A : Finset G // A.Nonempty}, expansion K S A
/-
**Finset.le_connectivity_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma le_connectivity_iff (hK : K ≤ 1) (hS : S.Nonempty) {r : ℝ} :
    r ≤ connectivity K S ↔ ∀ ⦃A : Finset G⦄, A.Nonempty → r ≤ expansion K S A := by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, le_ciInf_iff, bddBelow_expansion, *]
/-
**Finset.connectivity_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma connectivity_lt_iff (hK : K ≤ 1) (hS : S.Nonempty) {r : ℝ} :
    connectivity K S < r ↔ ∃ A : Finset G, A.Nonempty ∧ expansion K S A < r := by
  have : Nonempty {A : Finset G // A.Nonempty} := ⟨{1}, by simp⟩
  simp [connectivity, ciInf_lt_iff, bddBelow_expansion, *]
/-
**Finset.connectivity_le_expansion** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma connectivity_le_expansion (hK : K ≤ 1) (hS : S.Nonempty) (hA : A.Nonempty) :
    connectivity K S ≤ expansion K S A := (le_connectivity_iff hK hS).1 le_rfl hA
/-
**Finset.connectivity_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma connectivity_nonneg (hK : K ≤ 1) (hS : S.Nonempty) :
    0 ≤ connectivity K S := by simp [*]

/-- Given `K ∈ ℝ` and a finite `S ⊆ G`, a fragment of `G` with respect to `K` and `S` is a finite
nonempty `A ⊆ G` whose expansion attains the value of the connectivity, that is,
`expansion K S A = κ`. -/
/-
**Finset.IsFragment** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K ∈ ℝ` and a finite `S ⊆ G`, a fragment of `G` with respect to `K` and `S
` is a finite
nonempty `A ⊆ G` whose expansion attains the value of the connectivity, that is,
`expansion K S A = κ`.
-/
private def IsFragment (K : ℝ) (S A : Finset G) : Prop := expansion K S A = connectivity K S

/-- Given `K ∈ ℝ` and a finite `S ⊆ G`, an atom of `G` with respect to `K` and `S` is a (finite
and nonempty) fragment `A` of minimal cardinality. -/
/-
**Finset.IsAtom** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `K ∈ ℝ` and a finite `S ⊆ G`, an atom of `G` with respect to `K` and `S` i
s a (finite
and nonempty) fragment `A` of minimal cardinality.
-/
private def IsAtom (K : ℝ) (S A : Finset G) : Prop := MinimalFor (IsFragment K S) card A
/-
**Finset.IsAtom.isFragment** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAtom.isFragment (hA : IsAtom K S A) : IsFragment K S A := hA.1
/-
**Finset.isFragment_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma isFragment_smul_finset : IsFragment K S (a • A) ↔ IsFragment K S A := by
  simp [IsFragment]
/-
**Finset.isAtom_smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] private lemma isAtom_smul_finset : IsAtom K S (a • A) ↔ IsAtom K S A := by
  simp [IsAtom, MinimalFor]
/-
**Finset.IsFragment.smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsFragment.smul_finset (a : G) (hA : IsFragment K S A) : IsFragment K S (a • A) :=
  isFragment_smul_finset.2 hA
/-
**Finset.IsAtom.smul_finset** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAtom.smul_finset (a : G) (hA : IsAtom K S A) : IsAtom K S (a • A) :=
  isAtom_smul_finset.2 hA
/-
**Finset.IsFragment.inter** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsFragment.inter (hK : K ≤ 1) (hS : S.Nonempty) (hA : IsFragment K S A)
    (hB : IsFragment K S B) (hAB : (A ∩ B).Nonempty) : IsFragment K S (A ∩ B) := by
  unfold IsFragment at *
  have := expansion_submodularity (S := S) (A := A) (B := B) (K := K)
  have := connectivity_le_expansion hK hS hAB
  have := connectivity_le_expansion hK hS <| hAB.mono inter_subset_union
  linarith
/-
**Finset.IsAtom.eq_of_inter_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAtom.eq_of_inter_nonempty (hK : K ≤ 1) (hS : S.Nonempty)
    (hA : IsAtom K S A) (hB : IsAtom K S B) (hAB : (A ∩ B).Nonempty) : A = B := by
  replace hAB := hA.isFragment.inter hK hS hB.isFragment hAB
  replace hA := hA.2 hAB <| by grw [inter_subset_left]
  replace hB := hB.2 hAB <| by grw [inter_subset_right]
  replace hA := eq_of_subset_of_card_le inter_subset_left hA
  replace hB := eq_of_subset_of_card_le inter_subset_right hB
  exact hA.symm.trans hB

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- For `K < 1` and `S ⊆ G` finite and nonempty, the value of connectivity is attained by a
nonempty finite subset of `G`. That is, a fragment for given `K` and `S` exists. -/
/-
**Finset.exists_nonempty_isFragment** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `K < 1` and `S ⊆ G` finite and nonempty, the value of connectivity is attain
ed by a
nonempty finite subset of `G`. That is, a fragment for given `K` and `S` exists.
-/
private lemma exists_nonempty_isFragment (hK : K < 1) (hS : S.Nonempty) :
    ∃ A, A.Nonempty ∧ IsFragment K S A := by
  -- We will show this lemma by contradiction. So we suppose that the infimum in the definition of
  -- connectivity is not attained by a nonempty finite subset of `G`, or, equivalently, that for
  -- every `κ < k` where `κ` is the connectivity, there is nonempty `A` such that `κ < ex A < k`.
  by_contra! H
  let ex := expansion K S
  let κ := connectivity K S
  -- Some useful calculations
  have κ_add_one_pos : 0 < κ + 1 := by linarith [connectivity_nonneg hK.le hS]
  have one_sub_K_pos : 0 < 1 - K := by linarith
  -- First we show that for large enough `A`, `κ + 1 < ex A`. Calculations show that
  -- `#A > ⌊(κ + 1) / (1 - K)⌋` suffices. We will actually use the contrapositive of this result: if
  -- `ex A` is near `κ`, then `A` will need to be small.
  let t := Nat.floor ((κ + 1) / (1 - K))
  have largeA {A : Finset G} (hA : t < #A) : κ + 1 < ex A := by
    rw [Nat.lt_iff_add_one_le] at hA
    calc
          κ + 1
      _ = (κ + 1) / ((κ + 1) / (1 - K)) * ((κ + 1) / (1 - K)) := by field
      _ < (κ + 1) / ((κ + 1) / (1 - K)) * (t + 1) := by gcongr; exact Nat.lt_floor_add_one _
      _ = (1 - K) * (t + 1) := by field
      _ ≤ (1 - K) * #A      := by norm_cast; gcongr
      _ ≤ ex A              := mul_card_le_expansion hS
  -- On the other hand, we essentially show that there are only finitely many possible values for
  -- `A` with `#A ≤ t`, and these values are found in the set `M = (⟦#S, t#S⟧ - K⟦1, t⟧) ∩ (κ, ∞)`.
  let M := {x ∈ ((Icc #S (t * #S)).map Nat.castEmbedding -
    K • (Icc 1 t).map Nat.castEmbedding : Finset ℝ) | κ < x}
  have smallA {A : Finset G} (hA : A.Nonempty) (hAt : #A ≤ t) : ex A ∈ M := by
    rw [mem_filter]
    refine ⟨sub_mem_sub ?_ ?_, (connectivity_le_expansion hK.le hS hA).lt_of_ne' <| H _ hA⟩
    · apply mem_map_of_mem
      exact mem_Icc.2 ⟨card_le_card_mul_left hA, by grw [card_mul_le, hAt]⟩
    · apply smul_mem_smul_finset
      apply mem_map_of_mem
      exact mem_Icc.2 ⟨Nat.one_le_iff_ne_zero.mpr hA.card_ne_zero, hAt⟩
  -- Now we take the minimum value of `M` (union `{κ + 1}` to handle the eventual emptiness of `M`
  -- and get better bounds). This will be strictly larger than `κ` by definition.
  have : (M ∪ {κ + 1}).Nonempty := by simp
  let k := (M ∪ {κ + 1}).min' this
  have : κ < k := by simp [k, M]
  -- By the property of infimum and the previous claim, there is `A` with `κ < ex A < k ≤ κ + 1`.
  -- But then the claim about large `A` implies that `#A ≤ t` and thus `ex A ∈ M` and `k ≤ ex A`,
  -- a contradiction.
  obtain ⟨A, hA, hAk⟩ := (connectivity_lt_iff hK.le hS).mp this
  have : ex A ≤ κ + 1 := hAk.le.trans <| min'_le _ _ (by simp)
  have := not_lt.mp (mt largeA this.not_gt)
  exact hAk.not_ge <| min'_le (M ∪ {κ + 1}) _ <| subset_union_left <| smallA hA this
/-
**Finset.exists_isFragment** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_isFragment (hK : K < 1) (hS : S.Nonempty) :
    ∃ A, IsFragment K S A := let ⟨A, _, hA⟩ := exists_nonempty_isFragment hK hS; ⟨A, hA⟩
/-
**Finset.exists_isAtom** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma exists_isAtom (hK : K < 1) (hS : S.Nonempty) : ∃ A, IsAtom K S A :=
  exists_minimalFor_of_wellFoundedLT _ _ <| exists_isFragment hK hS
/-
**Finset.connectivity_pos** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma connectivity_pos (hK : K < 1) (hS : S.Nonempty) : 0 < connectivity K S := by
  obtain ⟨A, hA, hSA⟩ := exists_nonempty_isFragment hK hS
  exact (expansion_pos hK hS hA).trans_eq hSA
/-
**Finset.not_isFragment_empty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma not_isFragment_empty (hK : K < 1) (hS : S.Nonempty) : ¬ IsFragment K S ∅ := by
  simp [IsFragment, (connectivity_pos hK hS).ne]
/-
**Finset.IsFragment.nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsFragment.nonempty (hK : K < 1) (hS : S.Nonempty) (hA : IsFragment K S A) :
    A.Nonempty := by
  by_contra! rfl
  simp [*, not_isFragment_empty hK hS] at hA
/-
**Finset.IsAtom.nonempty** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma IsAtom.nonempty (hK : K < 1) (hS : S.Nonempty) (hA : IsAtom K S A) : A.Nonempty :=
  hA.isFragment.nonempty hK hS

/-- For `K < 1` and finite nonempty `S ⊆ G`, there exists a finite subgroup `H ≤ G` that is also
an atom for `K` and `S`. -/
/-
**Finset.exists_subgroup_isAtom** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `K < 1` and finite nonempty `S ⊆ G`, there exists a finite subgroup `H ≤ G` 
that is also
an atom for `K` and `S`.
-/
private lemma exists_subgroup_isAtom (hK : K < 1) (hS : S.Nonempty) :
    ∃ (H : Subgroup G) (_ : Fintype H), IsAtom K S (Set.toFinset H) := by
  -- We take any atom `N` of `G` with respect to `K` and `S`. Since left multiples of `N` (which
  -- are atoms as well) partition `G` by `IsAtom.eq_of_inter_nonempty`, we will deduce that a left
  -- multiple that contains `1` is a (finite) subgroup of `G`.
  obtain ⟨N, hN⟩ := exists_isAtom hK hS
  obtain ⟨n, hn⟩ := IsAtom.nonempty hK hS hN
  have one_mem_carrier : 1 ∈ n⁻¹ •> N := by simpa [mem_inv_smul_finset_iff]
  have self_mem_smul_carrier (x : G) : x ∈ x • n⁻¹ • N := by
    apply smul_mem_smul_finset (a := x) at one_mem_carrier
    simpa only [smul_eq_mul, mul_one] using! one_mem_carrier
  let H : Subgroup G := {
    carrier := n⁻¹ •> N
    one_mem' := mod_cast one_mem_carrier
    mul_mem' {a b} ha hb := by
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a) at hb
      rw [smul_eq_mul] at hb
      have : (n⁻¹ •> N ∩ a •> n⁻¹ •> N).Nonempty := ⟨a, by
        simpa only [mem_inter] using! ⟨ha, self_mem_smul_carrier a⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a) this] using! hb
    inv_mem' {a} ha := by
      rw [← coe_smul_finset, mem_coe] at *
      apply smul_mem_smul_finset (a := a⁻¹) at ha
      rw [smul_eq_mul, inv_mul_cancel] at ha
      have : (n⁻¹ •> N ∩ a⁻¹ •> n⁻¹ •> N).Nonempty := ⟨1, by simpa using! ⟨one_mem_carrier, ha⟩⟩
      simpa only [← (hN.smul_finset n⁻¹).eq_of_inter_nonempty hK.le hS
        ((hN.smul_finset n⁻¹).smul_finset a⁻¹) this] using! self_mem_smul_carrier a⁻¹
  }
  refine ⟨H, Fintype.ofFinset (n⁻¹ •> N) fun a => ?_, ?_⟩
  · simpa only [← mem_coe, coe_smul_finset] using! H.mem_carrier
  · simpa [Set.toFinset_smul_set, toFinset_coe, H] using! IsAtom.smul_finset n⁻¹ hN

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- If `S` is nonempty such that there is `A` with `|S| ≤ |A|` such that `|A * S| ≤ (2 - ε) * |S|`
for some `0 < ε ≤ 1`, then there is a finite subgroup `H` of `G` of size `|H| ≤ (2 / ε - 1) * |S|`
such that `S` is covered by at most `2 / ε - 1` right cosets of `H`. -/
/-
**Finset.card_mul_finset_lt_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：card_mul_finset_lt_two {ε : Real} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hS : S.Non
empty) (hA : exists A : Finset G, #S <= #A ∧ #(A * S) <= (2 - ε) * #S) : exists 
(H : Subgroup G) (_ : Fintype H) (Z : Finset G), Fintype.card H <= (2 / ε - 1) *
 #S ∧ #Z <= 2 / ε - 1 ∧ (S : Set G) subseteq H * Z
参数：hε₀ : 0 < ε；hε₁ : ε <= 1；hS : S.Nonempty；hA : exists A : Finset G, #S <= #A ∧
 #(A * S) <= (2 - ε) * #S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
（共 176 条，此处仅展示前 30 条）

--- 原说明 ---
If `S` is nonempty such that there is `A` with `|S| ≤ |A|` such that `|A * S| ≤ 
(2 - ε) * |S|`
for some `0 < ε ≤ 1`, then there is a finite subgroup `H` of `G` of size `|H| ≤ 
(2 / ε - 1) * |S|`
such that `S` is covered by at most `2 / ε - 1` right cosets of `H`.
-/
theorem card_mul_finset_lt_two {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hS : S.Nonempty)
    (hA : ∃ A : Finset G, #S ≤ #A ∧ #(A * S) ≤ (2 - ε) * #S) :
    ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      Fintype.card H ≤ (2 / ε - 1) * #S ∧ #Z ≤ 2 / ε - 1 ∧ (S : Set G) ⊆ H * Z := by
  let K := 1 - ε / 2
  have hK : K < 1 := by unfold K; linarith [hε₀]
  let ex := expansion K S
  let κ := connectivity K S
  -- We will show that an atomic subgroup `H ≤ G` with respect to `K` and `S` and the right coset
  -- representing finset of `S` acting on `H` are adequate choices for the theorem
  obtain ⟨H, _, hH⟩ := exists_subgroup_isAtom hK hS
  obtain ⟨Z, hZS, hHZS, hZinj⟩ := exists_subset_mul_eq_mul_injOn H S
  -- We only use the existence of `A` given by assumption to get a good bound on `ex H` solely
  -- in terms of `#S` and `ε`.
  obtain ⟨A, hA₁, hA₂⟩ := hA
  have calc₁ : ex (Set.toFinset H) ≤ (1 - ε / 2) * #S := by
    calc
          ex (Set.toFinset H)
      _ = κ                               := hH.isFragment
      _ ≤ #(A * S) - K * #A :=
        connectivity_le_expansion hK.le hS <| card_pos.mp <| hS.card_pos.trans_le hA₁
      _ ≤ (2 - ε) * #S - (1 - ε / 2) * #S := by gcongr; linarith
      _ = (1 - ε / 2) * #S                := by linarith
  refine ⟨H, inferInstance, Z, ?cardH, ?cardZ, by
    simpa only [hHZS] using Set.subset_mul_right _ H.one_mem⟩
  -- Bound on `#H` follows easily from the previous calculation.
  case cardH =>
    rw [← mul_le_mul_iff_right₀ (a := ε / 2) (by positivity)]
    calc
            ε / 2 * (Fintype.card H)
        _ = ε / 2 * #(H : Set G).toFinset   := by
          simp only [Set.toFinset_card, SetLike.coe_sort_coe]
        _ = (1 - K) * #(H : Set G).toFinset := by ring
        _ ≤ ex (Set.toFinset H)             := mul_card_le_expansion hS
        _ ≤ (1 - ε / 2) * #S                := calc₁
        _ = ε / 2 * ((2 / ε - 1) * #S)      := by field
  -- To show the bound on `#Z`, we note that `#Z = #(HS) / #H` and show `#(HS) ≤ (2 / ε - 1) * #H`.
  case cardZ =>
    calc
          (#Z : ℝ)
      _ = #(H : Set G).toFinset * #Z / #(H : Set G).toFinset          := by field
      _ = #(Set.toFinset H * Z) / #(H : Set G).toFinset               := by
        simp [← card_mul_eq_mul_card_of_injOn_opSMul hZinj, Nat.cast_mul]
      _ = #(Set.toFinset H * S) / #(H : Set G).toFinset               := by
        congr 3; simpa using congr(($hHZS).toFinset)
      _ ≤ (2 / ε - 1) * #(H : Set G).toFinset / #(H : Set G).toFinset := ?_
      _ = 2 / ε - 1                                                   := by field
    gcongr
    -- Finally, to show `#(HS) ≤ (2 / ε - 1) * #H`, we multiply both sides by `1 - K = ε / 2` and
    -- show `#(HS) = K * #H + ex H ≤ K * #H + (1 - ε / 2) * #S ≤ K * #H + (1 - ε / 2) * #(HS)`,
    -- where we used `calc₁` again.
    rw [← mul_le_mul_iff_right₀ (show 0 < 1 - K by linarith [hK])]
    suffices (1 - K) * #(Set.toFinset H * S) ≤ (1 - ε / 2) * #(H : Set G).toFinset by
      apply le_of_le_of_eq this; simp [K]; field
    rw [sub_mul, one_mul, sub_le_iff_le_add]
    calc
          (#(Set.toFinset H * S) : ℝ)
      _ = K * #(H : Set G).toFinset + (#(Set.toFinset H * S) - K * #(H : Set G).toFinset) := by ring
      _ = K * #(H : Set G).toFinset + ex (Set.toFinset H)                 := rfl
      _ ≤ K * #(H : Set G).toFinset + (1 - ε / 2) * #(Set.toFinset H * S) := by
        grw [calc₁]
        gcongr
        · linarith
        · simp only [Set.mem_toFinset, SetLike.mem_coe, H.one_mem, subset_mul_right]

/-- Corollary of `card_mul_finset_lt_two` in the case `A = S`, giving characterisation of sets of
doubling less than `2 - ε`. -/
/-
**Finset.doubling_lt_two** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：doubling_lt_two {ε : Real} (hε₀ : 0 < ε) (hε₁ : ε <= 1) (hA₀ : A.Nonempty)
 (hA₁ : #(A * A) <= (2 - ε) * #A) : exists (H : Subgroup G) (_ : Fintype H) (Z :
 Finset G), Fintype.card H <= (2 / ε - 1) * #A ∧ #Z <= 2 / ε - 1 ∧ (A : Set G) s
ubseteq H * Z
参数：hε₀ : 0 < ε；hε₁ : ε <= 1；hA₀ : A.Nonempty；hA₁ : #(A * A) <= (2 - ε) * #A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finset.card_mul_finset_lt_two`：card_mul_finset_lt_two {ε : Real} (hε₀ : 
0 < ε) (hε₁ : ε <= 1) (hS : S.Nonempty) (hA : exists A : Finset G, #S <= #A ∧ #(
A * S) <= (2 - ε) *…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
Corollary of `card_mul_finset_lt_two` in the case `A = S`, giving characterisati
on of sets of
doubling less than `2 - ε`.
-/
theorem doubling_lt_two {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε ≤ 1) (hA₀ : A.Nonempty)
    (hA₁ : #(A * A) ≤ (2 - ε) * #A) : ∃ (H : Subgroup G) (_ : Fintype H) (Z : Finset G),
      Fintype.card H ≤ (2 / ε - 1) * #A ∧ #Z ≤ 2 / ε - 1 ∧ (A : Set G) ⊆ H * Z :=
  card_mul_finset_lt_two hε₀ hε₁ hA₀ ⟨A, by rfl, hA₁⟩

end Finset

