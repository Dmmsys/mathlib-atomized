/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Data.Finite.Prod
public import Mathlib.Algebra.Group.Pointwise.Set.Basic

/-! # Finiteness lemmas for pointwise operations on sets -/

public section

assert_not_exists MulAction MonoidWithZero

open scoped Pointwise

variable {F α β γ : Type*}

namespace Set

section One

variable [One α]

@[to_additive (attr := simp)]
/--
theorem `finite_one` / 定理 `finite_one`

English:
theorem finite_one
  statement: (1 : Set α).Finite
  proof: finite_singleton _

中文:
定理 finite_one
  结论: (1 : 集合 α).有限
  证明: finite_singleton _

Depends on / 依赖: finite_singleton
-/
theorem finite_one : (1 : Set α).Finite :=
  finite_singleton _

end One

section Mul

variable [Mul α] {s t : Set α}

@[to_additive]
/--
theorem `Finite.mul` / 定理 `Finite.mul`

English:
theorem Finite.mul
  statement: s.Finite -> t.Finite -> (s * t).Finite
  proof: Finite.image2 _

中文:
定理 有限.mul
  结论: s.有限 -> t.有限 -> (s * t).有限
  证明: Finite.image2 _

Depends on / 依赖: Finite, Finite.image2, image2
-/
theorem Finite.mul : s.Finite -> t.Finite -> (s * t).Finite :=
  Finite.image2 _

/-- Multiplication preserves finiteness. -/
@[to_additive /-- Addition preserves finiteness. -/]
/--
Instance `fintypeMul` / 实例 `fintypeMul`

English:
instance fintypeMul
  signature: [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t]
  body: Set.fintypeImage2 _ _ _

中文:
实例 fintypeMul
  签名: [DecidableEq α] (s t : 集合 α) [有限类型 s] [有限类型 t]
  定义体: Set.fintypeImage2 _ _ _

Depends on / 依赖: Set.fintypeImage2, fintypeImage2
-/
instance fintypeMul [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s * t) :=
  Set.fintypeImage2 _ _ _

end Mul

section Monoid

variable [Monoid α] {s t : Set α}

@[to_additive]
/--
Instance `decidableMemMul` / 实例 `decidableMemMul`

English:
instance decidableMemMul
  signature: [Fintype α] [DecidableEq α] [DecidablePred (· in s)]
  body: fun _ => decidable_of_iff _ mem_mul.symm

@[to_additive]

中文:
实例 decidableMemMul
  签名: [有限类型 α] [DecidableEq α] [DecidablePred (· in s)]
  定义体: fun _ => decidable_of_iff _ mem_mul.symm

@[to_additive]

Depends on / 依赖: decidable_of_iff, mem_mul, mem_mul.symm
-/
instance decidableMemMul [Fintype α] [DecidableEq α] [DecidablePred (· in s)]
    [DecidablePred (· in t)] : DecidablePred (· in s * t) := fun _ => decidable_of_iff _ mem_mul.symm

@[to_additive]
/--
Instance `decidableMemPow` / 实例 `decidableMemPow`

English:
instance decidableMemPow
  signature: [Fintype α] [DecidableEq α] [DecidablePred (· in s)] (n : Nat)
  body: by
  induction n with
  | zero =>
    simp only [pow_zero, mem_one]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    infer_instance

中文:
实例 decidableMemPow
  签名: [有限类型 α] [DecidableEq α] [DecidablePred (· in s)] (n : 自然数)
  定义体: by
  induction n with
  | zero =>
    simp only [pow_zero, mem_one]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    infer_instance

Depends on / 依赖: infer_instance, mem_one, pow_succ, pow_zero
-/
instance decidableMemPow [Fintype α] [DecidableEq α] [DecidablePred (· in s)] (n : Nat) :
    DecidablePred (· in s ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, mem_one]
    infer_instance
  | succ n ih =>
    rw [pow_succ]
    infer_instance

end Monoid

section SMul

variable [SMul α β] {s : Set α} {t : Set β}

@[to_additive]
/--
theorem `Finite.smul` / 定理 `Finite.smul`

English:
theorem Finite.smul
  statement: s.Finite -> t.Finite -> (s • t).Finite
  proof: Finite.image2 _

中文:
定理 有限.smul
  结论: s.有限 -> t.有限 -> (s • t).有限
  证明: Finite.image2 _

Depends on / 依赖: Finite, Finite.image2, image2
-/
theorem Finite.smul : s.Finite -> t.Finite -> (s • t).Finite :=
  Finite.image2 _

end SMul

section HasSMulSet

variable [SMul α β] {s : Set β} {a : α}

@[to_additive]
/--
theorem `Finite.smul_set` / 定理 `Finite.smul_set`

English:
theorem Finite.smul_set
  statement: s.Finite -> (a • s).Finite
  proof: Finite.image _

@[to_additive]

中文:
定理 有限.smul_set
  结论: s.有限 -> (a • s).有限
  证明: Finite.image _

@[to_additive]

Depends on / 依赖: Finite, Finite.image
-/
theorem Finite.smul_set : s.Finite -> (a • s).Finite :=
  Finite.image _

@[to_additive]
/--
theorem `Infinite.of_smul_set` / 定理 `Infinite.of_smul_set`

English:
theorem Infinite.of_smul_set
  statement: (a • s).Infinite -> s.Infinite
  proof: Infinite.of_image _

中文:
定理 无限.of_smul_set
  结论: (a • s).无限 -> s.无限
  证明: Infinite.of_image _

Depends on / 依赖: Infinite, Infinite.of_image, of_image
-/
theorem Infinite.of_smul_set : (a • s).Infinite -> s.Infinite :=
  Infinite.of_image _

end HasSMulSet

section Vsub

variable [VSub α β] {s t : Set β}

/--
theorem `Finite.vsub` / 定理 `Finite.vsub`

English:
theorem Finite.vsub
  given: (hs : s.Finite) (ht : t.Finite)
  statement: Set.Finite (s -ᵥ t)
  proof: hs.image2 _ ht

中文:
定理 有限.vsub
  条件: (hs : s.有限) (ht : t.有限)
  结论: 集合.有限 (s -ᵥ t)
  证明: hs.image2 _ ht

Depends on / 依赖: hs.image2, image2
-/
theorem Finite.vsub (hs : s.Finite) (ht : t.Finite) : Set.Finite (s -ᵥ t) :=
  hs.image2 _ ht

end Vsub

section Cancel

variable [Mul α] [IsLeftCancelMul α] [IsRightCancelMul α] {s t : Set α}

@[to_additive]
/--
lemma `finite_mul` / 引理 `finite_mul`

English:
lemma finite_mul
  statement: (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅
  proof: finite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

@[to_additive]

中文:
引理 finite_mul
  结论: (s * t).有限 ↔ s.有限 ∧ t.有限 ∨ s = ∅ ∨ t = ∅
  证明: finite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

@[to_additive]

Depends on / 依赖: finite_image2, mul_left_injective, mul_right_injective
-/
lemma finite_mul : (s * t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

@[to_additive]
/--
lemma `infinite_mul` / 引理 `infinite_mul`

English:
lemma infinite_mul
  statement: (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty
  proof: infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

中文:
引理 infinite_mul
  结论: (s * t).无限 ↔ s.无限 ∧ t.非空 ∨ t.无限 ∧ s.非空
  证明: infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

Depends on / 依赖: infinite_image2, mul_left_injective, mul_right_injective
-/
lemma infinite_mul : (s * t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ => (mul_left_injective _).injOn) fun _ _ => (mul_right_injective _).injOn

end Cancel

section InvolutiveInv
variable [InvolutiveInv α] {s : Set α}

/--
lemma `finite_inv` / 引理 `finite_inv`

English:
lemma finite_inv
  statement: s⁻¹.Finite ↔ s.Finite
  proof: by
  rw [← image_inv_eq_inv]; rw [finite_image_iff inv_injective.injOn]

中文:
引理 finite_inv
  结论: s⁻¹.有限 ↔ s.有限
  证明: by
  rw [← image_inv_eq_inv]; rw [finite_image_iff inv_injective.injOn]
-/
@[to_additive (attr := simp)] lemma finite_inv : s⁻¹.Finite ↔ s.Finite := by
  rw [← image_inv_eq_inv]; rw [finite_image_iff inv_injective.injOn]

/--
lemma `infinite_inv` / 引理 `infinite_inv`

English:
lemma infinite_inv
  statement: s⁻¹.Infinite ↔ s.Infinite
  proof: finite_inv.not

@[to_additive] alias ⟨Finite.of_inv, Finite.inv⟩ := finite_inv

中文:
引理 infinite_inv
  结论: s⁻¹.无限 ↔ s.无限
  证明: finite_inv.not

@[to_additive] alias ⟨Finite.of_inv, Finite.inv⟩ := finite_inv
-/
@[to_additive (attr := simp)] lemma infinite_inv : s⁻¹.Infinite ↔ s.Infinite := finite_inv.not

@[to_additive] alias ⟨Finite.of_inv, Finite.inv⟩ := finite_inv

end InvolutiveInv

section Div
variable [Div α] {s t : Set α}

/--
lemma `Finite.div` / 引理 `Finite.div`

English:
lemma Finite.div
  statement: s.Finite -> t.Finite -> (s / t).Finite
  proof: .image2 _

中文:
引理 有限.div
  结论: s.有限 -> t.有限 -> (s / t).有限
  证明: .image2 _
-/
@[to_additive] lemma Finite.div : s.Finite -> t.Finite -> (s / t).Finite := .image2 _

/-- Division preserves finiteness. -/
@[to_additive /-- Subtraction preserves finiteness. -/]
/--
Instance `fintypeDiv` / 实例 `fintypeDiv`

English:
instance fintypeDiv
  signature: [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t]
  body: Set.fintypeImage2 _ _ _

中文:
实例 fintypeDiv
  签名: [DecidableEq α] (s t : 集合 α) [有限类型 s] [有限类型 t]
  定义体: Set.fintypeImage2 _ _ _

Depends on / 依赖: Set.fintypeImage2, fintypeImage2
-/
instance fintypeDiv [DecidableEq α] (s t : Set α) [Fintype s] [Fintype t] : Fintype (s / t) :=
  Set.fintypeImage2 _ _ _

end Div

section Group

variable [Group α] {s t : Set α}

@[to_additive]
/--
lemma `finite_div` / 引理 `finite_div`

English:
lemma finite_div
  statement: (s / t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅
  proof: finite_image2 (fun _ _ => div_left_injective.injOn) fun _ _ => div_right_injective.injOn

@[to_additive]

中文:
引理 finite_div
  结论: (s / t).有限 ↔ s.有限 ∧ t.有限 ∨ s = ∅ ∨ t = ∅
  证明: finite_image2 (fun _ _ => div_left_injective.injOn) fun _ _ => div_right_injective.injOn

@[to_additive]

Depends on / 依赖: div_left_injective, div_left_injective.injOn, div_right_injective, div_right_injective.injOn, finite_image2
-/
lemma finite_div : (s / t).Finite ↔ s.Finite ∧ t.Finite ∨ s = ∅ ∨ t = ∅ :=
  finite_image2 (fun _ _ => div_left_injective.injOn) fun _ _ => div_right_injective.injOn

@[to_additive]
/--
lemma `infinite_div` / 引理 `infinite_div`

English:
lemma infinite_div
  statement: (s / t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty
  proof: infinite_image2 (fun _ _ => div_left_injective.injOn) fun _ _ => div_right_injective.injOn

中文:
引理 infinite_div
  结论: (s / t).无限 ↔ s.无限 ∧ t.非空 ∨ t.无限 ∧ s.非空
  证明: infinite_image2 (fun _ _ => div_left_injective.injOn) fun _ _ => div_right_injective.injOn

Depends on / 依赖: div_left_injective, div_left_injective.injOn, div_right_injective, div_right_injective.injOn, infinite_image2
-/
lemma infinite_div : (s / t).Infinite ↔ s.Infinite ∧ t.Nonempty ∨ t.Infinite ∧ s.Nonempty :=
  infinite_image2 (fun _ _ => div_left_injective.injOn) fun _ _ => div_right_injective.injOn

end Group

end Set

open Set

namespace Group

variable {G : Type*} [Group G] [Fintype G] (S : Set G)

@[to_additive]
/--
theorem `card_pow_eq_card_pow_card_univ` / 定理 `card_pow_eq_card_pow_card_univ`

English:
theorem card_pow_eq_card_pow_card_univ
  given: [forall k : Nat, DecidablePred (· in S ^ k)]
  proof: by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases S.eq_empty_or_nonempty with (rfl | ⟨a, ha⟩)
  · refine fun k hk => Fintype.card_congr ?_
    rw [empty_pow (hG.trans_le hk).ne']; rw [empty_pow (ne_of_gt hG)]
  have key : forall (a) (s t : Set G) [Fintype s] [Fintype t],
      (forall b

中文:
定理 card_pow_eq_card_pow_card_univ
  条件: [对任意 k : 自然数, DecidablePred (· in S ^ k)]
  证明: by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases S.eq_empty_or_nonempty with (rfl | ⟨a, ha⟩)
  · refine fun k hk => Fintype.card_congr ?_
    rw [empty_pow (hG.trans_le hk).ne']; rw [empty_pow (ne_of_gt hG)]
  have key : forall (a) (s t : Set G) [Fintype s] [Fintype t],
      (forall b

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_congr, Fintype.card_le_of_injective, Fintype.card_pos, S.eq_empty_or_nonempty, Subtype, Subtype.ext, card_congr, card_le_of_injective, card_pos, empty_pow, eq_empty_or_nonempty, hG.trans_le, mul_right_c, ne_of_gt, trans_le
-/
theorem card_pow_eq_card_pow_card_univ [forall k : Nat, DecidablePred (· in S ^ k)] :
    forall k, Fintype.card G <= k -> Fintype.card (↥(S ^ k)) = Fintype.card (↥(S ^ Fintype.card G)) := by
  have hG : 0 < Fintype.card G := Fintype.card_pos
  rcases S.eq_empty_or_nonempty with (rfl | ⟨a, ha⟩)
  · refine fun k hk => Fintype.card_congr ?_
    rw [empty_pow (hG.trans_le hk).ne']; rw [empty_pow (ne_of_gt hG)]
  have key : forall (a) (s t : Set G) [Fintype s] [Fintype t],
      (forall b : G, b in s -> b * a in t) -> Fintype.card s <= Fintype.card t := by
    refine fun a s t _ _ h => Fintype.card_le_of_injective (fun ⟨b, hb⟩ => ⟨b * a, h b hb⟩) ?_
    rintro ⟨b, hb⟩ ⟨c, hc⟩ hbc
    exact Subtype.ext (mul_right_cancel (Subtype.ext_iff.mp hbc))
  have mono : Monotone (fun n => Fintype.card (↥(S ^ n)) : Nat -> Nat) :=
    monotone_nat_of_le_succ fun n => key a _ _ fun b hb => Set.mul_mem_mul hb ha
  refine fun _ => Nat.stabilises_of_monotone mono (fun n => set_fintype_card_le_univ (S ^ n))
    fun n h => le_antisymm (mono (n + 1).le_succ) (key a⁻¹ (S ^ (n + 2)) (S ^ (n + 1)) ?_)
  replace h₂ : S ^ n * {a} = S ^ (n + 1) := by
    have : Fintype (S ^ n * Set.singleton a) := by
      classical
      apply fintypeMul
    refine Set.eq_of_subset_of_card_le ?_ (le_trans (ge_of_eq h) ?_)
    · exact mul_subset_mul Set.Subset.rfl (Set.singleton_subset_iff.mpr ha)
    · convert! key a (S ^ n) (S ^ n * { a }) fun b hb => Set.mul_mem_mul hb (Set.mem_singleton a)
  rw [pow_succ']; rw [← h₂]; rw [← mul_assoc]; rw [← pow_succ']; rw [h₂]; rw [mul_singleton]; rw [forall_mem_image]
  intro x hx
  rwa [mul_inv_cancel_right]

end Group
