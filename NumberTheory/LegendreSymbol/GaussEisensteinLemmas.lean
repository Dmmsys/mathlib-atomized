/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Nat.Prime.Factorial
public import Mathlib.NumberTheory.LegendreSymbol.Basic

/-!
# Lemmas of Gauss and Eisenstein

This file contains the Lemmas of Gauss and Eisenstein on the Legendre symbol.
The main results are `ZMod.gauss_lemma` and `ZMod.eisenstein_lemma`.
-/

public section


open Finset Nat

open scoped Nat

section GaussEisenstein

namespace ZMod

/-- The image of the map sending a nonzero natural number `x ≤ p / 2` to the absolute value
  of the integer in `(-p/2, p/2]` that is congruent to `a * x mod p` is the set
  of nonzero natural numbers `x` such that `x ≤ p / 2`. -/
/-
**ZMod.Ico_map_valMinAbs_natAbs_eq_Ico_map_id** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：Ico_map_valMinAbs_natAbs_eq_Ico_map_id (p : Nat) [hp : Fact p.Prime] (a : 
ZMod p) (hap : a != 0) : ((Ico 1 (p / 2).succ).1.map fun (x : Nat) => (a * x).va
lMinAbs.natAbs) = (Ico 1 (p / 2).succ).1.map fun a => a
参数：p : Nat；a : ZMod p；hap : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `not_lt_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a ≤ b → ¬b
 < a
· 使用定理 `Nat.le_of_dvd`：∀ {m n : ℕ}, 0 < n → m ∣ n → m ≤ n
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `ZMod.natAbs_valMinAbs_le`：natAbs_valMinAbs_le [NeZero n] (x : ZMod n) : 
x.valMinAbs.natAbs <= n / 2
· 使用定理 `NeZero.of_gt'`：∀ {α : Type u_1} {a : α} [inst : Zero α] [inst_1 : Preord
er α] [IsBotZeroClass α] [inst_3 : One α] [Fact (1 < a)],   NeZero a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
The image of the map sending a nonzero natural number `x ≤ p / 2` to the absolut
e value
  of the integer in `(-p/2, p/2]` that is congruent to `a * x mod p` is the set
  of nonzero natural numbers `x` such that `x ≤ p / 2`.
-/
theorem Ico_map_valMinAbs_natAbs_eq_Ico_map_id (p : ℕ) [hp : Fact p.Prime] (a : ZMod p)
    (hap : a ≠ 0) : ((Ico 1 (p / 2).succ).1.map fun (x : ℕ) => (a * x).valMinAbs.natAbs) =
    (Ico 1 (p / 2).succ).1.map fun a => a := by
  have he : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x ≠ 0 ∧ x ≤ p / 2 := by grind
  have hep : ∀ {x}, x ∈ Ico 1 (p / 2).succ → x < p := fun hx =>
    lt_of_le_of_lt (he hx).2 (Nat.div_lt_self hp.1.pos (by decide))
  have hpe : ∀ {x}, x ∈ Ico 1 (p / 2).succ → ¬p ∣ x := fun hx hpx =>
    not_lt_of_ge (le_of_dvd (Nat.pos_of_ne_zero (he hx).1) hpx) (hep hx)
  have hmem : ∀ (x : ℕ) (_ : x ∈ Ico 1 (p / 2).succ),
      (a * x : ZMod p).valMinAbs.natAbs ∈ Ico 1 (p / 2).succ := by
    intro x hx
    simp [hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hx, one_le_iff_ne_zero, natAbs_valMinAbs_le _]
  have hsurj : ∀ (b : ℕ) (hb : b ∈ Ico 1 (p / 2).succ),
      ∃ x, ∃ _ : x ∈ Ico 1 (p / 2).succ, (a * x : ZMod p).valMinAbs.natAbs = b := by
    intro b hb
    refine ⟨(b / a : ZMod p).valMinAbs.natAbs, mem_Ico.mpr ⟨?_, ?_⟩, ?_⟩
    · apply Nat.pos_of_ne_zero
      simp only [div_eq_mul_inv, hap, CharP.cast_eq_zero_iff (ZMod p) p, hpe hb, not_false_iff,
        valMinAbs_eq_zero, inv_eq_zero, Int.natAbs_eq_zero, Ne, _root_.mul_eq_zero, or_self_iff]
    · apply lt_succ_of_le; apply natAbs_valMinAbs_le
    · rw [natCast_natAbs_valMinAbs]
      split_ifs
      · rw [mul_div_cancel₀ _ hap, valMinAbs_def_pos, val_cast_of_lt (hep hb),
          if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
      · rw [mul_neg, mul_div_cancel₀ _ hap, natAbs_valMinAbs_neg, valMinAbs_def_pos,
          val_cast_of_lt (hep hb), if_pos (le_of_lt_succ (mem_Ico.1 hb).2), Int.natAbs_natCast]
  exact Multiset.map_eq_map_of_bij_of_nodup _ _ (Finset.nodup _) (Finset.nodup _)
    (fun x _ => (a * x : ZMod p).valMinAbs.natAbs) hmem
    (inj_on_of_surj_on_of_card_le _ hmem hsurj le_rfl) hsurj (fun _ _ => rfl)
/-
**ZMod.gauss_lemma_aux** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：gauss_lemma_aux (p : Nat) [hp : Fact p.Prime] {a : Int} (hap : (a : ZMod p
) != 0) : (a ^ (p / 2) : ZMod p) = ((-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (
a * x.cast : ZMod p).val} :)
参数：p : Nat；hap : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Nat.Prime.dvd_factorial`：∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p
 ≤ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `_private.Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas.0.ZMo
d.gauss_lemma_aux₁`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] {a : ℤ},   ↑a ≠ 0 →   
  ↑a ^ (p / 2) * ↑(p / 2).factorial =       (-1) ^ {x ∈ Finset.Ico 1 (p / 2).suc
…
-/
private theorem gauss_lemma_aux₁ (p : ℕ) [Fact p.Prime] {a : ℤ} (hap : (a : ZMod p) ≠ 0) :
    (a ^ (p / 2) * (p / 2)! : ZMod p) =
     (-1 : ZMod p) ^ #{x ∈ Ico 1 (p / 2).succ | ¬ (a * x.cast : ZMod p).val ≤ p / 2} * (p / 2)! :=
  calc
    (a ^ (p / 2) * (p / 2)! : ZMod p) = ∏ x ∈ Ico 1 (p / 2).succ, a * x := by
      rw [prod_mul_distrib, ← prod_natCast, prod_Ico_id_eq_factorial, prod_const, card_Ico,
        Nat.add_one_sub_one]; simp
    _ = ∏ x ∈ Ico 1 (p / 2).succ, ↑((a * x : ZMod p).val) := by simp
    _ = ∏ x ∈ Ico 1 (p / 2).succ, (if (a * x : ZMod p).val ≤ p / 2 then (1 : ZMod p) else -1) *
        (a * x : ZMod p).valMinAbs.natAbs :=
      (prod_congr rfl fun _ _ => by
        simp only [natCast_natAbs_valMinAbs]
        split_ifs <;> simp)
    _ = (-1 : ZMod p) ^ #{x ∈ Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val ≤ p / 2} *
          ∏ x ∈ Ico 1 (p / 2).succ, ↑((a * x : ZMod p).valMinAbs.natAbs) := by
      rw [prod_mul_distrib, Finset.prod_ite]
      simp
    _ = (-1 : ZMod p) ^ #{x ∈ Ico 1 (p / 2).succ | ¬(a * x.cast : ZMod p).val ≤ p / 2} *
          (p / 2)! := by
      rw [← prod_natCast, Finset.prod_eq_multiset_prod,
        Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap, ← Finset.prod_eq_multiset_prod,
        prod_Ico_id_eq_factorial]
/-
**ZMod.gauss_lemma_aux** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：gauss_lemma_aux (p : Nat) [hp : Fact p.Prime] {a : Int} (hap : (a : ZMod p
) != 0) : (a ^ (p / 2) : ZMod p) = ((-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < (
a * x.cast : ZMod p).val} :)
参数：p : Nat；hap : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `mul_left_inj'`：mul_left_inj' (hc : c != 0) : a * c = b * c ↔ a = b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `CharP.cast_eq_zero_iff`：∀ (R : Type u_2) {inst : AddMonoidWithOne R} (p 
: outParam ℕ) [self : CharP R p] (x : ℕ), ↑x = 0 ↔ p ∣ x
· 使用定理 `Nat.Prime.dvd_factorial`：∀ {n p : ℕ}, Nat.Prime p → (p ∣ n.factorial ↔ p
 ≤ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_pow`：∀ {R : Type u_1} [inst : Ring R] (n : ℤ) (m : ℕ), ↑(n ^ m)
 = ↑n ^ m
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `_private.Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas.0.ZMo
d.gauss_lemma_aux₁`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] {a : ℤ},   ↑a ≠ 0 →   
  ↑a ^ (p / 2) * ↑(p / 2).factorial =       (-1) ^ {x ∈ Finset.Ico 1 (p / 2).suc
…
-/
theorem gauss_lemma_aux (p : ℕ) [hp : Fact p.Prime] {a : ℤ} (hap : (a : ZMod p) ≠ 0) :
    (a ^ (p / 2) : ZMod p) =
      ((-1) ^ #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} :) :=
  (mul_left_inj' (show ((p / 2)! : ZMod p) ≠ 0 by
    rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p, hp.1.dvd_factorial, not_le]
    exact Nat.div_lt_self hp.1.pos (by decide))).1 <| by
      simpa using gauss_lemma_aux₁ p hap

/-- **Gauss' lemma**. The Legendre symbol can be computed by considering the number of naturals less
  than `p/2` such that `(a * x) % p > p / 2`. -/
/-
**ZMod.gauss_lemma** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：gauss_lemma {p : Nat} [h : Fact p.Prime] {a : Int} (hp : p != 2) (ha0 : (a
 : ZMod p) != 0) : legendreSym p a = (-1) ^ #{x in Ico 1 (p / 2).succ | p / 2 < 
(a * x.cast : ZMod p).val}
参数：hp : p != 2；ha0 : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.Prime.odd_of_ne_two`：∀ {p : ℕ}, Nat.Prime p → p ≠ 2 → Odd p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `legendreSym.eq_pow`：eq_pow (a : Int) : (legendreSym p a : ZMod p) = (a :
 ZMod p) ^ (p / 2)
· 使用定理 `ZMod.gauss_lemma_aux`：gauss_lemma_aux (p : Nat) [hp : Fact p.Prime] {a :
 Int} (hap : (a : ZMod p) != 0) : (a ^ (p / 2) : ZMod p) = ((-1) ^ #{x in Ico 1 
(p / 2).su…
· 使用定理 `legendreSym.eq_one_or_neg_one`：eq_one_or_neg_one {a : Int} (ha : (a : ZM
od p) != 0) : legendreSym p a = 1 ∨ legendreSym p a = -1
· 使用定理 `neg_one_pow_eq_or`：∀ (R : Type u) [inst : Monoid R] [inst_1 : HasDistrib
Neg R] (n : ℕ), (-1) ^ n = 1 ∨ (-1) ^ n = -1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ZMod.ne_neg_self`：ne_neg_self {n : Nat} (hn : Odd n) {a : ZMod n} (ha : 
a != 0) : a != -a
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.Prime.one_lt'`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], Fact (1 < p)
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
**Gauss' lemma**. The Legendre symbol can be computed by considering the number 
of naturals less
  than `p/2` such that `(a * x) % p > p / 2`.
-/
theorem gauss_lemma {p : ℕ} [h : Fact p.Prime] {a : ℤ} (hp : p ≠ 2) (ha0 : (a : ZMod p) ≠ 0) :
    legendreSym p a = (-1) ^ #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} := by
  replace hp : Odd p := h.out.odd_of_ne_two hp
  have : (legendreSym p a : ZMod p) =
      (((-1) ^ #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} : ℤ) : ZMod p) := by
    rw [legendreSym.eq_pow, gauss_lemma_aux p ha0]
  cases legendreSym.eq_one_or_neg_one p ha0 <;>
  cases neg_one_pow_eq_or ℤ #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} <;>
  simp_all [ne_neg_self hp one_ne_zero, (ne_neg_self hp one_ne_zero).symm]
/-
**ZMod.eisenstein_lemma_aux** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：eisenstein_lemma_aux (p : Nat) [Fact p.Prime] [Fact (p % 2 = 1)] {a : Nat}
 (ha2 : a % 2 = 1) (hap : (a : ZMod p) != 0) : #{x in Ico 1 (p / 2).succ | p / 2
 < (a * x.cast : ZMod p).val} ≡ ∑ x in Ico 1 (p / 2).succ, x * a / p [MOD 2]
参数：p : Nat；p % 2 = 1；ha2 : a % 2 = 1；hap : (a : ZMod p) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ZMod.neg_eq_self_mod_two`：neg_eq_self_mod_two (a : ZMod 2) : -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas.0.ZMo
d.eisenstein_lemma_aux₁`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] [hp2 : Fact (p % 
2 = 1)] {a : ℕ},   ↑a ≠ 0 →     ↑(∑ x ∈ Finset.Ico 1 (p / 2).succ, a * x) =     
  ↑{x…
-/
private theorem eisenstein_lemma_aux₁ (p : ℕ) [Fact p.Prime] [hp2 : Fact (p % 2 = 1)] {a : ℕ}
    (hap : (a : ZMod p) ≠ 0) :
    ((∑ x ∈ Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =
      #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
        ∑ x ∈ Ico 1 (p / 2).succ, x + (∑ x ∈ Ico 1 (p / 2).succ, a * x / p : ℕ) :=
  have hp2 : (p : ZMod 2) = (1 : ℕ) := (natCast_eq_natCast_iff _ _ _).2 hp2.1
  calc
    ((∑ x ∈ Ico 1 (p / 2).succ, a * x : ℕ) : ZMod 2) =
        ((∑ x ∈ Ico 1 (p / 2).succ, (a * x % p + p * (a * x / p)) : ℕ) : ZMod 2) := by
      simp only [mod_add_div]
    _ = (∑ x ∈ Ico 1 (p / 2).succ, ((a * x : ℕ) : ZMod p).val : ℕ) +
        (∑ x ∈ Ico 1 (p / 2).succ, a * x / p : ℕ) := by
      simp only [val_natCast]
      simp [sum_add_distrib, ← mul_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_sum, hp2]
    _ = _ :=
      congr_arg (· + _) <|
        calc
          ((∑ x ∈ Ico 1 (p / 2).succ, ((a * x : ℕ) : ZMod p).val : ℕ) : ZMod 2) =
              ∑ x ∈ Ico 1 (p / 2).succ, (((a * x : ZMod p).valMinAbs +
                if (a * x : ZMod p).val ≤ p / 2 then 0 else p : ℤ) : ZMod 2) := by
            simp only [(val_eq_ite_valMinAbs _).symm]; simp [Nat.cast_sum]
          _ = #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} +
              (∑ x ∈ Ico 1 (p / 2).succ, (a * x.cast : ZMod p).valMinAbs.natAbs : ℕ) := by
            simp [add_comm, sum_add_distrib, Finset.sum_ite, hp2, Nat.cast_sum]
          _ = _ := by
            rw [Finset.sum_eq_multiset_sum, Ico_map_valMinAbs_natAbs_eq_Ico_map_id p a hap, ←
              Finset.sum_eq_multiset_sum]
/-
**ZMod.eisenstein_lemma_aux** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：eisenstein_lemma_aux (p : Nat) [Fact p.Prime] [Fact (p % 2 = 1)] {a : Nat}
 (ha2 : a % 2 = 1) (hap : (a : ZMod p) != 0) : #{x in Ico 1 (p / 2).succ | p / 2
 < (a * x.cast : ZMod p).val} ≡ ∑ x in Ico 1 (p / 2).succ, x * a / p [MOD 2]
参数：p : Nat；p % 2 = 1；ha2 : a % 2 = 1；hap : (a : ZMod p) != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ZMod.natCast_eq_natCast_iff`：natCast_eq_natCast_iff (a b c : Nat) : (a :
 ZMod c) = (b : ZMod c) ↔ a ≡ b [MOD c]
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `ZMod.neg_eq_self_mod_two`：neg_eq_self_mod_two (a : ZMod 2) : -a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.NumberTheory.LegendreSymbol.GaussEisensteinLemmas.0.ZMo
d.eisenstein_lemma_aux₁`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)] [hp2 : Fact (p % 
2 = 1)] {a : ℕ},   ↑a ≠ 0 →     ↑(∑ x ∈ Finset.Ico 1 (p / 2).succ, a * x) =     
  ↑{x…
-/
theorem eisenstein_lemma_aux (p : ℕ) [Fact p.Prime] [Fact (p % 2 = 1)] {a : ℕ} (ha2 : a % 2 = 1)
    (hap : (a : ZMod p) ≠ 0) :
    #{x ∈ Ico 1 (p / 2).succ | p / 2 < (a * x.cast : ZMod p).val} ≡
      ∑ x ∈ Ico 1 (p / 2).succ, x * a / p [MOD 2] :=
  have ha2 : (a : ZMod 2) = (1 : ℕ) := (natCast_eq_natCast_iff _ _ _).2 ha2
  (natCast_eq_natCast_iff _ _ 2).1 <| sub_eq_zero.1 <| by
    simpa [add_left_comm, sub_eq_add_neg, ← mul_sum, mul_comm, ha2, Nat.cast_sum,
      add_neg_eq_iff_eq_add.symm, add_assoc] using
      Eq.symm (eisenstein_lemma_aux₁ p hap)
/-
**ZMod.div_eq_filter_card** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：div_eq_filter_card {a b c : Nat} (hb0 : 0 < b) (hc : a / b <= c) : a / b =
 #{x in Ico 1 c.succ | x * b <= a}
参数：hb0 : 0 < b；hc : a / b <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.card_Ico`：∀ (a b : ℕ), (Finset.Ico a b).card = b - a
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_div_iff_mul_le`：∀ {k x y : ℕ}, 0 < k → (x ≤ y / k ↔ x * k ≤ y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
-/
theorem div_eq_filter_card {a b c : ℕ} (hb0 : 0 < b) (hc : a / b ≤ c) :
    a / b = #{x ∈ Ico 1 c.succ | x * b ≤ a} :=
  calc
    a / b = #(Ico 1 (a / b).succ) := by simp
    _ = #{x ∈ Ico 1 c.succ | x * b ≤ a} :=
      congr_arg _ <| Finset.ext fun x => by
        have : x * b ≤ a → x ≤ c := fun h => le_trans (by rwa [le_div_iff_mul_le hb0]) hc
        simp [le_div_iff_mul_le hb0]; tauto

/-- The given sum is the number of integer points in the triangle formed by the diagonal of the
  rectangle `(0, p/2) × (0, q/2)`. -/
/-
**ZMod.sum_Ico_eq_card_lt** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The given sum is the number of integer points in the triangle formed by the diag
onal of the
  rectangle `(0, p/2) × (0, q/2)`.
-/
private theorem sum_Ico_eq_card_lt {p q : ℕ} :
    ∑ a ∈ Ico 1 (p / 2).succ, a * q / p =
      #{x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p ≤ x.1 * q} :=
  if hp0 : p = 0 then by simp [hp0]
  else
    calc
      ∑ a ∈ Ico 1 (p / 2).succ, a * q / p =
          ∑ a ∈ Ico 1 (p / 2).succ, #{x ∈ Ico 1 (q / 2).succ | x * p ≤ a * q} :=
        Finset.sum_congr rfl fun x hx => div_eq_filter_card (Nat.pos_of_ne_zero hp0) <|
          calc
            x * q / p ≤ p / 2 * q / p := by have := le_of_lt_succ (mem_Ico.mp hx).2; gcongr
            _ ≤ _ := Nat.div_mul_div_le_div _ _ _
      _ = _ := by simp only [card_eq_sum_ones, sum_filter, sum_product]

/-- Each of the sums in this lemma is the cardinality of the set of integer points in each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. Adding them
  gives the number of points in the rectangle. -/
/-
**ZMod.sum_mul_div_add_sum_mul_div_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：sum_mul_div_add_sum_mul_div_eq_mul (p q : Nat) [hp : Fact p.Prime] (hq0 : 
(q : ZMod p) != 0) : ∑ a in Ico 1 (p / 2).succ, a * q / p + ∑ a in Ico 1 (q / 2)
.succ, a * p / q = p / 2 * (q / 2)
参数：p q : Nat；hq0 : (q : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.card_equiv`：card_equiv (e : α ≃ β) (hst : forall i, i in s ↔ e i 
in t) : #s = #t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_filter`：disjoint_filter {s : Finset α} {p q : α -> Prop}
 [DecidablePred p] [DecidablePred q] : Disjoint (s.filter p) (s.filter q) ↔ fora
ll x in s, p…
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Nat.div_lt_self`：∀ {n k : ℕ}, 0 < n → 1 < k → n / k < n
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ZMod.instIsDomain`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsDomain (ZMod p
)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ZMod.val_zero`：∀ {n : ℕ}, ZMod.val 0 = 0
· 使用定理 `ZMod.val_cast_of_lt`：val_cast_of_lt {n : Nat} {a : Nat} (h : a < n) : (a
 : ZMod n).val = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Each of the sums in this lemma is the cardinality of the set of integer points i
n each of the
  two triangles formed by the diagonal of the rectangle `(0, p/2) × (0, q/2)`. A
dding them
  gives the number of points in the rectangle.
-/
theorem sum_mul_div_add_sum_mul_div_eq_mul (p q : ℕ) [hp : Fact p.Prime] (hq0 : (q : ZMod p) ≠ 0) :
    ∑ a ∈ Ico 1 (p / 2).succ, a * q / p + ∑ a ∈ Ico 1 (q / 2).succ, a * p / q =
    p / 2 * (q / 2) := by
  have hswap :
    #{x ∈ Ico 1 (q / 2).succ ×ˢ Ico 1 (p / 2).succ | x.2 * q ≤ x.1 * p} =
      #{x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q ≤ x.2 * p} :=
    card_equiv (Equiv.prodComm _ _)
      (fun ⟨_, _⟩ => by
        simp +contextual only [mem_filter, Prod.swap_prod_mk,
          mem_product, Equiv.prodComm_apply, and_assoc, and_left_comm])
  have hdisj :
    Disjoint {x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p ≤ x.1 * q}
      {x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q ≤ x.2 * p} := by
    apply disjoint_filter.2 fun x hx hpq hqp => ?_
    have hxp : x.1 < p := lt_of_le_of_lt (b := p / 2)
      (by grind) (Nat.div_lt_self hp.1.pos (by decide))
    have : (x.1 : ZMod p) = 0 := by
      simpa [hq0] using congr_arg ((↑) : ℕ → ZMod p) (le_antisymm hpq hqp)
    apply_fun ZMod.val at this
    rw [val_cast_of_lt hxp, val_zero] at this
    simp only [this, nonpos_iff_eq_zero, mem_Ico, one_ne_zero, false_and, mem_product] at hx
  have hunion :
      {x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.2 * p ≤ x.1 * q} ∪
        {x ∈ Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ | x.1 * q ≤ x.2 * p} =
      Ico 1 (p / 2).succ ×ˢ Ico 1 (q / 2).succ :=
    Finset.ext fun x => by
      have := le_total (x.2 * p) (x.1 * q)
      simp only [mem_union, mem_filter, mem_Ico, mem_product]
      tauto
  rw [sum_Ico_eq_card_lt, sum_Ico_eq_card_lt, hswap, ← card_union_of_disjoint hdisj, hunion,
    card_product]
  simp only [card_Ico, succ_sub_succ_eq_sub, Nat.sub_zero]

/-- **Eisenstein's lemma** -/
/-
**ZMod.eisenstein_lemma** 是 Mathlib 中的一个定理，位于命名空间 `ZMod`。
形式化陈述：eisenstein_lemma {p : Nat} [Fact p.Prime] (hp : p != 2) {a : Nat} (ha1 : a
 % 2 = 1) (ha0 : (a : ZMod p) != 0) : legendreSym p a = (-1) ^ ∑ x in Ico 1 (p /
 2).succ, x * a / p
参数：hp : p != 2；ha1 : a % 2 = 1；ha0 : (a : ZMod p) != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.Prime.mod_two_eq_one_iff_ne_two`：∀ {p : ℕ}, Nat.Prime p → (p % 2 = 1
 ↔ p ≠ 2)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Int.cast_natCast`：cast_natCast (n : Nat) : ((n : Int) : R) = n
· 使用引理 `neg_one_pow_eq_pow_mod_two`：neg_one_pow_eq_pow_mod_two (n : Nat) : (-1 :
 R) ^ n = (-1) ^ (n % 2)
· 使用定理 `ZMod.gauss_lemma`：gauss_lemma {p : Nat} [h : Fact p.Prime] {a : Int} (hp
 : p != 2) (ha0 : (a : ZMod p) != 0) : legendreSym p a = (-1) ^ #{x in Ico 1 (p 
/ 2).s…
· 使用定理 `ZMod.eisenstein_lemma_aux`：eisenstein_lemma_aux (p : Nat) [Fact p.Prime]
 [Fact (p % 2 = 1)] {a : Nat} (ha2 : a % 2 = 1) (hap : (a : ZMod p) != 0) : #{x 
in Ico 1 (p / 2…

--- 原说明 ---
**Eisenstein's lemma**
-/
theorem eisenstein_lemma {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {a : ℕ} (ha1 : a % 2 = 1)
    (ha0 : (a : ZMod p) ≠ 0) : legendreSym p a = (-1) ^ ∑ x ∈ Ico 1 (p / 2).succ, x * a / p := by
  have hp' : Fact (p % 2 = 1) := ⟨(Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp⟩
  have ha0' : ((a : ℤ) : ZMod p) ≠ 0 := by norm_cast
  rw [neg_one_pow_eq_pow_mod_two, gauss_lemma hp ha0', neg_one_pow_eq_pow_mod_two,
    (by norm_cast : ((a : ℤ) : ZMod p) = (a : ZMod p)),
    show _ = _ from eisenstein_lemma_aux p ha1 ha0]

end ZMod

end GaussEisenstein

