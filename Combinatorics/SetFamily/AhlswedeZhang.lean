/-
Copyright (c) 2023 Yaël Dillies, Vladimir Ivanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Vladimir Ivanov
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Finset.Sups
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Data.Rat.Defs
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Pow

/-!
# The Ahlswede-Zhang identity

This file proves the Ahlswede-Zhang identity, which is a nontrivial relation between the size of the
"truncated unions" of a set family. It sharpens the Lubell-Yamamoto-Meshalkin inequality
`Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`, by making explicit the correction
term.

For a set family `𝒜` over a ground set of size `n`, the Ahlswede-Zhang identity states that the sum
of `|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|)` over all sets `A` is exactly `1`. This implies the LYM
inequality since for an antichain `𝒜` and every `A ∈ 𝒜` we have
`|⋂ B ∈ 𝒜, B ⊆ A, B|/(|A| * n.choose |A|) = 1 / n.choose |A|`.

## Main declarations

* `Finset.truncatedSup`: `s.truncatedSup a` is the supremum of all `b ≥ a` in `𝒜` if there are
  some, or `⊤` if there are none.
* `Finset.truncatedInf`: `s.truncatedInf a` is the infimum of all `b ≤ a` in `𝒜` if there are
  some, or `⊥` if there are none.
* `AhlswedeZhang.infSum`: LHS of the Ahlswede-Zhang identity.
* `AhlswedeZhang.le_infSum`: The sum of `1 / n.choose |A|` over an antichain is less than the RHS of
  the Ahlswede-Zhang identity.
* `AhlswedeZhang.infSum_eq_one`: Ahlswede-Zhang identity.

## References

* [R. Ahlswede, Z. Zhang, *An identity in combinatorial extremal theory*](https://doi.org/10.1016/0001-8708(90)90023-G)
* [D. T. Tru, *An AZ-style identity and Bollobás deficiency*](https://doi.org/10.1016/j.jcta.2007.03.005)
-/

@[expose] public section

section
variable (α : Type*) [Fintype α] [Nonempty α] {m n : ℕ}

open Finset Fintype Nat

/-
**binomial_sum_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma binomial_sum_eq (h : n < m) :
    ∑ i ∈ range (n + 1), (n.choose i * (m - n) / ((m - i) * m.choose i) : ℚ) = 1 := by
  set f : ℕ → ℚ := fun i ↦ n.choose i * (m.choose i : ℚ)⁻¹ with hf
  suffices ∀ i ∈ range (n + 1), f i - f (i + 1) = n.choose i * (m - n) / ((m - i) * m.choose i) by
    rw [← sum_congr rfl this, sum_range_sub', hf]
    simp [choose_zero_right]
  intro i h₁
  rw [mem_range] at h₁
  have h₁ := le_of_lt_succ h₁
  have h₂ := h₁.trans_lt h
  have h₃ := h₂.le
  have hi₄ : (i + 1 : ℚ) ≠ 0 := i.cast_add_one_ne_zero
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq m i)
  push_cast at this
  dsimp [f, hf]
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have := congr_arg ((↑) : ℕ → ℚ) (choose_succ_right_eq n i)
  push_cast at this
  rw [(eq_mul_inv_iff_mul_eq₀ hi₄).mpr this]
  have : (m - i : ℚ) ≠ 0 := sub_ne_zero_of_ne (cast_lt.mpr h₂).ne'
  have : (m.choose i : ℚ) ≠ 0 := cast_ne_zero.2 (choose_pos h₂.le).ne'
  simp [field, *]

set_option backward.isDefEq.respectTransparency false in
/-
**Fintype.sum_div_mul_card_choose_card** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma Fintype.sum_div_mul_card_choose_card :
    ∑ s : Finset α, (card α / ((card α - #s) * (card α).choose #s) : ℚ) =
      card α * ∑ k ∈ range (card α), (↑k)⁻¹ + 1 := by
  rw [← powerset_univ, powerset_card_disjiUnion, sum_disjiUnion]
  have : ∀ {x : ℕ}, ∀ s ∈ powersetCard x (univ : Finset α),
    (card α / ((card α - #s) * (card α).choose #s) : ℚ) =
      card α / ((card α - x) * (card α).choose x) := by
    intro n s hs
    rw [mem_powersetCard_univ.1 hs]
  simp_rw [Finset.sum_congr rfl this, sum_const, card_powersetCard, card_univ, nsmul_eq_mul,
    mul_div, mul_comm, ← mul_div]
  rw [← mul_sum, ← mul_inv_cancel₀ (cast_ne_zero.mpr card_ne_zero : (card α : ℚ) ≠ 0), ← mul_add,
    add_comm _ ((card α)⁻¹ : ℚ), ← sum_insert (f := fun x : ℕ ↦ (x⁻¹ : ℚ)) notMem_range_self,
    ← range_add_one]
  have (n) (hn : n ∈ range (card α + 1)) :
      ((card α).choose n / ((card α - n) * (card α).choose n) : ℚ) = (card α - n : ℚ)⁻¹ := by
    rw [div_mul_cancel_right₀]
    exact cast_ne_zero.2 (choose_pos <| mem_range_succ_iff.1 hn).ne'
  simp only [Finset.sum_congr rfl this, mul_eq_mul_left_iff, cast_eq_zero]
  convert! Or.inl <| sum_range_reflect _ _ with a ha
  rw [add_tsub_cancel_right, cast_sub (mem_range_succ_iff.mp ha)]

end

open scoped FinsetFamily

namespace Finset
variable {α β : Type*}

/-! ### Truncated supremum, truncated infimum -/

section SemilatticeSup
variable [SemilatticeSup α] [SemilatticeSup β] [BoundedOrder β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in
/-
**Finset.sup_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sup_aux [DecidableLE α] : a ∈ lowerClosure s → {b ∈ s | a ≤ b}.Nonempty :=
  fun ⟨b, hb, hab⟩ ↦ ⟨b, mem_filter.2 ⟨hb, hab⟩⟩
/-
**Finset.lower_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma lower_aux [DecidableEq α] :
    a ∈ lowerClosure ↑(s ∪ t) ↔ a ∈ lowerClosure s ∨ a ∈ lowerClosure t := by
  rw [coe_union, lowerClosure_union, LowerSet.mem_sup_iff]

variable [DecidableLE α] [OrderTop α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The supremum of the elements of `s` less than `a` if there are some, otherwise `⊤`. -/
/-
**Finset.truncatedSup** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：truncatedSup (s : Finset α) (a : α) : α
参数：s : Finset α；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty

--- 原说明 ---
The supremum of the elements of `s` less than `a` if there are some, otherwise `
⊤`.
-/
def truncatedSup (s : Finset α) (a : α) : α :=
  if h : a ∈ lowerClosure s then {b ∈ s | a ≤ b}.sup' (sup_aux h) id else ⊤

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.truncatedSup_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_of_mem (h : a in lowerClosure s) : truncatedSup s a = {b in s
 | a <= b}.sup' (sup_aux h) id
参数：h : a in lowerClosure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
-/
lemma truncatedSup_of_mem (h : a ∈ lowerClosure s) :
    truncatedSup s a = {b ∈ s | a ≤ b}.sup' (sup_aux h) id := dif_pos h
/-
**Finset.truncatedSup_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_of_notMem (h : a ∉ lowerClosure s) : truncatedSup s a = ⊤
参数：h : a ∉ lowerClosure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
-/
lemma truncatedSup_of_notMem (h : a ∉ lowerClosure s) : truncatedSup s a = ⊤ := dif_neg h
/-
**Finset.truncatedSup_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : DecidableLE α] [inst_
2 : OrderTop α] (a : α), ∅.truncatedSup a = ⊤
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.truncatedSup_of_notMem`：truncatedSup_of_notMem (h : a ∉ lowerClos
ure s) : truncatedSup s a = ⊤
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `lowerClosure_empty`：∀ {α : Type u_1} [inst : Preorder α], lowerClosure ∅
 = ⊥
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma truncatedSup_empty (a : α) : truncatedSup ∅ a = ⊤ := truncatedSup_of_notMem (by simp)
/-
**Finset.truncatedSup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : DecidableLE α] [inst_
2 : OrderTop α] (b a : α),   {b}.truncatedSup a = if a ≤ b then b else ⊤
参数：b a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `lowerClosure_singleton`：∀ {α : Type u_1} [inst : Preorder α] (a : α), lo
werClosure {a} = LowerSet.Iic a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma truncatedSup_singleton (b a : α) : truncatedSup {b} a = if a ≤ b then b else ⊤ := by
  simp [truncatedSup]; split_ifs <;> simp [Finset.filter_true_of_mem, *]
/-
**Finset.le_truncatedSup** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：le_truncatedSup : a <= truncatedSup s a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.truncatedSup.eq_1`：∀ {α : Type u_1} [inst : SemilatticeSup α] [in
st_1 : DecidableLE α] [inst_2 : OrderTop α] (s : Finset α) (a : α),   s.truncate
dSup a = if h …
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma le_truncatedSup : a ≤ truncatedSup s a := by
  rw [truncatedSup]
  split_ifs with h
  · obtain ⟨ℬ, hb, h⟩ := h
    exact h.trans <| le_sup' id <| mem_filter.2 ⟨hb, h⟩
  · exact le_top
/-
**Finset.map_truncatedSup** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_truncatedSup [DecidableLE β] (e : α ≃o β) (s : Finset α) (a : α) : e (
truncatedSup s a) = truncatedSup (s.map e.toEquiv.toEmbedding) (e a)
参数：e : α ≃o β；s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `lowerClosure_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α] 
[inst_1 : Preorder β] {s : Set α} (f : α ≃o β),   lowerClosure (⇑f '' s) = (Lowe
rSet.map…
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `map_finset_sup'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeSup α] [inst_1 : SemilatticeSup β]   [inst_2 : FunLike
 F α …
· 使用定理 `OrderIsoClass.toSupHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : SemilatticeSup α]   [inst_2 : Semilattice
Sup β] [OrderIsoC…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `TopHomClass.map_top`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Top α} {inst_1 : Top β}   {inst_2 : FunLike F α β} [se
lf : TopH…
· 使用定理 `OrderIsoClass.toTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : LE α] [inst_2 : OrderTop α]   [inst_3 : P
artialOrder β] [i…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.map_nonempty`：map_nonempty : (s.map f).Nonempty ↔ s.Nonempty
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_map`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : 
SemilatticeSup α] {s : Finset γ} {f : γ ↪ β} (g : β → α)   (hs : (Finset.map f s
).Non…
（共 31 条，此处仅展示前 30 条）
-/
lemma map_truncatedSup [DecidableLE β] (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedSup s a) = truncatedSup (s.map e.toEquiv.toEmbedding) (e a) := by
  have : e a ∈ lowerClosure (s.map e.toEquiv.toEmbedding : Set β) ↔ a ∈ lowerClosure s := by simp
  simp_rw [truncatedSup, apply_dite e, map_finset_sup', map_top, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, sup'_map]
/-
**Finset.truncatedSup_of_isAntichain** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_of_isAntichain (hs : IsAntichain (· <= ·) (s : Set α)) (ha : 
a in s) : truncatedSup s a = a
参数：hs : IsAntichain (· <= ·) (s : Set α)；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `subset_lowerClosure`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, s
 ⊆ ↑(lowerClosure s)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.truncatedSup_of_mem`：truncatedSup_of_mem (h : a in lowerClosure s
) : truncatedSup s a = {b in s | a <= b}.sup' (sup_aux h) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
· 使用引理 `Finset.le_truncatedSup`：le_truncatedSup : a <= truncatedSup s a
-/
lemma truncatedSup_of_isAntichain (hs : IsAntichain (· ≤ ·) (s : Set α)) (ha : a ∈ s) :
    truncatedSup s a = a := by
  refine le_antisymm ?_ le_truncatedSup
  simp_rw [truncatedSup_of_mem (subset_lowerClosure ha), sup'_le_iff, mem_filter]
  rintro b ⟨hb, hab⟩
  exact (hs.eq ha hb hab).ge

variable [DecidableEq α]
/-
**Finset.truncatedSup_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_union (hs : a in lowerClosure s) (ht : a in lowerClosure t) :
 truncatedSup (s union t) a = truncatedSup s a ⊔ truncatedSup t a
参数：hs : a in lowerClosure s；ht : a in lowerClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.lower_au
x`：∀ {α : Type u_1} [inst : SemilatticeSup α] {s t : Finset α} {a : α} [inst_1 :
 DecidableEq α],   a ∈ lowerClosure ↑(s ∪ t) ↔ a ∈ lowerClosure…
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.truncatedSup_of_mem`：truncatedSup_of_mem (h : a in lowerClosure s
) : truncatedSup s a = {b in s | a <= b}.sup' (sup_aux h) id
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty)   (h₂ : s₂.N
onempty…
-/
lemma truncatedSup_union (hs : a ∈ lowerClosure s) (ht : a ∈ lowerClosure t) :
    truncatedSup (s ∪ t) a = truncatedSup s a ⊔ truncatedSup t a := by
  simpa only [truncatedSup_of_mem, hs, ht, lower_aux.2 (Or.inl hs), filter_union] using
    sup'_union _ _ _
/-
**Finset.truncatedSup_union_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_union_left (hs : a in lowerClosure s) (ht : a ∉ lowerClosure 
t) : truncatedSup (s union t) a = truncatedSup s a
参数：hs : a in lowerClosure s；ht : a ∉ lowerClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.lower_au
x`：∀ {α : Type u_1} [inst : SemilatticeSup α] {s t : Finset α} {a : α} [inst_1 :
 DecidableEq α],   a ∈ lowerClosure ↑(s ∪ t) ↔ a ∈ lowerClosure…
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.union_empty`：union_empty (s : Finset α) : s union ∅ = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.truncatedSup_of_mem`：truncatedSup_of_mem (h : a in lowerClosure s
) : truncatedSup s a = {b in s | a <= b}.sup' (sup_aux h) id
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncatedSup_union_left (hs : a ∈ lowerClosure s) (ht : a ∉ lowerClosure t) :
    truncatedSup (s ∪ t) a = truncatedSup s a := by
  simp only [mem_lowerClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedSup_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    lower_aux.2 (Or.inl hs)]
/-
**Finset.truncatedSup_union_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_union_right (hs : a ∉ lowerClosure s) (ht : a in lowerClosure
 t) : truncatedSup (s union t) a = truncatedSup t a
参数：hs : a ∉ lowerClosure s；ht : a in lowerClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用引理 `Finset.truncatedSup_union_left`：truncatedSup_union_left (hs : a in lower
Closure s) (ht : a ∉ lowerClosure t) : truncatedSup (s union t) a = truncatedSup
 s a
-/
lemma truncatedSup_union_right (hs : a ∉ lowerClosure s) (ht : a ∈ lowerClosure t) :
    truncatedSup (s ∪ t) a = truncatedSup t a := by rw [union_comm, truncatedSup_union_left ht hs]
/-
**Finset.truncatedSup_union_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_union_of_notMem (hs : a ∉ lowerClosure s) (ht : a ∉ lowerClos
ure t) : truncatedSup (s union t) a = ⊤
参数：hs : a ∉ lowerClosure s；ht : a ∉ lowerClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.truncatedSup_of_notMem`：truncatedSup_of_notMem (h : a ∉ lowerClos
ure s) : truncatedSup s a = ⊤
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.lower_au
x`：∀ {α : Type u_1} [inst : SemilatticeSup α] {s t : Finset α} {a : α} [inst_1 :
 DecidableEq α],   a ∈ lowerClosure ↑(s ∪ t) ↔ a ∈ lowerClosure…
-/
lemma truncatedSup_union_of_notMem (hs : a ∉ lowerClosure s) (ht : a ∉ lowerClosure t) :
    truncatedSup (s ∪ t) a = ⊤ := truncatedSup_of_notMem fun h ↦ (lower_aux.1 h).elim hs ht

end SemilatticeSup

section SemilatticeInf
variable [SemilatticeInf α] [SemilatticeInf β]
  [BoundedOrder β] [DecidableLE β] {s t : Finset α} {a : α}

set_option backward.privateInPublic true in
/-
**Finset.inf_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma inf_aux [DecidableLE α] : a ∈ upperClosure s → {b ∈ s | b ≤ a}.Nonempty :=
  fun ⟨b, hb, hab⟩ ↦ ⟨b, mem_filter.2 ⟨hb, hab⟩⟩
/-
**Finset.upper_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma upper_aux [DecidableEq α] :
    a ∈ upperClosure ↑(s ∪ t) ↔ a ∈ upperClosure s ∨ a ∈ upperClosure t := by
  rw [coe_union, upperClosure_union, UpperSet.mem_inf_iff]

variable [DecidableLE α] [BoundedOrder α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥`. -/
/-
**Finset.truncatedInf** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：truncatedInf (s : Finset α) (a : α) : α
参数：s : Finset α；a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty

--- 原说明 ---
The infimum of the elements of `s` less than `a` if there are some, otherwise `⊥
`.
-/
def truncatedInf (s : Finset α) (a : α) : α :=
  if h : a ∈ upperClosure s then {b ∈ s | b ≤ a}.inf' (inf_aux h) id else ⊥

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.truncatedInf_of_mem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_of_mem (h : a in upperClosure s) : truncatedInf s a = {b in s
 | b <= a}.inf' (inf_aux h) id
参数：h : a in upperClosure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
-/
lemma truncatedInf_of_mem (h : a ∈ upperClosure s) :
    truncatedInf s a = {b ∈ s | b ≤ a}.inf' (inf_aux h) id := dif_pos h
/-
**Finset.truncatedInf_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_of_notMem (h : a ∉ upperClosure s) : truncatedInf s a = ⊥
参数：h : a ∉ upperClosure s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
-/
lemma truncatedInf_of_notMem (h : a ∉ upperClosure s) : truncatedInf s a = ⊥ := dif_neg h
/-
**Finset.truncatedInf_le** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_le : truncatedInf s a <= a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `LE.le.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b ≤ a → 
c ≤ b → c ≤ a
· 使用定理 `Finset.inf'_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeInf α
] {s : Finset β} (f : β → α) {b : β} (h : b ∈ s),   s.inf' ⋯ f ≤ f b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_filter`：∀ {α : Type u_1} {p : α → Prop} [inst : DecidablePred
 p] {s : Finset α} {a : α}, a ∈ Finset.filter p s ↔ a ∈ s ∧ p a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
lemma truncatedInf_le : truncatedInf s a ≤ a := by
  unfold truncatedInf
  split_ifs with h
  · obtain ⟨b, hb, hba⟩ := h
    exact hba.trans' <| inf'_le id <| mem_filter.2 ⟨hb, ‹_›⟩
  · exact bot_le
/-
**Finset.truncatedInf_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : DecidableLE α] [inst_
2 : BoundedOrder α] (a : α),   ∅.truncatedInf a = ⊥
参数：a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.truncatedInf_of_notMem`：truncatedInf_of_notMem (h : a ∉ upperClos
ure s) : truncatedInf s a = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `upperClosure_empty`：upperClosure_empty : upperClosure (∅ : Set α) = ⊤
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
@[simp] lemma truncatedInf_empty (a : α) : truncatedInf ∅ a = ⊥ := truncatedInf_of_notMem (by simp)
/-
**Finset.truncatedInf_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : DecidableLE α] [inst_
2 : BoundedOrder α] (b a : α),   {b}.truncatedInf a = if b ≤ a then b else ⊥
参数：b a : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `upperClosure_singleton`：upperClosure_singleton (a : α) : upperClosure ({
a} : Set α) = UpperSet.Ici a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.filter_true_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Decid
ablePred p] {s : Finset α}, (∀ x ∈ s, p x) → Finset.filter p s = s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
@[simp] lemma truncatedInf_singleton (b a : α) : truncatedInf {b} a = if b ≤ a then b else ⊥ := by
  simp only [truncatedInf, coe_singleton, upperClosure_singleton, UpperSet.mem_Ici_iff,
    id_eq]
  split_ifs <;> simp [Finset.filter_true_of_mem, *]
/-
**Finset.map_truncatedInf** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：map_truncatedInf (e : α ≃o β) (s : Finset α) (a : α) : e (truncatedInf s a
) = truncatedInf (s.map e.toEquiv.toEmbedding) (e a)
参数：e : α ≃o β；s : Finset α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `upperClosure_image`：upperClosure_image (f : α ≃o β) : upperClosure (f ''
 s) = UpperSet.map f (upperClosure s)
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `map_finset_inf'`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} {ι : Typ
e u_5} [inst : SemilatticeInf α] [inst_1 : SemilatticeInf β]   [inst_2 : FunLike
 F α …
· 使用定理 `InfTopHomClass.toInfHomClass`：∀ {F : Type u_6} {α : Type u_7} {β : Type 
u_8} {inst : Min α} {inst_1 : Min β} {inst_2 : Top α} {inst_3 : Top β}   {inst_4
 : FunLike F α β} …
· 使用定理 `OrderIsoClass.toInfTopHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Typ
e u_3} [inst : EquivLike F α β] [inst_1 : SemilatticeInf α]   [inst_2 : OrderTop
 α] [inst_3 : Semila…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
· 使用定理 `BotHomClass.map_bot`：∀ {F : Type u_6} {α : outParam (Type u_7)} {β : out
Param (Type u_8)} {inst : Bot α} {inst_1 : Bot β}   {inst_2 : FunLike F α β} [se
lf : BotH…
· 使用定理 `OrderIsoClass.toBotHomClass`：∀ {F : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : EquivLike F α β] [inst_1 : LE α] [inst_2 : OrderBot α]   [inst_3 : P
artialOrder β] [i…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `instSubsingletonDecidable`：∀ (p : Prop), Subsingleton (Decidable p)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.map_nonempty`：map_nonempty : (s.map f).Nonempty ↔ s.Nonempty
· 使用定理 `Finset.filter_map`：filter_map {p : β -> Prop} [DecidablePred p] : (s.map
 f).filter p = (s.filter (p ∘ f)).map f
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
（共 32 条，此处仅展示前 30 条）
-/
lemma map_truncatedInf (e : α ≃o β) (s : Finset α) (a : α) :
    e (truncatedInf s a) = truncatedInf (s.map e.toEquiv.toEmbedding) (e a) := by
  have : e a ∈ upperClosure (s.map e.toEquiv.toEmbedding) ↔ a ∈ upperClosure s := by simp
  simp_rw [truncatedInf, apply_dite e, map_finset_inf', map_bot, this]
  congr with h
  simp only [filter_map, Function.comp_def, Equiv.coe_toEmbedding, RelIso.coe_fn_toEquiv,
    OrderIso.le_iff_le, id, inf'_map]
/-
**Finset.truncatedInf_of_isAntichain** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_of_isAntichain (hs : IsAntichain (· <= ·) (s : Set α)) (ha : 
a in s) : truncatedInf s a = a
参数：hs : IsAntichain (· <= ·) (s : Set α)；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Finset.truncatedInf_le`：truncatedInf_le : truncatedInf s a <= a
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `subset_upperClosure`：subset_upperClosure : s subseteq upperClosure s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.truncatedInf_of_mem`：truncatedInf_of_mem (h : a in upperClosure s
) : truncatedInf s a = {b in s | b <= a}.inf' (inf_aux h) id
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsAntichain.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}, IsAntic
hain r s → ∀ {a b : α}, a ∈ s → b ∈ s → r a b → a = b
-/
lemma truncatedInf_of_isAntichain (hs : IsAntichain (· ≤ ·) (s : Set α)) (ha : a ∈ s) :
    truncatedInf s a = a := by
  refine le_antisymm truncatedInf_le ?_
  simp_rw [truncatedInf_of_mem (subset_upperClosure ha), le_inf'_iff, mem_filter]
  rintro b ⟨hb, hba⟩
  exact (hs.eq hb ha hba).ge

variable [DecidableEq α]
/-
**Finset.truncatedInf_union** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_union (hs : a in upperClosure s) (ht : a in upperClosure t) :
 truncatedInf (s union t) a = truncatedInf s a ⊓ truncatedInf t a
参数：hs : a in upperClosure s；ht : a in upperClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.upper_au
x`：∀ {α : Type u_1} [inst : SemilatticeInf α] {s t : Finset α} {a : α} [inst_1 :
 DecidableEq α],   a ∈ upperClosure ↑(s ∪ t) ↔ a ∈ upperClosure…
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.truncatedInf_of_mem`：truncatedInf_of_mem (h : a in upperClosure s
) : truncatedInf s a = {b in s | b <= a}.inf' (inf_aux h) id
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.inf'_union`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] [inst_1 : DecidableEq β] {s₁ s₂ : Finset β} (h₁ : s₁.Nonempty)   (h₂ : s₂.N
onempty…
-/
lemma truncatedInf_union (hs : a ∈ upperClosure s) (ht : a ∈ upperClosure t) :
    truncatedInf (s ∪ t) a = truncatedInf s a ⊓ truncatedInf t a := by
  simpa only [truncatedInf_of_mem, hs, ht, upper_aux.2 (Or.inl hs), filter_union] using
    inf'_union _ _ _
/-
**Finset.truncatedInf_union_left** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_union_left (hs : a in upperClosure s) (ht : a ∉ upperClosure 
t) : truncatedInf (s union t) a = truncatedInf s a
参数：hs : a in upperClosure s；ht : a ∉ upperClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.upper_au
x`：∀ {α : Type u_1} [inst : SemilatticeInf α] {s t : Finset α} {a : α} [inst_1 :
 DecidableEq α],   a ∈ upperClosure ↑(s ∪ t) ↔ a ∈ upperClosure…
· 使用定理 `Finset.filter_union`：filter_union (s₁ s₂ : Finset α) : (s₁ union s₂).fil
ter p = s₁.filter p union s₂.filter p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_false_of_mem`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, (∀ x ∈ s, ¬p x) → Finset.filter p s = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finset.union_empty`：union_empty (s : Finset α) : s union ∅ = s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Finset.truncatedInf_of_mem`：truncatedInf_of_mem (h : a in upperClosure s
) : truncatedInf s a = {b in s | b <= a}.inf' (inf_aux h) id
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncatedInf_union_left (hs : a ∈ upperClosure s) (ht : a ∉ upperClosure t) :
    truncatedInf (s ∪ t) a = truncatedInf s a := by
  simp only [mem_upperClosure, mem_coe, not_exists, not_and] at ht
  simp only [truncatedInf_of_mem, hs, filter_union, filter_false_of_mem ht, union_empty,
    upper_aux.2 (Or.inl hs)]
/-
**Finset.truncatedInf_union_right** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_union_right (hs : a ∉ upperClosure s) (ht : a in upperClosure
 t) : truncatedInf (s union t) a = truncatedInf t a
参数：hs : a ∉ upperClosure s；ht : a in upperClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.union_comm`：union_comm (s₁ s₂ : Finset α) : s₁ union s₂ = s₂ unio
n s₁
· 使用引理 `Finset.truncatedInf_union_left`：truncatedInf_union_left (hs : a in upper
Closure s) (ht : a ∉ upperClosure t) : truncatedInf (s union t) a = truncatedInf
 s a
-/
lemma truncatedInf_union_right (hs : a ∉ upperClosure s) (ht : a ∈ upperClosure t) :
    truncatedInf (s ∪ t) a = truncatedInf t a := by
  rw [union_comm, truncatedInf_union_left ht hs]
/-
**Finset.truncatedInf_union_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_union_of_notMem (hs : a ∉ upperClosure s) (ht : a ∉ upperClos
ure t) : truncatedInf (s union t) a = ⊥
参数：hs : a ∉ upperClosure s；ht : a ∉ upperClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.truncatedInf_of_notMem`：truncatedInf_of_notMem (h : a ∉ upperClos
ure s) : truncatedInf s a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_union`：coe_union (s₁ s₂ : Finset α) : ↑(s₁ union s₂) = (s₁ un
ion s₂ : Set α)
· 使用定理 `upperClosure_union`：upperClosure_union (s t : Set α) : upperClosure (s u
nion t) = upperClosure s ⊓ upperClosure t
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
-/
lemma truncatedInf_union_of_notMem (hs : a ∉ upperClosure s) (ht : a ∉ upperClosure t) :
    truncatedInf (s ∪ t) a = ⊥ :=
  truncatedInf_of_notMem <| by rw [coe_union, upperClosure_union]; exact fun h ↦ h.elim hs ht

end SemilatticeInf

section DistribLattice
variable [DistribLattice α] [DecidableEq α] {s t : Finset α} {a : α}

/-
**Finset.infs_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma infs_aux : a ∈ lowerClosure ↑(s ⊼ t) ↔ a ∈ lowerClosure s ∧ a ∈ lowerClosure t := by
  rw [coe_infs, lowerClosure_infs, LowerSet.mem_inf_iff]
/-
**Finset.sups_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma sups_aux : a ∈ upperClosure ↑(s ⊻ t) ↔ a ∈ upperClosure s ∧ a ∈ upperClosure t := by
  rw [coe_sups, upperClosure_sups, UpperSet.mem_sup_iff]

variable [DecidableLE α] [BoundedOrder α]
/-
**Finset.truncatedSup_infs** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_infs (hs : a in lowerClosure s) (ht : a in lowerClosure t) : 
truncatedSup (s ⊼ t) a = truncatedSup s a ⊓ truncatedSup t a
参数：hs : a in lowerClosure s；ht : a in lowerClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sup_aux`
：∀ {α : Type u_1} [inst : SemilatticeSup α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ lowerClosure ↑s → {b ∈ s | a ≤ b}.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.infs_aux
`：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : DecidableEq α] {s t : Fin
set α} {a : α},   a ∈ lowerClosure ↑(s ⊼ t) ↔ a ∈ lowerClosure…
· 使用引理 `Finset.filter_infs_le`：filter_infs_le [DecidableLE α] (s t : Finset α) (
a : α) : {b in s ⊼ t | a <= b} = {b in s | a <= b} ⊼ {b in t | a <= b}
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.truncatedSup_of_mem`：truncatedSup_of_mem (h : a in lowerClosure s
) : truncatedSup s a = {b in s | a <= b}.sup' (sup_aux h) id
· 使用定理 `Finset.sup'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.sup'_inf_sup'`：∀ {α : Type u_2} {ι : Type u_5} {κ : Type u_6} [in
st : DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty)   (ht : t
.Nonempty)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `Finset.sup'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeSup α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncatedSup_infs (hs : a ∈ lowerClosure s) (ht : a ∈ lowerClosure t) :
    truncatedSup (s ⊼ t) a = truncatedSup s a ⊓ truncatedSup t a := by
  simp only [truncatedSup_of_mem, hs, ht, infs_aux.2 ⟨hs, ht⟩, sup'_inf_sup', filter_infs_le]
  simp_rw [← image_inf_product]
  rw [sup'_image]
  simp [Function.uncurry_def]
/-
**Finset.truncatedInf_sups** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_sups (hs : a in upperClosure s) (ht : a in upperClosure t) : 
truncatedInf (s ⊻ t) a = truncatedInf s a ⊔ truncatedInf t a
参数：hs : a in upperClosure s；ht : a in upperClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.inf'`：inf'_one [SemilatticeInf β] (f : α -> β) : inf' 1 one_nonem
pty f = f 1
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.inf_aux`
：∀ {α : Type u_1} [inst : SemilatticeInf α] {s : Finset α} {a : α} [inst_1 : Dec
idableLE α],   a ∈ upperClosure ↑s → {b ∈ s | b ≤ a}.Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Finset.sups_aux
`：∀ {α : Type u_1} [inst : DistribLattice α] [inst_1 : DecidableEq α] {s t : Fin
set α} {a : α},   a ∈ upperClosure ↑(s ⊻ t) ↔ a ∈ upperClosure…
· 使用引理 `Finset.filter_sups_le`：filter_sups_le [DecidableLE α] (s t : Finset α) (
a : α) : {b in s ⊻ t | b <= a} = {b in s | b <= a} ⊻ {b in t | b <= a}
· 使用定理 `Finset.Nonempty.product`：∀ {α : Type u_1} {β : Type u_2} {s : Finset α} 
{t : Finset β}, s.Nonempty → t.Nonempty → (s ×ˢ t).Nonempty
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.truncatedInf_of_mem`：truncatedInf_of_mem (h : a in upperClosure s
) : truncatedInf s a = {b in s | b <= a}.inf' (inf_aux h) id
· 使用定理 `Finset.inf'_congr`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeIn
f α] {s : Finset β} (H : s.Nonempty) {t : Finset β} {f g : β → α}   (h₁ : s = t)
, (∀ x …
· 使用定理 `Finset.inf'_sup_inf'`：∀ {α : Type u_2} {ι : Type u_5} {κ : Type u_6} [in
st : DistribLattice α] {s : Finset ι} {t : Finset κ} (hs : s.Nonempty)   (ht : t
.Nonempty)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.Nonempty.of_image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decida
bleEq β] {f : α → β} {s : Finset α},   (Finset.image f s).Nonempty → s.Nonempty
· 使用定理 `Finset.inf'_image`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: SemilatticeInf α] [inst_1 : DecidableEq β] {s : Finset γ}   {f : γ → β} (hs : 
(Finset…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma truncatedInf_sups (hs : a ∈ upperClosure s) (ht : a ∈ upperClosure t) :
    truncatedInf (s ⊻ t) a = truncatedInf s a ⊔ truncatedInf t a := by
  simp only [truncatedInf_of_mem, hs, ht, sups_aux.2 ⟨hs, ht⟩, inf'_sup_inf', filter_sups_le]
  simp_rw [← image_sup_product]
  rw [inf'_image]
  simp [Function.uncurry_def]
/-
**Finset.truncatedSup_infs_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedSup_infs_of_notMem (ha : a ∉ lowerClosure s ⊓ lowerClosure t) : t
runcatedSup (s ⊼ t) a = ⊤
参数：ha : a ∉ lowerClosure s ⊓ lowerClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.truncatedSup_of_notMem`：truncatedSup_of_notMem (h : a ∉ lowerClos
ure s) : truncatedSup s a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_infs`：coe_infs : (↑(s ⊼ t) : Set α) = ↑s ⊼ ↑t
· 使用定理 `lowerClosure_infs`：lowerClosure_infs [SemilatticeInf α] (s t : Set α) : 
lowerClosure (s ⊼ t) = lowerClosure s ⊓ lowerClosure t
-/
lemma truncatedSup_infs_of_notMem (ha : a ∉ lowerClosure s ⊓ lowerClosure t) :
    truncatedSup (s ⊼ t) a = ⊤ :=
  truncatedSup_of_notMem <| by rwa [coe_infs, lowerClosure_infs]
/-
**Finset.truncatedInf_sups_of_notMem** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：truncatedInf_sups_of_notMem (ha : a ∉ upperClosure s ⊔ upperClosure t) : t
runcatedInf (s ⊻ t) a = ⊥
参数：ha : a ∉ upperClosure s ⊔ upperClosure t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.truncatedInf_of_notMem`：truncatedInf_of_notMem (h : a ∉ upperClos
ure s) : truncatedInf s a = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_sups`：coe_sups : (↑(s ⊻ t) : Set α) = ↑s ⊻ ↑t
· 使用定理 `upperClosure_sups`：upperClosure_sups [SemilatticeSup α] (s t : Set α) : 
upperClosure (s ⊻ t) = upperClosure s ⊔ upperClosure t
-/
lemma truncatedInf_sups_of_notMem (ha : a ∉ upperClosure s ⊔ upperClosure t) :
    truncatedInf (s ⊻ t) a = ⊥ :=
  truncatedInf_of_notMem <| by rwa [coe_sups, upperClosure_sups]

end DistribLattice

section BooleanAlgebra
variable [BooleanAlgebra α] [DecidableLE α]

/-
**Finset.compl_truncatedSup** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] [inst_1 : DecidableLE α] (s : F
inset α) (a : α),   (s.truncatedSup a)ᶜ = s.compls.truncatedInf aᶜ
参数：s : Finset α；a : α；s.truncatedSup a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_truncatedSup`：map_truncatedSup [DecidableLE β] (e : α ≃o β) (
s : Finset α) (a : α) : e (truncatedSup s a) = truncatedSup (s.map e.toEquiv.toE
mbedding) (e …
-/
@[simp] lemma compl_truncatedSup (s : Finset α) (a : α) :
    (truncatedSup s a)ᶜ = truncatedInf sᶜˢ aᶜ := map_truncatedSup (OrderIso.compl α) _ _
/-
**Finset.compl_truncatedInf** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ {α : Type u_1} [inst : BooleanAlgebra α] [inst_1 : DecidableLE α] (s : F
inset α) (a : α),   (s.truncatedInf a)ᶜ = s.compls.truncatedSup aᶜ
参数：s : Finset α；a : α；s.truncatedInf a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.map_truncatedInf`：map_truncatedInf (e : α ≃o β) (s : Finset α) (a
 : α) : e (truncatedInf s a) = truncatedInf (s.map e.toEquiv.toEmbedding) (e a)
-/
@[simp] lemma compl_truncatedInf (s : Finset α) (a : α) :
    (truncatedInf s a)ᶜ = truncatedSup sᶜˢ aᶜ := map_truncatedInf (OrderIso.compl α) _ _

end BooleanAlgebra

variable [DecidableEq α] [Fintype α]

/-
**Finset.card_truncatedSup_union_add_card_truncatedSup_infs** 是 Mathlib 中的一个引理，位
于命名空间 `Finset`。
形式化陈述：card_truncatedSup_union_add_card_truncatedSup_infs (𝒜 ℬ : Finset (Finset α
)) (s : Finset α) : #(truncatedSup (𝒜 union ℬ) s) + #(truncatedSup (𝒜 ⊼ ℬ) s) = 
#(truncatedSup 𝒜 s) + #(truncatedSup ℬ s)
参数：𝒜 ℬ : Finset (Finset α)；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.truncatedSup_union`：truncatedSup_union (hs : a in lowerClosure s)
 (ht : a in lowerClosure t) : truncatedSup (s union t) a = truncatedSup s a ⊔ tr
uncatedSup t a
· 使用引理 `Finset.truncatedSup_infs`：truncatedSup_infs (hs : a in lowerClosure s) (
ht : a in lowerClosure t) : truncatedSup (s ⊼ t) a = truncatedSup s a ⊓ truncate
dSup t a
· 使用定理 `Finset.card_union_add_card_inter`：card_union_add_card_inter (s t : Finse
t α) : #(s union t) + #(s inter t) = #s + #t
· 使用引理 `Finset.truncatedSup_union_left`：truncatedSup_union_left (hs : a in lower
Closure s) (ht : a ∉ lowerClosure t) : truncatedSup (s union t) a = truncatedSup
 s a
· 使用引理 `Finset.truncatedSup_of_notMem`：truncatedSup_of_notMem (h : a ∉ lowerClos
ure s) : truncatedSup s a = ⊤
· 使用引理 `Finset.truncatedSup_infs_of_notMem`：truncatedSup_infs_of_notMem (ha : a 
∉ lowerClosure s ⊓ lowerClosure t) : truncatedSup (s ⊼ t) a = ⊤
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.truncatedSup_union_right`：truncatedSup_union_right (hs : a ∉ lowe
rClosure s) (ht : a in lowerClosure t) : truncatedSup (s union t) a = truncatedS
up t a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Finset.truncatedSup_union_of_notMem`：truncatedSup_union_of_notMem (hs : 
a ∉ lowerClosure s) (ht : a ∉ lowerClosure t) : truncatedSup (s union t) a = ⊤
-/
lemma card_truncatedSup_union_add_card_truncatedSup_infs (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
    #(truncatedSup (𝒜 ∪ ℬ) s) + #(truncatedSup (𝒜 ⊼ ℬ) s) =
      #(truncatedSup 𝒜 s) + #(truncatedSup ℬ s) := by
  by_cases h𝒜 : s ∈ lowerClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s ∈ lowerClosure (ℬ : Set <| Finset α)
  · rw [truncatedSup_union h𝒜 hℬ, truncatedSup_infs h𝒜 hℬ]
    exact card_union_add_card_inter _ _
  · rw [truncatedSup_union_left h𝒜 hℬ, truncatedSup_of_notMem hℬ,
      truncatedSup_infs_of_notMem fun h ↦ hℬ h.2]
  · rw [truncatedSup_union_right h𝒜 hℬ, truncatedSup_of_notMem h𝒜,
      truncatedSup_infs_of_notMem fun h ↦ h𝒜 h.1, add_comm]
  · rw [truncatedSup_of_notMem h𝒜, truncatedSup_of_notMem hℬ,
      truncatedSup_union_of_notMem h𝒜 hℬ, truncatedSup_infs_of_notMem fun h ↦ h𝒜 h.1]
/-
**Finset.card_truncatedInf_union_add_card_truncatedInf_sups** 是 Mathlib 中的一个引理，位
于命名空间 `Finset`。
形式化陈述：card_truncatedInf_union_add_card_truncatedInf_sups (𝒜 ℬ : Finset (Finset α
)) (s : Finset α) : #(truncatedInf (𝒜 union ℬ) s) + #(truncatedInf (𝒜 ⊻ ℬ) s) = 
#(truncatedInf 𝒜 s) + #(truncatedInf ℬ s)
参数：𝒜 ℬ : Finset (Finset α)；s : Finset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.truncatedInf_union`：truncatedInf_union (hs : a in upperClosure s)
 (ht : a in upperClosure t) : truncatedInf (s union t) a = truncatedInf s a ⊓ tr
uncatedInf t a
· 使用引理 `Finset.truncatedInf_sups`：truncatedInf_sups (hs : a in upperClosure s) (
ht : a in upperClosure t) : truncatedInf (s ⊻ t) a = truncatedInf s a ⊔ truncate
dInf t a
· 使用定理 `Finset.card_inter_add_card_union`：card_inter_add_card_union (s t : Finse
t α) : #(s inter t) + #(s union t) = #s + #t
· 使用引理 `Finset.truncatedInf_union_left`：truncatedInf_union_left (hs : a in upper
Closure s) (ht : a ∉ upperClosure t) : truncatedInf (s union t) a = truncatedInf
 s a
· 使用引理 `Finset.truncatedInf_of_notMem`：truncatedInf_of_notMem (h : a ∉ upperClos
ure s) : truncatedInf s a = ⊥
· 使用引理 `Finset.truncatedInf_sups_of_notMem`：truncatedInf_sups_of_notMem (ha : a 
∉ upperClosure s ⊔ upperClosure t) : truncatedInf (s ⊻ t) a = ⊥
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.truncatedInf_union_right`：truncatedInf_union_right (hs : a ∉ uppe
rClosure s) (ht : a in upperClosure t) : truncatedInf (s union t) a = truncatedI
nf t a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用引理 `Finset.truncatedInf_union_of_notMem`：truncatedInf_union_of_notMem (hs : 
a ∉ upperClosure s) (ht : a ∉ upperClosure t) : truncatedInf (s union t) a = ⊥
-/
lemma card_truncatedInf_union_add_card_truncatedInf_sups (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
    #(truncatedInf (𝒜 ∪ ℬ) s) + #(truncatedInf (𝒜 ⊻ ℬ) s) =
      #(truncatedInf 𝒜 s) + #(truncatedInf ℬ s) := by
  by_cases h𝒜 : s ∈ upperClosure (𝒜 : Set <| Finset α) <;>
    by_cases hℬ : s ∈ upperClosure (ℬ : Set <| Finset α)
  · rw [truncatedInf_union h𝒜 hℬ, truncatedInf_sups h𝒜 hℬ]
    exact card_inter_add_card_union _ _
  · rw [truncatedInf_union_left h𝒜 hℬ, truncatedInf_of_notMem hℬ,
      truncatedInf_sups_of_notMem fun h ↦ hℬ h.2]
  · rw [truncatedInf_union_right h𝒜 hℬ, truncatedInf_of_notMem h𝒜,
      truncatedInf_sups_of_notMem fun h ↦ h𝒜 h.1, add_comm]
  · rw [truncatedInf_of_notMem h𝒜, truncatedInf_of_notMem hℬ,
      truncatedInf_union_of_notMem h𝒜 hℬ, truncatedInf_sups_of_notMem fun h ↦ h𝒜 h.1]

end Finset

open Finset hiding card
open Fintype Nat

namespace AhlswedeZhang
variable {α : Type*} [Fintype α] [DecidableEq α] {𝒜 : Finset (Finset α)} {s : Finset α}

/-- Weighted sum of the size of the truncated infima of a set family. Relevant to the
Ahlswede-Zhang identity. -/
/-
**AhlswedeZhang.infSum** 是 Mathlib 中的一个定义，位于命名空间 `AhlswedeZhang`。
形式化陈述：infSum (𝒜 : Finset (Finset α)) : Rat
参数：𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weighted sum of the size of the truncated infima of a set family. Relevant to th
e
Ahlswede-Zhang identity.
-/
def infSum (𝒜 : Finset (Finset α)) : ℚ :=
  ∑ s, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s)

/-- Weighted sum of the size of the truncated suprema of a set family. Relevant to the
Ahlswede-Zhang identity. -/
/-
**AhlswedeZhang.supSum** 是 Mathlib 中的一个定义，位于命名空间 `AhlswedeZhang`。
形式化陈述：supSum (𝒜 : Finset (Finset α)) : Rat
参数：𝒜 : Finset (Finset α)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Weighted sum of the size of the truncated suprema of a set family. Relevant to t
he
Ahlswede-Zhang identity.
-/
def supSum (𝒜 : Finset (Finset α)) : ℚ :=
  ∑ s, #(truncatedSup 𝒜 s) / ((card α - #s) * (card α).choose #s)
/-
**AhlswedeZhang.supSum_union_add_supSum_infs** 是 Mathlib 中的一个引理，位于命名空间 `Ahlswede
Zhang`。
形式化陈述：supSum_union_add_supSum_infs (𝒜 ℬ : Finset (Finset α)) : supSum (𝒜 union ℬ
) + supSum (𝒜 ⊼ ℬ) = supSum 𝒜 + supSum ℬ
参数：𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.card_truncatedSup_union_add_card_truncatedSup_infs`：card_truncate
dSup_union_add_card_truncatedSup_infs (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
 #(truncatedSup (𝒜 union ℬ) s) + #(truncatedSup…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma supSum_union_add_supSum_infs (𝒜 ℬ : Finset (Finset α)) :
    supSum (𝒜 ∪ ℬ) + supSum (𝒜 ⊼ ℬ) = supSum 𝒜 + supSum ℬ := by
  unfold supSum
  rw [← sum_add_distrib, ← sum_add_distrib, Finset.sum_congr rfl fun s _ ↦ _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedSup_union_add_card_truncatedSup_infs]
  simp
/-
**AhlswedeZhang.infSum_union_add_infSum_sups** 是 Mathlib 中的一个引理，位于命名空间 `Ahlswede
Zhang`。
形式化陈述：infSum_union_add_infSum_sups (𝒜 ℬ : Finset (Finset α)) : infSum (𝒜 union ℬ
) + infSum (𝒜 ⊻ ℬ) = infSum 𝒜 + infSum ℬ
参数：𝒜 ℬ : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finset.card_truncatedInf_union_add_card_truncatedInf_sups`：card_truncate
dInf_union_add_card_truncatedInf_sups (𝒜 ℬ : Finset (Finset α)) (s : Finset α) :
 #(truncatedInf (𝒜 union ℬ) s) + #(truncatedInf…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma infSum_union_add_infSum_sups (𝒜 ℬ : Finset (Finset α)) :
    infSum (𝒜 ∪ ℬ) + infSum (𝒜 ⊻ ℬ) = infSum 𝒜 + infSum ℬ := by
  unfold infSum
  rw [← sum_add_distrib, ← sum_add_distrib, Finset.sum_congr rfl fun s _ ↦ _]
  simp_rw [← add_div, ← Nat.cast_add, card_truncatedInf_union_add_card_truncatedInf_sups]
  simp
/-
**AhlswedeZhang.IsAntichain.le_infSum** 是 Mathlib 中的一个定理，位于命名空间 `AhlswedeZhang.I
sAntichain`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {𝒜 : Finset (
Finset α)},   IsAntichain (fun x1 x2 => x1 ⊆ x2) ↑𝒜 →     ∅ ∉ 𝒜 → ∑ s ∈ 𝒜, (↑((F
intype.card α).choose s.card))⁻¹ ≤ AhlswedeZhang.infSum 𝒜
参数：Finset α；fun x1 x2 => x1 ⊆ x2；↑((Fintype.card α).choose s.card)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.truncatedInf_of_isAntichain`：truncatedInf_of_isAntichain (hs : Is
Antichain (· <= ·) (s : Set α)) (ha : a in s) : truncatedInf s a = a
· 使用引理 `div_mul_cancel_left₀`：div_mul_cancel_left₀ (ha : a != 0) (b : G₀) : a / 
(a * b) = b⁻¹
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Finset.sum_le_univ_sum_of_nonneg`：∀ {ι : Type u_1} {N : Type u_5} [inst 
: AddCommMonoid N] [inst_1 : Preorder N] {f : ι → N} [AddLeftMono N]   [inst_3 :
 Fintype ι] {s : Finse…
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
-/
lemma IsAntichain.le_infSum (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) (h𝒜₀ : ∅ ∉ 𝒜) :
    ∑ s ∈ 𝒜, ((card α).choose #s : ℚ)⁻¹ ≤ infSum 𝒜 := by
  calc
    _ = ∑ s ∈ 𝒜, #(truncatedInf 𝒜 s) / (#s * (card α).choose #s : ℚ) := ?_
    _ ≤ _ := sum_le_univ_sum_of_nonneg fun s ↦ by positivity
  refine sum_congr rfl fun s hs ↦ ?_
  rw [truncatedInf_of_isAntichain h𝒜 hs, div_mul_cancel_left₀]
  have := (nonempty_iff_ne_empty.2 <| ne_of_mem_of_not_mem hs h𝒜₀).card_pos
  positivity

variable [Nonempty α]
/-
**AhlswedeZhang.supSum_singleton** 是 Mathlib 中的一个定理，位于命名空间 `AhlswedeZhang`。
形式化陈述：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : DecidableEq α] {s : Finset α
} [Nonempty α],   s ≠ Finset.univ → AhlswedeZhang.supSum {s} = ↑(Fintype.card α)
 * ∑ k ∈ Finset.range (Fintype.card α), (↑k)⁻¹
参数：Fintype.card α；Fintype.card α；↑k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.truncatedSup_singleton`：∀ {α : Type u_1} [inst : SemilatticeSup α
] [inst_1 : DecidableLE α] [inst_2 : OrderTop α] (b a : α),   {b}.truncatedSup a
 = if a ≤ b then b …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_of_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a = 
c + b → a - b = c
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Fintype.sum_div
_mul_card_choose_card`：∀ (α : Type u_1) [inst : Fintype α] [Nonempty α],   ∑ s, 
↑(Fintype.card α) / ((↑(Fintype.card α) - ↑s.card) * ↑((Fintype.card α).choose s
.ca…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_ite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M]
 {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f g : ι → M), (∑ x 
∈ s,…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `Finset.filter_subset_univ`：filter_subset_univ [DecidableEq α] (s : Finse
t α) : ({t | t subseteq s} : Finset _) = powerset s
· 使用定理 `Finset.sum_powerset`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMono
id β] (s : Finset α) (f : Finset α → β),   ∑ t ∈ s.powerset, f t = ∑ j ∈ Finset.
range (s.…
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.binomial_sum_eq
`：∀ {m n : ℕ}, n < m → ∑ i ∈ Finset.range (n + 1), ↑(n.choose i) * (↑m - ↑n) / (
(↑m - ↑i) * ↑(m.choose i)) = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.card_lt_iff_ne_univ`：Finset.card_lt_iff_ne_univ [Fintype α] (s : 
Finset α) : #s < Fintype.card α ↔ s != Finset.univ
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Finset.sum_powersetCard`：∀ {α : Type u_1} {β : Type u_2} [inst : AddComm
Monoid β] (n : ℕ) (s : Finset α) (f : ℕ → β),   ∑ t ∈ Finset.powersetCard n s, f
 t.card = s.c…
-/
@[simp] lemma supSum_singleton (hs : s ≠ univ) :
    supSum ({s} : Finset (Finset α)) = card α * ∑ k ∈ range (card α), (k : ℚ)⁻¹ := by
  have : ∀ t : Finset α,
    (card α - #(truncatedSup {s} t) : ℚ) / ((card α - #t) * (card α).choose #t) =
    if t ⊆ s then (card α - #s : ℚ) / ((card α - #t) * (card α).choose #t) else 0 := by
    rintro t
    simp_rw [truncatedSup_singleton]
    split_ifs <;> simp
  simp_rw [← sub_eq_of_eq_add (Fintype.sum_div_mul_card_choose_card α), eq_sub_iff_add_eq,
    ← eq_sub_iff_add_eq', supSum, ← sum_sub_distrib, ← sub_div]
  rw [sum_congr rfl fun t _ ↦ this t, sum_ite, sum_const_zero, add_zero, filter_subset_univ,
    sum_powerset, ← binomial_sum_eq ((card_lt_iff_ne_univ _).2 hs), eq_comm]
  refine sum_congr rfl fun n _ ↦ ?_
  rw [mul_div_assoc, ← nsmul_eq_mul]
  exact sum_powersetCard n s fun m ↦ (card α - #s : ℚ) / ((card α - m) * (card α).choose m)

/-- The **Ahlswede-Zhang Identity**. -/
/-
**AhlswedeZhang.infSum_compls_add_supSum** 是 Mathlib 中的一个引理，位于命名空间 `AhlswedeZhan
g`。
形式化陈述：infSum_compls_add_supSum (𝒜 : Finset (Finset α)) : infSum 𝒜ᶜˢ + supSum 𝒜 =
 card α * ∑ k in range (card α), (k : Rat)⁻¹ + 1
参数：𝒜 : Finset (Finset α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `compl_injective`：compl_injective : Function.Injective (compl : α -> α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.map_univ_of_surjective`：map_univ_of_surjective [Fintype β] {f : β
 ↪ α} (hf : Surjective f) : univ.map f = univ
· 使用定理 `compl_surjective`：compl_surjective : Function.Surjective (compl : α -> α
)
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
· 使用定理 `Nat.choose_symm`：choose_symm {n k : Nat} (hk : k <= n) : choose n (n - k
) = choose n k
· 使用定理 `Finset.univ_map_embedding`：Finset.univ_map_embedding {α : Type*} [Fintyp
e α] (e : α ↪ α) : univ.map e = univ
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `_private.Mathlib.Combinatorics.SetFamily.AhlswedeZhang.0.Fintype.sum_div
_mul_card_choose_card`：∀ (α : Type u_1) [inst : Fintype α] [Nonempty α],   ∑ s, 
↑(Fintype.card α) / ((↑(Fintype.card α) - ↑s.card) * ↑((Fintype.card α).choose s
.ca…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The **Ahlswede-Zhang Identity**.
-/
lemma infSum_compls_add_supSum (𝒜 : Finset (Finset α)) :
    infSum 𝒜ᶜˢ + supSum 𝒜 = card α * ∑ k ∈ range (card α), (k : ℚ)⁻¹ + 1 := by
  unfold infSum supSum
  rw [← @map_univ_of_surjective (Finset α) _ _ _ ⟨compl, compl_injective⟩ compl_surjective, sum_map]
  simp only [Function.Embedding.coeFn_mk, univ_map_embedding, ← compl_truncatedSup,
    ← sum_add_distrib, card_compl, cast_sub (card_le_univ _), choose_symm (card_le_univ _),
    ← add_div, sub_add_cancel, Fintype.sum_div_mul_card_choose_card]
/-
**AhlswedeZhang.supSum_of_univ_notMem** 是 Mathlib 中的一个引理，位于命名空间 `AhlswedeZhang`。
形式化陈述：supSum_of_univ_notMem (h𝒜₁ : 𝒜.Nonempty) (h𝒜₂ : univ ∉ 𝒜) : supSum 𝒜 = car
d α * ∑ k in range (card α), (k : Rat)⁻¹
参数：h𝒜₁ : 𝒜.Nonempty；h𝒜₂ : univ ∉ 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Nonempty.exists_eq_singleton_or_nontrivial`：∀ {α : Type u_1} {s :
 Finset α}, s.Nonempty → (∃ a, s = {a}) ∨ s.Nontrivial
· 使用定理 `AhlswedeZhang.supSum_singleton`：∀ {α : Type u_1} [inst : Fintype α] [ins
t_1 : DecidableEq α] {s : Finset α} [Nonempty α],   s ≠ Finset.univ → AhlswedeZh
ang.supSum {s} = ↑(F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_succ`：card_eq_succ : #s = n + 1 ↔ exists a t, a ∉ t ∧ ins
ert a t = s ∧ #t = n
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LawfulSingleton.insert_empty_eq`：∀ {α : Type u} {β : Type v} {inst : Emp
tyCollection β} {inst_1 : Insert α β} {inst_2 : Singleton α β}   [self : LawfulS
ingleton α β] (x : α)…
· 使用定理 `Finset.instLawfulSingleton`：∀ {α : Type u_1} [inst : DecidableEq α], Law
fulSingleton α (Finset α)
· 使用定理 `Finset.insert_eq`：insert_eq (a : α) (s : Finset α) : insert a s = {a} un
ion s
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用引理 `AhlswedeZhang.supSum_union_add_supSum_infs`：supSum_union_add_supSum_infs
 (𝒜 ℬ : Finset (Finset α)) : supSum (𝒜 union ℬ) + supSum (𝒜 ⊼ ℬ) = supSum 𝒜 + su
pSum ℬ
· 使用定理 `Finset.singleton_infs`：∀ {α : Type u_2} [inst : DecidableEq α] [inst_1 :
 SemilatticeInf α] {t : Finset α} {a : α},   {a} ⊼ t = Finset.image (fun x => a 
⊓ x) t
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Finset.card_image_le`：card_image_le [DecidableEq β] : #(s.image f) <= #s
· 使用定理 `Finset.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} [inst : Decidable
Eq β] {s : Finset α},   s.Nonempty → ∀ (f : α → β), (Finset.image f s).Nonempty
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
lemma supSum_of_univ_notMem (h𝒜₁ : 𝒜.Nonempty) (h𝒜₂ : univ ∉ 𝒜) :
    supSum 𝒜 = card α * ∑ k ∈ range (card α), (k : ℚ)⁻¹ := by
  set m := 𝒜.card with hm
  clear_value m
  induction m using Nat.strongRecOn generalizing 𝒜 with | ind m ih => _
  replace ih := fun 𝒜 h𝒜 h𝒜₁ h𝒜₂ ↦ @ih _ h𝒜 𝒜 h𝒜₁ h𝒜₂ rfl
  obtain ⟨a, rfl⟩ | h𝒜₃ := h𝒜₁.exists_eq_singleton_or_nontrivial
  · refine supSum_singleton ?_
    simpa [eq_comm] using h𝒜₂
  cases m
  · cases h𝒜₁.card_pos.ne hm
  obtain ⟨s, 𝒜, hs, rfl, rfl⟩ := card_eq_succ.1 hm.symm
  have h𝒜 : 𝒜.Nonempty := by by_contra! rfl; simp at h𝒜₃
  rw [insert_eq, eq_sub_of_add_eq (supSum_union_add_supSum_infs _ _), singleton_infs,
    supSum_singleton (ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂), ih, ih, add_sub_cancel_right]
  · exact card_image_le.trans_lt (lt_add_one _)
  · exact h𝒜.image _
  · simpa using fun _ ↦ ne_of_mem_of_not_mem (mem_insert_self _ _) h𝒜₂
  · exact lt_add_one _
  · exact h𝒜
  · exact fun h ↦ h𝒜₂ (mem_insert_of_mem h)

/-- The **Ahlswede-Zhang Identity**. -/
/-
**AhlswedeZhang.infSum_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `AhlswedeZhang`。
形式化陈述：infSum_eq_one (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) : infSum 𝒜 = 1
参数：h𝒜₁ : 𝒜.Nonempty；h𝒜₀ : ∅ ∉ 𝒜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.compls_compls`：∀ {α : Type u_2} [inst : BooleanAlgebra α] (s : Fi
nset α), s.compls.compls = s
· 使用定理 `eq_sub_of_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a + 
c = b → a = b - c
· 使用引理 `AhlswedeZhang.infSum_compls_add_supSum`：infSum_compls_add_supSum (𝒜 : Fi
nset (Finset α)) : infSum 𝒜ᶜˢ + supSum 𝒜 = card α * ∑ k in range (card α), (k : 
Rat)⁻¹ + 1
· 使用引理 `AhlswedeZhang.supSum_of_univ_notMem`：supSum_of_univ_notMem (h𝒜₁ : 𝒜.None
mpty) (h𝒜₂ : univ ∉ 𝒜) : supSum 𝒜 = card α * ∑ k in range (card α), (k : Rat)⁻¹
· 使用定理 `Finset.Nonempty.compls`：∀ {α : Type u_2} [inst : BooleanAlgebra α] {s : 
Finset α}, s.Nonempty → s.compls.Nonempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.compl_univ`：compl_univ : (univ : Finset α)ᶜ = ∅
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b

--- 原说明 ---
The **Ahlswede-Zhang Identity**.
-/
lemma infSum_eq_one (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) : infSum 𝒜 = 1 := by
  rw [← compls_compls 𝒜, eq_sub_of_add_eq (infSum_compls_add_supSum _),
    supSum_of_univ_notMem h𝒜₁.compls, add_sub_cancel_left]
  simpa

end AhlswedeZhang

