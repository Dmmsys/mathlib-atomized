/-
Copyright (c) 2022 Bhavik Mehta, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Order.Ring.NNRat
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SetFamily.Shadow
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# Lubell-Yamamoto-Meshalkin inequality and Sperner's theorem

This file proves the local LYM and LYM inequalities as well as Sperner's theorem.

## Main declarations

* `Finset.local_lubell_yamamoto_meshalkin_inequality_div`: Local Lubell-Yamamoto-Meshalkin
  inequality. The shadow of a set `𝒜` in a layer takes a greater proportion of its layer than `𝒜`
  does.
* `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`: Lubell-Yamamoto-Meshalkin
  inequality. The sum of densities of `𝒜` in each layer is at most `1` for any antichain `𝒜`.
* `IsAntichain.sperner`: Sperner's theorem. The size of any antichain in `Finset α` is at most the
  size of the maximal layer of `Finset α`. It is a corollary of
  `lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`.

## TODO

Prove upward local LYM.

Provide equality cases. Local LYM gives that the equality case of LYM and Sperner is precisely when
`𝒜` is a middle layer.

`falling` could be useful more generally in grade orders.

## References

* http://b-mehta.github.io/maths-notes/iii/mich/combinatorics.pdf
* http://discretemath.imp.fu-berlin.de/DMII-2015-16/kruskal.pdf

## Tags

shadow, lym, slice, sperner, antichain
-/

@[expose] public section

open Finset Nat
open scoped FinsetFamily

variable {𝕜 α : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

namespace Finset

/-! ### Local LYM inequality -/

section LocalLYM
variable [DecidableEq α] [Fintype α] {𝒜 : Finset (Finset α)} {r : ℕ}

/-- The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`. -/
/-
**Finset.local_lubell_yamamoto_meshalkin_inequality_mul** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：local_lubell_yamamoto_meshalkin_inequality_mul (h𝒜 : (𝒜 : Set (Finset α)).
Sized r) : #𝒜 * r <= #(∂ 𝒜) * (Fintype.card α - r + 1)
参数：h𝒜 : (𝒜 : Set (Finset α)).Sized r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_mul_le_card_mul'`：card_mul_le_card_mul' [forall a b, Decidab
le (r a b)] (hn : forall b in t, n <= #(s.bipartiteBelow r b)) (hm : forall a in
 s, #(t.bipartiteA…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_image_of_injOn`：card_image_of_injOn [DecidableEq β] (H : Set
.InjOn f s) : #(s.image f) = #s
· 使用定理 `Finset.erase_injOn`：erase_injOn (s : Finset α) : Set.InjOn s.erase s
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.erase_mem_shadow`：erase_mem_shadow (hs : s in 𝒜) (ha : a in s) : 
erase s a in ∂ 𝒜
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Set.Sized.shadow`：∀ {α : Type u_1} [inst : DecidableEq α] {𝒜 : Finset (F
inset α)} {r : ℕ}, Set.Sized r ↑𝒜 → Set.Sized (r - 1) ↑𝒜.shadow
· 使用定理 `Finset.card_compl`：Finset.card_compl [DecidableEq α] [Fintype α] (s : Fi
nset α) : #sᶜ = Fintype.card α - #s
· 使用定理 `Finset.insert_inj_on'`：insert_inj_on' (s : Finset α) : Set.InjOn (fun a 
=> insert a s) (sᶜ : Finset α)
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Set.Sized.empty_mem_iff`：∀ {α : Type u_1} {A : Set (Finset α)} {r : ℕ}, 
Set.Sized r A → (∅ ∈ A ↔ A = {∅})
· 使用定理 `Finset.coe_eq_singleton`：coe_eq_singleton {s : Finset α} {a : α} : (s : 
Set α) = {a} ↔ s = {a}
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Finset.shadow_singleton_empty`：shadow_singleton_empty : ∂ ({∅} : Finset 
(Finset α)) = ∅
· 使用定理 `Finset.mem_bipartiteAbove`：mem_bipartiteAbove {b : β} : b in t.bipartite
Above r a ↔ b in t ∧ r a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.exists_eq_insert_iff`：exists_eq_insert_iff [DecidableEq α] : (exi
sts a ∉ s, insert a s = t) ↔ s subseteq t ∧ #s + 1 = #t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.sized_shadow_iff`：sized_shadow_iff (h : ∅ ∉ 𝒜) : (∂ 𝒜 : Set (Fins
et α)).Sized r ↔ (𝒜 : Set (Finset α)).Sized (r + 1)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {a} (h : a in s) 
: f a in s.image f
· 使用定理 `Finset.mem_compl`：mem_compl : a in sᶜ ↔ a ∉ s
· 使用定理 `tsub_tsub_le_tsub_add`：tsub_tsub_le_tsub_add {a b c : α} : a - (b - c) <
= a - b + c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α

--- 原说明 ---
The downward **local LYM inequality**, with cancelled denominators. `𝒜` takes up
 less of `α^(r)`
(the finsets of card `r`) than `∂𝒜` takes up of `α^(r - 1)`.
-/
theorem local_lubell_yamamoto_meshalkin_inequality_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) :
    #𝒜 * r ≤ #(∂ 𝒜) * (Fintype.card α - r + 1) := by
  let i : DecidableRel ((· ⊆ ·) : Finset α → Finset α → Prop) := fun _ _ => Classical.dec _
  refine card_mul_le_card_mul' (· ⊆ ·) (fun s hs => ?_) (fun s hs => ?_)
  · rw [← h𝒜 hs, ← card_image_of_injOn s.erase_injOn]
    refine card_le_card ?_
    simp_rw [image_subset_iff, mem_bipartiteBelow]
    exact fun a ha => ⟨erase_mem_shadow hs ha, erase_subset _ _⟩
  refine le_trans ?_ tsub_tsub_le_tsub_add
  rw [← (Set.Sized.shadow h𝒜) hs, ← card_compl, ← card_image_of_injOn (insert_inj_on' _)]
  refine card_le_card fun t ht => ?_
  rw [mem_bipartiteAbove] at ht
  have : ∅ ∉ 𝒜 := by
    rw [← mem_coe, h𝒜.empty_mem_iff, coe_eq_singleton]
    rintro rfl
    rw [shadow_singleton_empty] at hs
    exact notMem_empty s hs
  have h := exists_eq_insert_iff.2 ⟨ht.2, by
    rw [(sized_shadow_iff this).1 (Set.Sized.shadow h𝒜) ht.1, (Set.Sized.shadow h𝒜) hs]⟩
  rcases h with ⟨a, ha, rfl⟩
  exact mem_image_of_mem _ (mem_compl.2 ha)

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_mul]
alias card_mul_le_card_shadow_mul := local_lubell_yamamoto_meshalkin_inequality_mul

/-- The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`. -/
/-
**Finset.local_lubell_yamamoto_meshalkin_inequality_div** 是 Mathlib 中的一个定理，位于命名空
间 `Finset`。
形式化陈述：local_lubell_yamamoto_meshalkin_inequality_div (hr : r != 0) (h𝒜 : (𝒜 : Se
t (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r <= #(∂ 𝒜) / (Finty
pe.card α).choose (r - 1)
参数：hr : r != 0；h𝒜 : (𝒜 : Set (Finset α)).Sized r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg`：cast_nonneg {α} [Semiring α] [PartialOrder α] [IsOrdere
dRing α] (n : Nat) : 0 <= (n : α)
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Finset.local_lubell_yamamoto_meshalkin_inequality_mul`：local_lubell_yama
moto_meshalkin_inequality_mul (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : #𝒜 * r <= #(
∂ 𝒜) * (Fintype.card α - r + 1)
· 使用引理 `div_le_div_iff₀`：div_le_div_iff₀ (hb : 0 < b) (hd : 0 < d) : a / b <= c 
/ d ↔ a * d <= c * b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `le_of_mul_le_mul_right`：le_of_mul_le_mul_right [MulPosReflectLE α] (bc :
 b * a <= c * a) (a0 : 0 < a) : b <= c
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `add_tsub_cancel_right`：add_tsub_cancel_right (a b : α) : a + b - b = a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
The downward **local LYM inequality**. `𝒜` takes up less of `α^(r)` (the finsets
 of card `r`)
than `∂𝒜` takes up of `α^(r - 1)`.
-/
theorem local_lubell_yamamoto_meshalkin_inequality_div (hr : r ≠ 0)
    (h𝒜 : (𝒜 : Set (Finset α)).Sized r) : (#𝒜 : 𝕜) / (Fintype.card α).choose r
    ≤ #(∂ 𝒜) / (Fintype.card α).choose (r - 1) := by
  obtain hr' | hr' := lt_or_ge (Fintype.card α) r
  · rw [choose_eq_zero_of_lt hr', cast_zero, div_zero]
    exact div_nonneg (cast_nonneg _) (cast_nonneg _)
  replace h𝒜 := local_lubell_yamamoto_meshalkin_inequality_mul h𝒜
  rw [div_le_div_iff₀] <;> norm_cast
  · rcases r with - | r
    · exact (hr rfl).elim
    rw [tsub_add_eq_add_tsub hr', add_tsub_add_eq_tsub_right] at h𝒜
    apply le_of_mul_le_mul_right _ (pos_iff_ne_zero.2 hr)
    convert! Nat.mul_le_mul_right ((Fintype.card α).choose r) h𝒜 using 1
    · simpa [mul_assoc, Nat.choose_succ_right_eq] using Or.inl (mul_comm _ _)
    · simp only [mul_assoc, choose_succ_right_eq, mul_eq_mul_left_iff]
      exact Or.inl (mul_comm _ _)
  · exact Nat.choose_pos hr'
  · exact Nat.choose_pos (r.pred_le.trans hr')

@[inherit_doc local_lubell_yamamoto_meshalkin_inequality_div]
alias card_div_choose_le_card_shadow_div_choose := local_lubell_yamamoto_meshalkin_inequality_div

end LocalLYM

/-! ### LYM inequality -/

section LYM

section Falling

variable [DecidableEq α] (k : ℕ) (𝒜 : Finset (Finset α))

/-- `falling k 𝒜` is all the finsets of cardinality `k` which are a subset of something in `𝒜`. -/
/-
**Finset.falling** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：falling : Finset (Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`falling k 𝒜` is all the finsets of cardinality `k` which are a subset of someth
ing in `𝒜`.
-/
def falling : Finset (Finset α) :=
  𝒜.sup <| powersetCard k

variable {𝒜 k} {s : Finset α}
/-
**Finset.mem_falling** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：mem_falling : s in falling k 𝒜 ↔ (exists t in 𝒜, s subseteq t) ∧ #s = k
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_falling : s ∈ falling k 𝒜 ↔ (∃ t ∈ 𝒜, s ⊆ t) ∧ #s = k := by
  grind [falling, mem_sup]

variable (𝒜 k)
/-
**Finset.sized_falling** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_falling`：mem_falling : s in falling k 𝒜 ↔ (exists t in 𝒜, s s
ubseteq t) ∧ #s = k
-/
theorem sized_falling : (falling k 𝒜 : Set (Finset α)).Sized k := fun _ hs => (mem_falling.1 hs).2
/-
**Finset.slice_subset_falling** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：slice_subset_falling : 𝒜 # k subseteq falling k 𝒜
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_falling`：mem_falling : s in falling k 𝒜 ↔ (exists t in 𝒜, s s
ubseteq t) ∧ #s = k
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_slice`：mem_slice : A in 𝒜 # r ↔ A in 𝒜 ∧ #A = r
-/
theorem slice_subset_falling : 𝒜 # k ⊆ falling k 𝒜 := fun s hs =>
  mem_falling.2 <| (mem_slice.1 hs).imp_left fun h => ⟨s, h, Subset.refl _⟩
/-
**Finset.falling_zero_subset** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：falling_zero_subset : falling 0 𝒜 subseteq {∅}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.subset_singleton_iff'`：subset_singleton_iff' {s : Finset α} {a : 
α} : s subseteq {a} ↔ forall b in s, b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.sized_falling`：sized_falling : (falling k 𝒜 : Set (Finset α)).Siz
ed k
-/
theorem falling_zero_subset : falling 0 𝒜 ⊆ {∅} :=
  subset_singleton_iff'.2 fun _ ht => card_eq_zero.1 <| sized_falling _ _ ht
/-
**Finset.slice_union_shadow_falling_succ** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：slice_union_shadow_falling_succ : 𝒜 # k union ∂ (falling (k + 1) 𝒜) = fall
ing k 𝒜
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.ssubset_iff`：ssubset_iff : s ⊂ t ↔ exists a ∉ s, insert a s subse
teq t
· 使用定理 `ssubset_of_subset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Membership.mem.ne_of_notMem`：∀ {α : Type u_1} {β : Type u_2} [inst : Mem
bership α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.card_insert_of_notMem`：card_insert_of_notMem (h : a ∉ s) : #(inse
rt a s) = #s + 1
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用定理 `Finset.erase_insert`：erase_insert {a : α} {s : Finset α} (h : a ∉ s) : (
insert a s).erase a = s
-/
theorem slice_union_shadow_falling_succ : 𝒜 # k ∪ ∂ (falling (k + 1) 𝒜) = falling k 𝒜 := by
  ext s
  simp_rw [mem_union, mem_slice, mem_shadow_iff, mem_falling]
  constructor
  · rintro (h | ⟨s, ⟨⟨t, ht, hst⟩, hs⟩, a, ha, rfl⟩)
    · exact ⟨⟨s, h.1, Subset.refl _⟩, h.2⟩
    refine ⟨⟨t, ht, (erase_subset _ _).trans hst⟩, ?_⟩
    rw [card_erase_of_mem ha, hs]
    rfl
  · rintro ⟨⟨t, ht, hst⟩, hs⟩
    by_cases h : s ∈ 𝒜
    · exact Or.inl ⟨h, hs⟩
    obtain ⟨a, ha, hst⟩ := ssubset_iff.1 (ssubset_of_subset_of_ne hst (ht.ne_of_notMem h).symm)
    refine Or.inr ⟨insert a s, ⟨⟨t, ht, hst⟩, ?_⟩, a, mem_insert_self _ _, erase_insert ha⟩
    rw [card_insert_of_notMem ha, hs]

variable {𝒜 k}

/-- The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, thanks to the
antichain property. -/
/-
**Finset.IsAntichain.disjoint_slice_shadow_falling** 是 Mathlib 中的一个定理，位于命名空间 `Fi
nset.IsAntichain`。
形式化陈述：∀ {α : Type u_2} [inst : DecidableEq α] {𝒜 : Finset (Finset α)} {m n : ℕ},
   IsAntichain (fun x1 x2 => x1 ⊆ x2) ↑𝒜 → Disjoint (𝒜.slice m) (Finset.falling 
n 𝒜).shadow
参数：Finset α；fun x1 x2 => x1 ⊆ x2；𝒜.slice m；Finset.falling n 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in 
t -> a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.slice_subset`：slice_subset : 𝒜 # r subseteq 𝒜
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.erase_subset`：erase_subset (a : α) (s : Finset α) : erase s a sub
seteq s

--- 原说明 ---
The shadow of `falling m 𝒜` is disjoint from the `n`-sized elements of `𝒜`, than
ks to the
antichain property.
-/
theorem IsAntichain.disjoint_slice_shadow_falling {m n : ℕ}
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) : Disjoint (𝒜 # m) (∂ (falling n 𝒜)) :=
  disjoint_right.2 fun s h₁ h₂ => by
    simp_rw [mem_shadow_iff, mem_falling] at h₁
    obtain ⟨s, ⟨⟨t, ht, hst⟩, _⟩, a, ha, rfl⟩ := h₁
    refine h𝒜 (slice_subset h₂) ht ?_ ((erase_subset _ _).trans hst)
    rintro rfl
    exact notMem_erase _ _ (hst ha)

/-- A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`. -/
/-
**Finset.le_card_falling_div_choose** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：le_card_falling_div_choose [Fintype α] (hk : k <= Fintype.card α) (h𝒜 : Is
Antichain (· subseteq ·) (𝒜 : Set (Finset α))) : (∑ r in range (k + 1), (#(𝒜 # (
Fintype.card α - r)) : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) <= (fa
lling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k
)
参数：hk : k <= Fintype.card α；h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.slice_subset_falling`：slice_subset_falling : 𝒜 # k subseteq falli
ng k 𝒜
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.slice_union_shadow_falling_succ`：slice_union_shadow_falling_succ 
: 𝒜 # k union ∂ (falling (k + 1) 𝒜) = falling k 𝒜
· 使用定理 `Finset.card_union_of_disjoint`：∀ {α : Type u_1} {s t : Finset α} [inst :
 DecidableEq α], Disjoint s t → (s ∪ t).card = s.card + t.card
· 使用定理 `Finset.IsAntichain.disjoint_slice_shadow_falling`：∀ {α : Type u_2} [inst
 : DecidableEq α] {𝒜 : Finset (Finset α)} {m n : ℕ},   IsAntichain (fun x1 x2 =>
 x1 ⊆ x2) ↑𝒜 → Disjoint (𝒜.slice m) (F…
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `tsub_tsub`：tsub_tsub (b a c : α) : b - a - c = b - (a + c)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `le_tsub_of_add_le_left`：le_tsub_of_add_le_left (h : a + b <= c) : b <= c
 - a
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
A bound on any top part of the sum in LYM in terms of the size of `falling k 𝒜`.
-/
theorem le_card_falling_div_choose [Fintype α] (hk : k ≤ Fintype.card α)
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    (∑ r ∈ range (k + 1),
        (#(𝒜 # (Fintype.card α - r)) : 𝕜) / (Fintype.card α).choose (Fintype.card α - r)) ≤
      (falling (Fintype.card α - k) 𝒜).card / (Fintype.card α).choose (Fintype.card α - k) := by
  induction k with
  | zero =>
    simp only [cast_one, cast_le, sum_singleton, div_one, choose_self, range_one,
      zero_add, range_one, sum_singleton,
      choose_self, cast_one, div_one, cast_le, tsub_zero]
    exact card_le_card (slice_subset_falling _ _)
  | succ k ih =>
    rw [sum_range_succ, ← slice_union_shadow_falling_succ,
      card_union_of_disjoint (IsAntichain.disjoint_slice_shadow_falling h𝒜),
      cast_add, _root_.add_div, add_comm]
    rw [← tsub_tsub, tsub_add_cancel_of_le (le_tsub_of_add_le_left hk)]
    grw [ih <| le_of_succ_le hk, local_lubell_yamamoto_meshalkin_inequality_div
      (tsub_pos_iff_lt.2 <| Nat.succ_le_iff.1 hk).ne' <| sized_falling _ _]

end Falling

variable [Fintype α] {𝒜 : Finset (Finset α)}

/-- The **Lubell-Yamamoto-Meshalkin inequality**, also known as the **LYM inequality**.

If `𝒜` is an antichain, then the sum of the proportion of elements it takes from each layer is less
than `1`. -/
/-
**Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose** 是 Mathlib 中的
一个定理，位于命名空间 `Finset`。
形式化陈述：lubell_yamamoto_meshalkin_inequality_sum_card_div_choose (h𝒜 : IsAntichain
 (· subseteq ·) (𝒜 : Set (Finset α))) : ∑ r in range (Fintype.card α + 1), (#(𝒜 
# r) / (Fintype.card α).choose r : 𝕜) <= 1
参数：h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_flip`：∀ {M : Type u_4} [inst : AddCommMonoid M] {n : ℕ} (f : 
ℕ → M),   ∑ r ∈ Finset.range (n + 1), f (n - r) = ∑ k ∈ Finset.range (n + 1), f 
k
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Finset.le_card_falling_div_choose`：le_card_falling_div_choose [Fintype α
] (hk : k <= Fintype.card α) (h𝒜 : IsAntichain (· subseteq ·) (𝒜 : Set (Finset α
))) : (∑ r in range (k …
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.sub_self`：∀ (n : ℕ), n - n = 0
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Set.Sized.card_le`：∀ {α : Type u_1} [inst : Fintype α] {𝒜 : Finset (Fins
et α)} {r : ℕ}, Set.Sized r ↑𝒜 → 𝒜.card ≤ (Fintype.card α).choose r
· 使用定理 `Finset.sized_falling`：sized_falling : (falling k 𝒜 : Set (Finset α)).Siz
ed k

--- 原说明 ---
The **Lubell-Yamamoto-Meshalkin inequality**, also known as the **LYM inequality
**.

If `𝒜` is an antichain, then the sum of the proportion of elements it takes from
 each layer is less
than `1`.
-/
theorem lubell_yamamoto_meshalkin_inequality_sum_card_div_choose
    (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    ∑ r ∈ range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) ≤ 1 := by
  classical
    rw [← sum_flip]
    refine (le_card_falling_div_choose le_rfl h𝒜).trans ?_
    rw [div_le_iff₀] <;> norm_cast
    · simpa only [Nat.sub_self, one_mul, Nat.choose_zero_right, falling] using
        Set.Sized.card_le (sized_falling 0 𝒜)
    · rw [tsub_self, choose_zero_right]
      exact zero_lt_one

@[inherit_doc lubell_yamamoto_meshalkin_inequality_sum_card_div_choose]
alias sum_card_slice_div_choose_le_one := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose

/-- The **Lubell-Yamamoto-Meshalkin inequality**, also known as the **LYM inequality**.

If `𝒜` is an antichain, then the sum of `(#α.choose #s)⁻¹` over `s ∈ 𝒜` is less than `1`. -/
/-
**Finset.lubell_yamamoto_meshalkin_inequality_sum_inv_choose** 是 Mathlib 中的一个定理，
位于命名空间 `Finset`。
形式化陈述：lubell_yamamoto_meshalkin_inequality_sum_inv_choose (h𝒜 : IsAntichain (· s
ubseteq ·) (SetLike.coe 𝒜)) : ∑ s in 𝒜, ((Fintype.card α).choose #s : 𝕜)⁻¹ <= 1
参数：h𝒜 : IsAntichain (· subseteq ·) (SetLike.coe 𝒜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_fiberwise_of_maps_to'`：∀ {ι : Type u_1} {κ : Type u_2} {M : T
ype u_4} [inst : AddCommMonoid M] {s : Finset ι} {t : Finset κ}   [inst_1 : Deci
dableEq κ] {g : ι → κ}…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose`：lubell_
yamamoto_meshalkin_inequality_sum_card_div_choose (h𝒜 : IsAntichain (· subseteq 
·) (𝒜 : Set (Finset α))) : ∑ r in range (Fintype.card…

--- 原说明 ---
The **Lubell-Yamamoto-Meshalkin inequality**, also known as the **LYM inequality
**.

If `𝒜` is an antichain, then the sum of `(#α.choose #s)⁻¹` over `s ∈ 𝒜` is less 
than `1`.
-/
theorem lubell_yamamoto_meshalkin_inequality_sum_inv_choose
    (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : 𝕜)⁻¹ ≤ 1 := by
  calc
    _ = ∑ r ∈ range (Fintype.card α + 1),
        ∑ s ∈ 𝒜 with #s = r, ((Fintype.card α).choose r : 𝕜)⁻¹ := by
      rw [sum_fiberwise_of_maps_to']; simp [card_le_univ]
    _ = ∑ r ∈ range (Fintype.card α + 1), (#(𝒜 # r) / (Fintype.card α).choose r : 𝕜) := by
      simp [slice, div_eq_mul_inv]
    _ ≤ 1 := lubell_yamamoto_meshalkin_inequality_sum_card_div_choose h𝒜

/-! ### Sperner's theorem -/

/-- **Sperner's theorem**. The size of an antichain in `Finset α` is bounded by the size of the
maximal layer in `Finset α`. This precisely means that `Finset α` is a Sperner order. -/
/-
**Finset._root_.IsAntichain.sperner** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
**Sperner's theorem**. The size of an antichain in `Finset α` is bounded by the 
size of the
maximal layer in `Finset α`. This precisely means that `Finset α` is a Sperner o
rder.
-/
theorem _root_.IsAntichain.sperner (h𝒜 : IsAntichain (· ⊆ ·) (SetLike.coe 𝒜)) :
    #𝒜 ≤ (Fintype.card α).choose (Fintype.card α / 2) := by
  have : 0 < ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0) :=
    Nat.cast_pos.2 <| choose_pos (Nat.div_le_self _ _)
  have h := calc
    ∑ s ∈ 𝒜, ((Fintype.card α).choose (Fintype.card α / 2) : ℚ≥0)⁻¹
    _ ≤ ∑ s ∈ 𝒜, ((Fintype.card α).choose #s : ℚ≥0)⁻¹ := by
      gcongr with s hs
      · exact mod_cast choose_pos s.card_le_univ
      · exact choose_le_middle _ _
    _ ≤ 1 := lubell_yamamoto_meshalkin_inequality_sum_inv_choose h𝒜
  simpa [mul_inv_le_iff₀' this] using h

end LYM
end Finset

