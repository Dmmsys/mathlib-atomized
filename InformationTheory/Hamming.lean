/-
Copyright (c) 2022 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Mathlib.Analysis.Normed.Group.Basic

/-!
# Hamming spaces

The Hamming metric counts the number of places two members of a (finite) Pi type
differ. The Hamming norm is the same as the Hamming metric over additive groups, and
counts the number of places a member of a (finite) Pi type differs from zero.

This is a useful notion in various applications, but in particular it is relevant
in coding theory, in which it is fundamental for defining the minimum distance of a
code.

## Main definitions
* `hammingDist x y`: the Hamming distance between `x` and `y`, the number of entries which differ.
* `hammingNorm x`: the Hamming norm of `x`, the number of non-zero entries.
* `Hamming β`: a type synonym for `Π i, β i` with `dist` and `norm` provided by the above.
* `Hamming.toHamming`, `Hamming.ofHamming`: functions for casting between `Hamming β` and
  `Π i, β i`.
* the Hamming norm forms a normed group on `Hamming β`.
-/

@[expose] public section


section HammingDistNorm

open Finset Function

variable {α ι : Type*} {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]
variable {γ : ι → Type*} [∀ i, DecidableEq (γ i)]

/-- The Hamming distance function to the naturals. -/
/-
**hammingDist** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hammingDist (x y : forall i, β i) : Nat
参数：x y : forall i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hamming distance function to the naturals.
-/
def hammingDist (x y : ∀ i, β i) : ℕ := #{i | x i ≠ y i}

/-- Corresponds to `dist_self`. -/
@[simp]
/-
**hammingDist_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_self (x : forall i, β i) : hammingDist x x = 0
参数：x : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist.eq_1`：∀ {ι : Type u_2} {β : ι → Type u_3} [inst : Fintype ι]
 [inst_1 : (i : ι) → DecidableEq (β i)] (x y : (i : ι) → β i),   hammingDist x y
 = {i …
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用定理 `Finset.filter_eq_empty_iff`：∀ {α : Type u_1} {p : α → Prop} [inst : Deci
dablePred p] {s : Finset α}, Finset.filter p s = ∅ ↔ ∀ ⦃x : α⦄, x ∈ s → ¬p x

--- 原说明 ---
Corresponds to `dist_self`.
-/
theorem hammingDist_self (x : ∀ i, β i) : hammingDist x x = 0 := by
  rw [hammingDist, card_eq_zero, filter_eq_empty_iff]
  exact fun _ _ H => H rfl

-- TODO: this seems unnecessary.
/-- Corresponds to `dist_nonneg`. -/
/-
**hammingDist_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_nonneg {x y : forall i, β i} : 0 <= hammingDist x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Corresponds to `dist_nonneg`.
-/
theorem hammingDist_nonneg {x y : ∀ i, β i} : 0 ≤ hammingDist x y :=
  zero_le

/-- Corresponds to `dist_comm`. -/
/-
**hammingDist_comm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_comm (x y : forall i, β i) : hammingDist x y = hammingDist y x
参数：x y : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Corresponds to `dist_comm`.
-/
theorem hammingDist_comm (x y : ∀ i, β i) : hammingDist x y = hammingDist y x := by
  simp_rw [hammingDist, ne_comm]

/-- Corresponds to `dist_triangle`. -/
/-
**hammingDist_triangle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_triangle (x y z : forall i, β i) : hammingDist x z <= hammingD
ist x y + hammingDist y z
参数：x y z : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Finset.card_mono`：card_mono : Monotone (@card α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.filter_or`：filter_or (s : Finset α) : (s.filter fun a => p a ∨ q 
a) = s.filter p union s.filter q
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Ne.ne_or_ne`：Ne.ne_or_ne {x y : α} (z : α) (h : x != y) : x != z ∨ y != 
z
· 使用定理 `Finset.card_union_le`：card_union_le (s t : Finset α) : #(s union t) <= #
s + #t

--- 原说明 ---
Corresponds to `dist_triangle`.
-/
theorem hammingDist_triangle (x y z : ∀ i, β i) :
    hammingDist x z ≤ hammingDist x y + hammingDist y z := by
  classical
    unfold hammingDist
    refine le_trans (card_mono ?_) (card_union_le _ _)
    rw [← filter_or]
    exact monotone_filter_right _ fun i _ h ↦ (h.ne_or_ne _).imp_right Ne.symm

/-- Corresponds to `dist_triangle_left`. -/
/-
**hammingDist_triangle_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_triangle_left (x y z : forall i, β i) : hammingDist x y <= ham
mingDist z x + hammingDist z y
参数：x y z : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist_comm`：hammingDist_comm (x y : forall i, β i) : hammingDist x
 y = hammingDist y x
· 使用定理 `hammingDist_triangle`：hammingDist_triangle (x y z : forall i, β i) : ham
mingDist x z <= hammingDist x y + hammingDist y z

--- 原说明 ---
Corresponds to `dist_triangle_left`.
-/
theorem hammingDist_triangle_left (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist z x + hammingDist z y := by
  rw [hammingDist_comm z]
  exact hammingDist_triangle _ _ _

/-- Corresponds to `dist_triangle_right`. -/
/-
**hammingDist_triangle_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_triangle_right (x y z : forall i, β i) : hammingDist x y <= ha
mmingDist x z + hammingDist y z
参数：x y z : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist_comm`：hammingDist_comm (x y : forall i, β i) : hammingDist x
 y = hammingDist y x
· 使用定理 `hammingDist_triangle`：hammingDist_triangle (x y z : forall i, β i) : ham
mingDist x z <= hammingDist x y + hammingDist y z

--- 原说明 ---
Corresponds to `dist_triangle_right`.
-/
theorem hammingDist_triangle_right (x y z : ∀ i, β i) :
    hammingDist x y ≤ hammingDist x z + hammingDist y z := by
  rw [hammingDist_comm y]
  exact hammingDist_triangle _ _ _

/-- Corresponds to `swap_dist`. -/
/-
**swap_hammingDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hammingDist_comm`：hammingDist_comm (x y : forall i, β i) : hammingDist x
 y = hammingDist y x

--- 原说明 ---
Corresponds to `swap_dist`.
-/
theorem swap_hammingDist : swap (@hammingDist _ β _ _) = hammingDist := by
  funext x y
  exact hammingDist_comm _ _

/-- Corresponds to `eq_of_dist_eq_zero`. -/
/-
**eq_of_hammingDist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_of_hammingDist_eq_zero {x y : forall i, β i} : hammingDist x y = 0 -> x
 = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p

--- 原说明 ---
Corresponds to `eq_of_dist_eq_zero`.
-/
theorem eq_of_hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 → x = y := by
  simp_rw [hammingDist, card_eq_zero, filter_eq_empty_iff, Classical.not_not, funext_iff, mem_univ,
    forall_true_left, imp_self]

/-- Corresponds to `dist_eq_zero`. -/
@[simp]
/-
**hammingDist_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_eq_zero {x y : forall i, β i} : hammingDist x y = 0 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_hammingDist_eq_zero`：eq_of_hammingDist_eq_zero {x y : forall i, β 
i} : hammingDist x y = 0 -> x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist_self`：hammingDist_self (x : forall i, β i) : hammingDist x x
 = 0

--- 原说明 ---
Corresponds to `dist_eq_zero`.
-/
theorem hammingDist_eq_zero {x y : ∀ i, β i} : hammingDist x y = 0 ↔ x = y :=
  ⟨eq_of_hammingDist_eq_zero, fun H => by
    rw [H]
    exact hammingDist_self _⟩

/-- Corresponds to `zero_eq_dist`. -/
@[simp]
/-
**hamming_zero_eq_dist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hamming_zero_eq_dist {x y : forall i, β i} : 0 = hammingDist x y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `hammingDist_eq_zero`：hammingDist_eq_zero {x y : forall i, β i} : hamming
Dist x y = 0 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Corresponds to `zero_eq_dist`.
-/
theorem hamming_zero_eq_dist {x y : ∀ i, β i} : 0 = hammingDist x y ↔ x = y := by
  rw [eq_comm, hammingDist_eq_zero]

/-- Corresponds to `dist_ne_zero`. -/
/-
**hammingDist_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_ne_zero {x y : forall i, β i} : hammingDist x y != 0 ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `hammingDist_eq_zero`：hammingDist_eq_zero {x y : forall i, β i} : hamming
Dist x y = 0 ↔ x = y

--- 原说明 ---
Corresponds to `dist_ne_zero`.
-/
theorem hammingDist_ne_zero {x y : ∀ i, β i} : hammingDist x y ≠ 0 ↔ x ≠ y :=
  hammingDist_eq_zero.not

/-- Corresponds to `dist_pos`. -/
@[simp]
/-
**hammingDist_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_pos {x y : forall i, β i} : 0 < hammingDist x y ↔ x != y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `hammingDist_ne_zero`：hammingDist_ne_zero {x y : forall i, β i} : hamming
Dist x y != 0 ↔ x != y
· 使用定理 `iff_not_comm`：iff_not_comm : (a ↔ ¬b) ↔ (b ↔ ¬a)
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.le_zero`：∀ {i : ℕ}, i ≤ 0 ↔ i = 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Corresponds to `dist_pos`.
-/
theorem hammingDist_pos {x y : ∀ i, β i} : 0 < hammingDist x y ↔ x ≠ y := by
  rw [← hammingDist_ne_zero, iff_not_comm, not_lt, Nat.le_zero]
/-
**hammingDist_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_lt_one {x y : forall i, β i} : hammingDist x y < 1 ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `hammingDist_eq_zero`：hammingDist_eq_zero {x y : forall i, β i} : hamming
Dist x y = 0 ↔ x = y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem hammingDist_lt_one {x y : ∀ i, β i} : hammingDist x y < 1 ↔ x = y := by
  rw [Nat.lt_one_iff, hammingDist_eq_zero]
/-
**hammingDist_le_card_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_le_card_fintype {x y : forall i, β i} : hammingDist x y <= Fin
type.card ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_univ`：Finset.card_le_univ [Fintype α] (s : Finset α) : #s
 <= Fintype.card α
-/
theorem hammingDist_le_card_fintype {x y : ∀ i, β i} : hammingDist x y ≤ Fintype.card ι :=
  card_le_univ _
/-
**hammingDist_comp_le_hammingDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_comp_le_hammingDist (f : forall i, γ i -> β i) {x y : forall i
, γ i} : hammingDist (fun i => f i (x i)) (fun i => f i (y i)) <= hammingDist x 
y
参数：f : forall i, γ i -> β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem hammingDist_comp_le_hammingDist (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} :
    hammingDist (fun i => f i (x i)) (fun i => f i (y i)) ≤ hammingDist x y := by
  dsimp [hammingDist]; gcongr; simp +contextual
/-
**hammingDist_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_comp (f : forall i, γ i -> β i) {x y : forall i, γ i} (hf : fo
rall i, Injective (f i)) : hammingDist (fun i => f i (x i)) (fun i => f i (y i))
 = hammingDist x y
参数：f : forall i, γ i -> β i；hf : forall i, Injective (f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `hammingDist_comp_le_hammingDist`：hammingDist_comp_le_hammingDist (f : fo
rall i, γ i -> β i) {x y : forall i, γ i} : hammingDist (fun i => f i (x i)) (fu
n i => f i (y i)) <= …
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Finset.monotone_filter_right`：∀ {α : Type u_1} (s : Finset α) ⦃p q : α →
 Prop⦄ [inst : DecidablePred p] [inst_1 : DecidablePred q],   (∀ a ∈ s, p a → q 
a) → Finset.filter…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem hammingDist_comp (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} (hf : ∀ i, Injective (f i)) :
    hammingDist (fun i => f i (x i)) (fun i => f i (y i)) = hammingDist x y :=
  le_antisymm (hammingDist_comp_le_hammingDist _) <| by dsimp [hammingDist]; gcongr; exact @hf _ _ _
/-
**hammingDist_smul_le_hammingDist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_smul_le_hammingDist [forall i, SMul α (β i)] {k : α} {x y : fo
rall i, β i} : hammingDist (k • x) (k • y) <= hammingDist x y
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_comp_le_hammingDist`：hammingDist_comp_le_hammingDist (f : fo
rall i, γ i -> β i) {x y : forall i, γ i} : hammingDist (fun i => f i (x i)) (fu
n i => f i (y i)) <= …
-/
theorem hammingDist_smul_le_hammingDist [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i} :
    hammingDist (k • x) (k • y) ≤ hammingDist x y :=
  hammingDist_comp_le_hammingDist fun i => (k • · : β i → β i)

/-- Corresponds to `dist_smul` with the discrete norm on `α`. -/
/-
**hammingDist_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_smul [forall i, SMul α (β i)] {k : α} {x y : forall i, β i} (h
k : forall i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist
 x y
参数：β i；hk : forall i, IsSMulRegular (β i) k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_comp`：hammingDist_comp (f : forall i, γ i -> β i) {x y : for
all i, γ i} (hf : forall i, Injective (f i)) : hammingDist (fun i => f i (x i)) 
(fun i…

--- 原说明 ---
Corresponds to `dist_smul` with the discrete norm on `α`.
-/
theorem hammingDist_smul [∀ i, SMul α (β i)] {k : α} {x y : ∀ i, β i}
    (hk : ∀ i, IsSMulRegular (β i) k) : hammingDist (k • x) (k • y) = hammingDist x y :=
  hammingDist_comp (fun i => (k • · : β i → β i)) hk

section Zero

variable [∀ i, Zero (β i)] [∀ i, Zero (γ i)]

/-- The Hamming weight function to the naturals. -/
/-
**hammingNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：hammingNorm (x : forall i, β i) : Nat
参数：x : forall i, β i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Hamming weight function to the naturals.
-/
def hammingNorm (x : ∀ i, β i) : ℕ := #{i | x i ≠ 0}

/-- Corresponds to `dist_zero_right`. -/
@[simp]
/-
**hammingDist_zero_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_zero_right (x : forall i, β i) : hammingDist x 0 = hammingNorm
 x
参数：x : forall i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Corresponds to `dist_zero_right`.
-/
theorem hammingDist_zero_right (x : ∀ i, β i) : hammingDist x 0 = hammingNorm x :=
  rfl

/-- Corresponds to `dist_zero_left`. -/
@[simp]
/-
**hammingDist_zero_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_zero_left : hammingDist (0 : forall i, β i) = hammingNorm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist_comm`：hammingDist_comm (x y : forall i, β i) : hammingDist x
 y = hammingDist y x
· 使用定理 `hammingDist_zero_right`：hammingDist_zero_right (x : forall i, β i) : ham
mingDist x 0 = hammingNorm x

--- 原说明 ---
Corresponds to `dist_zero_left`.
-/
theorem hammingDist_zero_left : hammingDist (0 : ∀ i, β i) = hammingNorm :=
  funext fun x => by rw [hammingDist_comm, hammingDist_zero_right]

-- TODO: this seems unnecessary.
/-- Corresponds to `norm_nonneg`. -/
/-
**hammingNorm_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_nonneg {x : forall i, β i} : 0 <= hammingNorm x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
Corresponds to `norm_nonneg`.
-/
theorem hammingNorm_nonneg {x : ∀ i, β i} : 0 ≤ hammingNorm x :=
  zero_le

/-- Corresponds to `norm_zero`. -/
@[simp]
/-
**hammingNorm_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_zero : hammingNorm (0 : forall i, β i) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_self`：hammingDist_self (x : forall i, β i) : hammingDist x x
 = 0

--- 原说明 ---
Corresponds to `norm_zero`.
-/
theorem hammingNorm_zero : hammingNorm (0 : ∀ i, β i) = 0 :=
  hammingDist_self _

/-- Corresponds to `norm_eq_zero`. -/
@[simp]
/-
**hammingNorm_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_eq_zero {x : forall i, β i} : hammingNorm x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_eq_zero`：hammingDist_eq_zero {x y : forall i, β i} : hamming
Dist x y = 0 ↔ x = y

--- 原说明 ---
Corresponds to `norm_eq_zero`.
-/
theorem hammingNorm_eq_zero {x : ∀ i, β i} : hammingNorm x = 0 ↔ x = 0 :=
  hammingDist_eq_zero

/-- Corresponds to `norm_ne_zero_iff`. -/
/-
**hammingNorm_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_ne_zero_iff {x : forall i, β i} : hammingNorm x != 0 ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `hammingNorm_eq_zero`：hammingNorm_eq_zero {x : forall i, β i} : hammingNo
rm x = 0 ↔ x = 0

--- 原说明 ---
Corresponds to `norm_ne_zero_iff`.
-/
theorem hammingNorm_ne_zero_iff {x : ∀ i, β i} : hammingNorm x ≠ 0 ↔ x ≠ 0 :=
  hammingNorm_eq_zero.not

/-- Corresponds to `norm_pos_iff`. -/
@[simp]
/-
**hammingNorm_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_pos_iff {x : forall i, β i} : 0 < hammingNorm x ↔ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_pos`：hammingDist_pos {x y : forall i, β i} : 0 < hammingDist
 x y ↔ x != y

--- 原说明 ---
Corresponds to `norm_pos_iff`.
-/
theorem hammingNorm_pos_iff {x : ∀ i, β i} : 0 < hammingNorm x ↔ x ≠ 0 :=
  hammingDist_pos
/-
**hammingNorm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_lt_one {x : forall i, β i} : hammingNorm x < 1 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_lt_one`：hammingDist_lt_one {x y : forall i, β i} : hammingDi
st x y < 1 ↔ x = y
-/
theorem hammingNorm_lt_one {x : ∀ i, β i} : hammingNorm x < 1 ↔ x = 0 :=
  hammingDist_lt_one
/-
**hammingNorm_le_card_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_le_card_fintype {x : forall i, β i} : hammingNorm x <= Fintype
.card ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingDist_le_card_fintype`：hammingDist_le_card_fintype {x y : forall i
, β i} : hammingDist x y <= Fintype.card ι
-/
theorem hammingNorm_le_card_fintype {x : ∀ i, β i} : hammingNorm x ≤ Fintype.card ι :=
  hammingDist_le_card_fintype
/-
**hammingNorm_comp_le_hammingNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_comp_le_hammingNorm (f : forall i, γ i -> β i) {x : forall i, 
γ i} (hf : forall i, f i 0 = 0) : (hammingNorm fun i => f i (x i)) <= hammingNor
m x
参数：f : forall i, γ i -> β i；hf : forall i, f i 0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist.congr_simp`：∀ {ι : Type u_2} {β : ι → Type u_3} [inst : Fint
ype ι] {inst_1 : (i : ι) → DecidableEq (β i)}   [inst_2 : (i : ι) → DecidableEq 
(β i)] (x x_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hammingDist_comp_le_hammingDist`：hammingDist_comp_le_hammingDist (f : fo
rall i, γ i -> β i) {x y : forall i, γ i} : hammingDist (fun i => f i (x i)) (fu
n i => f i (y i)) <= …
-/
theorem hammingNorm_comp_le_hammingNorm (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf : ∀ i, f i 0 = 0) :
    (hammingNorm fun i => f i (x i)) ≤ hammingNorm x := by
  simpa only [← hammingDist_zero_right, hf]
    using! hammingDist_comp_le_hammingDist f (y := fun _ ↦ 0)
/-
**hammingNorm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_comp (f : forall i, γ i -> β i) {x : forall i, γ i} (hf₁ : for
all i, Injective (f i)) (hf₂ : forall i, f i 0 = 0) : (hammingNorm fun i => f i 
(x i)) = hammingNorm x
参数：f : forall i, γ i -> β i；hf₁ : forall i, Injective (f i)；hf₂ : forall i, f i 
0 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hammingDist.congr_simp`：∀ {ι : Type u_2} {β : ι → Type u_3} [inst : Fint
ype ι] {inst_1 : (i : ι) → DecidableEq (β i)}   [inst_2 : (i : ι) → DecidableEq 
(β i)] (x x_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `hammingDist_comp`：hammingDist_comp (f : forall i, γ i -> β i) {x y : for
all i, γ i} (hf : forall i, Injective (f i)) : hammingDist (fun i => f i (x i)) 
(fun i…
-/
theorem hammingNorm_comp (f : ∀ i, γ i → β i) {x : ∀ i, γ i} (hf₁ : ∀ i, Injective (f i))
    (hf₂ : ∀ i, f i 0 = 0) : (hammingNorm fun i => f i (x i)) = hammingNorm x := by
  simpa only [← hammingDist_zero_right, hf₂] using! hammingDist_comp f hf₁ (y := fun _ ↦ 0)
/-
**hammingNorm_smul_le_hammingNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_smul_le_hammingNorm [Zero α] [forall i, SMulWithZero α (β i)] 
{k : α} {x : forall i, β i} : hammingNorm (k • x) <= hammingNorm x
参数：β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingNorm_comp_le_hammingNorm`：hammingNorm_comp_le_hammingNorm (f : fo
rall i, γ i -> β i) {x : forall i, γ i} (hf : forall i, f i 0 = 0) : (hammingNor
m fun i => f i (x i))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hammingNorm_smul_le_hammingNorm [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    {x : ∀ i, β i} : hammingNorm (k • x) ≤ hammingNorm x :=
  hammingNorm_comp_le_hammingNorm (fun i (c : β i) => k • c) fun i => by simp_rw [smul_zero]
/-
**hammingNorm_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingNorm_smul [Zero α] [forall i, SMulWithZero α (β i)] {k : α} (hk : f
orall i, IsSMulRegular (β i) k) (x : forall i, β i) : hammingNorm (k • x) = hamm
ingNorm x
参数：β i；hk : forall i, IsSMulRegular (β i) k；x : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hammingNorm_comp`：hammingNorm_comp (f : forall i, γ i -> β i) {x : foral
l i, γ i} (hf₁ : forall i, Injective (f i)) (hf₂ : forall i, f i 0 = 0) : (hammi
ngNorm…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem hammingNorm_smul [Zero α] [∀ i, SMulWithZero α (β i)] {k : α}
    (hk : ∀ i, IsSMulRegular (β i) k) (x : ∀ i, β i) : hammingNorm (k • x) = hammingNorm x :=
  hammingNorm_comp (fun i (c : β i) => k • c) hk fun i => by simp_rw [smul_zero]

end Zero

/-- Corresponds to `dist_eq_norm`. -/
/-
**hammingDist_eq_hammingNorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hammingDist_eq_hammingNorm [forall i, AddGroup (β i)] (x y : forall i, β i
) : hammingDist x y = hammingNorm (-x + y)
参数：β i；x y : forall i, β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Corresponds to `dist_eq_norm`.
-/
theorem hammingDist_eq_hammingNorm [∀ i, AddGroup (β i)] (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (-x + y) := by
  simp_rw [hammingNorm, hammingDist, Pi.add_apply, Pi.neg_apply, ne_eq, neg_add_eq_zero]

end HammingDistNorm

/-! ### The `Hamming` type synonym -/

/-- Type synonym for a Pi type which inherits the usual algebraic instances, but is equipped with
the Hamming metric and norm, instead of `Pi.normedAddCommGroup` which uses the sup norm. -/
/-
**Hamming** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Hamming {ι : Type*} (β : ι -> Type*) : Type _
参数：β : ι -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type synonym for a Pi type which inherits the usual algebraic instances, but is 
equipped with
the Hamming metric and norm, instead of `Pi.normedAddCommGroup` which uses the s
up norm.
-/
def Hamming {ι : Type*} (β : ι → Type*) : Type _ :=
  ∀ i, β i

namespace Hamming

variable {α ι : Type*} {β : ι → Type*}

/-! Instances inherited from normal Pi types. -/

/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Instances inherited from normal Pi types.
-/
instance [∀ i, Inhabited (β i)] : Inhabited (Hamming β) :=
  inferInstanceAs <| Inhabited (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq ι] [Fintype ι] [∀ i, Fintype (β i)] : Fintype (Hamming β) :=
  inferInstanceAs <| Fintype (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited ι] [∀ i, Nonempty (β i)] [Nontrivial (β default)] : Nontrivial (Hamming β) :=
  inferInstanceAs <| Nontrivial (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype ι] [∀ i, DecidableEq (β i)] : DecidableEq (Hamming β) :=
  inferInstanceAs <| DecidableEq (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Zero (β i)] : Zero (Hamming β) :=
  inferInstanceAs <| Zero (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Neg (β i)] : Neg (Hamming β) :=
  inferInstanceAs <| Neg (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Add (β i)] : Add (Hamming β) :=
  inferInstanceAs <| Add (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Sub (β i)] : Sub (Hamming β) :=
  inferInstanceAs <| Sub (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SMul α (β i)] : SMul α (Hamming β) :=
  inferInstanceAs <| SMul α (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] [∀ i, Zero (β i)] [∀ i, SMulWithZero α (β i)] : SMulWithZero α (Hamming β) :=
  inferInstanceAs <| SMulWithZero α (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddMonoid (β i)] : AddMonoid (Hamming β) :=
  inferInstanceAs <| AddMonoid (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddGroup (β i)] : AddGroup (Hamming β) :=
  inferInstanceAs <| AddGroup (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddCommMonoid (β i)] : AddCommMonoid (Hamming β) :=
  inferInstanceAs <| AddCommMonoid (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddCommGroup (β i)] : AddCommGroup (Hamming β) :=
  inferInstanceAs <| AddCommGroup (∀ i, β i)
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α) [Semiring α] (β : ι → Type*) [∀ i, AddCommMonoid (β i)] [∀ i, Module α (β i)] :
    Module α (Hamming β) :=
  inferInstanceAs <| Module α (∀ i, β i)

/-! API to/from the type synonym. -/


/-- `Hamming.toHamming` is the identity function to the `Hamming` of a type. -/
@[match_pattern]
/-
**Hamming.toHamming** 是 Mathlib 中的一个定义，位于命名空间 `Hamming`。
形式化陈述：toHamming : (forall i, β i) ≃ Hamming β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`Hamming.toHamming` is the identity function to the `Hamming` of a type.
-/
def toHamming : (∀ i, β i) ≃ Hamming β :=
  Equiv.refl _

/-- `Hamming.ofHamming` is the identity function from the `Hamming` of a type. -/
@[match_pattern]
/-
**Hamming.ofHamming** 是 Mathlib 中的一个定义，位于命名空间 `Hamming`。
形式化陈述：ofHamming : Hamming β ≃ forall i, β i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`Hamming.ofHamming` is the identity function from the `Hamming` of a type.
-/
def ofHamming : Hamming β ≃ ∀ i, β i :=
  Equiv.refl _

@[simp]
/-
**Hamming.toHamming_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_symm_eq : (@toHamming _ β).symm = ofHamming
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toHamming_symm_eq : (@toHamming _ β).symm = ofHamming :=
  rfl

@[simp]
/-
**Hamming.ofHamming_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_symm_eq : (@ofHamming _ β).symm = toHamming
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofHamming_symm_eq : (@ofHamming _ β).symm = toHamming :=
  rfl

@[simp]
/-
**Hamming.toHamming_ofHamming** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_ofHamming (x : Hamming β) : toHamming (ofHamming x) = x
参数：x : Hamming β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHamming_ofHamming (x : Hamming β) : toHamming (ofHamming x) = x :=
  rfl

@[simp]
/-
**Hamming.ofHamming_toHamming** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_toHamming (x : forall i, β i) : ofHamming (toHamming x) = x
参数：x : forall i, β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHamming_toHamming (x : ∀ i, β i) : ofHamming (toHamming x) = x :=
  rfl
/-
**Hamming.toHamming_inj** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_inj {x y : forall i, β i} : toHamming x = toHamming y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toHamming_inj {x y : ∀ i, β i} : toHamming x = toHamming y ↔ x = y :=
  Iff.rfl
/-
**Hamming.ofHamming_inj** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofHamming_inj {x y : Hamming β} : ofHamming x = ofHamming y ↔ x = y :=
  Iff.rfl

@[simp]
/-
**Hamming.toHamming_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_zero [forall i, Zero (β i)] : toHamming (0 : forall i, β i) = 0
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHamming_zero [∀ i, Zero (β i)] : toHamming (0 : ∀ i, β i) = 0 :=
  rfl

@[simp]
/-
**Hamming.ofHamming_zero** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_zero [forall i, Zero (β i)] : ofHamming (0 : Hamming β) = 0
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHamming_zero [∀ i, Zero (β i)] : ofHamming (0 : Hamming β) = 0 :=
  rfl

@[simp]
/-
**Hamming.toHamming_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_neg [forall i, Neg (β i)] {x : forall i, β i} : toHamming (-x) =
 -toHamming x
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHamming_neg [∀ i, Neg (β i)] {x : ∀ i, β i} : toHamming (-x) = -toHamming x :=
  rfl

@[simp]
/-
**Hamming.ofHamming_neg** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_neg [forall i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -of
Hamming x
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHamming_neg [∀ i, Neg (β i)] {x : Hamming β} : ofHamming (-x) = -ofHamming x :=
  rfl

@[simp]
/-
**Hamming.toHamming_add** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_add [forall i, Add (β i)] {x y : forall i, β i} : toHamming (x +
 y) = toHamming x + toHamming y
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHamming_add [∀ i, Add (β i)] {x y : ∀ i, β i} :
    toHamming (x + y) = toHamming x + toHamming y :=
  rfl

@[simp]
/-
**Hamming.ofHamming_add** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_add [forall i, Add (β i)] {x y : Hamming β} : ofHamming (x + y) 
= ofHamming x + ofHamming y
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHamming_add [∀ i, Add (β i)] {x y : Hamming β} :
    ofHamming (x + y) = ofHamming x + ofHamming y :=
  rfl

@[simp]
/-
**Hamming.toHamming_sub** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_sub [forall i, Sub (β i)] {x y : forall i, β i} : toHamming (x -
 y) = toHamming x - toHamming y
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHamming_sub [∀ i, Sub (β i)] {x y : ∀ i, β i} :
    toHamming (x - y) = toHamming x - toHamming y :=
  rfl

@[simp]
/-
**Hamming.ofHamming_sub** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_sub [forall i, Sub (β i)] {x y : Hamming β} : ofHamming (x - y) 
= ofHamming x - ofHamming y
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHamming_sub [∀ i, Sub (β i)] {x y : Hamming β} :
    ofHamming (x - y) = ofHamming x - ofHamming y :=
  rfl

@[simp]
/-
**Hamming.toHamming_smul** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：toHamming_smul [forall i, SMul α (β i)] {r : α} {x : forall i, β i} : toHa
mming (r • x) = r • toHamming x
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toHamming_smul [∀ i, SMul α (β i)] {r : α} {x : ∀ i, β i} :
    toHamming (r • x) = r • toHamming x :=
  rfl

@[simp]
/-
**Hamming.ofHamming_smul** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：ofHamming_smul [forall i, SMul α (β i)] {r : α} {x : Hamming β} : ofHammin
g (r • x) = r • ofHamming x
参数：β i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHamming_smul [∀ i, SMul α (β i)] {r : α} {x : Hamming β} :
    ofHamming (r • x) = r • ofHamming x :=
  rfl

section

/-! Instances equipping `Hamming` with `hammingNorm` and `hammingDist`. -/

variable [Fintype ι] [∀ i, DecidableEq (β i)]

/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Dist (Hamming β) :=
  ⟨fun x y => hammingDist (ofHamming x) (ofHamming y)⟩

@[simp, push_cast]
/-
**Hamming.dist_eq_hammingDist** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：dist_eq_hammingDist (x y : Hamming β) : dist x y = hammingDist (ofHamming 
x) (ofHamming y)
参数：x y : Hamming β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dist_eq_hammingDist (x y : Hamming β) :
    dist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PseudoMetricSpace (Hamming β) where
  dist_self := by
    push_cast
    exact mod_cast hammingDist_self
  dist_comm := by
    push_cast
    exact mod_cast hammingDist_comm
  dist_triangle := by
    push_cast
    exact mod_cast hammingDist_triangle
  toUniformSpace := ⊥
  uniformity_dist := uniformity_dist_of_mem_uniformity _ _ fun s => by
    push_cast
    constructor
    · refine fun hs ↦ ⟨1, zero_lt_one, fun hab ↦ hs <| by simpa using hab⟩
    · rintro ⟨_, hε, hs⟩ ⟨_, _⟩ rfl
      refine hs (lt_of_eq_of_lt ?_ hε)
      exact mod_cast hammingDist_self _
  toBornology := ⟨⊥, bot_le⟩
  cobounded_sets := by
    ext
    push_cast
    refine iff_of_true (Filter.mem_sets.mpr Filter.mem_bot) ⟨Fintype.card ι, fun _ _ _ _ => ?_⟩
    exact mod_cast hammingDist_le_card_fintype

@[simp, push_cast]
/-
**Hamming.nndist_eq_hammingDist** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：nndist_eq_hammingDist (x y : Hamming β) : nndist x y = hammingDist (ofHamm
ing x) (ofHamming y)
参数：x y : Hamming β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nndist_eq_hammingDist (x y : Hamming β) :
    nndist x y = hammingDist (ofHamming x) (ofHamming y) :=
  rfl
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DiscreteTopology (Hamming β) := ⟨rfl⟩
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MetricSpace (Hamming β) := .ofT0PseudoMetricSpace _
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Zero (β i)] : Norm (Hamming β) :=
  ⟨fun x => hammingNorm (ofHamming x)⟩

@[simp, push_cast]
/-
**Hamming.norm_eq_hammingNorm** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：norm_eq_hammingNorm [forall i, Zero (β i)] (x : Hamming β) : ‖x‖ = hamming
Norm (ofHamming x)
参数：β i；x : Hamming β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem norm_eq_hammingNorm [∀ i, Zero (β i)] (x : Hamming β) : ‖x‖ = hammingNorm (ofHamming x) :=
  rfl
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddGroup (β i)] : NormedAddGroup (Hamming β) where
  dist_eq := by push_cast; exact mod_cast hammingDist_eq_hammingNorm
/-
**Hamming.** 是 Mathlib 中的一个实例，位于命名空间 `Hamming`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddCommGroup (β i)] : NormedAddCommGroup (Hamming β) where
  dist_eq := fun x y => NormedAddGroup.dist_eq x y

@[simp, push_cast]
/-
**Hamming.nnnorm_eq_hammingNorm** 是 Mathlib 中的一个定理，位于命名空间 `Hamming`。
形式化陈述：nnnorm_eq_hammingNorm [forall i, AddGroup (β i)] (x : Hamming β) : ‖x‖₊ = 
hammingNorm (ofHamming x)
参数：β i；x : Hamming β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nnnorm_eq_hammingNorm [∀ i, AddGroup (β i)] (x : Hamming β) :
    ‖x‖₊ = hammingNorm (ofHamming x) := rfl

end

end Hamming

