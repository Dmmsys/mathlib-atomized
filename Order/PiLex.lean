/-
Copyright (c) 2019 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Order.Lex
public import Mathlib.Order.WellFounded
public import Mathlib.Tactic.Common

/-!
# Lexicographic order on Pi types

This file defines the lexicographic and colexicographic orders for Pi types.

* In the lexicographic order, `a` is less than `b` if `a i = b i` for all `i` up to some point
  `k`, and `a k < b k`.
* In the colexicographic order, `a` is less than `b` if `a i = b i` for all `i` above some point
  `k`, and `a k < b k`.

## Notation

* `Πₗ i, α i`: Pi type equipped with the lexicographic order. Type synonym of `Π i, α i`.

## See also

Related files are:
* `Data.Finset.Colex`: Colexicographic order on finite sets.
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Sigma.Order`: Lexicographic order on `Σₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σₗ' i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.
-/

@[expose] public section

assert_not_exists Monoid

variable {ι : Type*} {β : ι → Type*} (r : ι → ι → Prop) (s : ∀ {i}, β i → β i → Prop)

namespace Pi

/-- The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
and each `β i` is ordered by `s`.

The `<` relation on `Lex (∀ i, β i)` is `Pi.Lex (· < ·) (· < ·)`, while the `<` relation on
`Colex (∀ i, β i)` is `Pi.Lex (· > ·) (· < ·)`. -/
/-
**Pi.Lex** 是 Mathlib 中的一个定义，位于命名空间 `Pi`。
形式化陈述：{ι : Type u_1} →   {β : ι → Type u_2} → (ι → ι → Prop) → ({i : ι} → β i → 
β i → Prop) → ((i : ι) → β i) → ((i : ι) → β i) → Prop
参数：ι → ι → Prop；{i : ι} → β i → β i → Prop；(i : ι) → β i；(i : ι) → β i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographic relation on `Π i : ι, β i`, where `ι` is ordered by `r`,
and each `β i` is ordered by `s`.

The `<` relation on `Lex (∀ i, β i)` is `Pi.Lex (· < ·) (· < ·)`, while the `<` 
relation on
`Colex (∀ i, β i)` is `Pi.Lex (· > ·) (· < ·)`.
-/
protected def Lex (x y : ∀ i, β i) : Prop :=
  ∃ i, (∀ j, r j i → x j = y j) ∧ s (x i) (y i)

/- This unfortunately results in a type that isn't delta-reduced, so we keep the notation out of the
basic API, just in case -/
/-- The notation `Πₗ i, α i` refers to a pi type equipped with the lexicographic order. -/
notation3 (prettyPrint := false) "Πₗ " (...) ", " r:(scoped p => Lex (∀ i, p i)) => r

/-
**Pi.lex_lt_of_lt_of_preorder** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lex_lt_of_lt_of_preorder [forall i, Preorder (β i)] {r} (hwf : WellFounded
 r) {x y : forall i, β i} (hlt : x < y) : exists i, (forall j, r j i -> x j <= y
 j ∧ y j <= x j) ∧ x i < y i
参数：β i；hwf : WellFounded r；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用引理 `lt_of_le_not_ge`：lt_of_le_not_ge (hab : a <= b) (hba : ¬ b <= a) : a < b
-/
theorem lex_lt_of_lt_of_preorder [∀ i, Preorder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : ∃ i, (∀ j, r j i → x j ≤ y j ∧ y j ≤ x j) ∧ x i < y i :=
  let h' := Pi.lt_def.1 hlt
  let ⟨i, hi, hl⟩ := hwf.has_min {i | x i < y i} h'.2
  ⟨i, fun j hj => ⟨h'.1 j, not_not.1 fun h => hl j (lt_of_le_not_ge (h'.1 j) h) hj⟩, hi⟩
/-
**Pi.lex_lt_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lex_lt_of_lt [forall i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y
 : forall i, β i} (hlt : x < y) : Pi.Lex r (· < ·) x y
参数：β i；hwf : WellFounded r；hlt : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Pi.lex_lt_of_lt_of_preorder`：lex_lt_of_lt_of_preorder [forall i, Preorde
r (β i)] {r} (hwf : WellFounded r) {x y : forall i, β i} (hlt : x < y) : exists 
i, (forall j, r j…
-/
theorem lex_lt_of_lt [∀ i, PartialOrder (β i)] {r} (hwf : WellFounded r) {x y : ∀ i, β i}
    (hlt : x < y) : Pi.Lex r (· < ·) x y := by
  simp_rw [Pi.Lex, le_antisymm_iff]
  exact lex_lt_of_lt_of_preorder hwf hlt
/-
**Pi.lex_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lex_iff_of_unique [Unique ι] [forall i, LT (β i)] {r} [Std.Irrefl r] {x y 
: forall i, β i} : Pi.Lex r (· < ·) x y ↔ x default < y default
参数：β i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lex_iff_of_unique [Unique ι] [∀ i, LT (β i)] {r} [Std.Irrefl r] {x y : ∀ i, β i} :
    Pi.Lex r (· < ·) x y ↔ x default < y default := by
  simp [Pi.Lex, Unique.forall_iff, Unique.exists_iff, irrefl]
/-
**Pi.trichotomous_lex** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：trichotomous_lex [forall i, Std.Trichotomous (α
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `Std.Trichotomous.trichotomous`：∀ {α : Sort u} {r : α → α → Prop} [self :
 Std.Trichotomous r] (a b : α), ¬r a b → ¬r b a → a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
-/
theorem trichotomous_lex [∀ i, Std.Trichotomous (α := β i) s] (wf : WellFounded r) :
    Std.Trichotomous (Pi.Lex r @s) :=
  { trichotomous a b hab hba := by
      by_contra! h
      rw [Function.ne_iff] at h
      let i := wf.min {i | a i ≠ b i} h
      have hri j (hr : r j i) : a j = b j := not_not.mp (fun h => wf.not_lt_min _ (by grind) hr)
      have := Std.Trichotomous.trichotomous (a i) (b i) (hab ⟨i, hri, ·⟩)
      exact hba ⟨i, (hri · · |>.symm), Not.imp_symm this <| wf.min_mem {i | a i ≠ b i} h⟩ }

@[deprecated (since := "2026-01-24")] alias isTrichotomous_lex := trichotomous_lex

/-
These instances are leaky, because they define the relation on `∀ i, β i` instead of
`Lex (∀ i, β i)`/`Colex (∀ i, β i)`. So, we would like to mark them `@[semireducible]`.
But the linter doesn't allow this, so we wrap them in `id` instead.
-/
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
These instances are leaky, because they define the relation on `∀ i, β i` instea
d of
`Lex (∀ i, β i)`/`Colex (∀ i, β i)`. So, we would like to mark them `@[semireduc
ible]`.
But the linter doesn't allow this, so we wrap them in `id` instead.
-/
instance [LT ι] [∀ a, LT (β a)] : LT (Lex (∀ i, β i)) :=
  id ⟨Pi.Lex (· < ·) (· < ·)⟩
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LT ι] [∀ a, LT (β a)] : LT (Colex (∀ i, β i)) :=
  id ⟨Pi.Lex (· > ·) (· < ·)⟩

-- If `Lex` and `Colex` are ever made into one-field structures, we need a `CoeFun` instance.
-- This will make `x i` syntactically equal to `ofLex x i` for `x : Πₗ i, α i`, thus making
-- the following theorems redundant.
/-
**Pi.toLex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} (x : (i : ι) → β i) (i : ι), toLex x i
 = x i
参数：x : (i : ι) → β i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toLex_apply (x : ∀ i, β i) (i : ι) : toLex x i = x i := rfl
/-
**Pi.ofLex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} (x : Lex ((i : ι) → β i)) (i : ι), ofL
ex x i = x i
参数：x : Lex ((i : ι) → β i)；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofLex_apply (x : Lex (∀ i, β i)) (i : ι) : ofLex x i = x i := rfl
/-
**Pi.toColex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} (x : (i : ι) → β i) (i : ι), toColex x
 i = x i
参数：x : (i : ι) → β i；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toColex_apply (x : ∀ i, β i) (i : ι) : toColex x i = x i := rfl
/-
**Pi.ofColex_apply** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} (x : Colex ((i : ι) → β i)) (i : ι), o
fColex x i = x i
参数：x : Colex ((i : ι) → β i)；i : ι。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ofColex_apply (x : Colex (∀ i, β i)) (i : ι) : ofColex x i = x i := rfl
/-
**Pi.Lex.lt_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : Unique ι] [inst_1 : (i : ι) → 
LT (β i)] [inst_2 : Preorder ι]   {x y : Lex ((i : ι) → β i)}, x < y ↔ x default
 < y default
参数：i : ι；β i；(i : ι) → β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lex_iff_of_unique`：lex_iff_of_unique [Unique ι] [forall i, LT (β i)] 
{r} [Std.Irrefl r] {x y : forall i, β i} : Pi.Lex r (· < ·) x y ↔ x default < y 
default
-/
theorem Lex.lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Lex (∀ i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique
/-
**Pi.Colex.lt_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : Unique ι] [inst_1 : (i : ι) → 
LT (β i)] [inst_2 : Preorder ι]   {x y : Colex ((i : ι) → β i)}, x < y ↔ x defau
lt < y default
参数：i : ι；β i；(i : ι) → β i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lex_iff_of_unique`：lex_iff_of_unique [Unique ι] [forall i, LT (β i)] 
{r} [Std.Irrefl r] {x y : forall i, β i} : Pi.Lex r (· < ·) x y ↔ x default < y 
default
· 使用定理 `instIrreflGt`：∀ {α : Type u} [inst : Preorder α], Std.Irrefl fun x1 x2 =
> x2 < x1
-/
theorem Colex.lt_iff_of_unique [Unique ι] [∀ i, LT (β i)] [Preorder ι] {x y : Colex (∀ i, β i)} :
    x < y ↔ x default < y default :=
  lex_iff_of_unique
/-
**Pi.Lex.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (a : 
ι) → PartialOrder (β a)],   IsStrictOrder (Lex ((i : ι) → β i)) fun x1 x2 => x1 
< x2
参数：a : ι；β a；Lex ((i : ι) → β i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance Lex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Lex (∀ i, β i)) (· < ·) where
  irrefl := fun a ⟨k, _, hk₂⟩ => lt_irrefl (a k) hk₂
  trans := by
    rintro a b c ⟨N₁, lt_N₁, a_lt_b⟩ ⟨N₂, lt_N₂, b_lt_c⟩
    rcases lt_trichotomy N₁ N₂ with (H | rfl | H)
    exacts [⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ <| hj.trans H), lt_N₂ _ H ▸ a_lt_b⟩,
      ⟨N₁, fun j hj => (lt_N₁ _ hj).trans (lt_N₂ _ hj), a_lt_b.trans b_lt_c⟩,
      ⟨N₂, fun j hj => (lt_N₁ _ (hj.trans H)).trans (lt_N₂ _ hj), (lt_N₁ _ H).symm ▸ b_lt_c⟩]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.Colex.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : LinearOrder ι] [inst_1 : (a : 
ι) → PartialOrder (β a)],   IsStrictOrder (Colex ((i : ι) → β i)) fun x1 x2 => x
1 < x2
参数：a : ι；β a；Colex ((i : ι) → β i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.isStrictOrder`：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : Linear
Order ι] [inst_1 : (a : ι) → PartialOrder (β a)],   IsStrictOrder (Lex ((i : ι) 
→ β i)) fu…
-/
instance Colex.isStrictOrder [LinearOrder ι] [∀ a, PartialOrder (β a)] :
    IsStrictOrder (Colex (∀ i, β i)) (· < ·) :=
  Lex.isStrictOrder (ι := ιᵒᵈ)
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Lex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [∀ a, PartialOrder (β a)] : PartialOrder (Colex (∀ i, β i)) :=
  partialOrderOfSO (· < ·)

/-- `Lex (∀ i, α i)` is a linear order if the original order has well-founded `<`. -/
/-
**Pi.Lex.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Pi.Lex`。
形式化陈述：{ι : Type u_1} →   {β : ι → Type u_2} →     [inst : LinearOrder ι] → [Well
FoundedLT ι] → [(a : ι) → LinearOrder (β a)] → LinearOrder (Lex ((i : ι) → β i))
参数：a : ι；β a；Lex ((i : ι) → β i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Lex (∀ i, α i)` is a linear order if the original order has well-founded `<`.
-/
noncomputable instance Lex.linearOrder [LinearOrder ι] [WellFoundedLT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Lex (∀ i, β i)) :=
  @linearOrderOfSTO (Πₗ i, β i) (· < ·)
    { trichotomous := (trichotomous_lex _ _ IsWellFounded.wf).1 } (Classical.decRel _)

set_option backward.isDefEq.respectTransparency.types false in
/-- `Colex (∀ i, α i)` is a linear order if the original order has well-founded `>`. -/
/-
**Pi.Colex.linearOrder** 是 Mathlib 中的一个定义，位于命名空间 `Pi.Colex`。
形式化陈述：{ι : Type u_1} →   {β : ι → Type u_2} →     [inst : LinearOrder ι] → [Well
FoundedGT ι] → [(a : ι) → LinearOrder (β a)] → LinearOrder (Colex ((i : ι) → β i
))
参数：a : ι；β a；Colex ((i : ι) → β i)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Colex (∀ i, α i)` is a linear order if the original order has well-founded `>`.
-/
noncomputable instance Colex.linearOrder [LinearOrder ι] [WellFoundedGT ι]
    [∀ a, LinearOrder (β a)] : LinearOrder (Colex (∀ i, β i)) :=
  Lex.linearOrder (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.lex_le_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lex_le_iff_of_unique [Unique ι] [LinearOrder ι] [forall i, PartialOrder (β
 i)] {x y : Lex (forall i, β i)} : x <= y ↔ x default <= y default
参数：β i；forall i, β i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem lex_le_iff_of_unique [Unique ι] [LinearOrder ι] [∀ i, PartialOrder (β i)]
    {x y : Lex (∀ i, β i)} : x ≤ y ↔ x default ≤ y default := by
  simp_rw [le_iff_lt_or_eq, Pi.Lex.lt_iff_of_unique, ← ofLex_inj, funext_iff, Unique.forall_iff,
    ofLex_apply]

set_option backward.isDefEq.respectTransparency false in
/-
**Pi.colex_le_iff_of_unique** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：colex_le_iff_of_unique [Unique ι] [LinearOrder ι] [forall i, PartialOrder 
(β i)] {x y : Colex (forall i, β i)} : x <= y ↔ x default <= y default
参数：β i；forall i, β i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem colex_le_iff_of_unique [Unique ι] [LinearOrder ι] [∀ i, PartialOrder (β i)]
    {x y : Colex (∀ i, β i)} : x ≤ y ↔ x default ≤ y default := by
  simp_rw [le_iff_lt_or_eq, Pi.Colex.lt_iff_of_unique, ← ofColex_inj, funext_iff, Unique.forall_iff,
    ofColex_apply]

section PartialOrder
variable [LinearOrder ι] {x : ∀ i, β i} {i : ι} {a : β i} [∀ i, PartialOrder (β i)]

open Function

section Lex
variable [WellFoundedLT ι]

/-
**Pi.toLex_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toLex_monotone : Monotone (@toLex (forall i, β i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
-/
theorem toLex_monotone : Monotone (@toLex (∀ i, β i)) := fun a b h =>
  or_iff_not_imp_left.2 fun hne =>
    let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i ≠ b i }
      (Function.ne_iff.1 hne)
    ⟨i, fun j hj => by
      contrapose! hl
      exact ⟨j, hl, hj⟩, (h i).lt_of_ne hi⟩
/-
**Pi.toLex_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toLex_strictMono : StrictMono (@toLex (forall i, β i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFounded.has_min`：∀ {α : Type u_4} {r : α → α → Prop}, WellFounded r 
→ ∀ (s : Set α), s.Nonempty → ∃ a ∈ s, ∀ x ∈ s, ¬r x a
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.ne_iff`：ne_iff {β : α -> Sort*} {f₁ f₂ : forall a, β a} : f₁ !=
 f₂ ↔ exists a, f₁ a != f₂ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem toLex_strictMono : StrictMono (@toLex (∀ i, β i)) := fun a b h =>
  let ⟨i, hi, hl⟩ := IsWellFounded.wf.has_min (r := (· < ·)) { i | a i ≠ b i }
    (Function.ne_iff.1 h.ne)
  ⟨i, fun j hj => by
    contrapose! hl
    exact ⟨j, hl, hj⟩, (h.le i).lt_of_ne hi⟩

@[simp]
/-
**Pi.lt_toLex_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lt_toLex_update_self_iff : toLex x < toLex (update x i a) ↔ x i < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Pi.toLex_strictMono`：toLex_strictMono : StrictMono (@toLex (forall i, β 
i))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_update_self_iff`：lt_update_self_iff : x < update x i a ↔ x i < a
-/
theorem lt_toLex_update_self_iff : toLex x < toLex (update x i a) ↔ x i < a := by
  refine ⟨?_, fun h => toLex_strictMono <| lt_update_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

@[simp]
/-
**Pi.toLex_update_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toLex_update_lt_self_iff : toLex (update x i a) < toLex x ↔ a < x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.false`：∀ {α : Type u_2} [inst : Preorder α] {a : α}, a < a → False
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Pi.toLex_strictMono`：toLex_strictMono : StrictMono (@toLex (forall i, β 
i))
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `update_lt_self_iff`：∀ {ι : Type u_1} {π : ι → Type u_4} [inst : Decidabl
eEq ι] [inst_1 : (i : ι) → Preorder (π i)] {x : (i : ι) → π i}   {i : ι} {a : π 
i}, Func…
-/
theorem toLex_update_lt_self_iff : toLex (update x i a) < toLex x ↔ a < x i := by
  refine ⟨?_, fun h => toLex_strictMono <| update_lt_self_iff.2 h⟩
  rintro ⟨j, hj, h⟩
  dsimp at h
  obtain rfl : j = i := by
    by_contra H
    rw [update_of_ne H] at h
    exact h.false
  rwa [update_self] at h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Pi.le_toLex_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：le_toLex_update_self_iff : toLex x <= toLex (update x i a) ↔ x i <= a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_toLex_update_self_iff : toLex x ≤ toLex (update x i a) ↔ x i ≤ a := by
  simp_rw [le_iff_lt_or_eq, lt_toLex_update_self_iff, toLex_inj, eq_update_self_iff]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Pi.toLex_update_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toLex_update_le_self_iff : toLex (update x i a) <= toLex x ↔ a <= x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem toLex_update_le_self_iff : toLex (update x i a) ≤ toLex x ↔ a ≤ x i := by
  simp_rw [le_iff_lt_or_eq, toLex_update_lt_self_iff, toLex_inj, update_eq_self_iff]

end Lex

section Colex
variable [WellFoundedGT ι]

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.toColex_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toColex_monotone : Monotone (@toColex (forall i, β i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.toLex_monotone`：toLex_monotone : Monotone (@toLex (forall i, β i))
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem toColex_monotone : Monotone (@toColex (∀ i, β i)) :=
  toLex_monotone (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.toColex_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toColex_strictMono : StrictMono (@toColex (forall i, β i))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.toLex_strictMono`：toLex_strictMono : StrictMono (@toLex (forall i, β 
i))
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem toColex_strictMono : StrictMono (@toColex (∀ i, β i)) :=
  toLex_strictMono (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Pi.lt_toColex_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lt_toColex_update_self_iff : toColex x < toColex (update x i a) ↔ x i < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.lt_toLex_update_self_iff`：lt_toLex_update_self_iff : toLex x < toLex 
(update x i a) ↔ x i < a
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem lt_toColex_update_self_iff : toColex x < toColex (update x i a) ↔ x i < a :=
  lt_toLex_update_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Pi.toColex_update_lt_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toColex_update_lt_self_iff : toColex (update x i a) < toColex x ↔ a < x i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.toLex_update_lt_self_iff`：toLex_update_lt_self_iff : toLex (update x 
i a) < toLex x ↔ a < x i
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem toColex_update_lt_self_iff : toColex (update x i a) < toColex x ↔ a < x i :=
  toLex_update_lt_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Pi.le_toColex_update_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：le_toColex_update_self_iff : toColex x <= toColex (update x i a) ↔ x i <= 
a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.le_toLex_update_self_iff`：le_toLex_update_self_iff : toLex x <= toLex
 (update x i a) ↔ x i <= a
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem le_toColex_update_self_iff : toColex x ≤ toColex (update x i a) ↔ x i ≤ a :=
  le_toLex_update_self_iff (ι := ιᵒᵈ)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Pi.toColex_update_le_self_iff** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：toColex_update_le_self_iff : toColex (update x i a) <= toColex x ↔ a <= x 
i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.toLex_update_le_self_iff`：toLex_update_le_self_iff : toLex (update x 
i a) <= toLex x ↔ a <= x i
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_lt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedLT α],
 IsWellOrder α fun x1 x2 => x1 < x2
· 使用定理 `instWellFoundedLTOrderDualOfWellFoundedGT`：∀ (α : Type u_1) [inst : LT α
] [h : WellFoundedGT α], WellFoundedLT αᵒᵈ
-/
theorem toColex_update_le_self_iff : toColex (update x i a) ≤ toColex x ↔ a ≤ x i :=
  toLex_update_le_self_iff (ι := ιᵒᵈ)

end Colex

end PartialOrder

section LinearOrder
variable [LinearOrder ι] {x y : ∀ i, β i} {i : ι} {a : β i} [∀ i, LinearOrder (β i)]

section Lex

/-
**Pi.apply_le_of_toLex** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：apply_le_of_toLex (hxy : toLex x <= toLex y) (h : forall j < i, x j = y j)
 : x i <= y i
参数：hxy : toLex x <= toLex y；h : forall j < i, x j = y j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem apply_le_of_toLex (hxy : toLex x ≤ toLex y) (h : ∀ j < i, x j = y j) : x i ≤ y i := by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

end Lex

section Colex

/-
**Pi.apply_le_of_toColex** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：apply_le_of_toColex (hxy : toColex x <= toColex y) (h : forall j > i, x j 
= y j) : x i <= y i
参数：hxy : toColex x <= toColex y；h : forall j > i, x j = y j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_le_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem apply_le_of_toColex (hxy : toColex x ≤ toColex y) (h : ∀ j > i, x j = y j) : x i ≤ y i := by
  contrapose! hxy
  apply not_le_of_gt
  use i
  aesop

end Colex

end LinearOrder

/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Lex (∀ a, β a)) where
  bot := toLex ⊥
  bot_le _ := toLex_monotone bot_le
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderBot (β a)] :
    OrderBot (Colex (∀ a, β a)) where
  bot := toColex ⊥
  bot_le _ := toColex_monotone bot_le
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Lex (∀ a, β a)) where
  top := toLex ⊤
  le_top _ := toLex_monotone le_top
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)] [∀ a, OrderTop (β a)] :
    OrderTop (Colex (∀ a, β a)) where
  top := toColex ⊤
  le_top _ := toColex_monotone le_top
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedLT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Lex (∀ a, β a)) where
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedGT ι] [∀ a, PartialOrder (β a)]
    [∀ a, BoundedOrder (β a)] : BoundedOrder (Colex (∀ a, β a)) where

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder ι] [∀ i, LT (β i)] [∀ i, DenselyOrdered (β i)] :
    DenselyOrdered (Lex (∀ i, β i)) :=
  ⟨by
    rintro _ a₂ ⟨i, h, hi⟩
    obtain ⟨a, ha₁, ha₂⟩ := exists_between hi
    classical
      refine ⟨Function.update a₂ _ a, ⟨i, fun j hj => ?_, ?_⟩, i, fun j hj => ?_, ?_⟩
      · rw [h j hj]
        dsimp only at hj
        rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i a]
      · rw [Function.update_of_ne hj.ne a]
      · rwa [Function.update_self i a]⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder ι] [∀ i, LT (β i)] [∀ i, DenselyOrdered (β i)] :
    DenselyOrdered (Colex (∀ i, β i)) :=
  inferInstanceAs (DenselyOrdered (Lex (∀ i : ιᵒᵈ, β (OrderDual.toDual i))))

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.Lex.noMaxOrder'** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Lex`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : Preorder ι] [inst_1 : (i : ι) 
→ LT (β i)] (i : ι) [NoMaxOrder (β i)],   NoMaxOrder (Lex ((i : ι) → β i))
参数：i : ι；β i；i : ι；β i；Lex ((i : ι) → β i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
-/
theorem Lex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Lex (∀ i, β i)) :=
  ⟨fun a => by
    let ⟨b, hb⟩ := exists_gt (a i)
    classical
    exact ⟨Function.update a i b, i, fun j hj =>
      (Function.update_of_ne hj.ne b a).symm, by rwa [Function.update_self i b]⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.Colex.noMaxOrder'** 是 Mathlib 中的一个定理，位于命名空间 `Pi.Colex`。
形式化陈述：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : Preorder ι] [inst_1 : (i : ι) 
→ LT (β i)] (i : ι) [NoMaxOrder (β i)],   NoMaxOrder (Colex ((i : ι) → β i))
参数：i : ι；β i；i : ι；β i；Colex ((i : ι) → β i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Pi.Lex.noMaxOrder'`：∀ {ι : Type u_1} {β : ι → Type u_2} [inst : Preorder
 ι] [inst_1 : (i : ι) → LT (β i)] (i : ι) [NoMaxOrder (β i)],   NoMaxOrder (Lex 
((i : ι)…
-/
theorem Colex.noMaxOrder' [Preorder ι] [∀ i, LT (β i)] (i : ι) [NoMaxOrder (β i)] :
    NoMaxOrder (Colex (∀ i, β i)) :=
  Lex.noMaxOrder' (ι := ιᵒᵈ) i
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Lex (∀ i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_gt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMaxOrder (β i)] : NoMaxOrder (Colex (∀ i, β i)) :=
  inferInstanceAs (NoMaxOrder (Lex (∀ i : ιᵒᵈ, β (OrderDual.toDual i))))
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedLT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Lex (∀ i, β i)) :=
  ⟨fun a =>
    let ⟨_, hb⟩ := exists_lt (ofLex a)
    ⟨_, toLex_strictMono hb⟩⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**Pi.** 是 Mathlib 中的一个实例，位于命名空间 `Pi`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [LinearOrder ι] [WellFoundedGT ι] [Nonempty ι] [∀ i, PartialOrder (β i)]
    [∀ i, NoMinOrder (β i)] : NoMinOrder (Colex (∀ i, β i)) :=
  inferInstanceAs (NoMinOrder (Lex (∀ i : ιᵒᵈ, β (OrderDual.toDual i))))

/-- If we swap two strictly decreasing values in a function, then the result is lexicographically
smaller than the original function. -/
/-
**Pi.lex_desc** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (h
₁ : i <= j) (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f
参数：h₁ : i <= j；h₂ : f j < f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b

--- 原说明 ---
If we swap two strictly decreasing values in a function, then the result is lexi
cographically
smaller than the original function.
-/
theorem lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex f :=
  ⟨i, fun _ hik => congr_arg f (Equiv.swap_apply_of_ne_of_ne hik.ne (hik.trans_le h₁).ne), by
    simpa only [Pi.toLex_apply, Function.comp_apply, Equiv.swap_apply_left] using h₂⟩

/-- If we swap two strictly increasing values in a function, then the result is colexicographically
smaller than the original function. -/
/-
**Pi.colex_asc** 是 Mathlib 中的一个定理，位于命名空间 `Pi`。
形式化陈述：colex_asc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> α} {i j : ι} (
h₁ : i <= j) (h₂ : f i < f j) : toColex (f ∘ Equiv.swap i j) < toColex f
参数：h₁ : i <= j；h₂ : f i < f j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.swap_comm`：swap_comm (a b : α) : swap a b = swap b a
· 使用定理 `Pi.lex_desc`：lex_desc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι -> 
α} {i j : ι} (h₁ : i <= j) (h₂ : f j < f i) : toLex (f ∘ Equiv.swap i j) < toLex
 …

--- 原说明 ---
If we swap two strictly increasing values in a function, then the result is cole
xicographically
smaller than the original function.
-/
theorem colex_asc {α} [Preorder ι] [DecidableEq ι] [LT α] {f : ι → α} {i j : ι} (h₁ : i ≤ j)
    (h₂ : f i < f j) : toColex (f ∘ Equiv.swap i j) < toColex f := by
  rw [Equiv.swap_comm]
  exact lex_desc (ι := ιᵒᵈ) h₁ h₂

end Pi

