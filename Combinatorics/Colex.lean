/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Alena Gusakov, Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Ring.GeomSum
public import Mathlib.Data.Finset.Slice
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Order.SupClosed
public import Mathlib.Order.UpperLower.Closure

/-!
# Colexicographic order

We define the colex order for finite sets, and give a couple of important lemmas and properties
relating to it.

The colex ordering likes to avoid large values: If the biggest element of `t` is bigger than all
elements of `s`, then `s < t`.

In the special case of `ℕ`, it can be thought of as the "binary" ordering. That is, order `s` based
on $∑_{i ∈ s} 2^i$. It's defined here on `Finset α` for any linear order `α`.

In the context of the Kruskal-Katona theorem, we are interested in how colex behaves for sets of a
fixed size. For example, for size 3, the colex order on ℕ starts
`012, 013, 023, 123, 014, 024, 124, 034, 134, 234, ...`

## Main statements

* Colex order properties - linearity, decidability and so on.
* `Finset.Colex.forall_lt_mono`: if `s < t` in colex, and everything in `t` is `< a`, then
  everything in `s` is `< a`. This confirms the idea that an enumeration under colex will exhaust
  all sets using elements `< a` before allowing `a` to be included.
* `Finset.toColex_image_le_toColex_image`: Strictly monotone functions preserve colex.
* `Finset.geomSum_le_geomSum_iff_toColex_le_toColex`: Colex for α = ℕ is the same as binary.
  This also proves binary expansions are unique.

## See also

Related files are:
* `Data.List.Lex`: Lexicographic order on lists.
* `Data.Pi.Lex`: Lexicographic order on `Πₗ i, α i`.
* `Data.PSigma.Order`: Lexicographic order on `Σ' i, α i`.
* `Data.Sigma.Order`: Lexicographic order on `Σ i, α i`.
* `Data.Prod.Lex`: Lexicographic order on `α × β`.

## TODO

* Generalise `Colex.initSeg` so that it applies to `ℕ`.

## References

* https://github.com/b-mehta/maths-notes/blob/master/iii/mich/combinatorics.pdf

## Tags

colex, colexicographic, binary
-/

@[expose] public section

open Function

variable {α β : Type*}

namespace Finset

open Colex

namespace Colex
section PartialOrder
variable [PartialOrder α] [PartialOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α}

/-
**Finset.Colex.instLE** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instLE : LE (Colex (Finset α)) where le s t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE : LE (Colex (Finset α)) where
  le s t := ∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b

-- TODO: This lemma is weirdly useful given how strange its statement is.
-- Is there a nicer statement? Should this lemma be made public?
/-
**Finset.Colex.trans_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma trans_aux (hst : toColex s ≤ toColex t) (htu : toColex t ≤ toColex u)
    (has : a ∈ s) (hat : a ∉ t) : ∃ b, b ∈ u ∧ b ∉ s ∧ a ≤ b := by
  classical
  let s' : Finset α := {b ∈ s | b ∉ t ∧ a ≤ b}
  have ⟨b, hb, hbmax⟩ := s'.exists_maximal ⟨a, by simp [s', has, hat]⟩
  simp only [s', mem_filter, and_imp] at hb hbmax
  have ⟨c, hct, hcs, hbc⟩ := hst hb.1 hb.2.1
  by_cases hcu : c ∈ u
  · exact ⟨c, hcu, hcs, hb.2.2.trans hbc⟩
  have ⟨d, hdu, hdt, hcd⟩ := htu hct hcu
  have had : a ≤ d := hb.2.2.trans <| hbc.trans hcd
  refine ⟨d, hdu, fun hds ↦ not_lt_iff_le_imp_ge.2 (hbmax hds hdt had) ?_, had⟩
  exact hbc.trans_lt <| hcd.lt_of_ne <| ne_of_mem_of_not_mem hct hdt

set_option backward.privateInPublic true in
/-
**Finset.Colex.antisymm_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma antisymm_aux (hst : toColex s ≤ toColex t) (hts : toColex t ≤ toColex s) : s ⊆ t := by
  intro a has
  by_contra hat
  have ⟨_b, hb₁, hb₂, _⟩ := trans_aux hst hts has hat
  exact hb₂ hb₁

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.Colex.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instPartialOrder : PartialOrder (Colex (Finset α)) where le_refl _ _ ha ha
'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder : PartialOrder (Colex (Finset α)) where
  le_refl _ _ ha ha' := (ha' ha).elim
  le_antisymm _ _ hst hts := (antisymm_aux hst hts).antisymm (antisymm_aux hts hst)
  le_trans s t u hst htu a has hau := by
    by_cases hat : a ∈ ofColex t
    · have ⟨b, hbu, hbt, hab⟩ := htu hat hau
      by_cases hbs : b ∈ ofColex s
      · have ⟨c, hcu, hcs, hbc⟩ := trans_aux hst htu hbs hbt
        exact ⟨c, hcu, hcs, hab.trans hbc⟩
      · exact ⟨b, hbu, hbs, hab⟩
    · exact trans_aux hst htu has hat
/-
**Finset.Colex.le_def** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：le_def {s t : Colex (Finset α)} : s <= t ↔ forall ⦃a⦄, a in ofColex s -> a
 ∉ ofColex t -> exists b, b in ofColex t ∧ b ∉ ofColex s ∧ a <= b
参数：Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def {s t : Colex (Finset α)} :
    s ≤ t ↔ ∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b :=
  Iff.rfl
/-
**Finset.Colex.toColex_le_toColex** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：toColex_le_toColex : toColex s <= toColex t ↔ forall ⦃a⦄, a in s -> a ∉ t 
-> exists b, b in t ∧ b ∉ s ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toColex_le_toColex :
    toColex s ≤ toColex t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := Iff.rfl
/-
**Finset.Colex.toColex_lt_toColex** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：toColex_lt_toColex : toColex s < toColex t ↔ s != t ∧ forall ⦃a⦄, a in s -
> a ∉ t -> exists b, b in t ∧ b ∉ s ∧ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toColex_lt_toColex :
    toColex s < toColex t ↔ s ≠ t ∧ ∀ ⦃a⦄, a ∈ s → a ∉ t → ∃ b, b ∈ t ∧ b ∉ s ∧ a ≤ b := by
  simp [lt_iff_le_and_ne, toColex_le_toColex, and_comm]

/-- If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
/-
**Finset.Colex.toColex_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：toColex_mono : Monotone (@toColex (Finset α))
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as
 inclusion does
not form a linear order.
-/
lemma toColex_mono : Monotone (@toColex (Finset α)) :=
  fun _s _t hst _a has hat ↦ (hat <| hst has).elim

/-- If `s ⊂ t`, then `s < t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
/-
**Finset.Colex.toColex_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：toColex_strictMono : StrictMono (@toColex (Finset α))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用引理 `Finset.Colex.toColex_mono`：toColex_mono : Monotone (@toColex (Finset α))
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
If `s ⊂ t`, then `s < t` in the colex order. Note the converse does not hold, as
 inclusion does
not form a linear order.
-/
lemma toColex_strictMono : StrictMono (@toColex (Finset α)) :=
  toColex_mono.strictMono_of_injective toColex.injective

/-- If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
/-
**Finset.Colex.toColex_le_toColex_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Co
lex`。
形式化陈述：toColex_le_toColex_of_subset (h : s subseteq t) : toColex s <= toColex t
参数：h : s subseteq t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.Colex.toColex_mono`：toColex_mono : Monotone (@toColex (Finset α))

--- 原说明 ---
If `s ⊆ t`, then `s ≤ t` in the colex order. Note the converse does not hold, as
 inclusion does
not form a linear order.
-/
lemma toColex_le_toColex_of_subset (h : s ⊆ t) : toColex s ≤ toColex t := toColex_mono h

/-- If `s ⊂ t`, then `s < t` in the colex order. Note the converse does not hold, as inclusion does
not form a linear order. -/
/-
**Finset.Colex.toColex_lt_toColex_of_ssubset** 是 Mathlib 中的一个引理，位于命名空间 `Finset.C
olex`。
形式化陈述：toColex_lt_toColex_of_ssubset (h : s ⊂ t) : toColex s < toColex t
参数：h : s ⊂ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.Colex.toColex_strictMono`：toColex_strictMono : StrictMono (@toCol
ex (Finset α))

--- 原说明 ---
If `s ⊂ t`, then `s < t` in the colex order. Note the converse does not hold, as
 inclusion does
not form a linear order.
-/
lemma toColex_lt_toColex_of_ssubset (h : s ⊂ t) : toColex s < toColex t := toColex_strictMono h
/-
**Finset.Colex.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instOrderBot : OrderBot (Colex (Finset α)) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot : OrderBot (Colex (Finset α)) where
  bot := toColex ∅
  bot_le s a ha := by cases ha
/-
**Finset.Colex.toColex_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α], toColex ∅ = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toColex_empty : toColex (∅ : Finset α) = ⊥ := rfl
/-
**Finset.Colex.ofColex_bot** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α], ofColex ⊥ = ∅
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofColex_bot : ofColex (⊥ : Colex (Finset α)) = ∅ := rfl

/-- If `s ≤ t` in colex, and all elements in `t` are small, then all elements in `s` are small. -/
/-
**Finset.Colex.forall_le_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：forall_le_mono (hst : toColex s <= toColex t) (ht : forall b in t, b <= a)
 : forall b in s, b <= a
参数：hst : toColex s <= toColex t；ht : forall b in t, b <= a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
If `s ≤ t` in colex, and all elements in `t` are small, then all elements in `s`
 are small.
-/
lemma forall_le_mono (hst : toColex s ≤ toColex t) (ht : ∀ b ∈ t, b ≤ a) : ∀ b ∈ s, b ≤ a := by
  rintro b hb
  by_cases b ∈ t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
    exact hbc.trans <| ht _ hct

/-- If `s ≤ t` in colex, and all elements in `t` are small, then all elements in `s` are small. -/
/-
**Finset.Colex.forall_lt_mono** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：forall_lt_mono (hst : toColex s <= toColex t) (ht : forall b in t, b < a) 
: forall b in s, b < a
参数：hst : toColex s <= toColex t；ht : forall b in t, b < a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c

--- 原说明 ---
If `s ≤ t` in colex, and all elements in `t` are small, then all elements in `s`
 are small.
-/
lemma forall_lt_mono (hst : toColex s ≤ toColex t) (ht : ∀ b ∈ t, b < a) : ∀ b ∈ s, b < a := by
  rintro b hb
  by_cases b ∈ t
  · exact ht _ ‹_›
  · obtain ⟨c, hct, -, hbc⟩ := hst hb ‹_›
    exact hbc.trans_lt <| ht _ hct

/-- `s ≤ {a}` in colex iff all elements of `s` are strictly less than `a`, except possibly `a` in
which case `s = {a}`. -/
/-
**Finset.Colex.toColex_le_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：toColex_le_singleton : toColex s <= toColex {a} ↔ forall b in s, b <= a ∧ 
(a in s -> b = a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
`s ≤ {a}` in colex iff all elements of `s` are strictly less than `a`, except po
ssibly `a` in
which case `s = {a}`.
-/
lemma toColex_le_singleton : toColex s ≤ toColex {a} ↔ ∀ b ∈ s, b ≤ a ∧ (a ∈ s → b = a) := by
  simp only [toColex_le_toColex, mem_singleton, exists_eq_left]
  refine forall₂_congr fun b _ ↦ ?_; obtain rfl | hba := eq_or_ne b a <;> aesop

/-- `s < {a}` in colex iff all elements of `s` are strictly less than `a`. -/
/-
**Finset.Colex.toColex_lt_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：toColex_lt_singleton : toColex s < toColex {a} ↔ forall b in s, b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用引理 `Finset.Colex.toColex_le_singleton`：toColex_le_singleton : toColex s <= t
oColex {a} ↔ forall b in s, b <= a ∧ (a in s -> b = a)
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `toColex_inj`：toColex_inj {a b : α} : toColex a = toColex b ↔ a = b
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem {s : Fin
set α} {a : α} : s = {a} ↔ a in s ∧ forall x in s, x = a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
`s < {a}` in colex iff all elements of `s` are strictly less than `a`.
-/
lemma toColex_lt_singleton : toColex s < toColex {a} ↔ ∀ b ∈ s, b < a := by
  rw [lt_iff_le_and_ne, toColex_le_singleton, ne_eq, toColex_inj]
  refine ⟨fun h b hb ↦ (h.1 _ hb).1.lt_of_ne ?_,
    fun h ↦ ⟨fun b hb ↦ ⟨(h _ hb).le, fun ha ↦ (lt_irrefl _ <| h _ ha).elim⟩, ?_⟩⟩ <;> rintro rfl
  · refine h.2 <| eq_singleton_iff_unique_mem.2 ⟨hb, fun c hc ↦ (h.1 _ hc).2 hb⟩
  · simp at h

/-- `{a} ≤ s` in colex iff `s` contains an element greater than or equal to `a`. -/
/-
**Finset.Colex.singleton_le_toColex** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：singleton_le_toColex : (toColex {a} : Colex (Finset α)) <= toColex s ↔ exi
sts x in s, a <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P

--- 原说明 ---
`{a} ≤ s` in colex iff `s` contains an element greater than or equal to `a`.
-/
lemma singleton_le_toColex : (toColex {a} : Colex (Finset α)) ≤ toColex s ↔ ∃ x ∈ s, a ≤ x := by
  simp [toColex_le_toColex]; by_cases a ∈ s <;> aesop

/-- Colex is an extension of the base order. -/
/-
**Finset.Colex.singleton_le_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：singleton_le_singleton : (toColex ({a} : Finset α)) <= toColex {b} ↔ a <= 
b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Colex is an extension of the base order.
-/
lemma singleton_le_singleton : (toColex ({a} : Finset α)) ≤ toColex {b} ↔ a ≤ b := by
  simp [toColex_le_singleton, eq_comm]

/-- Colex is an extension of the base order. -/
/-
**Finset.Colex.singleton_lt_singleton** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：singleton_lt_singleton : (toColex ({a} : Finset α)) < toColex {b} ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Colex is an extension of the base order.
-/
lemma singleton_lt_singleton : (toColex ({a} : Finset α)) < toColex {b} ↔ a < b := by
  simp [toColex_lt_singleton]
/-
**Finset.Colex.le_iff_sdiff_subset_lowerClosure** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t.Colex`。
形式化陈述：le_iff_sdiff_subset_lowerClosure {s t : Colex (Finset α)} : s <= t ↔ (↑(of
Colex s) : Set α) \ ↑(ofColex t) subseteq lowerClosure (↑(ofColex t) \ ↑(ofColex
 s) : Set α)
参数：Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma le_iff_sdiff_subset_lowerClosure {s t : Colex (Finset α)} :
    s ≤ t ↔ (↑(ofColex s) : Set α) \ ↑(ofColex t) ⊆
      lowerClosure (↑(ofColex t) \ ↑(ofColex s) : Set α) := by
  simp [le_def, Set.subset_def, and_assoc]

section DecidableEq
variable [DecidableEq α]

/-
**Finset.Colex.instDecidableLE** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instDecidableLE [DecidableLE α] : DecidableLE (Colex (Finset α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableLE [DecidableLE α] : DecidableLE (Colex (Finset α)) :=
  fun s t ↦ decidable_of_iff'
    (∀ ⦃a⦄, a ∈ ofColex s → a ∉ ofColex t → ∃ b, b ∈ ofColex t ∧ b ∉ ofColex s ∧ a ≤ b) Iff.rfl
/-
**Finset.Colex.instDecidableLT** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instDecidableLT [DecidableLE α] : DecidableLT (Colex (Finset α))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDecidableLT [DecidableLE α] : DecidableLT (Colex (Finset α)) :=
  decidableLTOfDecidableLE

/-- The colexicographic order is insensitive to removing the same elements from both sets. -/
/-
**Finset.Colex.toColex_sdiff_le_toColex_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset.
Colex`。
形式化陈述：toColex_sdiff_le_toColex_sdiff (hus : u subseteq s) (hut : u subseteq t) :
 toColex (s \ u) <= toColex (t \ u) ↔ toColex s <= toColex t
参数：hus : u subseteq s；hut : u subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `sdiff_sdiff_sdiff_cancel_right`：sdiff_sdiff_sdiff_cancel_right (hcb : z 
<= y) : (x \ z) \ (y \ z) = x \ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The colexicographic order is insensitive to removing the same elements from both
 sets.
-/
lemma toColex_sdiff_le_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) ≤ toColex (t \ u) ↔ toColex s ≤ toColex t := by
  simp_rw [toColex_le_toColex, ← and_imp, ← and_assoc, ← mem_sdiff,
    sdiff_sdiff_sdiff_cancel_right (show u ≤ s from hus),
    sdiff_sdiff_sdiff_cancel_right (show u ≤ t from hut)]

/-- The colexicographic order is insensitive to removing the same elements from both sets. -/
/-
**Finset.Colex.toColex_sdiff_lt_toColex_sdiff** 是 Mathlib 中的一个引理，位于命名空间 `Finset.
Colex`。
形式化陈述：toColex_sdiff_lt_toColex_sdiff (hus : u subseteq s) (hut : u subseteq t) :
 toColex (s \ u) < toColex (t \ u) ↔ toColex s < toColex t
参数：hus : u subseteq s；hut : u subseteq t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用引理 `Finset.Colex.toColex_sdiff_le_toColex_sdiff`：toColex_sdiff_le_toColex_sd
iff (hus : u subseteq s) (hut : u subseteq t) : toColex (s \ u) <= toColex (t \ 
u) ↔ toColex s <= toColex t

--- 原说明 ---
The colexicographic order is insensitive to removing the same elements from both
 sets.
-/
lemma toColex_sdiff_lt_toColex_sdiff (hus : u ⊆ s) (hut : u ⊆ t) :
    toColex (s \ u) < toColex (t \ u) ↔ toColex s < toColex t :=
  lt_iff_lt_of_le_iff_le' (toColex_sdiff_le_toColex_sdiff hut hus) <|
    toColex_sdiff_le_toColex_sdiff hus hut
/-
**Finset.Colex.toColex_sdiff_le_toColex_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 `Finset
.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {s t : Finset α} [inst_1 : Decida
bleEq α],   toColex (s \ t) ≤ toColex (t \ s) ↔ toColex s ≤ toColex t
参数：s \ t；t \ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sdiff_inter_self_left`：sdiff_inter_self_left (s t : Finset α) : s
 \ (s inter t) = s \ t
· 使用定理 `Finset.sdiff_inter_self_right`：sdiff_inter_self_right (s t : Finset α) :
 s \ (t inter s) = s \ t
· 使用引理 `Finset.Colex.toColex_sdiff_le_toColex_sdiff`：toColex_sdiff_le_toColex_sd
iff (hus : u subseteq s) (hut : u subseteq t) : toColex (s \ u) <= toColex (t \ 
u) ↔ toColex s <= toColex t
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
-/
@[simp] lemma toColex_sdiff_le_toColex_sdiff' :
    toColex (s \ t) ≤ toColex (t \ s) ↔ toColex s ≤ toColex t := by
  simpa using toColex_sdiff_le_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right
/-
**Finset.Colex.toColex_sdiff_lt_toColex_sdiff'** 是 Mathlib 中的一个定理，位于命名空间 `Finset
.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {s t : Finset α} [inst_1 : Decida
bleEq α],   toColex (s \ t) < toColex (t \ s) ↔ toColex s < toColex t
参数：s \ t；t \ s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sdiff_inter_self_left`：sdiff_inter_self_left (s t : Finset α) : s
 \ (s inter t) = s \ t
· 使用定理 `Finset.sdiff_inter_self_right`：sdiff_inter_self_right (s t : Finset α) :
 s \ (t inter s) = s \ t
· 使用引理 `Finset.Colex.toColex_sdiff_lt_toColex_sdiff`：toColex_sdiff_lt_toColex_sd
iff (hus : u subseteq s) (hut : u subseteq t) : toColex (s \ u) < toColex (t \ u
) ↔ toColex s < toColex t
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Finset.inter_subset_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₁ ∩ s₂ ⊆ s₂
-/
@[simp] lemma toColex_sdiff_lt_toColex_sdiff' :
    toColex (s \ t) < toColex (t \ s) ↔ toColex s < toColex t := by
  simpa using toColex_sdiff_lt_toColex_sdiff (inter_subset_left (s₁ := s)) inter_subset_right

end DecidableEq

/-
**Finset.Colex.cons_le_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {s : Finset α} {a b : α} (ha : a 
∉ s) (hb : b ∉ s),   toColex (Finset.cons a s ha) ≤ toColex (Finset.cons b s hb)
 ↔ a ≤ b
参数：ha : a ∉ s；hb : b ∉ s；Finset.cons a s ha；Finset.cons b s hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Colex.toColex_sdiff_le_toColex_sdiff'`：∀ {α : Type u_1} [inst : P
artialOrder α] {s t : Finset α} [inst_1 : DecidableEq α],   toColex (s \ t) ≤ to
Colex (t \ s) ↔ toColex s ≤ toCole…
· 使用引理 `Finset.cons_sdiff_cons`：cons_sdiff_cons (hab : a != b) (ha hb) : s.cons 
a ha \ s.cons b hb = {a}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Finset.Colex.singleton_le_singleton`：singleton_le_singleton : (toColex (
{a} : Finset α)) <= toColex {b} ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma cons_le_cons (ha hb) : toColex (s.cons a ha) ≤ toColex (s.cons b hb) ↔ a ≤ b := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  classical
  rw [← toColex_sdiff_le_toColex_sdiff', cons_sdiff_cons hab, cons_sdiff_cons hab.symm,
    singleton_le_singleton]
/-
**Finset.Colex.cons_lt_cons** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {s : Finset α} {a b : α} (ha : a 
∉ s) (hb : b ∉ s),   toColex (Finset.cons a s ha) < toColex (Finset.cons b s hb)
 ↔ a < b
参数：ha : a ∉ s；hb : b ∉ s；Finset.cons a s ha；Finset.cons b s hb。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `Finset.Colex.cons_le_cons`：∀ {α : Type u_1} [inst : PartialOrder α] {s :
 Finset α} {a b : α} (ha : a ∉ s) (hb : b ∉ s),   toColex (Finset.cons a s ha) ≤
 toColex (Finse…
-/
@[simp] lemma cons_lt_cons (ha hb) : toColex (s.cons a ha) < toColex (s.cons b hb) ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (cons_le_cons _ _) (cons_le_cons _ _)

variable [DecidableEq α]
/-
**Finset.Colex.insert_le_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：insert_le_insert (ha : a ∉ s) (hb : b ∉ s) : toColex (insert a s) <= toCol
ex (insert b s) ↔ a <= b
参数：ha : a ∉ s；hb : b ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Colex.cons_le_cons`：∀ {α : Type u_1} [inst : PartialOrder α] {s :
 Finset α} {a b : α} (ha : a ∉ s) (hb : b ∉ s),   toColex (Finset.cons a s ha) ≤
 toColex (Finse…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma insert_le_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) ≤ toColex (insert b s) ↔ a ≤ b := by
  rw [← cons_eq_insert _ _ ha, ← cons_eq_insert _ _ hb, cons_le_cons]
/-
**Finset.Colex.insert_lt_insert** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：insert_lt_insert (ha : a ∉ s) (hb : b ∉ s) : toColex (insert a s) < toCole
x (insert b s) ↔ a < b
参数：ha : a ∉ s；hb : b ∉ s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.cons_eq_insert`：cons_eq_insert (a s h) : @cons α a s h = insert a
 s
· 使用定理 `Finset.Colex.cons_lt_cons`：∀ {α : Type u_1} [inst : PartialOrder α] {s :
 Finset α} {a b : α} (ha : a ∉ s) (hb : b ∉ s),   toColex (Finset.cons a s ha) <
 toColex (Finse…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma insert_lt_insert (ha : a ∉ s) (hb : b ∉ s) :
    toColex (insert a s) < toColex (insert b s) ↔ a < b := by
  rw [← cons_eq_insert _ _ ha, ← cons_eq_insert _ _ hb, cons_lt_cons]
/-
**Finset.Colex.erase_le_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：erase_le_erase (ha : a in s) (hb : b in s) : toColex (s.erase a) <= toCole
x (s.erase b) ↔ b <= a
参数：ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.Colex.toColex_sdiff_le_toColex_sdiff'`：∀ {α : Type u_1} [inst : P
artialOrder α] {s t : Finset α} [inst_1 : DecidableEq α],   toColex (s \ t) ≤ to
Colex (t \ s) ↔ toColex s ≤ toCole…
· 使用引理 `Finset.erase_sdiff_erase`：erase_sdiff_erase (hab : a != b) (hb : b in s)
 : s.erase a \ s.erase b = {b}
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用引理 `Finset.Colex.singleton_le_singleton`：singleton_le_singleton : (toColex (
{a} : Finset α)) <= toColex {b} ↔ a <= b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma erase_le_erase (ha : a ∈ s) (hb : b ∈ s) :
    toColex (s.erase a) ≤ toColex (s.erase b) ↔ b ≤ a := by
  obtain rfl | hab := eq_or_ne a b
  · simp
  rw [← toColex_sdiff_le_toColex_sdiff', erase_sdiff_erase hab hb, erase_sdiff_erase hab.symm ha,
    singleton_le_singleton]
/-
**Finset.Colex.erase_lt_erase** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：erase_lt_erase (ha : a in s) (hb : b in s) : toColex (s.erase a) < toColex
 (s.erase b) ↔ b < a
参数：ha : a in s；hb : b in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用引理 `Finset.Colex.erase_le_erase`：erase_le_erase (ha : a in s) (hb : b in s) 
: toColex (s.erase a) <= toColex (s.erase b) ↔ b <= a
-/
lemma erase_lt_erase (ha : a ∈ s) (hb : b ∈ s) :
    toColex (s.erase a) < toColex (s.erase b) ↔ b < a :=
  lt_iff_lt_of_le_iff_le' (erase_le_erase hb ha) (erase_le_erase ha hb)

end PartialOrder

variable [LinearOrder α] [LinearOrder β] {f : α → β} {𝒜 𝒜₁ 𝒜₂ : Finset (Finset α)}
  {s t u : Finset α} {a b : α} {r : ℕ}

/-
**Finset.Colex.instLinearOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instLinearOrder : LinearOrder (Colex (Finset α)) where le_total s t
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLinearOrder : LinearOrder (Colex (Finset α)) where
  le_total s t := by
    obtain rfl | hts := eq_or_ne t s
    · simp
    have ⟨a, ha, hamax⟩ := exists_max_image _ id
      (symmDiff_nonempty.2 <| ofColex.injective.ne_iff.2 hts)
    simp_rw [mem_symmDiff] at ha hamax
    exact ha.imp (fun ha b hbs hbt ↦ ⟨a, ha.1, ha.2, hamax _ <| Or.inr ⟨hbs, hbt⟩⟩)
      (fun ha b hbt hbs ↦ ⟨a, ha.1, ha.2, hamax _ <| Or.inl ⟨hbt, hbs⟩⟩)
  toDecidableLE := instDecidableLE
  toDecidableLT := instDecidableLT

open scoped symmDiff

set_option backward.privateInPublic true in
/-
**Finset.Colex.max_mem_aux** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma max_mem_aux {s t : Colex (Finset α)} (hst : s ≠ t) :
    (ofColex s ∆ ofColex t).Nonempty := by
  simpa
/-
**Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt** 是 Mathlib 中的一个引理，位于命名空间
 `Finset.Colex`。
形式化陈述：toColex_lt_toColex_iff_exists_forall_lt : toColex s < toColex t ↔ exists a
 in t, a ∉ s ∧ forall b in s, b ∉ t -> b < a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用引理 `Finset.Colex.toColex_le_toColex`：toColex_le_toColex : toColex s <= toCol
ex t ↔ forall ⦃a⦄, a in s -> a ∉ t -> exists b, b in t ∧ b ∉ s ∧ a <= b
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma toColex_lt_toColex_iff_exists_forall_lt :
    toColex s < toColex t ↔ ∃ a ∈ t, a ∉ s ∧ ∀ b ∈ s, b ∉ t → b < a := by
  rw [← not_le, toColex_le_toColex, not_forall]
  simp only [not_forall, not_exists, not_and, not_le, exists_prop]
/-
**Finset.Colex.lt_iff_exists_forall_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：lt_iff_exists_forall_lt {s t : Colex (Finset α)} : s < t ↔ exists a in ofC
olex t, a ∉ ofColex s ∧ forall b in ofColex s, b ∉ ofColex t -> b < a
参数：Finset α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.Colex.toColex_lt_toColex_iff_exists_forall_lt`：toColex_lt_toColex
_iff_exists_forall_lt : toColex s < toColex t ↔ exists a in t, a ∉ s ∧ forall b 
in s, b ∉ t -> b < a
-/
lemma lt_iff_exists_forall_lt {s t : Colex (Finset α)} :
    s < t ↔ ∃ a ∈ ofColex t, a ∉ ofColex s ∧ ∀ b ∈ ofColex s, b ∉ ofColex t → b < a :=
  toColex_lt_toColex_iff_exists_forall_lt
/-
**Finset.Colex.toColex_le_toColex_iff_max'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset
.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s t : Finset α},   toColex s ≤ to
Colex t ↔ ∀ (hst : s ≠ t), (symmDiff s t).max' ⋯ ∈ t
参数：hst : s ≠ t；symmDiff s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.symmDiff_nonempty`：∀ {α : Type u_1} [inst : DecidableEq α] {s t :
 Finset α}, (symmDiff s t).Nonempty ↔ s ≠ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.max'_lt_iff`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset 
α) (H : s.Nonempty) {x : α}, s.max' H < x ↔ ∀ y ∈ s, y < x
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `Finset.mem_symmDiff`：mem_symmDiff : a in s ∆ t ↔ a in s ∧ a ∉ t ∨ a in t
 ∧ a ∉ s
· 使用定理 `ne_of_mem_of_not_mem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Membershi
p α β] {s t : β} {a : α}, a ∈ s → a ∉ t → s ≠ t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
-/
lemma toColex_le_toColex_iff_max'_mem :
    toColex s ≤ toColex t ↔ ∀ hst : s ≠ t, (s ∆ t).max' (symmDiff_nonempty.2 hst) ∈ t := by
  refine ⟨fun h hst ↦ ?_, fun h a has hat ↦ ?_⟩
  · set m := (s ∆ t).max' (symmDiff_nonempty.2 hst)
    by_contra hmt
    have hms : m ∈ s := by
      simpa [m, mem_symmDiff, hmt] using max'_mem _ <| symmDiff_nonempty.2 hst
    have ⟨b, hbt, hbs, hmb⟩ := h hms hmt
    exact lt_irrefl _ <| (max'_lt_iff _ _).1 (hmb.lt_of_ne <| ne_of_mem_of_not_mem hms hbs) _ <|
      mem_symmDiff.2 <| Or.inr ⟨hbt, hbs⟩
  · have hst : s ≠ t := ne_of_mem_of_not_mem' has hat
    refine ⟨_, h hst, ?_, le_max' _ _ <| mem_symmDiff.2 <| Or.inl ⟨has, hat⟩⟩
    simpa [mem_symmDiff, h hst] using max'_mem _ <| symmDiff_nonempty.2 hst

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.Colex.le_iff_max'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s t : Colex (Finset α)},   s ≤ t 
↔ ∀ (h : s ≠ t), (symmDiff (ofColex s) (ofColex t)).max' ⋯ ∈ ofColex t
参数：Finset α；h : s ≠ t；symmDiff (ofColex s) (ofColex t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Colex.toColex_le_toColex_iff_max'_mem`：∀ {α : Type u_1} [inst : L
inearOrder α] {s t : Finset α},   toColex s ≤ toColex t ↔ ∀ (hst : s ≠ t), (symm
Diff s t).max' ⋯ ∈ t
-/
lemma le_iff_max'_mem {s t : Colex (Finset α)} :
    s ≤ t ↔ ∀ h : s ≠ t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) ∈ ofColex t :=
  toColex_le_toColex_iff_max'_mem
/-
**Finset.Colex.toColex_lt_toColex_iff_max'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset
.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s t : Finset α},   toColex s < to
Colex t ↔ ∃ (hst : s ≠ t), (symmDiff s t).max' ⋯ ∈ t
参数：hst : s ≠ t；symmDiff s t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.symmDiff_nonempty`：∀ {α : Type u_1} [inst : DecidableEq α] {s t :
 Finset α}, (symmDiff s t).Nonempty ↔ s ≠ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Finset.Colex.toColex_le_toColex_iff_max'_mem`：∀ {α : Type u_1} [inst : L
inearOrder α] {s t : Finset α},   toColex s ≤ toColex t ↔ ∀ (hst : s ≠ t), (symm
Diff s t).max' ⋯ ∈ t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma toColex_lt_toColex_iff_max'_mem :
    toColex s < toColex t ↔ ∃ hst : s ≠ t, (s ∆ t).max' (symmDiff_nonempty.2 hst) ∈ t := by
  rw [lt_iff_le_and_ne, toColex_le_toColex_iff_max'_mem]; aesop

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**Finset.Colex.lt_iff_max'_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s t : Colex (Finset α)},   s < t 
↔ ∃ (h : s ≠ t), (symmDiff (ofColex s) (ofColex t)).max' ⋯ ∈ ofColex t
参数：Finset α；h : s ≠ t；symmDiff (ofColex s) (ofColex t)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `_private.Mathlib.Combinatorics.Colex.0.Finset.Colex.max_mem_aux`：∀ {α : 
Type u_1} [inst : LinearOrder α] {s t : Colex (Finset α)}, s ≠ t → (symmDiff (of
Colex s) (ofColex t)).Nonempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `Finset.Colex.le_iff_max'_mem`：∀ {α : Type u_1} [inst : LinearOrder α] {s
 t : Colex (Finset α)},   s ≤ t ↔ ∀ (h : s ≠ t), (symmDiff (ofColex s) (ofColex 
t)).max' ⋯ ∈ ofCol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma lt_iff_max'_mem {s t : Colex (Finset α)} :
    s < t ↔ ∃ h : s ≠ t, (ofColex s ∆ ofColex t).max' (max_mem_aux h) ∈ ofColex t := by
  rw [lt_iff_le_and_ne, le_iff_max'_mem]; aesop
/-
**Finset.Colex.lt_iff_exists_filter_lt** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：lt_iff_exists_filter_lt : toColex s < toColex t ↔ exists w in t \ s, {a in
 s | w < a} = {a in t | w < a}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.max'`：max'_one [LinearOrder α] : (1 : Finset α).max' one_nonempty
 = 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.max'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.max' H ∈ s
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `LT.lt.asymm`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b 
< a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Finset.le_max'`：le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
-/
lemma lt_iff_exists_filter_lt :
    toColex s < toColex t ↔ ∃ w ∈ t \ s, {a ∈ s | w < a} = {a ∈ t | w < a} := by
  simp only [lt_iff_exists_forall_lt, mem_sdiff, filter_inj, and_assoc]
  refine ⟨fun h ↦ ?_, ?_⟩
  · let u := {w ∈ t \ s | ∀ a ∈ s, a ∉ t → a < w}
    have mem_u {w : α} : w ∈ u ↔ w ∈ t ∧ w ∉ s ∧ ∀ a ∈ s, a ∉ t → a < w := by simp [u, and_assoc]
    have hu : u.Nonempty := h.imp fun _ ↦ mem_u.2
    let m := max' _ hu
    have ⟨hmt, hms, hm⟩ : m ∈ t ∧ m ∉ s ∧ ∀ a ∈ s, a ∉ t → a < m := mem_u.1 <| max'_mem _ _
    refine ⟨m, hmt, hms, fun a hma ↦ ⟨fun has ↦ not_imp_comm.1 (hm _ has) hma.asymm, fun hat ↦ ?_⟩⟩
    by_contra has
    have hau : a ∈ u := mem_u.2 ⟨hat, has, fun b hbs hbt ↦ (hm _ hbs hbt).trans hma⟩
    exact hma.not_ge <| le_max' _ _ hau
  · rintro ⟨w, hwt, hws, hw⟩
    refine ⟨w, hwt, hws, fun a has hat ↦ ?_⟩
    by_contra! hwa
    exact hat <| (hw <| hwa.lt_of_ne <| ne_of_mem_of_not_mem hwt hat).1 has

/-- If `s ≤ t` in colex and `#s ≤ #t`, then `s \ {a} ≤ t \ {min t}` for any `a ∈ s`. -/
/-
**Finset.Colex.erase_le_erase_min'** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：erase_le_erase_min' (hst : toColex s <= toColex t) (hcard : #s <= #t) (ha 
: a in s) : toColex (s.erase a) <= toColex (t.erase <| min' t <| card_pos.1 <| (
card_pos.2 ⟨a, ha⟩).trans_le hcard)
参数：hst : toColex s <= toColex t；hcard : #s <= #t；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.min'`：min'_one [LinearOrder α] : (1 : Finset α).min' one_nonempty
 = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.Colex.erase_le_erase`：erase_le_erase (ha : a in s) (hb : b in s) 
: toColex (s.erase a) <= toColex (s.erase b) ↔ b <= a
· 使用定理 `Finset.min'_mem`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) 
(H : s.Nonempty), s.min' H ∈ s
· 使用定理 `Finset.min'_le`：∀ {α : Type u_2} [inst : LinearOrder α] (s : Finset α) (
x : α) (H2 : x ∈ s), s.min' ⋯ ≤ x
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `toColex_inj`：toColex_inj {a b : α} : toColex a = toColex b ↔ a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Finset.Colex.lt_iff_exists_forall_lt`：lt_iff_exists_forall_lt {s t : Col
ex (Finset α)} : s < t ↔ exists a in ofColex t, a ∉ ofColex s ∧ forall b in ofCo
lex s, b ∉ ofColex t -> b …
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `not_ne_iff`：not_ne_iff {α : Sort*} {a b : α} : ¬a != b ↔ a = b
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Finset.mem_of_mem_erase`：mem_of_mem_erase : b in erase s a -> b in s
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `s ≤ t` in colex and `#s ≤ #t`, then `s \ {a} ≤ t \ {min t}` for any `a ∈ s`.
-/
lemma erase_le_erase_min' (hst : toColex s ≤ toColex t) (hcard : #s ≤ #t) (ha : a ∈ s) :
    toColex (s.erase a) ≤
      toColex (t.erase <| min' t <| card_pos.1 <| (card_pos.2 ⟨a, ha⟩).trans_le hcard) := by
  generalize_proofs ht
  set m := min' t ht
  -- Case on whether `s = t`
  obtain rfl | h' := eq_or_ne s t
  -- If `s = t`, then `s \ {a} ≤ s \ {m}` because `m ≤ a`
  · exact (erase_le_erase ha <| min'_mem _ _).2 <| min'_le _ _ <| ha
  -- If `s ≠ t`, call `w` the colex witness. Case on whether `w < a` or `a < w`
  replace hst := hst.lt_of_ne <| toColex_inj.not.2 h'
  simp only [lt_iff_exists_filter_lt, mem_sdiff, filter_inj, and_assoc] at hst
  obtain ⟨w, hwt, hws, hw⟩ := hst
  obtain hwa | haw := (ne_of_mem_of_not_mem ha hws).symm.lt_or_gt
  -- If `w < a`, then `a` is the colex witness for `s \ {a} < t \ {m}`
  · have hma : m < a := (min'_le _ _ hwt).trans_lt hwa
    refine (lt_iff_exists_forall_lt.2 ⟨a, mem_erase.2 ⟨hma.ne', (hw hwa).1 ha⟩,
      notMem_erase _ _, fun b hbs hbt ↦ ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase, not_and_or, not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hab
      exact hbt <| (hw <| hwa.trans_le hab).1 <| mem_of_mem_erase hbs
  -- If `a < w`, case on whether `m < w` or `m = w`
  obtain rfl | hmw : m = w ∨ m < w := (min'_le _ _ hwt).eq_or_lt
  -- If `m = w`, then `s \ {a} = t \ {m}`
  · have : erase t m ⊆ erase s a := by
      rintro b hb
      rw [mem_erase] at hb ⊢
      exact ⟨(haw.trans_le <| min'_le _ _ hb.2).ne',
        (hw <| hb.1.lt_of_le' <| min'_le _ _ hb.2).2 hb.2⟩
    rw [eq_of_subset_of_card_le this]
    rw [card_erase_of_mem ha, card_erase_of_mem (min'_mem _ _)]
    exact tsub_le_tsub_right hcard _
  -- If `m < w`, then `w` works as the colex witness for  `s \ {a} < t \ {m}`
  · refine (lt_iff_exists_forall_lt.2 ⟨w, mem_erase.2 ⟨hmw.ne', hwt⟩, mt mem_of_mem_erase hws,
      fun b hbs hbt ↦ ?_⟩).le
    change b ∉ t.erase m at hbt
    rw [mem_erase, not_and_or, not_ne_iff] at hbt
    obtain rfl | hbt := hbt
    · assumption
    · by_contra! hwb
      exact hbt <| (hw <| hwb.lt_of_ne <| ne_of_mem_of_not_mem hwt hbt).1 <| mem_of_mem_erase hbs

/-- Strictly monotone functions preserve the colex ordering. -/
/-
**Finset.Colex.toColex_image_le_toColex_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset.
Colex`。
形式化陈述：toColex_image_le_toColex_image (hf : StrictMono f) : toColex (s.image f) <
= toColex (t.image f) ↔ toColex s <= toColex t
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Strictly monotone functions preserve the colex ordering.
-/
lemma toColex_image_le_toColex_image (hf : StrictMono f) :
    toColex (s.image f) ≤ toColex (t.image f) ↔ toColex s ≤ toColex t := by
  simp [toColex_le_toColex, hf.le_iff_le, hf.injective.eq_iff]

/-- Strictly monotone functions preserve the colex ordering. -/
/-
**Finset.Colex.toColex_image_lt_toColex_image** 是 Mathlib 中的一个引理，位于命名空间 `Finset.
Colex`。
形式化陈述：toColex_image_lt_toColex_image (hf : StrictMono f) : toColex (s.image f) <
 toColex (t.image f) ↔ toColex s < toColex t
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le`：lt_iff_lt_of_le_iff_le {β} [LinearOrder α] [Line
arOrder β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) : b < a ↔ d < c
· 使用引理 `Finset.Colex.toColex_image_le_toColex_image`：toColex_image_le_toColex_im
age (hf : StrictMono f) : toColex (s.image f) <= toColex (t.image f) ↔ toColex s
 <= toColex t

--- 原说明 ---
Strictly monotone functions preserve the colex ordering.
-/
lemma toColex_image_lt_toColex_image (hf : StrictMono f) :
    toColex (s.image f) < toColex (t.image f) ↔ toColex s < toColex t :=
  lt_iff_lt_of_le_iff_le <| toColex_image_le_toColex_image hf
/-
**Finset.Colex.toColex_image_ofColex_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finse
t.Colex`。
形式化陈述：toColex_image_ofColex_strictMono (hf : StrictMono f) : StrictMono fun s =>
 toColex image f ofColex s
参数：hf : StrictMono f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.Colex.toColex_image_lt_toColex_image`：toColex_image_lt_toColex_im
age (hf : StrictMono f) : toColex (s.image f) < toColex (t.image f) ↔ toColex s 
< toColex t
-/
lemma toColex_image_ofColex_strictMono (hf : StrictMono f) :
    StrictMono fun s ↦ toColex <| image f <| ofColex s :=
  fun _s _t ↦ (toColex_image_lt_toColex_image hf).2

section Fintype
variable [Fintype α]

/-
**Finset.Colex.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Finset.Colex`。
形式化陈述：instBoundedOrder : BoundedOrder (Colex (Finset α)) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder : BoundedOrder (Colex (Finset α)) where
  top := toColex univ
  le_top _x := toColex_le_toColex_of_subset <| subset_univ _
/-
**Finset.Colex.toColex_univ** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Fintype α], toColex Fins
et.univ = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma toColex_univ : toColex (univ : Finset α) = ⊤ := rfl
/-
**Finset.Colex.ofColex_top** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] [inst_1 : Fintype α], ofColex ⊤ = 
Finset.univ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma ofColex_top : ofColex (⊤ : Colex (Finset α)) = univ := rfl

end Fintype

/-! ### Initial segments -/

/-- `𝒜` is an initial segment of the colexicographic order on sets of `r`, and that if `t` is below
`s` in colex where `t` has size `r` and `s` is in `𝒜`, then `t` is also in `𝒜`. In effect, `𝒜` is
downwards closed with respect to colex among sets of size `r`. -/
/-
**Finset.Colex.IsInitSeg** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Colex`。
形式化陈述：IsInitSeg (𝒜 : Finset (Finset α)) (r : Nat) : Prop
参数：𝒜 : Finset (Finset α)；r : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`𝒜` is an initial segment of the colexicographic order on sets of `r`, and that 
if `t` is below
`s` in colex where `t` has size `r` and `s` is in `𝒜`, then `t` is also in `𝒜`. 
In effect, `𝒜` is
downwards closed with respect to colex among sets of size `r`.
-/
def IsInitSeg (𝒜 : Finset (Finset α)) (r : ℕ) : Prop :=
  (𝒜 : Set (Finset α)).Sized r ∧
    ∀ ⦃s t : Finset α⦄, s ∈ 𝒜 → toColex t < toColex s ∧ #t = r → t ∈ 𝒜
/-
**Finset.Colex.isInitSeg_empty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {r : ℕ}, Finset.Colex.IsInitSeg ∅ 
r
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
@[simp] lemma isInitSeg_empty : IsInitSeg (∅ : Finset (Finset α)) r := by simp [IsInitSeg]

/-- Initial segments are nested in some way. In particular, if they're the same size they're equal.
-/
/-
**Finset.Colex.IsInitSeg.total** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex.IsInitSeg
`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {𝒜₁ 𝒜₂ : Finset (Finset α)} {r : ℕ
},   Finset.Colex.IsInitSeg 𝒜₁ r → Finset.Colex.IsInitSeg 𝒜₂ r → 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 
𝒜₁
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Initial segments are nested in some way. In particular, if they're the same size
 they're equal.
-/
lemma IsInitSeg.total (h₁ : IsInitSeg 𝒜₁ r) (h₂ : IsInitSeg 𝒜₂ r) : 𝒜₁ ⊆ 𝒜₂ ∨ 𝒜₂ ⊆ 𝒜₁ := by
  simp_rw [← sdiff_eq_empty_iff_subset]
  by_contra! h
  have ⟨⟨s, hs⟩, t, ht⟩ := h
  rw [mem_sdiff] at hs ht
  obtain hst | hst | hts := trichotomous_of (α := Colex (Finset α)) (· < ·) (toColex s) (toColex t)
  · exact hs.2 <| h₂.2 ht.1 ⟨hst, h₁.1 hs.1⟩
  · simp only [toColex_inj] at hst
    exact ht.2 <| hst ▸ hs.1
  · exact ht.2 <| h₁.2 hs.1 ⟨hts, h₂.1 ht.1⟩

variable [Fintype α]

/-- The initial segment of the colexicographic order on sets with `#s` elements and ending at
`s`. -/
/-
**Finset.Colex.initSeg** 是 Mathlib 中的一个定义，位于命名空间 `Finset.Colex`。
形式化陈述：initSeg (s : Finset α) : Finset (Finset α)
参数：s : Finset α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The initial segment of the colexicographic order on sets with `#s` elements and 
ending at
`s`.
-/
def initSeg (s : Finset α) : Finset (Finset α) := {t | #s = #t ∧ toColex t ≤ toColex s}

@[simp]
/-
**Finset.Colex.mem_initSeg** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：mem_initSeg : t in initSeg s ↔ #s = #t ∧ toColex t <= toColex s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_initSeg : t ∈ initSeg s ↔ #s = #t ∧ toColex t ≤ toColex s := by simp [initSeg]
/-
**Finset.Colex.mem_initSeg_self** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：mem_initSeg_self : s in initSeg s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma mem_initSeg_self : s ∈ initSeg s := by simp
/-
**Finset.Colex.initSeg_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {s : Finset α} [inst_1 : Fintype α
], (Finset.Colex.initSeg s).Nonempty
参数：Finset.Colex.initSeg s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.Colex.mem_initSeg_self`：mem_initSeg_self : s in initSeg s
-/
@[simp] lemma initSeg_nonempty : (initSeg s).Nonempty := ⟨s, mem_initSeg_self⟩
/-
**Finset.Colex.isInitSeg_initSeg** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Colex`。
形式化陈述：isInitSeg_initSeg : IsInitSeg (initSeg s) #s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Finset.Colex.mem_initSeg`：mem_initSeg : t in initSeg s ↔ #s = #t ∧ toCol
ex t <= toColex s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma isInitSeg_initSeg : IsInitSeg (initSeg s) #s := by
  refine ⟨fun t ht => (mem_initSeg.1 ht).1.symm, fun t₁ t₂ ht₁ ht₂ ↦ mem_initSeg.2 ⟨ht₂.2.symm, ?_⟩⟩
  rw [mem_initSeg] at ht₁
  exact ht₂.1.le.trans ht₁.2

set_option backward.isDefEq.respectTransparency false in
/-
**Finset.Colex.IsInitSeg.exists_initSeg** 是 Mathlib 中的一个定理，位于命名空间 `Finset.Colex.
IsInitSeg`。
形式化陈述：∀ {α : Type u_1} [inst : LinearOrder α] {𝒜 : Finset (Finset α)} {r : ℕ} [i
nst_1 : Fintype α],   Finset.Colex.IsInitSeg 𝒜 r → 𝒜.Nonempty → ∃ s, s.card = r 
∧ 𝒜 = Finset.Colex.initSeg s
参数：Finset α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Finset.sup'_mem`：∀ {α : Type u_2} [inst : SemilatticeSup α] (s : Set α),
   (∀ x ∈ s, ∀ y ∈ s, x ⊔ y ∈ s) →     ∀ {ι : Type u_7} (t : Finset ι) (H : t.No
nempt…
· 使用定理 `LinearOrder.supClosed`：∀ {α : Type u_3} [inst : LinearOrder α] (s : Set 
α), SupClosed s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.Colex.mem_initSeg`：mem_initSeg : t in initSeg s ↔ #s = #t ∧ toCol
ex t <= toColex s
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `toColex_inj`：toColex_inj {a b : α} : toColex a = toColex b ↔ a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma IsInitSeg.exists_initSeg (h𝒜 : IsInitSeg 𝒜 r) (h𝒜₀ : 𝒜.Nonempty) :
    ∃ s : Finset α, #s = r ∧ 𝒜 = initSeg s := by
  have hs := sup'_mem (ofColex ⁻¹' 𝒜) (LinearOrder.supClosed _) 𝒜 h𝒜₀ toColex
    (fun a ha ↦ by simpa using ha)
  refine ⟨_, h𝒜.1 hs, ?_⟩
  ext t
  rw [mem_initSeg]
  refine ⟨fun p ↦ ?_, ?_⟩
  · rw [h𝒜.1 p, h𝒜.1 hs]
    exact ⟨rfl, le_sup' _ p⟩
  rintro ⟨cards, le⟩
  obtain p | p := le.eq_or_lt
  · rwa [toColex_inj.1 p]
  · exact h𝒜.2 hs ⟨p, cards ▸ h𝒜.1 hs⟩

/-- Being a nonempty initial segment of colex is equivalent to being an `initSeg`. -/
/-
**Finset.Colex.isInitSeg_iff_exists_initSeg** 是 Mathlib 中的一个引理，位于命名空间 `Finset.Co
lex`。
形式化陈述：isInitSeg_iff_exists_initSeg : IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ exists s : Fin
set α, #s = r ∧ 𝒜 = initSeg s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.Colex.IsInitSeg.exists_initSeg`：∀ {α : Type u_1} [inst : LinearOr
der α] {𝒜 : Finset (Finset α)} {r : ℕ} [inst_1 : Fintype α],   Finset.Colex.IsIn
itSeg 𝒜 r → 𝒜.Nonempty → ∃ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Finset.Colex.isInitSeg_initSeg`：isInitSeg_initSeg : IsInitSeg (initSeg s
) #s
· 使用定理 `Finset.Colex.initSeg_nonempty`：∀ {α : Type u_1} [inst : LinearOrder α] {
s : Finset α} [inst_1 : Fintype α], (Finset.Colex.initSeg s).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Being a nonempty initial segment of colex is equivalent to being an `initSeg`.
-/
lemma isInitSeg_iff_exists_initSeg :
    IsInitSeg 𝒜 r ∧ 𝒜.Nonempty ↔ ∃ s : Finset α, #s = r ∧ 𝒜 = initSeg s := by
  refine ⟨fun h𝒜 ↦ h𝒜.1.exists_initSeg h𝒜.2, ?_⟩
  rintro ⟨s, rfl, rfl⟩
  exact ⟨isInitSeg_initSeg, initSeg_nonempty⟩

end Colex

/-!
### Colex on `ℕ`

The colexicographic order agrees with the order induced by interpreting a set of naturals as a
`n`-ary expansion.
-/

section Nat
variable {s t : Finset ℕ} {n : ℕ}

/-
**Finset.geomSum_ofColex_strictMono** 是 Mathlib 中的一个引理，位于命名空间 `Finset`。
形式化陈述：geomSum_ofColex_strictMono (hn : 2 <= n) : StrictMono fun s => ∑ k in ofCo
lex s, n ^ k
参数：hn : 2 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finset.Colex.lt_iff_exists_forall_lt`：lt_iff_exists_forall_lt {s t : Col
ex (Finset α)} : s < t ↔ exists a in ofColex t, a ∉ ofColex s ∧ forall b in ofCo
lex s, b ∉ ofColex t -> b …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_sdiff_lt_sum_sdiff`：∀ {ι : Type u_9} {M : Type u_10} [inst : 
AddCommMonoid M] [inst_1 : PartialOrder M] [IsOrderedCancelAddMonoid M]   [inst_
3 : DecidableEq ι] …
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `Nat.geomSum_lt`：Nat.geomSum_lt (hm : 2 <= m) (hs : forall k in s, k < n)
 : ∑ k in s, m ^ k < m ^ n
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_sdiff`：mem_sdiff : a in s \ t ↔ a in s ∧ a ∉ t
-/
lemma geomSum_ofColex_strictMono (hn : 2 ≤ n) : StrictMono fun s ↦ ∑ k ∈ ofColex s, n ^ k := by
  intro s t hst
  rw [Colex.lt_iff_exists_forall_lt] at hst
  obtain ⟨a, hat, has, ha⟩ := hst
  rw [← sum_sdiff_lt_sum_sdiff]
  exact (Nat.geomSum_lt hn <| by simpa).trans_le <| single_le_sum (fun _ _ ↦ by lia) <|
    mem_sdiff.2 ⟨hat, has⟩

/-- For finsets of naturals, the colexicographic order is equivalent to the order induced by the
`n`-ary expansion. -/
/-
**Finset.geomSum_le_geomSum_iff_toColex_le_toColex** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset`。
形式化陈述：geomSum_le_geomSum_iff_toColex_le_toColex (hn : 2 <= n) : ∑ k in s, n ^ k 
<= ∑ k in t, n ^ k ↔ toColex s <= toColex t
参数：hn : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用引理 `Finset.geomSum_ofColex_strictMono`：geomSum_ofColex_strictMono (hn : 2 <=
 n) : StrictMono fun s => ∑ k in ofColex s, n ^ k

--- 原说明 ---
For finsets of naturals, the colexicographic order is equivalent to the order in
duced by the
`n`-ary expansion.
-/
lemma geomSum_le_geomSum_iff_toColex_le_toColex (hn : 2 ≤ n) :
    ∑ k ∈ s, n ^ k ≤ ∑ k ∈ t, n ^ k ↔ toColex s ≤ toColex t :=
  (geomSum_ofColex_strictMono hn).le_iff_le

/-- For finsets of naturals, the colexicographic order is equivalent to the order induced by the
`n`-ary expansion. -/
/-
**Finset.geomSum_lt_geomSum_iff_toColex_lt_toColex** 是 Mathlib 中的一个引理，位于命名空间 `Fi
nset`。
形式化陈述：geomSum_lt_geomSum_iff_toColex_lt_toColex (hn : 2 <= n) : ∑ i in s, n ^ i 
< ∑ i in t, n ^ i ↔ toColex s < toColex t
参数：hn : 2 <= n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用引理 `Finset.geomSum_ofColex_strictMono`：geomSum_ofColex_strictMono (hn : 2 <=
 n) : StrictMono fun s => ∑ k in ofColex s, n ^ k

--- 原说明 ---
For finsets of naturals, the colexicographic order is equivalent to the order in
duced by the
`n`-ary expansion.
-/
lemma geomSum_lt_geomSum_iff_toColex_lt_toColex (hn : 2 ≤ n) :
    ∑ i ∈ s, n ^ i < ∑ i ∈ t, n ^ i ↔ toColex s < toColex t :=
  (geomSum_ofColex_strictMono hn).lt_iff_lt
/-
**Finset.geomSum_injective** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：geomSum_injective {n : Nat} (hn : 2 <= n) : Function.Injective (fun s : Fi
nset Nat => ∑ i in s, n ^ i)
参数：hn : 2 <= n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_antisymm_iff`：le_antisymm_iff : a = b ↔ a <= b ∧ b <= a
· 使用引理 `Finset.geomSum_le_geomSum_iff_toColex_le_toColex`：geomSum_le_geomSum_iff
_toColex_le_toColex (hn : 2 <= n) : ∑ k in s, n ^ k <= ∑ k in t, n ^ k ↔ toColex
 s <= toColex t
-/
theorem geomSum_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective (fun s : Finset ℕ ↦ ∑ i ∈ s, n ^ i) := by
  intro _ _ h
  rwa [le_antisymm_iff, geomSum_le_geomSum_iff_toColex_le_toColex hn,
    geomSum_le_geomSum_iff_toColex_le_toColex hn, ← le_antisymm_iff] at h
/-
**Finset.lt_geomSum_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：lt_geomSum_of_mem {a : Nat} (hn : 2 <= n) (hi : a in s) : a < ∑ i in s, n 
^ i
参数：hn : 2 <= n；hi : a in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.lt_pow_self`：∀ {n a : ℕ}, 1 < a → n < a ^ n
· 使用定理 `Finset.single_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMon
oid N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i 
∈ s, 0 ≤ f…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem lt_geomSum_of_mem {a : ℕ} (hn : 2 ≤ n) (hi : a ∈ s) : a < ∑ i ∈ s, n ^ i :=
  (a.lt_pow_self hn).trans_le <| single_le_sum (by simp) hi
/-
**Finset.toFinset_bitIndices_sum_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ (s : Finset ℕ), (∑ i ∈ s, 2 ^ i).bitIndices.toFinset = s
参数：s : Finset ℕ；∑ i ∈ s, 2 ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Finset.geomSum_injective`：geomSum_injective {n : Nat} (hn : 2 <= n) : Fu
nction.Injective (fun s : Finset Nat => ∑ i in s, n ^ i)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_toFinset`：∀ {ι : Type u_1} {M : Type u_5} [inst : DecidableEq ι
] [inst_1 : AddCommMonoid M] (f : ι → M) {l : List ι},   l.Nodup → l.toFinset.su
m f = (…
· 使用定理 `List.SortedLT.nodup`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
l.SortedLT → l.Nodup
· 使用定理 `Nat.bitIndices_sorted`：∀ {n : ℕ}, n.bitIndices.SortedLT
· 使用定理 `Nat.sum_map_two_pow_bitIndices`：∀ (n : ℕ), (List.map (fun i => 2 ^ i) n.
bitIndices).sum = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem toFinset_bitIndices_sum_two_pow (s : Finset ℕ) :
    (∑ i ∈ s, 2 ^ i).bitIndices.toFinset = s := by
  simp [← (geomSum_injective rfl.le).eq_iff, List.sum_toFinset _ Nat.bitIndices_sorted.nodup]
/-
**Finset.sum_toFinset_bitIndices_two_pow** 是 Mathlib 中的一个定理，位于命名空间 `Finset`。
形式化陈述：∀ (n : ℕ), ∑ i ∈ n.bitIndices.toFinset, 2 ^ i = n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.sum_toFinset`：∀ {ι : Type u_1} {M : Type u_5} [inst : DecidableEq ι
] [inst_1 : AddCommMonoid M] (f : ι → M) {l : List ι},   l.Nodup → l.toFinset.su
m f = (…
· 使用定理 `List.SortedLT.nodup`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
l.SortedLT → l.Nodup
· 使用定理 `Nat.bitIndices_sorted`：∀ {n : ℕ}, n.bitIndices.SortedLT
· 使用定理 `Nat.sum_map_two_pow_bitIndices`：∀ (n : ℕ), (List.map (fun i => 2 ^ i) n.
bitIndices).sum = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] theorem sum_toFinset_bitIndices_two_pow (n : ℕ) :
    ∑ i ∈ n.bitIndices.toFinset, 2 ^ i = n := by
  simp [List.sum_toFinset _ Nat.bitIndices_sorted.nodup]

@[deprecated (since := "2026-05-15")] alias toFinset_bitIndices_twoPowSum :=
  toFinset_bitIndices_sum_two_pow

@[deprecated (since := "2026-05-15")] alias twoPowSum_toFinset_bitIndices :=
  sum_toFinset_bitIndices_two_pow

/-- The equivalence between `ℕ` and `Finset ℕ` that maps `∑ i ∈ s, 2^i` to `s`. -/
/-
**Finset.equivBitIndices** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：ℕ ≃ Finset ℕ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_toFinset_bitIndices_two_pow`：∀ (n : ℕ), ∑ i ∈ n.bitIndices.to
Finset, 2 ^ i = n
· 使用定理 `Finset.toFinset_bitIndices_sum_two_pow`：∀ (s : Finset ℕ), (∑ i ∈ s, 2 ^ 
i).bitIndices.toFinset = s

--- 原说明 ---
The equivalence between `ℕ` and `Finset ℕ` that maps `∑ i ∈ s, 2^i` to `s`.
-/
@[simps] def equivBitIndices : ℕ ≃ Finset ℕ where
  toFun n := n.bitIndices.toFinset
  invFun s := ∑ i ∈ s, 2 ^ i
  left_inv := sum_toFinset_bitIndices_two_pow
  right_inv := toFinset_bitIndices_sum_two_pow

/-- The equivalence `Nat.equivBitIndices` enumerates `Finset ℕ` in colexicographic order. -/
/-
**Finset.orderIsoColex** 是 Mathlib 中的一个定义，位于命名空间 `Finset`。
形式化陈述：ℕ ≃o Colex (Finset ℕ)
参数：Finset ℕ。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The equivalence `Nat.equivBitIndices` enumerates `Finset ℕ` in colexicographic o
rder.
-/
@[simps] def orderIsoColex : ℕ ≃o Colex (Finset ℕ) where
  toFun n := toColex (equivBitIndices n)
  invFun s := equivBitIndices.symm (ofColex s)
  left_inv n := equivBitIndices.symm_apply_apply n
  right_inv s := equivBitIndices.apply_symm_apply _
  map_rel_iff' := by simp [← (Finset.geomSum_le_geomSum_iff_toColex_le_toColex rfl.le)]

end Nat
end Finset

