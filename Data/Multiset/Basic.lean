/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Multiset.ZeroCons

/-!
# Basic results on multisets

-/

@[expose] public section

-- No algebra should be required
assert_not_exists Monoid

universe v

open List Subtype Nat Function

variable {α : Type*} {β : Type v} {γ : Type*}

namespace Multiset

/-! ### `Multiset.toList` -/

section ToList

/-- Produces a list of the elements in the multiset using choice. -/
/-
**Multiset.toList** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：toList (s : Multiset α)
参数：s : Multiset α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces a list of the elements in the multiset using choice.
-/
noncomputable def toList (s : Multiset α) :=
  s.out

@[simp, norm_cast]
/-
**Multiset.coe_toList** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_toList (s : Multiset α) : (s.toList : Multiset α) = s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
-/
theorem coe_toList (s : Multiset α) : (s.toList : Multiset α) = s :=
  s.out_eq'

@[simp]
/-
**Multiset.toList_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toList_eq_nil {s : Multiset α} : s.toList = [] ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_eq_zero`：coe_eq_zero (l : List α) : (l : Multiset α) = 0 ↔ 
l = []
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toList_eq_nil {s : Multiset α} : s.toList = [] ↔ s = 0 := by
  rw [← coe_eq_zero, coe_toList]
/-
**Multiset.empty_toList** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：empty_toList {s : Multiset α} : s.toList.isEmpty ↔ s = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem empty_toList {s : Multiset α} : s.toList.isEmpty ↔ s = 0 := by simp

@[simp]
/-
**Multiset.toList_zero** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toList_zero : (Multiset.toList 0 : List α) = []
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.toList_eq_nil`：toList_eq_nil {s : Multiset α} : s.toList = [] ↔
 s = 0
-/
theorem toList_zero : (Multiset.toList 0 : List α) = [] :=
  toList_eq_nil.mpr rfl

@[simp]
/-
**Multiset.mem_toList** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：mem_toList {a : α} {s : Multiset α} : a in s.toList ↔ a in s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.mem_coe`：mem_coe {a : α} {l : List α} : a in (l : Multiset α) ↔
 a in l
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toList {a : α} {s : Multiset α} : a ∈ s.toList ↔ a ∈ s := by
  rw [← mem_coe, coe_toList]

@[simp]
/-
**Multiset.toList_eq_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toList_eq_singleton_iff {a : α} {m : Multiset α} : m.toList = [a] ↔ m = {a
}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.perm_singleton`：∀ {α : Type u_1} {a : α} {l : List α}, l.Perm [a] ↔
 l = [a]
· 使用定理 `Multiset.coe_eq_coe`：coe_eq_coe {l₁ l₂ : List α} : (l₁ : Multiset α) = l
₂ ↔ l₁ ~ l₂
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
· 使用定理 `Multiset.coe_singleton`：coe_singleton (a : α) : ([a] : Multiset α) = {a}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem toList_eq_singleton_iff {a : α} {m : Multiset α} : m.toList = [a] ↔ m = {a} := by
  rw [← perm_singleton, ← coe_eq_coe, coe_toList, coe_singleton]

@[simp]
/-
**Multiset.toList_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：toList_singleton (a : α) : ({a} : Multiset α).toList = [a]
参数：a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Multiset.toList_eq_singleton_iff`：toList_eq_singleton_iff {a : α} {m : M
ultiset α} : m.toList = [a] ↔ m = {a}
-/
theorem toList_singleton (a : α) : ({a} : Multiset α).toList = [a] :=
  Multiset.toList_eq_singleton_iff.2 rfl

@[simp]
/-
**Multiset.length_toList** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：length_toList (s : Multiset α) : s.toList.length = card s
参数：s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.coe_card`：coe_card (l : List α) : card (l : Multiset α) = lengt
h l
· 使用定理 `Multiset.coe_toList`：coe_toList (s : Multiset α) : (s.toList : Multiset 
α) = s
-/
theorem length_toList (s : Multiset α) : s.toList.length = card s := by
  rw [← coe_card, coe_toList]

end ToList

/-! ### Induction principles -/

/-- The strong induction principle for multisets. -/
@[elab_as_elim]
/-
**Multiset.strongInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：strongInductionOn {p : Multiset α -> Sort*} (s : Multiset α) (ih : forall 
s, (forall t < s, p t) -> p s) : p s
参数：s : Multiset α；ih : forall s, (forall t < s, p t) -> p s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The strong induction principle for multisets.
-/
def strongInductionOn {p : Multiset α → Sort*} (s : Multiset α) (ih : ∀ s, (∀ t < s, p t) → p s) :
    p s :=
    (ih s) fun t _h =>
      strongInductionOn t ih
termination_by card s
decreasing_by exact card_lt_card _h
/-
**Multiset.strongInductionOn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：strongInductionOn_eq {p : Multiset α -> Sort*} (s : Multiset α) (H) : @str
ongInductionOn _ p s H = H s fun t _h => @strongInductionOn _ p t H
参数：s : Multiset α；H。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.strongInductionOn.eq_1`：∀ {α : Type u_1} {p : Multiset α → Sort
 u_3} (s : Multiset α)   (ih : (s : Multiset α) → ((t : Multiset α) → t < s → p 
t) → p s),   s.strong…
-/
theorem strongInductionOn_eq {p : Multiset α → Sort*} (s : Multiset α) (H) :
    @strongInductionOn _ p s H = H s fun t _h => @strongInductionOn _ p t H := by
  rw [strongInductionOn]

@[elab_as_elim]
/-
**Multiset.case_strongInductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：case_strongInductionOn {p : Multiset α -> Prop} (s : Multiset α) (h₀ : p 0
) (h₁ : forall a s, (forall t <= s, p t) -> p (a ::ₘ s)) : p s
参数：s : Multiset α；h₀ : p 0；h₁ : forall a s, (forall t <= s, p t) -> p (a ::ₘ s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.induction_on`：∀ {α : Type u_1} {p : Multiset α → Prop} (s : Mul
tiset α), p 0 → (∀ (a : α) (s : Multiset α), p s → p (a ::ₘ s)) → p s
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Multiset.lt_cons_self`：lt_cons_self (s : Multiset α) (a : α) : s < a ::ₘ
 s
-/
theorem case_strongInductionOn {p : Multiset α → Prop} (s : Multiset α) (h₀ : p 0)
    (h₁ : ∀ a s, (∀ t ≤ s, p t) → p (a ::ₘ s)) : p s :=
  Multiset.strongInductionOn s fun s =>
    Multiset.induction_on s (fun _ => h₀) fun _a _s _ ih =>
      (h₁ _ _) fun _t h => ih _ <| lt_of_le_of_lt h <| lt_cons_self _ _

/-- Suppose that, given that `p t` can be defined on all supersets of `s` of cardinality less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for all multisets `s` of
cardinality less than `n`, starting from multisets of card `n` and iterating. This
can be used either to define data, or to prove properties. -/
/-
**Multiset.strongDownwardInduction** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：strongDownwardInduction {p : Multiset α -> Sort*} {n : Nat} (H : forall t₁
, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) -> card t₁ <= n ->
 p t₁) (s : Multiset α) : card s <= n -> p s
参数：H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) ->
 card t₁ <= n -> p t₁；s : Multiset α。
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Suppose that, given that `p t` can be defined on all supersets of `s` of cardina
lity less than
`n`, one knows how to define `p s`. Then one can inductively define `p s` for al
l multisets `s` of
cardinality less than `n`, starting from multisets of card `n` and iterating. Th
is
can be used either to define data, or to prove properties.
-/
def strongDownwardInduction {p : Multiset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁)
    (s : Multiset α) :
    card s ≤ n → p s :=
  H s fun {t} ht _h =>
    strongDownwardInduction H t ht
termination_by n - card s
decreasing_by have := (card_lt_card _h); lia
/-
**Multiset.strongDownwardInduction_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：strongDownwardInduction_eq {p : Multiset α -> Sort*} {n : Nat} (H : forall
 t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) -> card t₁ <= n
 -> p t₁) (s : Multiset α) : strongDownwardInduction H s = H s fun ht _hst => st
rongDownwardInduction H _ ht
参数：H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p t₂) ->
 card t₁ <= n -> p t₁；s : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.strongDownwardInduction.eq_1`：∀ {α : Type u_1} {p : Multiset α 
→ Sort u_3} {n : ℕ}   (H : (t₁ : Multiset α) → ({t₂ : Multiset α} → t₂.card ≤ n 
→ t₁ < t₂ → p t₂) → t₁.card…
-/
theorem strongDownwardInduction_eq {p : Multiset α → Sort*} {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁)
    (s : Multiset α) :
    strongDownwardInduction H s = H s fun ht _hst => strongDownwardInduction H _ ht := by
  rw [strongDownwardInduction]

/-- Analogue of `strongDownwardInduction` with order of arguments swapped. -/
@[elab_as_elim]
/-
**Multiset.strongDownwardInductionOn** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：strongDownwardInductionOn {p : Multiset α -> Sort*} {n : Nat} : forall s :
 Multiset α, (forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p
 t₂) -> card t₁ <= n -> p t₁) -> card s <= n -> p s
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Analogue of `strongDownwardInduction` with order of arguments swapped.
-/
def strongDownwardInductionOn {p : Multiset α → Sort*} {n : ℕ} :
    ∀ s : Multiset α,
      (∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁) →
        card s ≤ n → p s :=
  fun s H => strongDownwardInduction H s
/-
**Multiset.strongDownwardInductionOn_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：strongDownwardInductionOn_eq {p : Multiset α -> Sort*} (s : Multiset α) {n
 : Nat} (H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ < t₂ -> p 
t₂) -> card t₁ <= n -> p t₁) : s.strongDownwardInductionOn H = H s fun {t} ht _h
 => t.strongDownwardInductionOn H ht
参数：s : Multiset α；H : forall t₁, (forall {t₂ : Multiset α}, card t₂ <= n -> t₁ <
 t₂ -> p t₂) -> card t₁ <= n -> p t₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.strongDownwardInduction.eq_1`：∀ {α : Type u_1} {p : Multiset α 
→ Sort u_3} {n : ℕ}   (H : (t₁ : Multiset α) → ({t₂ : Multiset α} → t₂.card ≤ n 
→ t₁ < t₂ → p t₂) → t₁.card…
-/
theorem strongDownwardInductionOn_eq {p : Multiset α → Sort*} (s : Multiset α) {n : ℕ}
    (H : ∀ t₁, (∀ {t₂ : Multiset α}, card t₂ ≤ n → t₁ < t₂ → p t₂) → card t₁ ≤ n → p t₁) :
    s.strongDownwardInductionOn H = H s fun {t} ht _h => t.strongDownwardInductionOn H ht := by
  dsimp only [strongDownwardInductionOn]
  rw [strongDownwardInduction]

section Choose

variable (p : α → Prop) [DecidablePred p] (l : Multiset α)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `chooseX p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`. -/
/-
**Multiset.chooseX** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：chooseX : forall _hp : exists! a, a in l ∧ p a, { a // a in l ∧ p a }
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `chooseX 
p l hp` returns
that `a` together with proofs of `a ∈ l` and `p a`.
-/
def chooseX : ∀ _hp : ∃! a, a ∈ l ∧ p a, { a // a ∈ l ∧ p a } :=
  Quotient.recOn l (fun l' ex_unique => List.chooseX p l' (ExistsUnique.exists ex_unique))
    (by
      intro a b _
      funext hp
      suffices all_equal : ∀ x y : { t // t ∈ b ∧ p t }, x = y by
        apply all_equal
      rintro ⟨x, px⟩ ⟨y, py⟩
      rcases hp with ⟨z, ⟨_z_mem_l, _pz⟩, z_unique⟩
      congr
      calc
        x = z := z_unique x px
        _ = y := (z_unique y py).symm)

/-- Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p l hp` returns
that `a`. -/
/-
**Multiset.choose** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：choose (hp : exists! a, a in l ∧ p a) : α
参数：hp : exists! a, a in l ∧ p a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a proof `hp` that there exists a unique `a ∈ l` such that `p a`, `choose p
 l hp` returns
that `a`.
-/
def choose (hp : ∃! a, a ∈ l ∧ p a) : α :=
  chooseX p l hp
/-
**Multiset.choose_spec** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：choose_spec (hp : exists! a, a in l ∧ p a) : choose p l hp in l ∧ p (choos
e p l hp)
参数：hp : exists! a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem choose_spec (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l ∧ p (choose p l hp) :=
  (chooseX p l hp).property
/-
**Multiset.choose_mem** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：choose_mem (hp : exists! a, a in l ∧ p a) : choose p l hp in l
参数：hp : exists! a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Multiset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : choos
e p l hp in l ∧ p (choose p l hp)
-/
theorem choose_mem (hp : ∃! a, a ∈ l ∧ p a) : choose p l hp ∈ l :=
  (choose_spec _ _ _).1
/-
**Multiset.choose_property** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：choose_property (hp : exists! a, a in l ∧ p a) : p (choose p l hp)
参数：hp : exists! a, a in l ∧ p a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Multiset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : choos
e p l hp in l ∧ p (choose p l hp)
-/
theorem choose_property (hp : ∃! a, a ∈ l ∧ p a) : p (choose p l hp) :=
  (choose_spec _ _ _).2
/-
**Multiset.choose_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：choose_eq_iff (hp : exists! a, a in l ∧ p a) {a : α} : choose p l hp = a ↔
 a in l ∧ p a
参数：hp : exists! a, a in l ∧ p a。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Multiset.choose_spec`：choose_spec (hp : exists! a, a in l ∧ p a) : choos
e p l hp in l ∧ p (choose p l hp)
· 使用定理 `ExistsUnique.unique`：ExistsUnique.unique {p : α -> Prop} (h : exists! x,
 p x) {y₁ y₂ : α} (py₁ : p y₁) (py₂ : p y₂) : y₁ = y₂
-/
theorem choose_eq_iff (hp : ∃! a, a ∈ l ∧ p a) {a : α} : choose p l hp = a ↔ a ∈ l ∧ p a :=
  ⟨fun h => h ▸ choose_spec p l hp, hp.unique (choose_spec p l hp)⟩

end Choose

variable (α) in
/-- The equivalence between lists and multisets of a subsingleton type. -/
/-
**Multiset.subsingletonEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：subsingletonEquiv [Subsingleton α] : List α ≃ Multiset α where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between lists and multisets of a subsingleton type.
-/
def subsingletonEquiv [Subsingleton α] : List α ≃ Multiset α where
  toFun := ofList
  invFun :=
    (Quot.lift id) fun (a b : List α) (h : a ~ b) =>
      (List.ext_get h.length_eq) fun _ _ _ => Subsingleton.elim _ _
  right_inv m := Quot.inductionOn m fun _ => rfl

@[simp]
/-
**Multiset.coe_subsingletonEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：coe_subsingletonEquiv [Subsingleton α] : (subsingletonEquiv α : List α -> 
Multiset α) = ofList
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subsingletonEquiv [Subsingleton α] :
    (subsingletonEquiv α : List α → Multiset α) = ofList :=
  rfl

end Multiset

