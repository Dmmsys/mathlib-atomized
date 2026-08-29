/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Maximum and minimum of finite sets
-/

@[expose] public section

assert_not_exists IsOrderedMonoid MonoidWithZero

open Function Multiset OrderDual

variable {F α β γ ι κ : Type*}

namespace Finset

/-! ### max and min of finite sets -/

section MaxMin

variable [LinearOrder α]

/--
Definition of `max` / `max` 的定义

English:
definition max
  signature: (s : Finset α)
  body: sup s (↑)

中文:
定义 最大值
  签名: (s : 有限集 α)
  定义体: sup s (↑)
-/
protected def max (s : Finset α) : WithBot α :=
  sup s (↑)

/--
theorem `max_eq_sup_coe` / 定理 `max_eq_sup_coe`

English:
theorem max_eq_sup_coe
  given: {s : Finset α}
  statement: s.max = s.sup (↑)
  proof: rfl

中文:
定理 max_eq_sup_coe
  条件: {s : 有限集 α}
  结论: s.最大值 = s.上确界 (↑)
  证明: rfl
-/
theorem max_eq_sup_coe {s : Finset α} : s.max = s.sup (↑) :=
  rfl

/--
theorem `max_eq_sup_withBot` / 定理 `max_eq_sup_withBot`

English:
theorem max_eq_sup_withBot
  given: (s : Finset α)
  statement: s.max = sup s (↑)
  proof: rfl

@[simp]

中文:
定理 max_eq_sup_withBot
  条件: (s : 有限集 α)
  结论: s.最大值 = 上确界 s (↑)
  证明: rfl

@[simp]
-/
theorem max_eq_sup_withBot (s : Finset α) : s.max = sup s (↑) :=
  rfl

@[simp]
/--
theorem `max_empty` / 定理 `max_empty`

English:
theorem max_empty
  statement: (∅ : Finset α).max = ⊥
  proof: rfl

@[simp, grind =]

中文:
定理 max_empty
  结论: (∅ : 有限集 α).最大值 = ⊥
  证明: rfl

@[simp, grind =]
-/
theorem max_empty : (∅ : Finset α).max = ⊥ :=
  rfl

@[simp, grind =]
/--
theorem `max_insert` / 定理 `max_insert`

English:
theorem max_insert
  given: {a : α} {s : Finset α}
  statement: (insert a s).max = max ↑a s.max
  proof: fold_insert_idem

@[simp]

中文:
定理 max_insert
  条件: {a : α} {s : 有限集 α}
  结论: (insert a s).最大值 = 最大值 ↑a s.最大值
  证明: fold_insert_idem

@[simp]

Depends on / 依赖: fold_insert_idem
-/
theorem max_insert {a : α} {s : Finset α} : (insert a s).max = max ↑a s.max :=
  fold_insert_idem

@[simp]
/--
theorem `max_singleton` / 定理 `max_singleton`

English:
theorem max_singleton
  given: {a : α}
  statement: Finset.max {a} = (a : WithBot α)
  proof: by
  rw [← insert_empty_eq]
  exact max_insert

中文:
定理 max_singleton
  条件: {a : α}
  结论: 有限集.最大值 {a} = (a : WithBot α)
  证明: by
  rw [← insert_empty_eq]
  exact max_insert

Depends on / 依赖: insert_empty_eq, max_insert
-/
theorem max_singleton {a : α} : Finset.max {a} = (a : WithBot α) := by
  rw [← insert_empty_eq]
  exact max_insert

/--
lemma `max_pair` / 引理 `max_pair`

English:
lemma max_pair
  given: (a b : α)
  proof: by
  simp

中文:
引理 max_pair
  条件: (a b : α)
  证明: by
  simp
-/
lemma max_pair (a b : α) :
    Finset.max {a, b} = max (↑a) (↑b) := by
  simp

/--
theorem `max_of_mem` / 定理 `max_of_mem`

English:
theorem max_of_mem
  given: {s : Finset α} {a : α} (h : a in s)
  statement: exists b : α, s.max = b
  proof: let ⟨b, h, _⟩ := WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) _ rfl; ⟨b, h⟩

中文:
定理 max_of_mem
  条件: {s : 有限集 α} {a : α} (h : a in s)
  结论: 存在 b : α, s.最大值 = b
  证明: let ⟨b, h, _⟩ := WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) _ rfl; ⟨b, h⟩

Depends on / 依赖: WithBot, WithBot.le_iff_forall, le_iff_forall, le_sup
-/
theorem max_of_mem {s : Finset α} {a : α} (h : a in s) : exists b : α, s.max = b :=
  let ⟨b, h, _⟩ := WithBot.le_iff_forall.1 (le_sup (α := WithBot α) h) _ rfl; ⟨b, h⟩

/--
theorem `max_of_nonempty` / 定理 `max_of_nonempty`

English:
theorem max_of_nonempty
  given: {s : Finset α} (h : s.Nonempty)
  statement: exists a : α, s.max = a
  proof: let ⟨_, h⟩ := h
  max_of_mem h

中文:
定理 max_of_nonempty
  条件: {s : 有限集 α} (h : s.非空)
  结论: 存在 a : α, s.最大值 = a
  证明: let ⟨_, h⟩ := h
  max_of_mem h

Depends on / 依赖: max_of_mem
-/
theorem max_of_nonempty {s : Finset α} (h : s.Nonempty) : exists a : α, s.max = a :=
  let ⟨_, h⟩ := h
  max_of_mem h

/--
theorem `max_eq_bot` / 定理 `max_eq_bot`

English:
theorem max_eq_bot
  given: {s : Finset α}
  statement: s.max = ⊥ ↔ s = ∅
  proof: ⟨fun h => s.eq_empty_or_nonempty.elim id fun H => by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha; cases ha; , -- the `;` is needed since the `cases` syntax allows `cases a, b`
    fun h => h.symm ▸ max_empty⟩

中文:
定理 max_eq_bot
  条件: {s : 有限集 α}
  结论: s.最大值 = ⊥ ↔ s = ∅
  证明: ⟨fun h => s.eq_empty_or_nonempty.elim id fun H => by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha; cases ha; , -- the `;` is needed since the `cases` syntax allows `cases a, b`
    fun h => h.symm ▸ max_empty⟩

Depends on / 依赖: allows, eq_empty_or_nonempty, h.symm, max_empty, max_of_nonempty, needed, s.eq_empty_or_nonempty.elim, syntax
-/
theorem max_eq_bot {s : Finset α} : s.max = ⊥ ↔ s = ∅ :=
  ⟨fun h => s.eq_empty_or_nonempty.elim id fun H => by
      obtain ⟨a, ha⟩ := max_of_nonempty H
      rw [h] at ha; cases ha; , -- the `;` is needed since the `cases` syntax allows `cases a, b`
    fun h => h.symm ▸ max_empty⟩

/--
theorem `mem_of_max` / 定理 `mem_of_max`

English:
theorem mem_of_max
  given: {s : Finset α}
  statement: forall {a : α}, s.max = a -> a in s
  proof: by
  induction s using Finset.induction_on with
  | empty => intro _ H; cases H
  | _ => grind [WithBot.coe_eq_coe]

中文:
定理 mem_of_max
  条件: {s : 有限集 α}
  结论: 对任意 {a : α}, s.最大值 = a -> a in s
  证明: by
  induction s using Finset.induction_on with
  | empty => intro _ H; cases H
  | _ => grind [WithBot.coe_eq_coe]

Depends on / 依赖: Finset, Finset.induction_on, WithBot, WithBot.coe_eq_coe, coe_eq_coe, induction_on
-/
theorem mem_of_max {s : Finset α} : forall {a : α}, s.max = a -> a in s := by
  induction s using Finset.induction_on with
  | empty => intro _ H; cases H
  | _ => grind [WithBot.coe_eq_coe]

/--
theorem `le_max` / 定理 `le_max`

English:
theorem le_max
  given: {a : α} {s : Finset α} (as : a in s)
  statement: ↑a <= s.max
  proof: le_sup as

中文:
定理 le_max
  条件: {a : α} {s : 有限集 α} (as : a in s)
  结论: ↑a <= s.最大值
  证明: le_sup as

Depends on / 依赖: le_sup
-/
theorem le_max {a : α} {s : Finset α} (as : a in s) : ↑a <= s.max :=
  le_sup as

/--
theorem `notMem_of_max_lt_coe` / 定理 `notMem_of_max_lt_coe`

English:
theorem notMem_of_max_lt_coe
  given: {a : α} {s : Finset α} (h : s.max < a)
  statement: a ∉ s
  proof: mt le_max h.not_ge

中文:
定理 notMem_of_max_lt_coe
  条件: {a : α} {s : 有限集 α} (h : s.最大值 < a)
  结论: a ∉ s
  证明: mt le_max h.not_ge

Depends on / 依赖: h.not_ge, le_max, not_ge
-/
theorem notMem_of_max_lt_coe {a : α} {s : Finset α} (h : s.max < a) : a ∉ s :=
  mt le_max h.not_ge

/--
theorem `le_max_of_eq` / 定理 `le_max_of_eq`

English:
theorem le_max_of_eq
  given: {s : Finset α} {a b : α} (h₁ : a in s) (h₂ : s.max = b)
  statement: a <= b
  proof: WithBot.coe_le_coe.mp (le_max h₁).trans h₂.le

中文:
定理 le_max_of_eq
  条件: {s : 有限集 α} {a b : α} (h₁ : a in s) (h₂ : s.最大值 = b)
  结论: a <= b
  证明: WithBot.coe_le_coe.mp (le_max h₁).trans h₂.le

Depends on / 依赖: WithBot, WithBot.coe_le_coe.mp, coe_le_coe, le_max
-/
theorem le_max_of_eq {s : Finset α} {a b : α} (h₁ : a in s) (h₂ : s.max = b) : a <= b :=
WithBot.coe_le_coe.mp (le_max h₁).trans h₂.le

/--
theorem `notMem_of_max_lt` / 定理 `notMem_of_max_lt`

English:
theorem notMem_of_max_lt
  given: {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b)
  statement: a ∉ s
  proof: Finset.notMem_of_max_lt_coe h₂.trans_lt WithBot.coe_lt_coe.mpr h₁

中文:
定理 notMem_of_max_lt
  条件: {s : 有限集 α} {a b : α} (h₁ : b < a) (h₂ : s.最大值 = ↑b)
  结论: a ∉ s
  证明: Finset.notMem_of_max_lt_coe h₂.trans_lt WithBot.coe_lt_coe.mpr h₁

Depends on / 依赖: Finset, Finset.notMem_of_max_lt_coe, WithBot, WithBot.coe_lt_coe.mpr, coe_lt_coe, notMem_of_max_lt_coe, trans_lt
-/
theorem notMem_of_max_lt {s : Finset α} {a b : α} (h₁ : b < a) (h₂ : s.max = ↑b) : a ∉ s :=
Finset.notMem_of_max_lt_coe h₂.trans_lt WithBot.coe_lt_coe.mpr h₁

/--
theorem `max_union` / 定理 `max_union`

English:
theorem max_union
  given: {s t : Finset α}
  statement: (s union t).max = s.max ⊔ t.max
  proof: sup_union

@[gcongr]

中文:
定理 max_union
  条件: {s t : 有限集 α}
  结论: (s union t).最大值 = s.最大值 ⊔ t.最大值
  证明: sup_union

@[gcongr]

Depends on / 依赖: sup_union
-/
theorem max_union {s t : Finset α} : (s union t).max = s.max ⊔ t.max := sup_union

@[gcongr]
/--
theorem `max_mono` / 定理 `max_mono`

English:
theorem max_mono
  given: {s t : Finset α} (st : s subseteq t)
  statement: s.max <= t.max
  proof: sup_mono st

中文:
定理 max_mono
  条件: {s t : 有限集 α} (st : s subseteq t)
  结论: s.最大值 <= t.最大值
  证明: sup_mono st

Depends on / 依赖: sup_mono
-/
theorem max_mono {s t : Finset α} (st : s subseteq t) : s.max <= t.max :=
  sup_mono st

/--
theorem `max_le` / 定理 `max_le`

English:
theorem max_le
  given: {M : WithBot α} {s : Finset α} (st : forall a in s, (a : WithBot α) <= M)
  proof: Finset.sup_le st

@[simp]

中文:
定理 max_le
  条件: {M : WithBot α} {s : 有限集 α} (st : 对任意 a in s, (a : WithBot α) <= M)
  证明: Finset.sup_le st

@[simp]
-/
protected theorem max_le {M : WithBot α} {s : Finset α} (st : forall a in s, (a : WithBot α) <= M) :
    s.max <= M :=
  Finset.sup_le st

@[simp]
/--
lemma `max_le_iff` / 引理 `max_le_iff`

English:
lemma max_le_iff
  given: {m : WithBot α} {s : Finset α}
  statement: s.max <= m ↔ forall a in s, a <= m
  proof: Finset.sup_le_iff

@[simp]

中文:
引理 max_le_iff
  条件: {m : WithBot α} {s : 有限集 α}
  结论: s.最大值 <= m ↔ 对任意 a in s, a <= m
  证明: Finset.sup_le_iff

@[simp]
-/
protected lemma max_le_iff {m : WithBot α} {s : Finset α} : s.max <= m ↔ forall a in s, a <= m :=
  Finset.sup_le_iff

@[simp]
/--
lemma `max_eq_top` / 引理 `max_eq_top`

English:
lemma max_eq_top
  given: [OrderTop α] {s : Finset α}
  statement: s.max = ⊤ ↔ ⊤ in s
  proof: Finset.sup_eq_top_iff.trans by simp

中文:
引理 max_eq_top
  条件: [有顶序 α] {s : 有限集 α}
  结论: s.最大值 = ⊤ ↔ ⊤ in s
  证明: Finset.sup_eq_top_iff.trans by simp
-/
protected lemma max_eq_top [OrderTop α] {s : Finset α} : s.max = ⊤ ↔ ⊤ in s :=
Finset.sup_eq_top_iff.trans by simp

/--
Definition of `min` / `min` 的定义

English:
definition min
  signature: (s : Finset α)
  body: inf s (↑)

中文:
定义 最小值
  签名: (s : 有限集 α)
  定义体: inf s (↑)
-/
protected def min (s : Finset α) : WithTop α :=
  inf s (↑)

/--
theorem `min_eq_inf_withTop` / 定理 `min_eq_inf_withTop`

English:
theorem min_eq_inf_withTop
  given: (s : Finset α)
  statement: s.min = inf s (↑)
  proof: rfl

@[simp]

中文:
定理 min_eq_inf_withTop
  条件: (s : 有限集 α)
  结论: s.最小值 = 下确界 s (↑)
  证明: rfl

@[simp]
-/
theorem min_eq_inf_withTop (s : Finset α) : s.min = inf s (↑) :=
  rfl

@[simp]
/--
theorem `min_empty` / 定理 `min_empty`

English:
theorem min_empty
  statement: (∅ : Finset α).min = ⊤
  proof: rfl

@[simp]

中文:
定理 min_empty
  结论: (∅ : 有限集 α).最小值 = ⊤
  证明: rfl

@[simp]
-/
theorem min_empty : (∅ : Finset α).min = ⊤ :=
  rfl

@[simp]
/--
theorem `min_insert` / 定理 `min_insert`

English:
theorem min_insert
  given: {a : α} {s : Finset α}
  statement: (insert a s).min = min (↑a) s.min
  proof: fold_insert_idem

@[simp]

中文:
定理 min_insert
  条件: {a : α} {s : 有限集 α}
  结论: (insert a s).最小值 = 最小值 (↑a) s.最小值
  证明: fold_insert_idem

@[simp]

Depends on / 依赖: fold_insert_idem
-/
theorem min_insert {a : α} {s : Finset α} : (insert a s).min = min (↑a) s.min :=
  fold_insert_idem

@[simp]
/--
theorem `min_singleton` / 定理 `min_singleton`

English:
theorem min_singleton
  given: {a : α}
  statement: Finset.min {a} = (a : WithTop α)
  proof: by
  rw [← insert_empty_eq]
  exact min_insert

中文:
定理 min_singleton
  条件: {a : α}
  结论: 有限集.最小值 {a} = (a : WithTop α)
  证明: by
  rw [← insert_empty_eq]
  exact min_insert

Depends on / 依赖: insert_empty_eq, min_insert
-/
theorem min_singleton {a : α} : Finset.min {a} = (a : WithTop α) := by
  rw [← insert_empty_eq]
  exact min_insert

/--
lemma `min_pair` / 引理 `min_pair`

English:
lemma min_pair
  given: (a b : α)
  proof: by
  simp

中文:
引理 min_pair
  条件: (a b : α)
  证明: by
  simp
-/
lemma min_pair (a b : α) :
    Finset.min {a, b} = min (↑a) (↑b) := by
  simp

/--
theorem `min_of_mem` / 定理 `min_of_mem`

English:
theorem min_of_mem
  given: {s : Finset α} {a : α} (h : a in s)
  statement: exists b : α, s.min = b
  proof: let ⟨b, h, _⟩ := WithTop.le_iff_forall.1 (inf_le (α := WithTop α) h) _ rfl; ⟨b, h⟩

中文:
定理 min_of_mem
  条件: {s : 有限集 α} {a : α} (h : a in s)
  结论: 存在 b : α, s.最小值 = b
  证明: let ⟨b, h, _⟩ := WithTop.le_iff_forall.1 (inf_le (α := WithTop α) h) _ rfl; ⟨b, h⟩

Depends on / 依赖: WithTop, WithTop.le_iff_forall, inf_le, le_iff_forall
-/
theorem min_of_mem {s : Finset α} {a : α} (h : a in s) : exists b : α, s.min = b :=
  let ⟨b, h, _⟩ := WithTop.le_iff_forall.1 (inf_le (α := WithTop α) h) _ rfl; ⟨b, h⟩

/--
theorem `min_of_nonempty` / 定理 `min_of_nonempty`

English:
theorem min_of_nonempty
  given: {s : Finset α} (h : s.Nonempty)
  statement: exists a : α, s.min = a
  proof: let ⟨_, h⟩ := h
  min_of_mem h

@[simp]

中文:
定理 min_of_nonempty
  条件: {s : 有限集 α} (h : s.非空)
  结论: 存在 a : α, s.最小值 = a
  证明: let ⟨_, h⟩ := h
  min_of_mem h

@[simp]

Depends on / 依赖: min_of_mem
-/
theorem min_of_nonempty {s : Finset α} (h : s.Nonempty) : exists a : α, s.min = a :=
  let ⟨_, h⟩ := h
  min_of_mem h

@[simp]
/--
theorem `min_eq_top` / 定理 `min_eq_top`

English:
theorem min_eq_top
  given: {s : Finset α}
  statement: s.min = ⊤ ↔ s = ∅
  proof: by
  simp [Finset.min, eq_empty_iff_forall_notMem]

中文:
定理 min_eq_top
  条件: {s : 有限集 α}
  结论: s.最小值 = ⊤ ↔ s = ∅
  证明: by
  simp [Finset.min, eq_empty_iff_forall_notMem]

Depends on / 依赖: Finset, Finset.min, eq_empty_iff_forall_notMem
-/
theorem min_eq_top {s : Finset α} : s.min = ⊤ ↔ s = ∅ := by
  simp [Finset.min, eq_empty_iff_forall_notMem]

/--
theorem `mem_of_min` / 定理 `mem_of_min`

English:
theorem mem_of_min
  given: {s : Finset α}
  statement: forall {a : α}, s.min = a -> a in s
  proof: @mem_of_max αᵒᵈ _ s

中文:
定理 mem_of_min
  条件: {s : 有限集 α}
  结论: 对任意 {a : α}, s.最小值 = a -> a in s
  证明: @mem_of_max αᵒᵈ _ s

Depends on / 依赖: mem_of_max
-/
theorem mem_of_min {s : Finset α} : forall {a : α}, s.min = a -> a in s :=
  @mem_of_max αᵒᵈ _ s

/--
theorem `min_le` / 定理 `min_le`

English:
theorem min_le
  given: {a : α} {s : Finset α} (as : a in s)
  statement: s.min <= a
  proof: inf_le as

中文:
定理 min_le
  条件: {a : α} {s : 有限集 α} (as : a in s)
  结论: s.最小值 <= a
  证明: inf_le as

Depends on / 依赖: inf_le
-/
theorem min_le {a : α} {s : Finset α} (as : a in s) : s.min <= a :=
  inf_le as

/--
theorem `notMem_of_coe_lt_min` / 定理 `notMem_of_coe_lt_min`

English:
theorem notMem_of_coe_lt_min
  given: {a : α} {s : Finset α} (h : ↑a < s.min)
  statement: a ∉ s
  proof: mt min_le h.not_ge

中文:
定理 notMem_of_coe_lt_min
  条件: {a : α} {s : 有限集 α} (h : ↑a < s.最小值)
  结论: a ∉ s
  证明: mt min_le h.not_ge

Depends on / 依赖: h.not_ge, min_le, not_ge
-/
theorem notMem_of_coe_lt_min {a : α} {s : Finset α} (h : ↑a < s.min) : a ∉ s :=
  mt min_le h.not_ge

/--
theorem `min_le_of_eq` / 定理 `min_le_of_eq`

English:
theorem min_le_of_eq
  given: {s : Finset α} {a b : α} (h₁ : b in s) (h₂ : s.min = a)
  statement: a <= b
  proof: WithTop.coe_le_coe.mp h₂.ge.trans (min_le h₁)

中文:
定理 min_le_of_eq
  条件: {s : 有限集 α} {a b : α} (h₁ : b in s) (h₂ : s.最小值 = a)
  结论: a <= b
  证明: WithTop.coe_le_coe.mp h₂.ge.trans (min_le h₁)

Depends on / 依赖: WithTop, WithTop.coe_le_coe.mp, coe_le_coe, ge.trans, min_le
-/
theorem min_le_of_eq {s : Finset α} {a b : α} (h₁ : b in s) (h₂ : s.min = a) : a <= b :=
WithTop.coe_le_coe.mp h₂.ge.trans (min_le h₁)

/--
theorem `notMem_of_lt_min` / 定理 `notMem_of_lt_min`

English:
theorem notMem_of_lt_min
  given: {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b)
  statement: a ∉ s
  proof: Finset.notMem_of_coe_lt_min (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm

中文:
定理 notMem_of_lt_min
  条件: {s : 有限集 α} {a b : α} (h₁ : a < b) (h₂ : s.最小值 = ↑b)
  结论: a ∉ s
  证明: Finset.notMem_of_coe_lt_min (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm

Depends on / 依赖: Finset, Finset.notMem_of_coe_lt_min, WithTop, WithTop.coe_lt_coe.mpr, coe_lt_coe, notMem_of_coe_lt_min, trans_eq
-/
theorem notMem_of_lt_min {s : Finset α} {a b : α} (h₁ : a < b) (h₂ : s.min = ↑b) : a ∉ s :=
Finset.notMem_of_coe_lt_min (WithTop.coe_lt_coe.mpr h₁).trans_eq h₂.symm

/--
theorem `min_union` / 定理 `min_union`

English:
theorem min_union
  given: {s t : Finset α}
  statement: (s union t).min = s.min ⊓ t.min
  proof: inf_union

@[gcongr]

中文:
定理 min_union
  条件: {s t : 有限集 α}
  结论: (s union t).最小值 = s.最小值 ⊓ t.最小值
  证明: inf_union

@[gcongr]

Depends on / 依赖: inf_union
-/
theorem min_union {s t : Finset α} : (s union t).min = s.min ⊓ t.min := inf_union

@[gcongr]
/--
theorem `min_mono` / 定理 `min_mono`

English:
theorem min_mono
  given: {s t : Finset α} (st : s subseteq t)
  statement: t.min <= s.min
  proof: inf_mono st

中文:
定理 min_mono
  条件: {s t : 有限集 α} (st : s subseteq t)
  结论: t.最小值 <= s.最小值
  证明: inf_mono st

Depends on / 依赖: inf_mono
-/
theorem min_mono {s t : Finset α} (st : s subseteq t) : t.min <= s.min :=
  inf_mono st

/--
theorem `le_min` / 定理 `le_min`

English:
theorem le_min
  given: {m : WithTop α} {s : Finset α} (st : forall a : α, a in s -> m <= a)
  statement: m <= s.min
  proof: Finset.le_inf st

@[simp]

中文:
定理 le_min
  条件: {m : WithTop α} {s : 有限集 α} (st : 对任意 a : α, a in s -> m <= a)
  结论: m <= s.最小值
  证明: Finset.le_inf st

@[simp]
-/
protected theorem le_min {m : WithTop α} {s : Finset α} (st : forall a : α, a in s -> m <= a) : m <= s.min :=
  Finset.le_inf st

@[simp]
/--
theorem `le_min_iff` / 定理 `le_min_iff`

English:
theorem le_min_iff
  given: {m : WithTop α} {s : Finset α}
  statement: m <= s.min ↔ forall a in s, m <= a
  proof: Finset.le_inf_iff

@[simp]

中文:
定理 le_min_iff
  条件: {m : WithTop α} {s : 有限集 α}
  结论: m <= s.最小值 ↔ 对任意 a in s, m <= a
  证明: Finset.le_inf_iff

@[simp]
-/
protected theorem le_min_iff {m : WithTop α} {s : Finset α} : m <= s.min ↔ forall a in s, m <= a :=
  Finset.le_inf_iff

@[simp]
/--
theorem `min_eq_bot` / 定理 `min_eq_bot`

English:
theorem min_eq_bot
  given: [OrderBot α] {s : Finset α}
  statement: s.min = ⊥ ↔ ⊥ in s
  proof: Finset.max_eq_top (α := αᵒᵈ)

中文:
定理 min_eq_bot
  条件: [有底序 α] {s : 有限集 α}
  结论: s.最小值 = ⊥ ↔ ⊥ in s
  证明: Finset.max_eq_top (α := αᵒᵈ)
-/
protected theorem min_eq_bot [OrderBot α] {s : Finset α} : s.min = ⊥ ↔ ⊥ in s :=
  Finset.max_eq_top (α := αᵒᵈ)

/--
Definition of `min'` / `min'` 的定义

English:
definition min'
  signature: (s : Finset α) (H : s.Nonempty)
  body: inf' s H id

中文:
定义 最小值'
  签名: (s : 有限集 α) (H : s.非空)
  定义体: inf' s H id
-/
def min' (s : Finset α) (H : s.Nonempty) : α :=
  inf' s H id

/--
Definition of `max'` / `max'` 的定义

English:
definition max'
  signature: (s : Finset α) (H : s.Nonempty)
  body: sup' s H id

中文:
定义 最大值'
  签名: (s : 有限集 α) (H : s.非空)
  定义体: sup' s H id
-/
def max' (s : Finset α) (H : s.Nonempty) : α :=
  sup' s H id

variable (s : Finset α) (H : s.Nonempty) {x : α}

/--
theorem `min'_mem` / 定理 `min'_mem`

English:
theorem min'_mem
  statement: s.min' H in s
  proof: mem_of_min by simp only [Finset.min, min', id_eq, coe_inf', Function.comp_def]

中文:
定理 最小值'_mem
  结论: s.最小值' H in s
  证明: mem_of_min by simp only [Finset.min, min', id_eq, coe_inf', Function.comp_def]
-/
theorem min'_mem : s.min' H in s :=
mem_of_min by simp only [Finset.min, min', id_eq, coe_inf', Function.comp_def]

/--
theorem `min'_le` / 定理 `min'_le`

English:
theorem min'_le
  given: (x) (H2 : x in s)
  statement: s.min' ⟨x, H2⟩ <= x
  proof: min_le_of_eq H2 (WithTop.coe_untop _ _).symm

中文:
定理 最小值'_le
  条件: (x) (H2 : x in s)
  结论: s.最小值' ⟨x, H2⟩ <= x
  证明: min_le_of_eq H2 (WithTop.coe_untop _ _).symm
-/
theorem min'_le (x) (H2 : x in s) : s.min' ⟨x, H2⟩ <= x :=
  min_le_of_eq H2 (WithTop.coe_untop _ _).symm

/--
theorem `le_min'` / 定理 `le_min'`

English:
theorem le_min'
  given: (x) (H2 : forall y in s, x <= y)
  statement: x <= s.min' H
  proof: H2 _ min'_mem _ _

中文:
定理 le_min'
  条件: (x) (H2 : 对任意 y in s, x <= y)
  结论: x <= s.最小值' H
  证明: H2 _ min'_mem _ _

Depends on / 依赖: _mem
-/
theorem le_min' (x) (H2 : forall y in s, x <= y) : x <= s.min' H :=
H2 _ min'_mem _ _

/--
theorem `isLeast_min'` / 定理 `isLeast_min'`

English:
theorem isLeast_min'
  statement: IsLeast (↑s) (s.min' H)
  proof: ⟨min'_mem _ _, min'_le _⟩

@[simp]

中文:
定理 isLeast_min'
  结论: IsLeast (↑s) (s.最小值' H)
  证明: ⟨min'_mem _ _, min'_le _⟩

@[simp]

Depends on / 依赖: _mem
-/
theorem isLeast_min' : IsLeast (↑s) (s.min' H) :=
  ⟨min'_mem _ _, min'_le _⟩

@[simp]
/--
theorem `le_min'_iff` / 定理 `le_min'_iff`

English:
theorem le_min'_iff
  given: {x}
  statement: x <= s.min' H ↔ forall y in s, x <= y
  proof: le_isGLB_iff (isLeast_min' s H).isGLB

中文:
定理 le_min'_iff
  条件: {x}
  结论: x <= s.最小值' H ↔ 对任意 y in s, x <= y
  证明: le_isGLB_iff (isLeast_min' s H).isGLB
-/
theorem le_min'_iff {x} : x <= s.min' H ↔ forall y in s, x <= y :=
  le_isGLB_iff (isLeast_min' s H).isGLB

/-- `{a}.min' _` is `a`. -/
@[simp]
/--
theorem `min'_singleton` / 定理 `min'_singleton`

English:
theorem min'_singleton
  given: (a : α)
  statement: ({a} : Finset α).min' (singleton_nonempty _) = a
  proof: by simp [min']

中文:
定理 最小值'_singleton
  条件: (a : α)
  结论: ({a} : 有限集 α).最小值' (singleton_nonempty _) = a
  证明: by simp [min']
-/
theorem min'_singleton (a : α) : ({a} : Finset α).min' (singleton_nonempty _) = a := by simp [min']

/--
theorem `max'_mem` / 定理 `max'_mem`

English:
theorem max'_mem
  statement: s.max' H in s
  proof: mem_of_max by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

中文:
定理 最大值'_mem
  结论: s.最大值' H in s
  证明: mem_of_max by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]
-/
theorem max'_mem : s.max' H in s :=
mem_of_max by simp only [max', Finset.max, id_eq, coe_sup', Function.comp_def]

/--
theorem `le_max'` / 定理 `le_max'`

English:
theorem le_max'
  given: (x) (H2 : x in s)
  statement: x <= s.max' ⟨x, H2⟩
  proof: le_max_of_eq H2 (WithBot.coe_unbot _ _).symm

中文:
定理 le_max'
  条件: (x) (H2 : x in s)
  结论: x <= s.最大值' ⟨x, H2⟩
  证明: le_max_of_eq H2 (WithBot.coe_unbot _ _).symm

Depends on / 依赖: WithBot, WithBot.coe_unbot, coe_unbot, le_max_of_eq
-/
theorem le_max' (x) (H2 : x in s) : x <= s.max' ⟨x, H2⟩ :=
  le_max_of_eq H2 (WithBot.coe_unbot _ _).symm

/--
theorem `max'_le` / 定理 `max'_le`

English:
theorem max'_le
  given: (x) (H2 : forall y in s, y <= x)
  statement: s.max' H <= x
  proof: H2 _ max'_mem _ _

中文:
定理 最大值'_le
  条件: (x) (H2 : 对任意 y in s, y <= x)
  结论: s.最大值' H <= x
  证明: H2 _ max'_mem _ _
-/
theorem max'_le (x) (H2 : forall y in s, y <= x) : s.max' H <= x :=
H2 _ max'_mem _ _

/--
theorem `isGreatest_max'` / 定理 `isGreatest_max'`

English:
theorem isGreatest_max'
  statement: IsGreatest (↑s) (s.max' H)
  proof: ⟨max'_mem _ _, le_max' _⟩

@[simp]

中文:
定理 isGreatest_max'
  结论: IsGreatest (↑s) (s.最大值' H)
  证明: ⟨max'_mem _ _, le_max' _⟩

@[simp]

Depends on / 依赖: _mem, le_max
-/
theorem isGreatest_max' : IsGreatest (↑s) (s.max' H) :=
  ⟨max'_mem _ _, le_max' _⟩

@[simp]
/--
theorem `max'_le_iff` / 定理 `max'_le_iff`

English:
theorem max'_le_iff
  given: {x}
  statement: s.max' H <= x ↔ forall y in s, y <= x
  proof: isLUB_le_iff (isGreatest_max' s H).isLUB

@[simp]

中文:
定理 最大值'_le_iff
  条件: {x}
  结论: s.最大值' H <= x ↔ 对任意 y in s, y <= x
  证明: isLUB_le_iff (isGreatest_max' s H).isLUB

@[simp]
-/
theorem max'_le_iff {x} : s.max' H <= x ↔ forall y in s, y <= x :=
  isLUB_le_iff (isGreatest_max' s H).isLUB

@[simp]
/--
theorem `max'_lt_iff` / 定理 `max'_lt_iff`

English:
theorem max'_lt_iff
  given: {x}
  statement: s.max' H < x ↔ forall y in s, y < x
  proof: ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ s.max'_mem _⟩

@[simp]

中文:
定理 最大值'_lt_iff
  条件: {x}
  结论: s.最大值' H < x ↔ 对任意 y in s, y < x
  证明: ⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ s.max'_mem _⟩

@[simp]
-/
theorem max'_lt_iff {x} : s.max' H < x ↔ forall y in s, y < x :=
⟨fun Hlt y hy => (s.le_max' y hy).trans_lt Hlt, fun H => H _ s.max'_mem _⟩

@[simp]
/--
theorem `lt_min'_iff` / 定理 `lt_min'_iff`

English:
theorem lt_min'_iff
  statement: x < s.min' H ↔ forall y in s, x < y
  proof: @max'_lt_iff αᵒᵈ _ _ H _

中文:
定理 lt_min'_iff
  结论: x < s.最小值' H ↔ 对任意 y in s, x < y
  证明: @max'_lt_iff αᵒᵈ _ _ H _

Depends on / 依赖: _lt_iff
-/
theorem lt_min'_iff : x < s.min' H ↔ forall y in s, x < y :=
  @max'_lt_iff αᵒᵈ _ _ H _

/--
theorem `max'_eq_sup'` / 定理 `max'_eq_sup'`

English:
theorem max'_eq_sup'
  statement: s.max' H = s.sup' H id
  proof: rfl

中文:
定理 最大值'_eq_sup'
  结论: s.最大值' H = s.上确界' H id
  证明: rfl
-/
theorem max'_eq_sup' : s.max' H = s.sup' H id := rfl

/--
theorem `min'_eq_inf'` / 定理 `min'_eq_inf'`

English:
theorem min'_eq_inf'
  statement: s.min' H = s.inf' H id
  proof: rfl

中文:
定理 最小值'_eq_inf'
  结论: s.最小值' H = s.下确界' H id
  证明: rfl
-/
theorem min'_eq_inf' : s.min' H = s.inf' H id := rfl

/-- `{a}.max' _` is `a`. -/
@[simp]
/--
theorem `max'_singleton` / 定理 `max'_singleton`

English:
theorem max'_singleton
  given: (a : α)
  statement: ({a} : Finset α).max' (singleton_nonempty _) = a
  proof: by simp [max']

中文:
定理 最大值'_singleton
  条件: (a : α)
  结论: ({a} : 有限集 α).最大值' (singleton_nonempty _) = a
  证明: by simp [max']
-/
theorem max'_singleton (a : α) : ({a} : Finset α).max' (singleton_nonempty _) = a := by simp [max']

/--
lemma `min'_eq_iff` / 引理 `min'_eq_iff`

English:
lemma min'_eq_iff
  given: (a : α)
  statement: s.min' H = a ↔ a in s ∧ forall (b : α), b in s -> a <= b
  proof: ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩), fun h => le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩

中文:
引理 最小值'_eq_iff
  条件: (a : α)
  结论: s.最小值' H = a ↔ a in s ∧ 对任意 (b : α), b in s -> a <= b
  证明: ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩), fun h => le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩

Depends on / 依赖: dvd_mul, pp.dvd_mul
-/
lemma min'_eq_iff (a : α) : s.min' H = a ↔ a in s ∧ forall (b : α), b in s -> a <= b :=
  ⟨(· ▸ ⟨min'_mem _ _, min'_le _⟩), fun h => le_antisymm (min'_le _ _ h.1) (le_min' _ _ _ h.2)⟩

/--
lemma `max'_eq_iff` / 引理 `max'_eq_iff`

English:
lemma max'_eq_iff
  given: (a : α)
  statement: s.max' H = a ↔ a in s ∧ forall (b : α), b in s -> b <= a
  proof: ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩), fun h => le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩

中文:
引理 最大值'_eq_iff
  条件: (a : α)
  结论: s.最大值' H = a ↔ a in s ∧ 对任意 (b : α), b in s -> b <= a
  证明: ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩), fun h => le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩

Depends on / 依赖: dvd_of_dvd_pow, pp.prime.dvd_of_dvd_pow
-/
lemma max'_eq_iff (a : α) : s.max' H = a ↔ a in s ∧ forall (b : α), b in s -> b <= a :=
  ⟨(· ▸ ⟨max'_mem _ _, le_max' _⟩), fun h => le_antisymm (max'_le _ _ _ h.2) (le_max' _ _ h.1)⟩

/--
theorem `min'_le_max'` / 定理 `min'_le_max'`

English:
theorem min'_le_max'
  given: (hs : s.Nonempty)
  statement: s.min' hs <= s.max' hs
  proof: min'_le _ _ (max'_mem _ _)

中文:
定理 最小值'_le_max'
  条件: (hs : s.非空)
  结论: s.最小值' hs <= s.最大值' hs
  证明: min'_le _ _ (max'_mem _ _)
-/
theorem min'_le_max' (hs : s.Nonempty) : s.min' hs <= s.max' hs := min'_le _ _ (max'_mem _ _)

/--
theorem `min'_lt_max'` / 定理 `min'_lt_max'`

English:
theorem min'_lt_max'
  given: {i j} (H1 : i in s) (H2 : j in s) (H3 : i != j)
  proof: isGLB_lt_isLUB_of_ne (s.isLeast_min' _).isGLB (s.isGreatest_max' _).isLUB H1 H2 H3

中文:
定理 最小值'_lt_max'
  条件: {i j} (H1 : i in s) (H2 : j in s) (H3 : i != j)
  证明: isGLB_lt_isLUB_of_ne (s.isLeast_min' _).isGLB (s.isGreatest_max' _).isLUB H1 H2 H3
-/
theorem min'_lt_max' {i j} (H1 : i in s) (H2 : j in s) (H3 : i != j) :
    s.min' ⟨i, H1⟩ < s.max' ⟨i, H1⟩ :=
  isGLB_lt_isLUB_of_ne (s.isLeast_min' _).isGLB (s.isGreatest_max' _).isLUB H1 H2 H3

/--
theorem `min'_lt_max'_of_card` / 定理 `min'_lt_max'_of_card`

English:
theorem min'_lt_max'_of_card
  given: (h₂ : 1 < card s)
  proof: by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab

中文:
定理 最小值'_lt_max'_of_card
  条件: (h₂ : 1 < card s)
  证明: by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab
-/
theorem min'_lt_max'_of_card (h₂ : 1 < card s) :
    s.min' (Finset.card_pos.1 <| by lia) < s.max' (Finset.card_pos.1 <| by lia) := by
  rcases one_lt_card.1 h₂ with ⟨a, ha, b, hb, hab⟩
  exact s.min'_lt_max' ha hb hab

/--
theorem `max'_union` / 定理 `max'_union`

English:
theorem max'_union
  given: {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
  proof: sup'_union h₁ h₂ id

中文:
定理 最大值'_union
  条件: {s₁ s₂ : 有限集 α} (h₁ : s₁.非空) (h₂ : s₂.非空)
  证明: sup'_union h₁ h₂ id
-/
theorem max'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ union s₂).max' (h₁.mono subset_union_left) = s₁.max' h₁ ⊔ s₂.max' h₂ := sup'_union h₁ h₂ id

/--
theorem `min'_union` / 定理 `min'_union`

English:
theorem min'_union
  given: {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty)
  proof: inf'_union h₁ h₂ id

中文:
定理 最小值'_union
  条件: {s₁ s₂ : 有限集 α} (h₁ : s₁.非空) (h₂ : s₂.非空)
  证明: inf'_union h₁ h₂ id
-/
theorem min'_union {s₁ s₂ : Finset α} (h₁ : s₁.Nonempty) (h₂ : s₂.Nonempty) :
    (s₁ union s₂).min' (h₁.mono subset_union_left) = s₁.min' h₁ ⊓ s₂.min' h₂ := inf'_union h₁ h₂ id

/--
theorem `map_ofDual_min` / 定理 `map_ofDual_min`

English:
theorem map_ofDual_min
  given: (s : Finset αᵒᵈ)
  statement: s.min.map ofDual = (s.image ofDual).max
  proof: by
  rw [max_eq_sup_withBot]; rw [sup_image]
  exact congr_fun WithBot.map_id _

中文:
定理 map_ofDual_min
  条件: (s : 有限集 αᵒᵈ)
  结论: s.最小值.map ofDual = (s.像 ofDual).最大值
  证明: by
  rw [max_eq_sup_withBot]; rw [sup_image]
  exact congr_fun WithBot.map_id _

Depends on / 依赖: WithBot, WithBot.map_id, congr_fun, map_id, max_eq_sup_withBot, sup_image
-/
theorem map_ofDual_min (s : Finset αᵒᵈ) : s.min.map ofDual = (s.image ofDual).max := by
  rw [max_eq_sup_withBot]; rw [sup_image]
  exact congr_fun WithBot.map_id _

/--
theorem `map_ofDual_max` / 定理 `map_ofDual_max`

English:
theorem map_ofDual_max
  given: (s : Finset αᵒᵈ)
  statement: s.max.map ofDual = (s.image ofDual).min
  proof: by
  rw [min_eq_inf_withTop]; rw [inf_image]
  exact congr_fun WithTop.map_id _

中文:
定理 map_ofDual_max
  条件: (s : 有限集 αᵒᵈ)
  结论: s.最大值.map ofDual = (s.像 ofDual).最小值
  证明: by
  rw [min_eq_inf_withTop]; rw [inf_image]
  exact congr_fun WithTop.map_id _

Depends on / 依赖: WithTop, WithTop.map_id, congr_fun, inf_image, map_id, min_eq_inf_withTop
-/
theorem map_ofDual_max (s : Finset αᵒᵈ) : s.max.map ofDual = (s.image ofDual).min := by
  rw [min_eq_inf_withTop]; rw [inf_image]
  exact congr_fun WithTop.map_id _

/--
theorem `map_toDual_min` / 定理 `map_toDual_min`

English:
theorem map_toDual_min
  given: (s : Finset α)
  statement: s.min.map toDual = (s.image toDual).max
  proof: by
  rw [max_eq_sup_withBot]; rw [sup_image]
  exact congr_fun WithBot.map_id _

中文:
定理 map_toDual_min
  条件: (s : 有限集 α)
  结论: s.最小值.map toDual = (s.像 toDual).最大值
  证明: by
  rw [max_eq_sup_withBot]; rw [sup_image]
  exact congr_fun WithBot.map_id _

Depends on / 依赖: WithBot, WithBot.map_id, congr_fun, map_id, max_eq_sup_withBot, sup_image
-/
theorem map_toDual_min (s : Finset α) : s.min.map toDual = (s.image toDual).max := by
  rw [max_eq_sup_withBot]; rw [sup_image]
  exact congr_fun WithBot.map_id _

/--
theorem `map_toDual_max` / 定理 `map_toDual_max`

English:
theorem map_toDual_max
  given: (s : Finset α)
  statement: s.max.map toDual = (s.image toDual).min
  proof: by
  rw [min_eq_inf_withTop]; rw [inf_image]
  exact congr_fun WithTop.map_id _

中文:
定理 map_toDual_max
  条件: (s : 有限集 α)
  结论: s.最大值.map toDual = (s.像 toDual).最小值
  证明: by
  rw [min_eq_inf_withTop]; rw [inf_image]
  exact congr_fun WithTop.map_id _

Depends on / 依赖: WithTop, WithTop.map_id, congr_fun, inf_image, map_id, min_eq_inf_withTop
-/
theorem map_toDual_max (s : Finset α) : s.max.map toDual = (s.image toDual).min := by
  rw [min_eq_inf_withTop]; rw [inf_image]
  exact congr_fun WithTop.map_id _

/--
theorem `ofDual_min'` / 定理 `ofDual_min'`

English:
theorem ofDual_min'
  given: {s : Finset αᵒᵈ} (hs : s.Nonempty)
  proof: by
  simp [min'_eq_inf', max'_eq_sup']

中文:
定理 ofDual_min'
  条件: {s : 有限集 αᵒᵈ} (hs : s.非空)
  证明: by
  simp [min'_eq_inf', max'_eq_sup']

Depends on / 依赖: _eq_inf, _eq_sup
-/
theorem ofDual_min' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (min' s hs) = max' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

/--
theorem `ofDual_max'` / 定理 `ofDual_max'`

English:
theorem ofDual_max'
  given: {s : Finset αᵒᵈ} (hs : s.Nonempty)
  proof: by
  simp [min'_eq_inf', max'_eq_sup']

中文:
定理 ofDual_max'
  条件: {s : 有限集 αᵒᵈ} (hs : s.非空)
  证明: by
  simp [min'_eq_inf', max'_eq_sup']

Depends on / 依赖: _eq_inf, _eq_sup
-/
theorem ofDual_max' {s : Finset αᵒᵈ} (hs : s.Nonempty) :
    ofDual (max' s hs) = min' (s.image ofDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

/--
theorem `toDual_min'` / 定理 `toDual_min'`

English:
theorem toDual_min'
  given: {s : Finset α} (hs : s.Nonempty)
  proof: by
  simp [min'_eq_inf', max'_eq_sup']

中文:
定理 toDual_min'
  条件: {s : 有限集 α} (hs : s.非空)
  证明: by
  simp [min'_eq_inf', max'_eq_sup']

Depends on / 依赖: _eq_inf, _eq_sup
-/
theorem toDual_min' {s : Finset α} (hs : s.Nonempty) :
    toDual (min' s hs) = max' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

/--
theorem `toDual_max'` / 定理 `toDual_max'`

English:
theorem toDual_max'
  given: {s : Finset α} (hs : s.Nonempty)
  proof: by
  simp [min'_eq_inf', max'_eq_sup']

中文:
定理 toDual_max'
  条件: {s : 有限集 α} (hs : s.非空)
  证明: by
  simp [min'_eq_inf', max'_eq_sup']

Depends on / 依赖: _eq_inf, _eq_sup
-/
theorem toDual_max' {s : Finset α} (hs : s.Nonempty) :
    toDual (max' s hs) = min' (s.image toDual) (hs.image _) := by
  simp [min'_eq_inf', max'_eq_sup']

/--
theorem `max'_subset` / 定理 `max'_subset`

English:
theorem max'_subset
  given: {s t : Finset α} (H : s.Nonempty) (hst : s subseteq t)
  proof: le_max' _ _ (hst (s.max'_mem H))

中文:
定理 最大值'_subset
  条件: {s t : 有限集 α} (H : s.非空) (hst : s subseteq t)
  证明: le_max' _ _ (hst (s.max'_mem H))
-/
theorem max'_subset {s t : Finset α} (H : s.Nonempty) (hst : s subseteq t) :
    s.max' H <= t.max' (H.mono hst) :=
  le_max' _ _ (hst (s.max'_mem H))

/--
theorem `min'_subset` / 定理 `min'_subset`

English:
theorem min'_subset
  given: {s t : Finset α} (H : s.Nonempty) (hst : s subseteq t)
  proof: min'_le _ _ (hst (s.min'_mem H))

中文:
定理 最小值'_subset
  条件: {s t : 有限集 α} (H : s.非空) (hst : s subseteq t)
  证明: min'_le _ _ (hst (s.min'_mem H))
-/
theorem min'_subset {s t : Finset α} (H : s.Nonempty) (hst : s subseteq t) :
    t.min' (H.mono hst) <= s.min' H :=
  min'_le _ _ (hst (s.min'_mem H))

/--
theorem `max'_insert` / 定理 `max'_insert`

English:
theorem max'_insert
  given: (a : α) (s : Finset α) (H : s.Nonempty)
  proof: (isGreatest_max' _ _).unique by
    rw [coe_insert]
    exact (isGreatest_max' _ _).insert _

中文:
定理 最大值'_insert
  条件: (a : α) (s : 有限集 α) (H : s.非空)
  证明: (isGreatest_max' _ _).unique by
    rw [coe_insert]
    exact (isGreatest_max' _ _).insert _
-/
@[simp] theorem max'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).max' (s.insert_nonempty a) = max a (s.max' H) :=
(isGreatest_max' _ _).unique by
    rw [coe_insert]
    exact (isGreatest_max' _ _).insert _

/--
theorem `min'_insert` / 定理 `min'_insert`

English:
theorem min'_insert
  given: (a : α) (s : Finset α) (H : s.Nonempty)
  proof: (isLeast_min' _ _).unique by
    rw [coe_insert]
    exact (isLeast_min' _ _).insert _

中文:
定理 最小值'_insert
  条件: (a : α) (s : 有限集 α) (H : s.非空)
  证明: (isLeast_min' _ _).unique by
    rw [coe_insert]
    exact (isLeast_min' _ _).insert _
-/
@[simp] theorem min'_insert (a : α) (s : Finset α) (H : s.Nonempty) :
    (insert a s).min' (s.insert_nonempty a) = min a (s.min' H) :=
(isLeast_min' _ _).unique by
    rw [coe_insert]
    exact (isLeast_min' _ _).insert _

/--
lemma `min'_pair` / 引理 `min'_pair`

English:
lemma min'_pair
  given: (a b : α)
  proof: by
  simp

中文:
引理 最小值'_pair
  条件: (a b : α)
  证明: by
  simp
-/
lemma min'_pair (a b : α) :
    min' {a, b} (insert_nonempty _ _) = min a b := by
  simp

/--
lemma `max'_pair` / 引理 `max'_pair`

English:
lemma max'_pair
  given: (a b : α)
  proof: by
  simp

中文:
引理 最大值'_pair
  条件: (a b : α)
  证明: by
  simp
-/
lemma max'_pair (a b : α) :
    max' {a, b} (insert_nonempty _ _) = max a b := by
  simp

/--
theorem `lt_max'_of_mem_erase_max'` / 定理 `lt_max'_of_mem_erase_max'`

English:
theorem lt_max'_of_mem_erase_max'
  given: [DecidableEq α] {a : α} (ha : a in s.erase (s.max' H))
  proof: lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) ne_of_mem_of_not_mem ha notMem_erase _ _

中文:
定理 lt_max'_of_mem_erase_max'
  条件: [DecidableEq α] {a : α} (ha : a in s.erase (s.最大值' H))
  证明: lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) ne_of_mem_of_not_mem ha notMem_erase _ _

Depends on / 依赖: le_max, lt_of_le_of_ne, mem_of_mem_erase, ne_of_mem_of_not_mem, notMem_erase
-/
theorem lt_max'_of_mem_erase_max' [DecidableEq α] {a : α} (ha : a in s.erase (s.max' H)) :
    a < s.max' H :=
lt_of_le_of_ne (le_max' _ _ (mem_of_mem_erase ha)) ne_of_mem_of_not_mem ha notMem_erase _ _

/--
theorem `min'_lt_of_mem_erase_min'` / 定理 `min'_lt_of_mem_erase_min'`

English:
theorem min'_lt_of_mem_erase_min'
  given: [DecidableEq α] {a : α} (ha : a in s.erase (s.min' H))
  proof: @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha

中文:
定理 最小值'_lt_of_mem_erase_min'
  条件: [DecidableEq α] {a : α} (ha : a in s.erase (s.最小值' H))
  证明: @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha

Depends on / 依赖: Irreducible, Irreducible.ne_zero, ne_zero
-/
theorem min'_lt_of_mem_erase_min' [DecidableEq α] {a : α} (ha : a in s.erase (s.min' H)) :
    s.min' H < a :=
  @lt_max'_of_mem_erase_max' αᵒᵈ _ s H _ a ha

/-- To rewrite from right to left, use `Monotone.map_finset_max'`. -/
@[simp]
/--
theorem `max'_image` / 定理 `max'_image`

English:
theorem max'_image
  statement: [LinearOrder β] {f : α -> β} (hf : Monotone f) (s : Finset α)
  proof: by
  simp only [max', sup'_image]
exact .symm apply_sup'_eq_sup'_comp _ _ fun _ _ => hf.map_max

中文:
定理 最大值'_image
  结论: [线性序 β] {f : α -> β} (hf : 递增 f) (s : 有限集 α)
  证明: by
  simp only [max', sup'_image]
exact .symm apply_sup'_eq_sup'_comp _ _ fun _ _ => hf.map_max
-/
theorem max'_image [LinearOrder β] {f : α -> β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).max' h = f (s.max' h.of_image) := by
  simp only [max', sup'_image]
exact .symm apply_sup'_eq_sup'_comp _ _ fun _ _ => hf.map_max

/--
lemma `_root_.Monotone.map_finset_max'` / 引理 `_root_.Monotone.map_finset_max'`

English:
lemma _root_.Monotone.map_finset_max'
  statement: [LinearOrder β] {f : α -> β} (hf : Monotone f) {s : Finset α}
  proof: .symm max'_image hf ..

中文:
引理 _root_.递增.map_finset_max'
  结论: [线性序 β] {f : α -> β} (hf : 递增 f) {s : 有限集 α}
  证明: .symm max'_image hf ..

Depends on / 依赖: _image
-/
lemma _root_.Monotone.map_finset_max' [LinearOrder β] {f : α -> β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.max' h) = (s.image f).max' (h.image f) :=
.symm max'_image hf ..

/-- To rewrite from right to left, use `Monotone.map_finset_min'`. -/
@[simp]
/--
theorem `min'_image` / 定理 `min'_image`

English:
theorem min'_image
  statement: [LinearOrder β] {f : α -> β} (hf : Monotone f) (s : Finset α)
  proof: by
  simp only [min', inf'_image]
exact .symm apply_inf'_eq_inf'_comp _ _ fun _ _ => hf.map_min

中文:
定理 最小值'_image
  结论: [线性序 β] {f : α -> β} (hf : 递增 f) (s : 有限集 α)
  证明: by
  simp only [min', inf'_image]
exact .symm apply_inf'_eq_inf'_comp _ _ fun _ _ => hf.map_min
-/
theorem min'_image [LinearOrder β] {f : α -> β} (hf : Monotone f) (s : Finset α)
    (h : (s.image f).Nonempty) : (s.image f).min' h = f (s.min' h.of_image) := by
  simp only [min', inf'_image]
exact .symm apply_inf'_eq_inf'_comp _ _ fun _ _ => hf.map_min

/--
lemma `_root_.Monotone.map_finset_min'` / 引理 `_root_.Monotone.map_finset_min'`

English:
lemma _root_.Monotone.map_finset_min'
  statement: [LinearOrder β] {f : α -> β} (hf : Monotone f) {s : Finset α}
  proof: .symm min'_image hf ..

中文:
引理 _root_.递增.map_finset_min'
  结论: [线性序 β] {f : α -> β} (hf : 递增 f) {s : 有限集 α}
  证明: .symm min'_image hf ..

Depends on / 依赖: _image
-/
lemma _root_.Monotone.map_finset_min' [LinearOrder β] {f : α -> β} (hf : Monotone f) {s : Finset α}
    (h : s.Nonempty) : f (s.min' h) = (s.image f).min' (h.image f) :=
.symm min'_image hf ..

/--
theorem `coe_max'` / 定理 `coe_max'`

English:
theorem coe_max'
  given: {s : Finset α} (hs : s.Nonempty)
  statement: ↑(s.max' hs) = s.max
  proof: coe_sup' hs id

中文:
定理 coe_max'
  条件: {s : 有限集 α} (hs : s.非空)
  结论: ↑(s.最大值' hs) = s.最大值
  证明: coe_sup' hs id

Depends on / 依赖: coe_sup, hp.one_lt.ne, one_lt
-/
theorem coe_max' {s : Finset α} (hs : s.Nonempty) : ↑(s.max' hs) = s.max :=
  coe_sup' hs id

/--
theorem `coe_min'` / 定理 `coe_min'`

English:
theorem coe_min'
  given: {s : Finset α} (hs : s.Nonempty)
  statement: ↑(s.min' hs) = s.min
  proof: coe_inf' hs id

中文:
定理 coe_min'
  条件: {s : 有限集 α} (hs : s.非空)
  结论: ↑(s.最小值' hs) = s.最小值
  证明: coe_inf' hs id

Depends on / 依赖: coe_inf
-/
theorem coe_min' {s : Finset α} (hs : s.Nonempty) : ↑(s.min' hs) = s.min :=
  coe_inf' hs id

/--
theorem `max_mem_image_coe` / 定理 `max_mem_image_coe`

English:
theorem max_mem_image_coe
  given: {s : Finset α} (hs : s.Nonempty)
  proof: mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩

中文:
定理 max_mem_image_coe
  条件: {s : 有限集 α} (hs : s.非空)
  证明: mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩

Depends on / 依赖: _mem, coe_max, mem_image
-/
theorem max_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.max in (s.image (↑) : Finset (WithBot α)) :=
  mem_image.2 ⟨max' s hs, max'_mem _ _, coe_max' hs⟩

/--
theorem `min_mem_image_coe` / 定理 `min_mem_image_coe`

English:
theorem min_mem_image_coe
  given: {s : Finset α} (hs : s.Nonempty)
  proof: mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩

中文:
定理 min_mem_image_coe
  条件: {s : 有限集 α} (hs : s.非空)
  证明: mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩

Depends on / 依赖: _mem, coe_min, mem_image
-/
theorem min_mem_image_coe {s : Finset α} (hs : s.Nonempty) :
    s.min in (s.image (↑) : Finset (WithTop α)) :=
  mem_image.2 ⟨min' s hs, min'_mem _ _, coe_min' hs⟩

/--
theorem `max_mem_insert_bot_image_coe` / 定理 `max_mem_insert_bot_image_coe`

English:
theorem max_mem_insert_bot_image_coe
  given: (s : Finset α)
  proof: mem_insert.2 s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe

中文:
定理 max_mem_insert_bot_image_coe
  条件: (s : 有限集 α)
  证明: mem_insert.2 s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe

Depends on / 依赖: eq_empty_or_nonempty, max_eq_bot, max_mem_image_coe, mem_insert, s.eq_empty_or_nonempty.imp
-/
theorem max_mem_insert_bot_image_coe (s : Finset α) :
    s.max in (insert ⊥ (s.image (↑)) : Finset (WithBot α)) :=
mem_insert.2 s.eq_empty_or_nonempty.imp max_eq_bot.2 max_mem_image_coe

/--
theorem `min_mem_insert_top_image_coe` / 定理 `min_mem_insert_top_image_coe`

English:
theorem min_mem_insert_top_image_coe
  given: (s : Finset α)
  proof: mem_insert.2 s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe

中文:
定理 min_mem_insert_top_image_coe
  条件: (s : 有限集 α)
  证明: mem_insert.2 s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe

Depends on / 依赖: eq_empty_or_nonempty, mem_insert, min_eq_top, min_mem_image_coe, s.eq_empty_or_nonempty.imp
-/
theorem min_mem_insert_top_image_coe (s : Finset α) :
    s.min in (insert ⊤ (s.image (↑)) : Finset (WithTop α)) :=
mem_insert.2 s.eq_empty_or_nonempty.imp min_eq_top.2 min_mem_image_coe

/--
theorem `max'_erase_ne_self` / 定理 `max'_erase_ne_self`

English:
theorem max'_erase_ne_self
  given: {s : Finset α} (s0 : (s.erase x).Nonempty)
  statement: (s.erase x).max' s0 != x
  proof: ne_of_mem_erase (max'_mem _ s0)

中文:
定理 最大值'_erase_ne_self
  条件: {s : 有限集 α} (s0 : (s.erase x).非空)
  结论: (s.erase x).最大值' s0 != x
  证明: ne_of_mem_erase (max'_mem _ s0)
-/
theorem max'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).max' s0 != x :=
  ne_of_mem_erase (max'_mem _ s0)

/--
theorem `min'_erase_ne_self` / 定理 `min'_erase_ne_self`

English:
theorem min'_erase_ne_self
  given: {s : Finset α} (s0 : (s.erase x).Nonempty)
  statement: (s.erase x).min' s0 != x
  proof: ne_of_mem_erase (min'_mem _ s0)

中文:
定理 最小值'_erase_ne_self
  条件: {s : 有限集 α} (s0 : (s.erase x).非空)
  结论: (s.erase x).最小值' s0 != x
  证明: ne_of_mem_erase (min'_mem _ s0)
-/
theorem min'_erase_ne_self {s : Finset α} (s0 : (s.erase x).Nonempty) : (s.erase x).min' s0 != x :=
  ne_of_mem_erase (min'_mem _ s0)

/--
theorem `max_erase_ne_self` / 定理 `max_erase_ne_self`

English:
theorem max_erase_ne_self
  given: {s : Finset α}
  statement: (s.erase x).max != x
  proof: by
  by_cases! s0 : (s.erase x).Nonempty
  · refine ne_of_eq_of_ne (coe_max' s0).symm ?_
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [s0, max_empty]
    exact WithBot.bot_ne_coe

中文:
定理 max_erase_ne_self
  条件: {s : 有限集 α}
  结论: (s.erase x).最大值 != x
  证明: by
  by_cases! s0 : (s.erase x).Nonempty
  · refine ne_of_eq_of_ne (coe_max' s0).symm ?_
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [s0, max_empty]
    exact WithBot.bot_ne_coe

Depends on / 依赖: Nonempty, WithBot, WithBot.bot_ne_coe, WithBot.coe_eq_coe.not.mpr, _erase_ne_self, bot_ne_coe, coe_eq_coe, coe_max, max_empty, ne_of_eq_of_ne, s.erase
-/
theorem max_erase_ne_self {s : Finset α} : (s.erase x).max != x := by
  by_cases! s0 : (s.erase x).Nonempty
  · refine ne_of_eq_of_ne (coe_max' s0).symm ?_
    exact WithBot.coe_eq_coe.not.mpr (max'_erase_ne_self _)
  · rw [s0, max_empty]
    exact WithBot.bot_ne_coe

/--
theorem `min_erase_ne_self` / 定理 `min_erase_ne_self`

English:
theorem min_erase_ne_self
  given: {s : Finset α}
  statement: (s.erase x).min != x
  proof: by
  apply mt (congr_arg (WithTop.map toDual))
  rw [map_toDual_min]; rw [image_erase toDual.injective]; rw [WithTop.map_coe]
  apply max_erase_ne_self

中文:
定理 min_erase_ne_self
  条件: {s : 有限集 α}
  结论: (s.erase x).最小值 != x
  证明: by
  apply mt (congr_arg (WithTop.map toDual))
  rw [map_toDual_min]; rw [image_erase toDual.injective]; rw [WithTop.map_coe]
  apply max_erase_ne_self

Depends on / 依赖: WithTop, WithTop.map, WithTop.map_coe, congr_arg, image_erase, injective, map_coe, map_toDual_min, max_erase_ne_self, toDual, toDual.injective
-/
theorem min_erase_ne_self {s : Finset α} : (s.erase x).min != x := by
  apply mt (congr_arg (WithTop.map toDual))
  rw [map_toDual_min]; rw [image_erase toDual.injective]; rw [WithTop.map_coe]
  apply max_erase_ne_self

/--
theorem `exists_next_right` / 定理 `exists_next_right`

English:
theorem exists_next_right
  given: {x : α} {s : Finset α} (h : exists y in s, x < y)
  proof: have Hne : (s.filter (x < ·)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
  have aux := mem_filter.1 (min'_mem _ Hne)
⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ mem_filter.2 ⟨hzs, by simpa⟩⟩

中文:
定理 存在_next_right
  条件: {x : α} {s : 有限集 α} (h : 存在 y in s, x < y)
  证明: have Hne : (s.filter (x < ·)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
  have aux := mem_filter.1 (min'_mem _ Hne)
⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ mem_filter.2 ⟨hzs, by simpa⟩⟩

Depends on / 依赖: Nonempty, _mem, filter, h.imp, mem_filter, s.filter
-/
theorem exists_next_right {x : α} {s : Finset α} (h : exists y in s, x < y) :
    exists y in s, x < y ∧ forall z in s, x < z -> y <= z :=
  have Hne : (s.filter (x < ·)).Nonempty := h.imp fun y hy => mem_filter.2 (by simpa)
  have aux := mem_filter.1 (min'_mem _ Hne)
⟨min' _ Hne, aux.1, by simp, fun z hzs hz => min'_le _ _ mem_filter.2 ⟨hzs, by simpa⟩⟩

/--
theorem `exists_next_left` / 定理 `exists_next_left`

English:
theorem exists_next_left
  given: {x : α} {s : Finset α} (h : exists y in s, y < x)
  proof: @exists_next_right αᵒᵈ _ x s h

中文:
定理 存在_next_left
  条件: {x : α} {s : 有限集 α} (h : 存在 y in s, y < x)
  证明: @exists_next_right αᵒᵈ _ x s h

Depends on / 依赖: exists_next_right
-/
theorem exists_next_left {x : α} {s : Finset α} (h : exists y in s, y < x) :
    exists y in s, y < x ∧ forall z in s, z < x -> z <= y :=
  @exists_next_right αᵒᵈ _ x s h

/--
theorem `card_le_of_interleaved` / 定理 `card_le_of_interleaved`

English:
theorem card_le_of_interleaved
  statement: {s t : Finset α}
  proof: by
  replace h : forallᵉ (x in s) (y in s), x < y -> exists z in t, x < z ∧ z < y := by
    intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
rcases h x hx a has hxa fun z hzs hz => hz.2.not_ge ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
exact ⟨b, hbt, hxb, hba.trans_le ha _ hy hxy⟩
  set f : α -> WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x <= a := min_le (mem_filter.2 ⟨hat, by simpa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
WithTop.coe_lt_coe.2 hay.trans (by simpa using (mem_filter.1 hb).2)
  calc
    s.card = (s.image f).card := (card_image_of_injOn f_mono.injOn).symm
    _ <= (insert ⊤ (t.image (↑)) : Finset (WithTop α)).card :=
card_mono image_subset_iff.2 fun x _ =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ <= t.card + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)

中文:
定理 card_le_of_interleaved
  结论: {s t : 有限集 α}
  证明: by
  replace h : forallᵉ (x in s) (y in s), x < y -> exists z in t, x < z ∧ z < y := by
    intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
rcases h x hx a has hxa fun z hzs hz => hz.2.not_ge ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
exact ⟨b, hbt, hxb, hba.trans_le ha _ hy hxy⟩
  set f : α -> WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x <= a := min_le (mem_filter.2 ⟨hat, by simpa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
WithTop.coe_lt_coe.2 hay.trans (by simpa using (mem_filter.1 hb).2)
  calc
    s.card = (s.image f).card := (card_image_of_injOn f_mono.injOn).symm
    _ <= (insert ⊤ (t.image (↑)) : Finset (WithTop α)).card :=
card_mono image_subset_iff.2 fun x _ =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ <= t.card + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)

Depends on / 依赖: StrictMonoOn, WithTop, exists_next_right, f_mono, filter, hba.trans_le, min_le, not_ge, replace, t.filter, trans_le
-/
theorem card_le_of_interleaved {s t : Finset α}
    (h : forallᵉ (x in s) (y in s),
        x < y -> (forall z in s, z ∉ Set.Ioo x y) -> exists z in t, x < z ∧ z < y) :
    s.card <= t.card + 1 := by
  replace h : forallᵉ (x in s) (y in s), x < y -> exists z in t, x < z ∧ z < y := by
    intro x hx y hy hxy
    rcases exists_next_right ⟨y, hy, hxy⟩ with ⟨a, has, hxa, ha⟩
rcases h x hx a has hxa fun z hzs hz => hz.2.not_ge ha _ hzs hz.1 with ⟨b, hbt, hxb, hba⟩
exact ⟨b, hbt, hxb, hba.trans_le ha _ hy hxy⟩
  set f : α -> WithTop α := fun x => (t.filter fun y => x < y).min
  have f_mono : StrictMonoOn f s := by
    intro x hx y hy hxy
    rcases h x hx y hy hxy with ⟨a, hat, hxa, hay⟩
    calc
      f x <= a := min_le (mem_filter.2 ⟨hat, by simpa⟩)
      _ < f y :=
        (Finset.lt_inf_iff <| WithTop.coe_lt_top a).2 fun b hb =>
WithTop.coe_lt_coe.2 hay.trans (by simpa using (mem_filter.1 hb).2)
  calc
    s.card = (s.image f).card := (card_image_of_injOn f_mono.injOn).symm
    _ <= (insert ⊤ (t.image (↑)) : Finset (WithTop α)).card :=
card_mono image_subset_iff.2 fun x _ =>
          insert_subset_insert _ (image_subset_image <| filter_subset _ _)
            (min_mem_insert_top_image_coe _)
    _ <= t.card + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right card_image_le _)

/--
theorem `card_le_sdiff_of_interleaved` / 定理 `card_le_sdiff_of_interleaved`

English:
theorem card_le_sdiff_of_interleaved
  statement: {s t : Finset α}
  proof: card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩

@[deprecated (since := "2026-06-03")]
alias card_le_diff_of_interleaved := card_le_sdiff_of_interleaved

中文:
定理 card_le_sdiff_of_interleaved
  结论: {s t : 有限集 α}
  证明: card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩

@[deprecated (since := "2026-06-03")]
alias card_le_diff_of_interleaved := card_le_sdiff_of_interleaved

Depends on / 依赖: card_le_of_interleaved, mem_sdiff
-/
theorem card_le_sdiff_of_interleaved {s t : Finset α}
    (h :
      forallᵉ (x in s) (y in s),
        x < y -> (forall z in s, z ∉ Set.Ioo x y) -> exists z in t, x < z ∧ z < y) :
    s.card <= (t \ s).card + 1 :=
  card_le_of_interleaved fun x hx y hy hxy hs =>
    let ⟨z, hzt, hxz, hzy⟩ := h x hx y hy hxy hs
    ⟨z, mem_sdiff.2 ⟨hzt, fun hzs => hs z hzs ⟨hxz, hzy⟩⟩, hxz, hzy⟩

@[deprecated (since := "2026-06-03")]
alias card_le_diff_of_interleaved := card_le_sdiff_of_interleaved

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly greater than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
/--
theorem `induction_on_max` / 定理 `induction_on_max`

English:
theorem induction_on_max
  proof: by
  induction s using Finset.eraseInduction with | _ s ih
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact empty
  · have H : s.max' hne in s := max'_mem s hne
    rw [← insert_erase H]
    exact insert _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ih _ H)

中文:
定理 induction_on_max
  证明: by
  induction s using Finset.eraseInduction with | _ s ih
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact empty
  · have H : s.max' hne in s := max'_mem s hne
    rw [← insert_erase H]
    exact insert _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ih _ H)

Depends on / 依赖: Finset, Finset.eraseInduction, _mem, _of_mem_erase_max, eq_empty_or_nonempty, eraseInduction, insert, insert_erase, lt_max, s.eq_empty_or_nonempty, s.lt_max, s.max
-/
theorem induction_on_max
    [DecidableEq α] {motive : Finset α -> Prop} (s : Finset α) (empty : motive ∅)
    (insert : forall a s, (forall x in s, x < a) -> motive s -> motive (insert a s)) : motive s := by
  induction s using Finset.eraseInduction with | _ s ih
  rcases s.eq_empty_or_nonempty with (rfl | hne)
  · exact empty
  · have H : s.max' hne in s := max'_mem s hne
    rw [← insert_erase H]
    exact insert _ _ (fun x => s.lt_max'_of_mem_erase_max' hne) (ih _ H)

/-- Induction principle for `Finset`s in a linearly ordered type: a predicate is true on all
`s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` strictly less than all elements of `s`, `p s`
  implies `p (insert a s)`. -/
@[elab_as_elim]
/--
theorem `induction_on_min` / 定理 `induction_on_min`

English:
theorem induction_on_min
  proof: @induction_on_max αᵒᵈ _ _ _ s empty insert

中文:
定理 induction_on_min
  证明: @induction_on_max αᵒᵈ _ _ _ s empty insert

Depends on / 依赖: induction_on_max, insert
-/
theorem induction_on_min
    [DecidableEq α] {motive : Finset α -> Prop} (s : Finset α) (empty : motive ∅)
    (insert : forall a s, (forall x in s, a < x) -> motive s -> motive (insert a s)) : motive s :=
  @induction_on_max αᵒᵈ _ _ _ s empty insert

end MaxMin

section MaxMinInductionValue

variable [LinearOrder α] [LinearOrder β]

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f x ≤ f a`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
/--
theorem `induction_on_max_value` / 定理 `induction_on_max_value`

English:
theorem induction_on_max_value
  proof: by
  induction s using Finset.eraseInduction with | _ s ihs
  rcases (s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, empty]
  · have H : (s.image f).max' hne in s.image f := max'_mem (s.image f) hne
    simp only [mem_image] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine insert _ _ (notMem_erase a s) (fun x hx => ?_) (ihs a has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)

中文:
定理 induction_on_max_value
  证明: by
  induction s using Finset.eraseInduction with | _ s ihs
  rcases (s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, empty]
  · have H : (s.image f).max' hne in s.image f := max'_mem (s.image f) hne
    simp only [mem_image] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine insert _ _ (notMem_erase a s) (fun x hx => ?_) (ihs a has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)

Depends on / 依赖: Finset, Finset.eraseInduction, _mem, eq_empty_or_nonempty, eraseInduction, image_eq_empty, insert, insert_erase, le_max, mem_image, mem_image_of_mem, mem_of_mem_erase, notMem_erase, s.image
-/
theorem induction_on_max_value
    [DecidableEq ι] (f : ι -> α) {motive : Finset ι -> Prop} (s : Finset ι) (empty : motive ∅)
    (insert : forall a s, a ∉ s -> (forall x in s, f x <= f a) -> motive s -> motive (insert a s)) : motive s := by
  induction s using Finset.eraseInduction with | _ s ihs
  rcases (s.image f).eq_empty_or_nonempty with (hne | hne)
  · simp only [image_eq_empty] at hne
    simp only [hne, empty]
  · have H : (s.image f).max' hne in s.image f := max'_mem (s.image f) hne
    simp only [mem_image] at H
    rcases H with ⟨a, has, hfa⟩
    rw [← insert_erase has]
    refine insert _ _ (notMem_erase a s) (fun x hx => ?_) (ihs a has)
    rw [hfa]
    exact le_max' _ _ (mem_image_of_mem _ <| mem_of_mem_erase hx)

/-- Induction principle for `Finset`s in any type from which a given function `f` maps to a linearly
ordered type : a predicate is true on all `s : Finset α` provided that:

* it is true on the empty `Finset`,
* for every `s : Finset α` and an element `a` such that for elements of `s` denoted by `x` we have
  `f a ≤ f x`, `p s` implies `p (insert a s)`. -/
@[elab_as_elim]
/--
theorem `induction_on_min_value` / 定理 `induction_on_min_value`

English:
theorem induction_on_min_value
  proof: @induction_on_max_value αᵒᵈ ι _ _ _ _ s empty insert

中文:
定理 induction_on_min_value
  证明: @induction_on_max_value αᵒᵈ ι _ _ _ _ s empty insert

Depends on / 依赖: Irreducible, Irreducible.not_dvd_one, induction_on_max_value, insert, not_dvd_one
-/
theorem induction_on_min_value
    [DecidableEq ι] (f : ι -> α) {motive : Finset ι -> Prop} (s : Finset ι) (empty : motive ∅)
    (insert : forall a s, a ∉ s -> (forall x in s, f a <= f x) -> motive s -> motive (insert a s)) : motive s :=
  @induction_on_max_value αᵒᵈ ι _ _ _ _ s empty insert

end MaxMinInductionValue

section ExistsMaxMin

variable [LinearOrder α]

/--
theorem `exists_max_image` / 定理 `exists_max_image`

English:
theorem exists_max_image
  given: (s : Finset β) (f : β -> α) (h : s.Nonempty)
  proof: by
  obtain ⟨y, hy⟩ := max_of_nonempty (h.image f)
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩

中文:
定理 存在_max_image
  条件: (s : 有限集 β) (f : β -> α) (h : s.非空)
  证明: by
  obtain ⟨y, hy⟩ := max_of_nonempty (h.image f)
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩

Depends on / 依赖: h.image, le_max_of_eq, max_of_nonempty, mem_image, mem_image.mp, mem_image_of_mem, mem_of_max
-/
theorem exists_max_image (s : Finset β) (f : β -> α) (h : s.Nonempty) :
    exists x in s, forall x' in s, f x' <= f x := by
  obtain ⟨y, hy⟩ := max_of_nonempty (h.image f)
  rcases mem_image.mp (mem_of_max hy) with ⟨x, hx, rfl⟩
  exact ⟨x, hx, fun x' hx' => le_max_of_eq (mem_image_of_mem f hx') hy⟩

/--
theorem `exists_min_image` / 定理 `exists_min_image`

English:
theorem exists_min_image
  given: (s : Finset β) (f : β -> α) (h : s.Nonempty)
  proof: @exists_max_image αᵒᵈ β _ s f h

中文:
定理 存在_min_image
  条件: (s : 有限集 β) (f : β -> α) (h : s.非空)
  证明: @exists_max_image αᵒᵈ β _ s f h

Depends on / 依赖: exists_max_image
-/
theorem exists_min_image (s : Finset β) (f : β -> α) (h : s.Nonempty) :
    exists x in s, forall x' in s, f x <= f x' :=
  @exists_max_image αᵒᵈ β _ s f h

end ExistsMaxMin

/--
theorem `isGLB_iff_isLeast` / 定理 `isGLB_iff_isLeast`

English:
theorem isGLB_iff_isLeast
  given: [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty)
  proof: by
  refine ⟨fun his => ?_, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB]; rw [IsGreatest]; rw [mem_lowerBounds]; rw [mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))

中文:
定理 isGLB_iff_isLeast
  条件: [线性序 α] (i : α) (s : 有限集 α) (hs : s.非空)
  证明: by
  refine ⟨fun his => ?_, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB]; rw [IsGreatest]; rw [mem_lowerBounds]; rw [mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))

Depends on / 依赖: Finset, Finset.min, IsGreatest, IsLeast, IsLeast.isGLB, _mem, isLeast_min, le_antisymm, mem_lowerBounds, mem_upperBounds
-/
theorem isGLB_iff_isLeast [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsGLB (s : Set α) i ↔ IsLeast (↑s) i := by
  refine ⟨fun his => ?_, IsLeast.isGLB⟩
  suffices i = min' s hs by
    rw [this]
    exact isLeast_min' s hs
  rw [IsGLB]; rw [IsGreatest]; rw [mem_lowerBounds]; rw [mem_upperBounds] at his
  exact le_antisymm (his.1 (Finset.min' s hs) (Finset.min'_mem s hs)) (his.2 _ (Finset.min'_le s))

/--
theorem `isLUB_iff_isGreatest` / 定理 `isLUB_iff_isGreatest`

English:
theorem isLUB_iff_isGreatest
  given: [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty)
  proof: @isGLB_iff_isLeast αᵒᵈ _ i s hs

中文:
定理 isLUB_iff_isGreatest
  条件: [线性序 α] (i : α) (s : 有限集 α) (hs : s.非空)
  证明: @isGLB_iff_isLeast αᵒᵈ _ i s hs

Depends on / 依赖: isGLB_iff_isLeast
-/
theorem isLUB_iff_isGreatest [LinearOrder α] (i : α) (s : Finset α) (hs : s.Nonempty) :
    IsLUB (s : Set α) i ↔ IsGreatest (↑s) i :=
  @isGLB_iff_isLeast αᵒᵈ _ i s hs

/--
theorem `isGLB_mem` / 定理 `isGLB_mem`

English:
theorem isGLB_mem
  statement: [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
  proof: by
  rw [← mem_coe]
  exact ((isGLB_iff_isLeast i s hs).mp his).1

中文:
定理 isGLB_mem
  结论: [线性序 α] {i : α} (s : 有限集 α) (his : IsGLB (s : 集合 α) i)
  证明: by
  rw [← mem_coe]
  exact ((isGLB_iff_isLeast i s hs).mp his).1

Depends on / 依赖: isGLB_iff_isLeast, mem_coe
-/
theorem isGLB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsGLB (s : Set α) i)
    (hs : s.Nonempty) : i in s := by
  rw [← mem_coe]
  exact ((isGLB_iff_isLeast i s hs).mp his).1

/--
theorem `isLUB_mem` / 定理 `isLUB_mem`

English:
theorem isLUB_mem
  statement: [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
  proof: @isGLB_mem αᵒᵈ _ i s his hs

中文:
定理 isLUB_mem
  结论: [线性序 α] {i : α} (s : 有限集 α) (his : IsLUB (s : 集合 α) i)
  证明: @isGLB_mem αᵒᵈ _ i s his hs

Depends on / 依赖: isGLB_mem
-/
theorem isLUB_mem [LinearOrder α] {i : α} (s : Finset α) (his : IsLUB (s : Set α) i)
    (hs : s.Nonempty) : i in s :=
  @isGLB_mem αᵒᵈ _ i s his hs

end Finset

/--
theorem `Multiset.exists_max_image` / 定理 `Multiset.exists_max_image`

English:
theorem Multiset.exists_max_image
  statement: {α R : Type*} [LinearOrder R] (f : α -> R) {s : Multiset α}
  proof: by
  classical
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s.toFinset f (toFinset_nonempty.mpr hs)
  exact ⟨y, mem_toFinset.mp hys, fun _ hz => hy _ (mem_toFinset.mpr hz)⟩

中文:
定理 Multiset.存在_max_image
  结论: {α R : 类型} [线性序 R] (f : α -> R) {s : Multiset α}
  证明: by
  classical
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s.toFinset f (toFinset_nonempty.mpr hs)
  exact ⟨y, mem_toFinset.mp hys, fun _ hz => hy _ (mem_toFinset.mpr hz)⟩

Depends on / 依赖: Finset, Finset.exists_max_image, classical, exists_max_image, mem_toFinset, mem_toFinset.mp, mem_toFinset.mpr, s.toFinset, toFinset, toFinset_nonempty, toFinset_nonempty.mpr
-/
theorem Multiset.exists_max_image {α R : Type*} [LinearOrder R] (f : α -> R) {s : Multiset α}
    (hs : s != 0) : exists y in s, forall z in s, f z <= f y := by
  classical
  obtain ⟨y, hys, hy⟩ := Finset.exists_max_image s.toFinset f (toFinset_nonempty.mpr hs)
  exact ⟨y, mem_toFinset.mp hys, fun _ hz => hy _ (mem_toFinset.mpr hz)⟩

/--
theorem `Multiset.exists_min_image` / 定理 `Multiset.exists_min_image`

English:
theorem Multiset.exists_min_image
  statement: {α R : Type*} [LinearOrder R] (f : α -> R) {s : Multiset α}
  proof: @exists_max_image α Rᵒᵈ _ f s hs

中文:
定理 Multiset.存在_min_image
  结论: {α R : 类型} [线性序 R] (f : α -> R) {s : Multiset α}
  证明: @exists_max_image α Rᵒᵈ _ f s hs

Depends on / 依赖: exists_max_image
-/
theorem Multiset.exists_min_image {α R : Type*} [LinearOrder R] (f : α -> R) {s : Multiset α}
    (hs : s != 0) : exists y in s, forall z in s, f y <= f z :=
  @exists_max_image α Rᵒᵈ _ f s hs
