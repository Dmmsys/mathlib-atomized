/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.SuccPred.Limit

/-!

# Relation between `IsSuccPrelimit` and `iSup` in (conditionally) complete linear orders.

-/

@[expose] public section

open Order Set

variable {ι : Sort*} {α : Type*}

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder α] [Nonempty ι] {f : ι → α} {s : Set α} {x : α}

@[to_dual]
/-
**csSup_mem_of_not_isSuccLimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_mem_of_not_isSuccLimit (hne : s.Nonempty) (hbdd : BddAbove s) (hlim 
: ¬ IsSuccLimit (sSup s)) : sSup s in s
参数：hne : s.Nonempty；hbdd : BddAbove s；hlim : ¬ IsSuccLimit (sSup s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `not_and_or`：not_and_or : ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `Order.isSuccLimit_iff`：∀ {α : Type u_1} [inst : Preorder α] (a : α), Ord
er.IsSuccLimit a ↔ ¬IsMin a ∧ Order.IsSuccPrelimit a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsMin.eq_of_le`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, IsMi
n a → b ≤ a → b = a
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `exists_lt_of_lt_csSup`：exists_lt_of_lt_csSup (hs : s.Nonempty) (hb : b <
 sSup s) : exists a in s, b < a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma csSup_mem_of_not_isSuccLimit (hne : s.Nonempty) (hbdd : BddAbove s)
    (hlim : ¬ IsSuccLimit (sSup s)) : sSup s ∈ s := by
  rw [isSuccLimit_iff, not_and_or, not_not] at hlim
  rcases hlim with (hmin | hlim)
  · have ⟨a, has⟩ := hne
    rwa [← hmin.eq_of_le <| le_csSup hbdd has]
  · have ⟨y, hy⟩ := not_forall_not.mp hlim
    have ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
    exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

@[to_dual]
/-
**exists_eq_ciSup_of_not_isSuccLimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_eq_ciSup_of_not_isSuccLimit (hbdd : BddAbove (range f)) (hf : ¬ IsS
uccLimit (⨆ i, f i)) : exists i, f i = ⨆ i, f i
参数：hbdd : BddAbove (range f)；hf : ¬ IsSuccLimit (⨆ i, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `csSup_mem_of_not_isSuccLimit`：csSup_mem_of_not_isSuccLimit (hne : s.None
mpty) (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) : sSup s in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
lemma exists_eq_ciSup_of_not_isSuccLimit (hbdd : BddAbove (range f))
    (hf : ¬ IsSuccLimit (⨆ i, f i)) : ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccLimit (range_nonempty f) hbdd hf

@[deprecated csInf_mem_of_not_isPredLimit (since := "2026-04-24")]
/-
**csInf_mem_of_not_isPredPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csInf_mem_of_not_isPredPrelimit (hne : s.Nonempty) (hbdd : BddBelow s) (hl
im : ¬ IsPredPrelimit (sInf s)) : sInf s in s
参数：hne : s.Nonempty；hbdd : BddBelow s；hlim : ¬ IsPredPrelimit (sInf s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `csInf_mem_of_not_isPredLimit`：∀ {α : Type u_2} [inst : ConditionallyComp
leteLinearOrder α] {s : Set α},   s.Nonempty → BddBelow s → ¬Order.IsPredLimit (
sInf s) → sInf s ∈…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
lemma csInf_mem_of_not_isPredPrelimit (hne : s.Nonempty) (hbdd : BddBelow s)
    (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s ∈ s :=
  csInf_mem_of_not_isPredLimit hne hbdd <| mt IsPredLimit.isPredPrelimit hlim

@[deprecated exists_eq_ciInf_of_not_isPredLimit (since := "2026-04-24")]
/-
**exists_eq_ciInf_of_not_isPredPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_eq_ciInf_of_not_isPredPrelimit (hf : BddBelow (range f)) (hf' : ¬ I
sPredPrelimit (⨅ i, f i)) : exists i, f i = ⨅ i, f i
参数：hf : BddBelow (range f)；hf' : ¬ IsPredPrelimit (⨅ i, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_eq_ciInf_of_not_isPredLimit`：∀ {ι : Sort u_1} {α : Type u_2} [ins
t : ConditionallyCompleteLinearOrder α] [Nonempty ι] {f : ι → α},   BddBelow (Se
t.range f) → ¬Order.IsPr…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
lemma exists_eq_ciInf_of_not_isPredPrelimit (hf : BddBelow (range f))
    (hf' : ¬ IsPredPrelimit (⨅ i, f i)) : ∃ i, f i = ⨅ i, f i :=
  exists_eq_ciInf_of_not_isPredLimit hf <| mt IsPredLimit.isPredPrelimit hf'

@[to_dual]
/-
**IsLUB.mem_of_nonempty_of_not_isSuccLimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.mem_of_nonempty_of_not_isSuccLimit (hs : IsLUB s x) (hne : s.Nonempt
y) (hx : ¬ IsSuccLimit x) : x in s
参数：hs : IsLUB s x；hne : s.Nonempty；hx : ¬ IsSuccLimit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `csSup_mem_of_not_isSuccLimit`：csSup_mem_of_not_isSuccLimit (hne : s.None
mpty) (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) : sSup s in s
· 使用定理 `IsLUB.bddAbove`：IsLUB.bddAbove (h : IsLUB s a) : BddAbove s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
-/
lemma IsLUB.mem_of_nonempty_of_not_isSuccLimit (hs : IsLUB s x) (hne : s.Nonempty)
    (hx : ¬ IsSuccLimit x) : x ∈ s :=
  hs.csSup_eq hne ▸ csSup_mem_of_not_isSuccLimit hne hs.bddAbove (hs.csSup_eq hne ▸ hx)

@[to_dual]
/-
**IsLUB.exists_of_nonempty_of_not_isSuccLimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.exists_of_nonempty_of_not_isSuccLimit (hf : IsLUB (range f) x) (hx :
 ¬ IsSuccLimit x) : exists i, f i = x
参数：hf : IsLUB (range f) x；hx : ¬ IsSuccLimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLUB.mem_of_nonempty_of_not_isSuccLimit`：IsLUB.mem_of_nonempty_of_not_i
sSuccLimit (hs : IsLUB s x) (hne : s.Nonempty) (hx : ¬ IsSuccLimit x) : x in s
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
-/
lemma IsLUB.exists_of_nonempty_of_not_isSuccLimit (hf : IsLUB (range f) x) (hx : ¬ IsSuccLimit x) :
    ∃ i, f i = x :=
  hf.mem_of_nonempty_of_not_isSuccLimit (range_nonempty f) hx

@[deprecated mem_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]
/-
**IsLUB.mem_of_nonempty_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.mem_of_nonempty_of_not_isSuccPrelimit (hs : IsLUB s x) (hne : s.None
mpty) (hx : ¬ IsSuccPrelimit x) : x in s
参数：hs : IsLUB s x；hne : s.Nonempty；hx : ¬ IsSuccPrelimit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLUB.mem_of_nonempty_of_not_isSuccLimit`：IsLUB.mem_of_nonempty_of_not_i
sSuccLimit (hs : IsLUB s x) (hne : s.Nonempty) (hx : ¬ IsSuccLimit x) : x in s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
lemma IsLUB.mem_of_nonempty_of_not_isSuccPrelimit
    (hs : IsLUB s x) (hne : s.Nonempty) (hx : ¬ IsSuccPrelimit x) : x ∈ s :=
  hs.mem_of_nonempty_of_not_isSuccLimit hne <| mt IsSuccLimit.isSuccPrelimit hx

@[deprecated mem_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]
/-
**IsGLB.mem_of_nonempty_of_not_isPredPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGLB.mem_of_nonempty_of_not_isPredPrelimit (hs : IsGLB s x) (hne : s.None
mpty) (hx : ¬ IsPredPrelimit x) : x in s
参数：hs : IsGLB s x；hne : s.Nonempty；hx : ¬ IsPredPrelimit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.mem_of_nonempty_of_not_isPredLimit`：∀ {α : Type u_2} [inst : Condi
tionallyCompleteLinearOrder α] {s : Set α} {x : α},   IsGLB s x → s.Nonempty → ¬
Order.IsPredLimit x → x ∈ s
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
lemma IsGLB.mem_of_nonempty_of_not_isPredPrelimit
    (hs : IsGLB s x) (hne : s.Nonempty) (hx : ¬ IsPredPrelimit x) : x ∈ s :=
  hs.mem_of_nonempty_of_not_isPredLimit hne <| mt IsPredLimit.isPredPrelimit hx

@[deprecated exists_of_nonempty_of_not_isSuccLimit (since := "2026-04-24")]
/-
**IsLUB.exists_of_nonempty_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLUB.exists_of_nonempty_of_not_isSuccPrelimit (hf : IsLUB (range f) x) (h
x : ¬ IsSuccPrelimit x) : exists i, f i = x
参数：hf : IsLUB (range f) x；hx : ¬ IsSuccPrelimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLUB.exists_of_nonempty_of_not_isSuccLimit`：IsLUB.exists_of_nonempty_of
_not_isSuccLimit (hf : IsLUB (range f) x) (hx : ¬ IsSuccLimit x) : exists i, f i
 = x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
lemma IsLUB.exists_of_nonempty_of_not_isSuccPrelimit
    (hf : IsLUB (range f) x) (hx : ¬ IsSuccPrelimit x) : ∃ i, f i = x :=
  hf.exists_of_nonempty_of_not_isSuccLimit <| mt IsSuccLimit.isSuccPrelimit hx

@[deprecated exists_of_nonempty_of_not_isPredLimit (since := "2026-04-24")]
/-
**IsGLB.exists_of_nonempty_of_not_isPredPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGLB.exists_of_nonempty_of_not_isPredPrelimit (hf : IsGLB (range f) x) (h
x : ¬ IsPredPrelimit x) : exists i, f i = x
参数：hf : IsGLB (range f) x；hx : ¬ IsPredPrelimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.exists_of_nonempty_of_not_isPredLimit`：∀ {ι : Sort u_1} {α : Type 
u_2} [inst : ConditionallyCompleteLinearOrder α] [Nonempty ι] {f : ι → α} {x : α
},   IsGLB (Set.range f) x → ¬Ord…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsPredLimit.isPredPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsPredLimit a → Order.IsPredPrelimit a
-/
lemma IsGLB.exists_of_nonempty_of_not_isPredPrelimit
    (hf : IsGLB (range f) x) (hx : ¬ IsPredPrelimit x) : ∃ i, f i = x :=
  hf.exists_of_nonempty_of_not_isPredLimit <| mt IsPredLimit.isPredPrelimit hx

/-- Every conditionally complete linear order with well-founded `<` is a successor order, by setting
the successor of an element to be the infimum of all larger elements. -/
@[instance_reducible, deprecated SuccOrder.ofLinearWellFoundedLT (since := "2026-04-12")]
/-
**ConditionallyCompleteLinearOrder.toSuccOrder** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConditionallyCompleteLinearOrder.toSuccOrder [WellFoundedLT α] : SuccOrder
 α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every conditionally complete linear order with well-founded `<` is a successor o
rder, by setting
the successor of an element to be the infimum of all larger elements.
-/
noncomputable def ConditionallyCompleteLinearOrder.toSuccOrder [WellFoundedLT α] :
    SuccOrder α := .ofLinearWellFoundedLT _

end ConditionallyCompleteLinearOrder

section ConditionallyCompleteLinearOrderBot
variable [ConditionallyCompleteLinearOrderBot α] {f : ι → α} {s : Set α} {x : α}

/-- See `csSup_mem_of_not_isSuccLimit` for the `ConditionallyCompleteLinearOrder` version. -/
/-
**csSup_mem_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：csSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup 
s in s
参数：hlim : ¬ IsSuccPrelimit (sSup s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `csSup_mem_of_not_isSuccLimit`：csSup_mem_of_not_isSuccLimit (hne : s.None
mpty) (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) : sSup s in s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用引理 `csSup_of_not_bddAbove`：csSup_of_not_bddAbove (hs : ¬BddAbove s) : sSup s
 = sSup ∅
· 使用定理 `Order.isSuccPrelimit_bot`：isSuccPrelimit_bot [OrderBot α] : IsSuccPrelim
it (⊥ : α)
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a

--- 原说明 ---
See `csSup_mem_of_not_isSuccLimit` for the `ConditionallyCompleteLinearOrder` ve
rsion.
-/
lemma csSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s ∈ s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · simp [isSuccPrelimit_bot] at hlim
  · apply csSup_mem_of_not_isSuccLimit hs _ <| mt IsSuccLimit.isSuccPrelimit hlim
    contrapose! hlim
    rw [csSup_of_not_bddAbove hlim, csSup_empty]
    exact isSuccPrelimit_bot

@[deprecated (since := "2026-04-24")]
alias csSup_mem_of_not_isSuccPrelimit' := csSup_mem_of_not_isSuccPrelimit

/-- See `exists_eq_ciSup_of_not_isSuccLimit` for the `ConditionallyCompleteLinearOrder` version. -/
/-
**exists_eq_ciSup_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_eq_ciSup_of_not_isSuccPrelimit (hf' : ¬ IsSuccPrelimit (⨆ i, f i)) 
: exists i, f i = ⨆ i, f i
参数：hf' : ¬ IsSuccPrelimit (⨆ i, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `csSup_mem_of_not_isSuccPrelimit`：csSup_mem_of_not_isSuccPrelimit (hlim :
 ¬ IsSuccPrelimit (sSup s)) : sSup s in s

--- 原说明 ---
See `exists_eq_ciSup_of_not_isSuccLimit` for the `ConditionallyCompleteLinearOrd
er` version.
-/
lemma exists_eq_ciSup_of_not_isSuccPrelimit (hf' : ¬ IsSuccPrelimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccPrelimit hf'

@[deprecated (since := "2026-04-24")]
alias exists_eq_ciSup_of_not_isSuccPrelimit' := exists_eq_ciSup_of_not_isSuccPrelimit
/-
**Order.IsSuccPrelimit.sSup_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Order.IsSuccPrelimit.sSup_Iio (h : IsSuccPrelimit x) : sSup (Iio x) = x
参数：h : IsSuccPrelimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_bot_or_bot_lt`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Order
Bot α] (a : α), a = ⊥ ∨ ⊥ < a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsMin.Iio_eq`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, IsMin a → Se
t.Iio a = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `csSup_empty`：csSup_empty : (sSup ∅ : α) = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLUB.csSup_eq`：IsLUB.csSup_eq (H : IsLUB s a) (ne : s.Nonempty) : sSup 
s = a
· 使用定理 `Order.IsSuccPrelimit.isLUB_Iio`：∀ {α : Type u_1} {a : α} [inst : LinearO
rder α], Order.IsSuccPrelimit a → IsLUB (Set.Iio a) a
-/
theorem Order.IsSuccPrelimit.sSup_Iio (h : IsSuccPrelimit x) : sSup (Iio x) = x := by
  obtain rfl | hx := eq_bot_or_bot_lt x
  · simp
  · exact h.isLUB_Iio.csSup_eq ⟨⊥, hx⟩
/-
**Order.IsSuccPrelimit.iSup_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Order.IsSuccPrelimit.iSup_Iio (h : IsSuccPrelimit x) : ⨆ a : Iio x, a.1 = 
x
参数：h : IsSuccPrelimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Order.IsSuccPrelimit.sSup_Iio`：Order.IsSuccPrelimit.sSup_Iio (h : IsSucc
Prelimit x) : sSup (Iio x) = x
-/
theorem Order.IsSuccPrelimit.iSup_Iio (h : IsSuccPrelimit x) : ⨆ a : Iio x, a.1 = x := by
  rw [← sSup_eq_iSup', h.sSup_Iio]
/-
**Order.IsSuccLimit.sSup_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Order.IsSuccLimit.sSup_Iio (h : IsSuccLimit x) : sSup (Iio x) = x
参数：h : IsSuccLimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.sSup_Iio`：Order.IsSuccPrelimit.sSup_Iio (h : IsSucc
Prelimit x) : sSup (Iio x) = x
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem Order.IsSuccLimit.sSup_Iio (h : IsSuccLimit x) : sSup (Iio x) = x :=
  h.isSuccPrelimit.sSup_Iio
/-
**Order.IsSuccLimit.iSup_Iio** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Order.IsSuccLimit.iSup_Iio (h : IsSuccLimit x) : ⨆ a : Iio x, a.1 = x
参数：h : IsSuccLimit x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Order.IsSuccPrelimit.iSup_Iio`：Order.IsSuccPrelimit.iSup_Iio (h : IsSucc
Prelimit x) : ⨆ a : Iio x, a.1 = x
· 使用定理 `Order.IsSuccLimit.isSuccPrelimit`：∀ {α : Type u_1} [inst : Preorder α] {
a : α}, Order.IsSuccLimit a → Order.IsSuccPrelimit a
-/
theorem Order.IsSuccLimit.iSup_Iio (h : IsSuccLimit x) : ⨆ a : Iio x, a.1 = x :=
  h.isSuccPrelimit.iSup_Iio
/-
**sSup_Iio_eq_self_iff_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sSup_Iio_eq_self_iff_isSuccPrelimit : sSup (Iio x) = x ↔ IsSuccPrelimit x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `csSup_mem_of_not_isSuccPrelimit`：csSup_mem_of_not_isSuccPrelimit (hlim :
 ¬ IsSuccPrelimit (sSup s)) : sSup s in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Order.IsSuccPrelimit.sSup_Iio`：Order.IsSuccPrelimit.sSup_Iio (h : IsSucc
Prelimit x) : sSup (Iio x) = x
-/
theorem sSup_Iio_eq_self_iff_isSuccPrelimit : sSup (Iio x) = x ↔ IsSuccPrelimit x := by
  refine ⟨fun h ↦ ?_, IsSuccPrelimit.sSup_Iio⟩
  by_contra hx
  rw [← h] at hx
  simpa [h] using csSup_mem_of_not_isSuccPrelimit hx
/-
**iSup_Iio_eq_self_iff_isSuccPrelimit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_Iio_eq_self_iff_isSuccPrelimit : ⨆ a : Iio x, a.1 = x ↔ IsSuccPrelimi
t x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `sSup_Iio_eq_self_iff_isSuccPrelimit`：sSup_Iio_eq_self_iff_isSuccPrelimit
 : sSup (Iio x) = x ↔ IsSuccPrelimit x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem iSup_Iio_eq_self_iff_isSuccPrelimit : ⨆ a : Iio x, a.1 = x ↔ IsSuccPrelimit x := by
  rw [← sSup_eq_iSup', sSup_Iio_eq_self_iff_isSuccPrelimit]
/-
**iSup_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSup_succ [SuccOrder α] (x : α) : ⨆ a : Iio x, succ a.1 = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `ciSup_le_iff'`：ciSup_le_iff' {f : ι -> α} (h : BddAbove (range f)) {a : 
α} : ⨆ i, f i <= a ↔ forall i, f i <= a
· 使用定理 `Order.succ_le_of_lt`：succ_le_of_lt {a b : α} : a < b -> succ a <= b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_of_forall_lt`：le_of_forall_lt (H : forall c, c < a -> c < b) : a <= b
· 使用定理 `lt_ciSup_iff'`：lt_ciSup_iff' {f : ι -> α} (h : BddAbove (range f)) : a <
 iSup f ↔ exists i, a < f i
· 使用定理 `Order.lt_succ_of_not_isMax`：∀ {α : Type u_1} [inst : Preorder α] [inst_1
 : SuccOrder α] {a : α}, ¬IsMax a → a < Order.succ a
· 使用定理 `LT.lt.not_isMax`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b →
 ¬IsMax a
-/
theorem iSup_succ [SuccOrder α] (x : α) : ⨆ a : Iio x, succ a.1 = x := by
  have H : BddAbove (range fun a : Iio x ↦ succ a.1) :=
    ⟨succ x, by simp +contextual [upperBounds, succ_le_succ, le_of_lt]⟩
  apply le_antisymm _ (le_of_forall_lt fun y hy ↦ ?_)
  · rw [ciSup_le_iff' H]
    exact fun a ↦ succ_le_of_lt a.2
  · rw [lt_ciSup_iff' H]
    exact ⟨⟨y, hy⟩, lt_succ_of_not_isMax hy.not_isMax⟩

end ConditionallyCompleteLinearOrderBot

section CompleteLinearOrder
variable [CompleteLinearOrder α] {s : Set α} {f : ι → α} {x : α}

/-
**sSup_mem_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s
 in s
参数：hlim : ¬ IsSuccPrelimit (sSup s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `lt_sSup_iff`：lt_sSup_iff : b < sSup s ↔ exists a in s, b < a
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma sSup_mem_of_not_isSuccPrelimit (hlim : ¬ IsSuccPrelimit (sSup s)) : sSup s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := lt_sSup_iff.mp hy.lt
  exact eq_of_le_of_not_lt (le_sSup his) (hy.2 hi) ▸ his
/-
**sInf_mem_of_not_isPredPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sInf_mem_of_not_isPredPrelimit (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s
 in s
参数：hlim : ¬ IsPredPrelimit (sInf s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_forall_not`：not_forall_not : (¬forall x, ¬p x) ↔ exists x, p x
· 使用定理 `sInf_lt_iff`：∀ {α : Type u_1} [inst : CompleteLinearOrder α] {s : Set α}
 {b : α}, sInf s < b ↔ ∃ a ∈ s, a < b
· 使用定理 `CovBy.lt`：CovBy.lt (h : a ⋖ b) : a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma sInf_mem_of_not_isPredPrelimit (hlim : ¬ IsPredPrelimit (sInf s)) : sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his
/-
**exists_eq_iSup_of_not_isSuccPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_eq_iSup_of_not_isSuccPrelimit (hf : ¬ IsSuccPrelimit (⨆ i, f i)) : 
exists i, f i = ⨆ i, f i
参数：hf : ¬ IsSuccPrelimit (⨆ i, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sSup_mem_of_not_isSuccPrelimit`：sSup_mem_of_not_isSuccPrelimit (hlim : ¬
 IsSuccPrelimit (sSup s)) : sSup s in s
-/
lemma exists_eq_iSup_of_not_isSuccPrelimit (hf : ¬ IsSuccPrelimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  sSup_mem_of_not_isSuccPrelimit hf
/-
**exists_eq_iInf_of_not_isPredPrelimit** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_eq_iInf_of_not_isPredPrelimit (hf : ¬ IsPredPrelimit (⨅ i, f i)) : 
exists i, f i = ⨅ i, f i
参数：hf : ¬ IsPredPrelimit (⨅ i, f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `sInf_mem_of_not_isPredPrelimit`：sInf_mem_of_not_isPredPrelimit (hlim : ¬
 IsPredPrelimit (sInf s)) : sInf s in s
-/
lemma exists_eq_iInf_of_not_isPredPrelimit (hf : ¬ IsPredPrelimit (⨅ i, f i)) :
    ∃ i, f i = ⨅ i, f i :=
  sInf_mem_of_not_isPredPrelimit hf

end CompleteLinearOrder

