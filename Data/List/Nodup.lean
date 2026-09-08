/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/
module

public import Mathlib.Data.List.Forall2

/-!
# Lists with no duplicates

`List.Nodup` is defined in `Data/List/Basic`. In this file we prove various properties of this
predicate.
-/

public section

universe u v

open Function

variable {α : Type u} {β : Type v} {l l₁ l₂ : List α} {r : α → α → Prop} {a : α}

namespace List

/-
**List.Pairwise.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u} {l : List α} {r : α → α → Prop} [Std.Irrefl r], List.Pairwi
se r l → l.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `ne_of_irrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [Std.Irrefl r] {x y : 
α}, r x y → x ≠ y
-/
protected theorem Pairwise.nodup {l : List α} {r : α → α → Prop} [Std.Irrefl r] (h : Pairwise r l) :
    Nodup l :=
  h.imp ne_of_irrefl

open scoped Relator in
/-
**List.rel_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：rel_nodup {r : α -> β -> Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (·
 ↔ ·)) Nodup Nodup | _, _, Forall₂.nil => by simp only [nodup_nil] | _, _, Foral
l₂.cons hab h => by simpa only [nodup_cons] using Relator.rel_and (Relator.rel_n
ot (rel_mem hr hab h)) (rel_nodup hr h)  protected theorem Nodup.cons (ha : a ∉ 
l) (hl : Nodup l) : Nodup (a :: l)
参数：hr : Relator.BiUnique r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Forall₂.brecOn`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop} 
  {motive : (a : List α) → (a_1 : List β) → List.Forall₂ R a a_1 → Prop} {a : Li
st α} {a_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Relator.rel_and`：rel_and : ((· ↔ ·) ⇒ (· ↔ ·) ⇒ (· ↔ ·)) (· ∧ ·) (· ∧ ·)
· 使用引理 `Relator.rel_not`：rel_not : (Iff ⇒ Iff) Not Not
· 使用定理 `List.rel_mem`：∀ {α : Type u_1} {β : Type u_2} {R : α → β → Prop},   Rela
tor.BiUnique R →     Relator.LiftFun R (Relator.LiftFun (List.Forall₂ R) Iff) (f
un…
-/
theorem rel_nodup {r : α → β → Prop} (hr : Relator.BiUnique r) : (Forall₂ r ⇒ (· ↔ ·)) Nodup Nodup
  | _, _, Forall₂.nil => by simp only [nodup_nil]
  | _, _, Forall₂.cons hab h => by
    simpa only [nodup_cons] using
      Relator.rel_and (Relator.rel_not (rel_mem hr hab h)) (rel_nodup hr h)
/-
**List.Nodup.cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α}, a ∉ l → l.Nodup → (a :: l).Nodup
参数：a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
-/
protected theorem Nodup.cons (ha : a ∉ l) (hl : Nodup l) : Nodup (a :: l) :=
  nodup_cons.2 ⟨ha, hl⟩
/-
**List.nodup_singleton** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_singleton (a : α) : Nodup [a]
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.pairwise_singleton`：∀ {α : Type u_1} (R : α → α → Prop) (a : α), Li
st.Pairwise R [a]
-/
theorem nodup_singleton (a : α) : Nodup [a] :=
  pairwise_singleton _ _
/-
**List.Nodup.of_cons** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup → l.Nodup
参数：a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
-/
theorem Nodup.of_cons (h : Nodup (a :: l)) : Nodup l :=
  (nodup_cons.1 h).2
/-
**List.Nodup.notMem** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup → a ∉ l
参数：a :: l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
-/
theorem Nodup.notMem (h : (a :: l).Nodup) : a ∉ l :=
  (nodup_cons.1 h).1
/-
**List.not_nodup_cons_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_nodup_cons_of_mem : a in l -> ¬Nodup (a :: l)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `imp_not_comm`：∀ {a b : Prop}, a → ¬b ↔ b → ¬a
· 使用定理 `List.Nodup.notMem`：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup →
 a ∉ l
-/
theorem not_nodup_cons_of_mem : a ∈ l → ¬Nodup (a :: l) :=
  imp_not_comm.1 Nodup.notMem
/-
**List.not_nodup_pair** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_nodup_pair (a : α) : ¬Nodup [a, a]
参数：a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_nodup_cons_of_mem`：not_nodup_cons_of_mem : a in l -> ¬Nodup (a 
:: l)
· 使用定理 `List.mem_singleton_self`：∀ {α : Type u_1} (a : α), a ∈ [a]
-/
theorem not_nodup_pair (a : α) : ¬Nodup [a, a] :=
  not_nodup_cons_of_mem <| mem_singleton_self _
/-
**List.nodup_iff_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_sublist {l : List α} : Nodup l ↔ forall a, ¬[a, a] <+ l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_nodup_pair`：not_nodup_pair (a : α) : ¬Nodup [a, a]
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.nodup_nil`：∀ {α : Type u_1}, [].Nodup
· 使用定理 `List.Nodup.cons`：∀ {α : Type u} {l : List α} {a : α}, a ∉ l → l.Nodup → 
(a :: l).Nodup
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.singleton_sublist`：∀ {α : Type u_1} {a : α} {l : List α}, [a].Subli
st l ↔ a ∈ l
· 使用定理 `List.sublist_cons_of_sublist`：sublist_cons_of_sublist (a : α) (h : l₁ <+
 l₂) : l₁ <+ a :: l₂
-/
theorem nodup_iff_sublist {l : List α} : Nodup l ↔ ∀ a, ¬[a, a] <+ l :=
  ⟨fun d a h => not_nodup_pair a (d.sublist h),
    by
      induction l <;> intro h; · exact nodup_nil
      case cons a l IH =>
        exact (IH fun a s => h a <| sublist_cons_of_sublist _ s).cons
          fun al => h a <| (singleton_sublist.2 al).cons_cons _⟩

@[simp]
/-
**List.nodup_mergeSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_mergeSort {l : List α} {le : α -> α -> Bool} : (l.mergeSort le).Nodu
p ↔ l.Nodup
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.mergeSort_perm`：∀ {α : Type u_1} (l : List α) (le : α → α → Bool), 
(l.mergeSort le).Perm l
-/
theorem nodup_mergeSort {l : List α} {le : α → α → Bool} : (l.mergeSort le).Nodup ↔ l.Nodup :=
  (mergeSort_perm l le).nodup_iff

protected alias ⟨_, Nodup.mergeSort⟩ := nodup_mergeSort
/-
**List.nodup_iff_injective_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_injective_getElem {l : List α} : Nodup l ↔ Function.Injective (f
un i : Fin l.length => l[i.1])
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.pairwise_iff_getElem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α},   List.Pairwise R l ↔ ∀ (i j : ℕ) (_hi : i < l.length) (_hj : j < l.length)
, i < j → R l[i…
· 使用定理 `Nat.lt_trichotomy`：∀ (a b : ℕ), a < b ∨ a = b ∨ b < a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `Fin.val_eq_of_eq`：∀ {n : ℕ} {i j : Fin n}, i = j → ↑i = ↑j
-/
theorem nodup_iff_injective_getElem {l : List α} :
    Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1]) :=
  pairwise_iff_getElem.trans
    ⟨fun h i j hg => by
      obtain ⟨i, hi⟩ := i; obtain ⟨j, hj⟩ := j
      rcases Nat.lt_trichotomy i j with (hij | rfl | hji)
      · exact (h i j hi hj hij hg).elim
      · rfl
      · exact (h j i hj hi hji hg.symm).elim,
      fun hinj i j hi hj hij h => Nat.ne_of_lt hij (Fin.val_eq_of_eq (@hinj ⟨i, hi⟩ ⟨j, hj⟩ h))⟩
/-
**List.nodup_iff_injective_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_injective_get {l : List α} : Nodup l ↔ Function.Injective l.get
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_iff_injective_getElem`：nodup_iff_injective_getElem {l : List 
α} : Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1])
-/
theorem nodup_iff_injective_get {l : List α} : Nodup l ↔ Function.Injective l.get :=
  nodup_iff_injective_getElem
/-
**List.Nodup.injective_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → Function.Injective l.get
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
-/
protected theorem Nodup.injective_get {l : List α} (h : Nodup l) : Function.Injective l.get :=
  nodup_iff_injective_get.mp h
/-
**List._root_.Function.Injective.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem _root_.Function.Injective.nodup {l : List α}
    (h : Function.Injective l.get) : l.Nodup := nodup_iff_injective_get.mpr h
/-
**List.Nodup.get_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i j : Fin l.length}, l.get i = l
.get j ↔ i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
-/
theorem Nodup.get_inj_iff {l : List α} (h : Nodup l) {i j : Fin l.length} :
    l.get i = l.get j ↔ i = j :=
  (nodup_iff_injective_get.1 h).eq_iff
/-
**List.Nodup.getElem_inj_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i : ℕ} {hi : i < l.length} {j : 
ℕ} {hj : j < l.length}, l[i] = l[j] ↔ i = j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.get_inj_iff`：∀ {α : Type u} {l : List α}, l.Nodup → ∀ {i j : 
Fin l.length}, l.get i = l.get j ↔ i = j
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
-/
theorem Nodup.getElem_inj_iff {l : List α} (h : Nodup l)
    {i : Nat} {hi : i < l.length} {j : Nat} {hj : j < l.length} :
    l[i] = l[j] ↔ i = j := by
  have := @Nodup.get_inj_iff _ _ h ⟨i, hi⟩ ⟨j, hj⟩
  simpa
/-
**List.nodup_iff_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_getElem?_ne_getElem? {l : List α} : l.Nodup ↔ forall i j : Nat, 
i < j -> j < l.length -> l[i]? != l[j]?
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nodup_iff_getElem?_ne_getElem? {l : List α} :
    l.Nodup ↔ ∀ i j : ℕ, i < j → j < l.length → l[i]? ≠ l[j]? := by
  grind [List.pairwise_iff_getElem]
/-
**List.Nodup.ne_singleton_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → ∀ (x : α), l ≠ [x] ↔ l = [] ∨ ∃ y ∈
 l, y ≠ x
参数：x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `List.Nodup.of_cons`：∀ {α : Type u} {l : List α} {a : α}, (a :: l).Nodup 
→ l.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem Nodup.ne_singleton_iff {l : List α} (h : Nodup l) (x : α) :
    l ≠ [x] ↔ l = [] ∨ ∃ y ∈ l, y ≠ x := by
  induction l with
  | nil => simp
  | cons hd tl hl =>
    specialize hl h.of_cons
    by_cases hx : tl = [x]
    · simpa [hx, and_comm, and_or_left] using h
    · rw [← Ne, hl] at hx
      rcases hx with (rfl | ⟨y, hy, hx⟩)
      · simp
      · suffices ∃ y ∈ hd :: tl, y ≠ x by simpa [ne_nil_of_mem hy]
        exact ⟨y, mem_cons_of_mem _ hy, hx⟩
/-
**List.not_nodup_of_get_eq_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：not_nodup_of_get_eq_of_ne (xs : List α) (n m : Fin xs.length) (h : xs.get 
n = xs.get m) (hne : n != m) : ¬Nodup xs
参数：xs : List α；n m : Fin xs.length；h : xs.get n = xs.get m；hne : n != m。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
-/
theorem not_nodup_of_get_eq_of_ne (xs : List α) (n m : Fin xs.length)
    (h : xs.get n = xs.get m) (hne : n ≠ m) : ¬Nodup xs := by
  rw [nodup_iff_injective_get]
  exact fun hinj => hne (hinj h)
/-
**List.Nodup.head_eq_getLast_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} (hne : l ≠ []), l.Nodup → (l.head hne = l.getL
ast hne ↔ ∃ x, l = [x])
参数：hne : l ≠ []；l.head hne = l.getLast hne ↔ ∃ x, l = [x]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma Nodup.head_eq_getLast_iff (hne : l ≠ []) (hnd : l.Nodup) :
    l.head hne = l.getLast hne ↔ ∃ x, l = [x] := by
  cases l <;> grind

-- This is incorrectly named and should be `idxOf_get`;
-- this already exists, so will require a deprecation dance.
/-
**List.get_idxOf** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_idxOf [BEq α] [LawfulBEq α] {l : List α} (H : Nodup l) (i : Fin l.leng
th) : idxOf (get l i) l = i
参数：H : Nodup l；i : Fin l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nodup.idxOf_getElem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] 
{xs : List α},   xs.Nodup → ∀ (i : ℕ) (h : i < xs.length), List.idxOf xs[i] xs =
 i
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_idxOf [BEq α] [LawfulBEq α] {l : List α} (H : Nodup l) (i : Fin l.length) :
    idxOf (get l i) l = i := by
  simp [H]
/-
**List.nodup_iff_count_le_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_count_le_one [BEq α] [LawfulBEq α] {l : List α} : Nodup l ↔ fora
ll a, count a l <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.nodup_iff_sublist`：nodup_iff_sublist {l : List α} : Nodup l ↔ foral
l a, ¬[a, a] <+ l
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `List.replicate_sublist_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α
] {n : ℕ} {a : α} {l : List α},   (List.replicate n a).Sublist l ↔ n ≤ List.coun
t a l
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Nat.not_lt`：∀ {a b : ℕ}, ¬a < b ↔ b ≤ a
-/
theorem nodup_iff_count_le_one [BEq α] [LawfulBEq α] {l : List α} : Nodup l ↔ ∀ a, count a l ≤ 1 :=
  nodup_iff_sublist.trans <|
    forall_congr' fun a =>
      have : replicate 2 a <+ l ↔ 1 < count a l := replicate_sublist_iff ..
      (not_congr this).trans Nat.not_lt
/-
**List.nodup_iff_count_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_iff_count_eq_one [BEq α] [LawfulBEq α] : Nodup l ↔ forall a in l, co
unt a l = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.count_pos_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, 0 < List.count a l ↔ a ∈ l
-/
theorem nodup_iff_count_eq_one [BEq α] [LawfulBEq α] : Nodup l ↔ ∀ a ∈ l, count a l = 1 :=
  nodup_iff_count_le_one.trans <| forall_congr' fun x => by rw [← count_pos_iff]; grind
/-
**List.get_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_bijective_iff [BEq α] [LawfulBEq α] : l.get.Bijective ↔ forall a, l.co
unt a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_count_eq_one`：nodup_iff_count_eq_one [BEq α] [LawfulBEq α
] : Nodup l ↔ forall a in l, count a l = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `List.mem_iff_get`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l ↔ ∃ n, l.
get n = a
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `List.one_le_count_iff`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a 
: α} {l : List α}, 1 ≤ List.count a l ↔ a ∈ l
-/
theorem get_bijective_iff [BEq α] [LawfulBEq α] : l.get.Bijective ↔ ∀ a, l.count a = 1 :=
  ⟨fun h a ↦ (nodup_iff_count_eq_one.mp <| nodup_iff_injective_get.mpr h.injective)
    a <| mem_iff_get.mpr <| h.surjective a,
  fun h ↦ ⟨nodup_iff_injective_get.mp <| nodup_iff_count_eq_one.mpr fun a _ ↦ h a,
    fun a ↦ mem_iff_get.mp <| List.one_le_count_iff.mp <| by grind⟩⟩
/-
**List.getElem_bijective_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_bijective_iff [BEq α] [LawfulBEq α] : (fun (n : Fin l.length) => l
[n]).Bijective ↔ forall a, l.count a = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_bijective_iff`：get_bijective_iff [BEq α] [LawfulBEq α] : l.get.
Bijective ↔ forall a, l.count a = 1
-/
theorem getElem_bijective_iff [BEq α] [LawfulBEq α] :
    (fun (n : Fin l.length) ↦ l[n]).Bijective ↔ ∀ a, l.count a = 1 :=
  get_bijective_iff

@[simp]
/-
**List.count_eq_one_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} (d : Nodup 
l) (h : a in l) : count a l = 1
参数：d : Nodup l；h : a in l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_count_eq_one`：nodup_iff_count_eq_one [BEq α] [LawfulBEq α
] : Nodup l ↔ forall a in l, count a l = 1
-/
theorem count_eq_one_of_mem [BEq α] [LawfulBEq α] {a : α} {l : List α} (d : Nodup l) (h : a ∈ l) :
    count a l = 1 :=
  nodup_iff_count_eq_one.mp d a h
/-
**List.Nodup.of_append_left** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, (l₁ ++ l₂).Nodup → l₁.Nodup
参数：l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.sublist_append_left`：∀ {α : Type u_1} (l₁ l₂ : List α), l₁.Sublist 
(l₁ ++ l₂)
-/
theorem Nodup.of_append_left : Nodup (l₁ ++ l₂) → Nodup l₁ :=
  Nodup.sublist (sublist_append_left l₁ l₂)
/-
**List.Nodup.of_append_right** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, (l₁ ++ l₂).Nodup → l₂.Nodup
参数：l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.sublist_append_right`：∀ {α : Type u_1} (l₁ l₂ : List α), l₂.Sublist
 (l₁ ++ l₂)
-/
theorem Nodup.of_append_right : Nodup (l₁ ++ l₂) → Nodup l₂ :=
  Nodup.sublist (sublist_append_right l₁ l₂)

/-- This is a variant of the `nodup_append` from the standard library,
which does not use `Disjoint`. -/
/-
**List.nodup_append'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_append' {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ 
Disjoint l₁ l₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
This is a variant of the `nodup_append` from the standard library,
which does not use `Disjoint`.
-/
theorem nodup_append' {l₁ l₂ : List α} :
    Nodup (l₁ ++ l₂) ↔ Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂ := by
  simp only [Nodup, pairwise_append, disjoint_iff_ne]
/-
**List.disjoint_of_nodup_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：disjoint_of_nodup_append {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂)) : Disjoin
t l₁ l₂
参数：d : Nodup (l₁ ++ l₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_append'`：nodup_append' {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ 
Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂
-/
theorem disjoint_of_nodup_append {l₁ l₂ : List α} (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂ :=
  (nodup_append'.1 d).2.2

protected alias Nodup.disjoint := disjoint_of_nodup_append
/-
**List.Nodup.append** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup → l₁.Disjoint l₂ → (l
₁ ++ l₂).Nodup
参数：l₁ ++ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_append'`：nodup_append' {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ 
Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂
-/
theorem Nodup.append (d₁ : Nodup l₁) (d₂ : Nodup l₂) (dj : Disjoint l₁ l₂) : Nodup (l₁ ++ l₂) :=
  nodup_append'.2 ⟨d₁, d₂, dj⟩
/-
**List.nodup_append_comm** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ Nodup (l₂ ++ l₁) := by
  simp only [nodup_append', and_left_comm, disjoint_comm]
/-
**List.nodup_middle** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_middle {a : α} {l₁ l₂ : List α} : Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :
: (l₁ ++ l₂))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_middle {a : α} {l₁ l₂ : List α} :
    Nodup (l₁ ++ a :: l₂) ↔ Nodup (a :: (l₁ ++ l₂)) := by
  simp only [nodup_append', not_or, and_left_comm, and_assoc, nodup_cons, mem_append,
    disjoint_cons_right]
/-
**List.Nodup.of_map** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α}, (List.map f l).Nodup
 → l.Nodup
参数：f : α → β；List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.of_map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop}
 {l : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), S (f a) (f b) → R 
a b) → Lis…
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem Nodup.of_map (f : α → β) {l : List α} : Nodup (map f l) → Nodup l :=
  (Pairwise.of_map f) fun _ _ => mt <| congr_arg f
/-
**List.Nodup.map_on** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β},   (∀ x ∈ l, ∀ y ∈ l,
 f x = f y → x = y) → l.Nodup → (List.map f l).Nodup
参数：∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y；List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.map`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Prop} {l
 : List α} {S : β → β → Prop} (f : α → β),   (∀ (a b : α), R a b → S (f a) (f b)
) → Lis…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Pairwise.and_mem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l ↔ List.Pairwise (fun x y => x ∈ l ∧ y ∈ l ∧ R x y) l
-/
theorem Nodup.map_on {f : α → β} (H : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (d : Nodup l) :
    (map f l).Nodup :=
  Pairwise.map _ (fun a b ⟨ma, mb, n⟩ e => n (H a ma b mb e)) (Pairwise.and_mem.1 d)
/-
**List.inj_on_of_nodup_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：inj_on_of_nodup_map {f : α -> β} {l : List α} (d : Nodup (map f l)) : fora
ll ⦃x⦄, x in l -> forall ⦃y⦄, y in l -> f x = f y -> x = y
参数：d : Nodup (map f l)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inj_on_of_nodup_map {f : α → β} {l : List α} (d : Nodup (map f l)) :
    ∀ ⦃x⦄, x ∈ l → ∀ ⦃y⦄, y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => simp
  | cons hd tl ih =>
    simp only [map, nodup_cons, mem_map, not_exists, not_and, ← Ne.eq_def] at d
    simp only [mem_cons]
    rintro _ (rfl | h₁) _ (rfl | h₂) h₃
    · rfl
    · apply (d.1 _ h₂ h₃.symm).elim
    · apply (d.1 _ h₁ h₃).elim
    · apply ih d.2 h₁ h₂ h₃
/-
**List.nodup_map_iff_inj_on** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_map_iff_inj_on {f : α -> β} {l : List α} (d : Nodup l) : Nodup (map 
f l) ↔ forall x in l, forall y in l, f x = f y -> x = y
参数：d : Nodup l。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.inj_on_of_nodup_map`：inj_on_of_nodup_map {f : α -> β} {l : List α} 
(d : Nodup (map f l)) : forall ⦃x⦄, x in l -> forall ⦃y⦄, y in l -> f x = f y ->
 x = y
· 使用定理 `List.Nodup.map_on`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β},
   (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (List.map f l).Nodup
-/
theorem nodup_map_iff_inj_on {f : α → β} {l : List α} (d : Nodup l) :
    Nodup (map f l) ↔ ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y :=
  ⟨inj_on_of_nodup_map, fun h => d.map_on h⟩
/-
**List.Nodup.map** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Function.Injective f
 → l.Nodup → (List.map f l).Nodup
参数：List.map f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.map_on`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β},
   (∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) → l.Nodup → (List.map f l).Nodup
-/
protected theorem Nodup.map {f : α → β} (hf : Injective f) : Nodup l → Nodup (map f l) :=
  Nodup.map_on fun _ _ _ _ h => hf h
/-
**List.nodup_map_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_map_iff {f : α -> β} {l : List α} (hf : Injective f) : Nodup (map f 
l) ↔ Nodup l
参数：hf : Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
-/
theorem nodup_map_iff {f : α → β} {l : List α} (hf : Injective f) : Nodup (map f l) ↔ Nodup l :=
  ⟨Nodup.of_map _, Nodup.map hf⟩

@[simp]
/-
**List.nodup_attach** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `List.attach_map_subtype_val`：∀ {α : Type u_1} (l : List α), List.map Sub
type.val l.attach = l
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem nodup_attach {l : List α} : Nodup (attach l) ↔ Nodup l :=
  ⟨fun h => attach_map_subtype_val l ▸ h.map fun _ _ => Subtype.ext, fun h =>
    Nodup.of_map Subtype.val ((attach_map_subtype_val l).symm ▸ h)⟩

protected alias ⟨Nodup.of_attach, Nodup.attach⟩ := nodup_attach
/-
**List.Nodup.pmap** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} {p : α → Prop} {f : (a : α) → p a → β} {l : Li
st α} {H : ∀ a ∈ l, p a},   (∀ (a : α) (ha : p a) (b : α) (hb : p b), f a ha = f
 b hb → a = b) → l.Nodup → (List.pmap f l H).Nodup
参数：a : α；∀ (a : α) (ha : p a) (b : α) (hb : p b), f a ha = f b hb → a = b；List.p
map f l H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nodup.pmap {p : α → Prop} {f : ∀ a, p a → β} {l : List α} {H}
    (hf : ∀ a ha b hb, f a ha = f b hb → a = b) (h : Nodup l) : Nodup (pmap f l H) := by
  grind
/-
**List.Nodup.filter** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} (p : α → Bool) {l : List α}, l.Nodup → (List.filter p l).No
dup
参数：p : α → Bool；List.filter p l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.filter`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α} (
p : α → Bool), List.Pairwise R l → List.Pairwise R (List.filter p l)
-/
theorem Nodup.filter (p : α → Bool) {l} : Nodup l → Nodup (filter p l) := by
  simpa using! Pairwise.filter p

@[simp]
/-
**List.nodup_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.pairwise_reverse`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α},
 List.Pairwise R l.reverse ↔ List.Pairwise (fun a b => R b a) l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nodup l :=
  pairwise_reverse.trans <| by simp only [Nodup, Ne, eq_comm]
/-
**List.nodup_concat** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_concat (l : List α) (u : α) : (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup
参数：l : List α；u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.nodup_reverse`：nodup_reverse {l : List α} : Nodup (reverse l) ↔ Nod
up l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.reverse_append`：∀ {α : Type u_1} {as bs : List α}, (as ++ bs).rever
se = bs.reverse ++ as.reverse
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_concat (l : List α) (u : α) : (l.concat u).Nodup ↔ u ∉ l ∧ l.Nodup := by
  rw [← nodup_reverse]
  simp
/-
**List.Nodup.tail** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α}, l.Nodup → l.tail.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.nodup`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.tail_sublist`：∀ {α : Type u_1} (l : List α), l.tail.Sublist l
-/
@[simp, grind ←] protected lemma Nodup.tail {l : List α} (h : Nodup l) : Nodup l.tail :=
  l.tail_sublist.nodup h
/-
**List.nodup_tail_reverse** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：nodup_tail_reverse (l : List α) (h : l[0]? = l.getLast?) : Nodup l.reverse
.tail ↔ Nodup l.tail
参数：l : List α；h : l[0]? = l.getLast?。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `List.reverse_cons`：∀ {α : Type u} {a : α} {as : List α}, (a :: as).rever
se = as.reverse ++ [a]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.tail_reverse`：∀ {α : Type u_1} {l : List α}, l.reverse.tail = l.dro
pLast.reverse
· 使用定理 `List.dropLast_cons_of_ne_nil`：∀ {α : Type u} {x : α} {l : List α}, l ≠ [
] → (x :: l).dropLast = x :: l.dropLast
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
· 使用定理 `List.getElem?_eq_getElem`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i <
 l.length), l[i]? = some l[i]
· 使用定理 `List.getElem_cons`：∀ {α : Type u_1} {i : ℕ} {a : α} {l : List α} (w : i 
< (a :: l).length), (a :: l)[i] = if h : i = 0 then a else l[i - 1]
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.getLast?_eq_getElem?`：∀ {α : Type u_1} {l : List α}, l.getLast? = l
[l.length - 1]?
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.dropLast_eq_take`：∀ {α : Type u_1} {l : List α}, l.dropLast = List.
take (l.length - 1) l
· 使用定理 `List.take_append_getLast`：∀ {α : Type u_1} (l : List α) (h : l ≠ []), Li
st.take (l.length - 1) l ++ [l.getLast h] = l
· 使用定理 `List.nodup_append_comm`：nodup_append_comm {l₁ l₂ : List α} : Nodup (l₁ +
+ l₂) ↔ Nodup (l₂ ++ l₁)
· 使用定理 `List.getLast_eq_getElem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.g
etLast h = l[l.length - 1]
-/
lemma nodup_tail_reverse (l : List α) (h : l[0]? = l.getLast?) :
    Nodup l.reverse.tail ↔ Nodup l.tail := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hl : l = []
    · simp_all
    · simp_all only [List.tail_reverse, List.nodup_reverse,
        List.dropLast_cons_of_ne_nil hl, List.tail_cons]
      simp only [length_cons, Nat.zero_lt_succ, getElem?_eq_getElem,
        Nat.add_one_sub_one, Nat.lt_add_one, Option.some.injEq, List.getElem_cons,
        show l.length ≠ 0 by aesop, ↓reduceDIte, getLast?_eq_getElem?] at h
      rw [h,
        show l.Nodup = (l.dropLast ++ [l.getLast hl]).Nodup by
          simp [List.dropLast_eq_take],
        List.nodup_append_comm]
      simp [List.getLast_eq_getElem]
/-
**List.Nodup.eq_of_head_mem_of_suffix** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁ <:+ l₂ → ∀ {hne : l₂ ≠ []}, l₂.head hn
e ∈ l₁ → l₂.Nodup → l₁ = l₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
-/
lemma Nodup.eq_of_head_mem_of_suffix (h : l₁ <:+ l₂) {hne : l₂ ≠ []} (hl : l₂.head hne ∈ l₁)
    (hnd : l₂.Nodup) : l₁ = l₂ := by
  grind [List.IsSuffix]
/-
**List.Nodup.eq_of_getLast_mem_of_prefix** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁ <+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.getLast
 hne ∈ l₁ → l₂.Nodup → l₁ = l₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
lemma Nodup.eq_of_getLast_mem_of_prefix (h : l₁ <+: l₂) {hne : l₂ ≠ []} (hl : l₂.getLast hne ∈ l₁)
    (hnd : l₂.Nodup) : l₁ = l₂ := by
  grind [List.IsPrefix]
/-
**List.Nodup.prefix_of_head_mem_of_infix** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.head h
ne ∈ l₁ → l₂.Nodup → l₁ <+: l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
-/
lemma Nodup.prefix_of_head_mem_of_infix (h : l₁ <:+: l₂) {hne : l₂ ≠ []} (hl : l₂.head hne ∈ l₁)
    (hnd : l₂.Nodup) : l₁ <+: l₂ := by
  grind [List.IsInfix]
/-
**List.Nodup.suffix_of_getLast_mem_of_infix** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodu
p`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α}, l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.getLas
t hne ∈ l₁ → l₂.Nodup → l₁ <:+ l₂
该定理/引理表达了一个蕴含关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
lemma Nodup.suffix_of_getLast_mem_of_infix (h : l₁ <:+: l₂) {hne : l₂ ≠ []}
    (hl : l₂.getLast hne ∈ l₁) (hnd : l₂.Nodup) : l₁ <:+ l₂ := by
  grind [List.IsInfix]
/-
**List.Nodup.eq_of_head_mem_of_getLast_mem_of_infix** 是 Mathlib 中的一个定理，位于命名空间 `L
ist.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α},   l₁ <:+: l₂ → ∀ {hne : l₂ ≠ []}, l₂.head
 hne ∈ l₁ → l₂.getLast hne ∈ l₁ → l₂.Nodup → l₁ = l₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
lemma Nodup.eq_of_head_mem_of_getLast_mem_of_infix (h : l₁ <:+: l₂) {hne : l₂ ≠ []}
    (hlh : l₂.head hne ∈ l₁) (hlg : l₂.getLast hne ∈ l₁) (hnd : l₂.Nodup) : l₁ = l₂ := by
  grind [List.IsInfix]
/-
**List.Nodup.erase_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} [inst : BEq α] [LawfulBEq α] {l : List α},   l.Nodup → ∀ (i
 : ℕ) (h : i < l.length), l.erase l[i] = l.eraseIdx i
参数：i : ℕ；h : i < l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.erase_cons_head`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), (a :: l).erase a = l
· 使用定理 `List.eraseIdx_zero`：∀ {α : Type u_1} {l : List α}, l.eraseIdx 0 = l.tail
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Nodup.erase_getElem [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup)
    (i : Nat) (h : i < l.length) : l.erase l[i] = l.eraseIdx ↑i := by
  induction l generalizing i with
  | nil => simp
  | cons a l IH =>
    cases i with
    | zero => simp
    | succ i => grind
/-
**List.Nodup.erase_get** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} [inst : BEq α] [LawfulBEq α] {l : List α},   l.Nodup → ∀ (i
 : Fin l.length), l.erase (l.get i) = l.eraseIdx ↑i
参数：i : Fin l.length；l.get i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nodup.erase_getElem`：∀ {α : Type u} [inst : BEq α] [LawfulBEq α] {l
 : List α},   l.Nodup → ∀ (i : ℕ) (h : i < l.length), l.erase l[i] = l.eraseIdx 
i
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Nodup.erase_get [BEq α] [LawfulBEq α] {l : List α} (hl : l.Nodup) (i : Fin l.length) :
    l.erase (l.get i) = l.eraseIdx ↑i := by
  simp [erase_getElem, hl]
/-
**List.Nodup.diff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} [inst : BEq α] [LawfulBEq α], l₁.Nodup → (
l₁.diff l₂).Nodup
参数：l₁.diff l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l
₂.Nodup → l₁.Nodup
· 使用定理 `List.diff_sublist`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (l₁ l₂ 
: List α), (l₁.diff l₂).Sublist l₁
-/
theorem Nodup.diff [BEq α] [LawfulBEq α] : l₁.Nodup → (l₁.diff l₂).Nodup :=
  Nodup.sublist <| diff_sublist _ _
/-
**List.nodup_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_flatten {L : List (List α)} : Nodup (flatten L) ↔ (forall l in L, No
dup l) ∧ Pairwise Disjoint L
参数：List α。
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
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.disjoint_left`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Disjoint l₂ ↔ 
∀ ⦃a : α⦄, a ∈ l₁ → a ∉ l₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nodup_flatten {L : List (List α)} :
    Nodup (flatten L) ↔ (∀ l ∈ L, Nodup l) ∧ Pairwise Disjoint L := by
  simp only [Nodup, pairwise_flatten, disjoint_left.symm, forall_mem_ne]
/-
**List.nodup_flatMap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nodup_flatMap {l₁ : List α} {f : α -> List β} : Nodup (l₁.flatMap f) ↔ (fo
rall x in l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `forall_comm`：∀ {α : Sort u_2} {β : Sort u_1} {p : α → β → Prop}, (∀ (a :
 α) (b : β), p a b) ↔ ∀ (b : β) (a : α), p a b
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `forall_eq'`：∀ {α : Sort u_1} {p : α → Prop} {a' : α}, (∀ (a : α), a' = a
 → p a) ↔ p a'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem nodup_flatMap {l₁ : List α} {f : α → List β} :
    Nodup (l₁.flatMap f) ↔
      (∀ x ∈ l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁ := by
  simp only [List.flatMap, nodup_flatten, pairwise_map, and_comm, mem_map,
    exists_imp, and_imp]
  rw [show (∀ (l : List β) (x : α), f x = l → x ∈ l₁ → Nodup l) ↔ ∀ x : α, x ∈ l₁ → Nodup (f x)
      from forall_comm.trans <| forall_congr' fun _ => forall_eq']
/-
**List.Nodup.product** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} {l₁ : List α} {l₂ : List β}, l₁.Nodup → l₂.Nod
up → (l₁ ×ˢ l₂).Nodup
参数：l₁ ×ˢ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_flatMap`：nodup_flatMap {l₁ : List α} {f : α -> List β} : Nodu
p (l₁.flatMap f) ↔ (forall x in l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
protected theorem Nodup.product {l₂ : List β} (d₁ : l₁.Nodup) (d₂ : l₂.Nodup) :
    (l₁ ×ˢ l₂).Nodup :=
  nodup_flatMap.2
    ⟨fun a _ => d₂.map <| LeftInverse.injective fun b => (rfl : (a, b).2 = b),
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
/-
**List.Nodup.sigma** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ : List α} {σ : α → Type u_1} {l₂ : (a : α) → List (σ a)
},   l₁.Nodup → (∀ (a : α), (l₂ a).Nodup) → (l₁.sigma l₂).Nodup
参数：a : α；σ a；∀ (a : α), (l₂ a).Nodup；l₁.sigma l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.nodup_flatMap`：nodup_flatMap {l₁ : List α} {f : α -> List β} : Nodu
p (l₁.flatMap f) ↔ (forall x in l₁, Nodup (f x)) ∧ Pairwise (Disjoint on f) l₁
· 使用定理 `List.Nodup.map`：∀ {α : Type u} {β : Type v} {l : List α} {f : α → β}, Fu
nction.Injective f → l.Nodup → (List.map f l).Nodup
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `List.Pairwise.imp`：∀ {α : Type u_1} {R S : α → α → Prop},   (∀ {a b : α}
, R a b → S a b) → ∀ {l : List α}, List.Pairwise R l → List.Pairwise S l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_map`：∀ {α : Type u_1} {β : Type u_2} {b : β} {f : α → β} {l : L
ist α}, b ∈ List.map f l ↔ ∃ a ∈ l, f a = b
-/
theorem Nodup.sigma {σ : α → Type*} {l₂ : ∀ a, List (σ a)} (d₁ : Nodup l₁)
    (d₂ : ∀ a, Nodup (l₂ a)) : (l₁.sigma l₂).Nodup :=
  nodup_flatMap.2
    ⟨fun a _ => (d₂ a).map fun b b' h => by injection h with _ h,
      d₁.imp fun {a₁ a₂} n x h₁ h₂ => by
        rcases mem_map.1 h₁ with ⟨b₁, _, rfl⟩
        rcases mem_map.1 h₂ with ⟨b₂, mb₂, ⟨⟩⟩
        exact n rfl⟩
/-
**List.Nodup.filterMap** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} {l : List α} {f : α → Option β},   (∀ (a a' : 
α), ∀ b ∈ f a, b ∈ f a' → a = a') → l.Nodup → (List.filterMap f l).Nodup
参数：∀ (a a' : α), ∀ b ∈ f a, b ∈ f a' → a = a'；List.filterMap f l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.filterMap`：∀ {β : Type u_1} {α : Type u_2} {R : α → α → Pr
op} {S : β → β → Prop} (f : α → Option β),   (∀ (a a' : α), R a a' → ∀ (b : β), 
f a = some b …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem Nodup.filterMap {f : α → Option β} (h : ∀ a a' b, b ∈ f a → b ∈ f a' → a = a') :
    Nodup l → Nodup (filterMap f l) :=
  (Pairwise.filterMap f) @fun a a' n b bm b' bm' e => n <| h a a' b' (by rw [← e]; exact bm) bm'
/-
**List.Nodup.concat** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α}, a ∉ l → l.Nodup → (l.concat a).Nodup
参数：l.concat a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.concat_eq_append`：∀ {α : Type u} {as : List α} {a : α}, as.concat a
 = as ++ [a]
· 使用定理 `List.Nodup.append`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Nodup → l₂.Nodup 
→ l₁.Disjoint l₂ → (l₁ ++ l₂).Nodup
· 使用定理 `List.nodup_singleton`：nodup_singleton (a : α) : Nodup [a]
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.disjoint_singleton`：∀ {α : Type u_1} {l : List α} {a : α}, l.Disjoi
nt [a] ↔ a ∉ l
-/
protected theorem Nodup.concat (h : a ∉ l) (h' : l.Nodup) : (l.concat a).Nodup := by
  rw [concat_eq_append]; exact h'.append (nodup_singleton _) (disjoint_singleton.2 h)
/-
**List.Nodup.insert** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {a : α} [inst : BEq α] [LawfulBEq α], l.Nodup 
→ (List.insert a l).Nodup
参数：List.insert a l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insert_of_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a : α
} {l : List α}, a ∈ l → List.insert a l = l
· 使用定理 `List.insert_of_not_mem`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] {a
 : α} {l : List α}, a ∉ l → List.insert a l = a :: l
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
-/
protected theorem Nodup.insert [BEq α] [LawfulBEq α] (h : l.Nodup) : (l.insert a).Nodup :=
  if h' : a ∈ l then by rw [insert_of_mem h']; exact h
  else by rw [insert_of_not_mem h', nodup_cons]; constructor <;> assumption
/-
**List.Nodup.union** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₂ : List α} [inst : BEq α] [LawfulBEq α] (l₁ : List α), l
₂.Nodup → (l₁ ∪ l₂).Nodup
参数：l₁ : List α；l₁ ∪ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.insert`：∀ {α : Type u} {l : List α} {a : α} [inst : BEq α] [L
awfulBEq α], l.Nodup → (List.insert a l).Nodup
-/
theorem Nodup.union [BEq α] [LawfulBEq α] (l₁ : List α) (h : Nodup l₂) : (l₁ ∪ l₂).Nodup := by
  induction l₁ generalizing l₂ with
  | nil => exact h
  | cons a l₁ ih => exact (ih h).insert
/-
**List.Nodup.inter** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ : List α} [inst : BEq α] (l₂ : List α), l₁.Nodup → (l₁ 
∩ l₂).Nodup
参数：l₂ : List α；l₁ ∩ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Nodup.filter`：∀ {α : Type u} (p : α → Bool) {l : List α}, l.Nodup →
 (List.filter p l).Nodup
-/
theorem Nodup.inter [BEq α] (l₂ : List α) : Nodup l₁ → Nodup (l₁ ∩ l₂) :=
  Nodup.filter _
/-
**List.Nodup.sdiff_eq_filter** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} [inst : BEq α] [inst_1 : LawfulBEq α] {l₁ l₂ : List α},   l
₁.Nodup → l₁.diff l₂ = List.filter (fun x => decide (x ∉ l₂)) l₁
参数：fun x => decide (x ∉ l₂)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nodup.sdiff_eq_filter [BEq α] [LawfulBEq α] :
    ∀ {l₁ l₂ : List α} (_ : l₁.Nodup), l₁.diff l₂ = l₁.filter (· ∉ l₂)
  | l₁, [], _ => by simp
  | l₁, a :: l₂, hl₁ => by
    rw [diff_cons, (hl₁.erase _).sdiff_eq_filter, hl₁.erase_eq_filter, filter_filter]
    simp only [decide_not, bne, Bool.and_comm, decide_mem_cons, Bool.not_or]

@[deprecated (since := "2026-06-03")] alias Nodup.diff_eq_filter := Nodup.sdiff_eq_filter
/-
**List.Nodup.mem_sdiff_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l₁ l₂ : List α} {a : α} [inst : BEq α] [LawfulBEq α], l₁.N
odup → (a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂)
参数：a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Nodup.sdiff_eq_filter`：∀ {α : Type u} [inst : BEq α] [inst_1 : Lawf
ulBEq α] {l₁ l₂ : List α},   l₁.Nodup → l₁.diff l₂ = List.filter (fun x => decid
e (x ∉ l₂)) l₁
· 使用定理 `List.mem_filter`：∀ {α : Type u_1} {p : α → Bool} {as : List α} {x : α}, 
x ∈ List.filter p as ↔ x ∈ as ∧ p x = true
· 使用定理 `decide_eq_true_iff`：∀ {p : Prop} [inst : Decidable p], decide p = true ↔
 p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Nodup.mem_sdiff_iff [BEq α] [LawfulBEq α] (hl₁ : l₁.Nodup) :
    a ∈ l₁.diff l₂ ↔ a ∈ l₁ ∧ a ∉ l₂ := by
  rw [hl₁.sdiff_eq_filter, mem_filter, decide_eq_true_iff]

@[deprecated (since := "2026-06-03")] alias Nodup.mem_diff_iff := Nodup.mem_sdiff_iff
/-
**List.Nodup.set** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {n : ℕ} {a : α}, l.Nodup → a ∉ l → (l.set n a)
.Nodup
参数：l.set n a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Nodup.set :
    ∀ {l : List α} {n : ℕ} {a : α} (_ : l.Nodup) (_ : a ∉ l), (l.set n a).Nodup
  | [], _, _, _, _ => nodup_nil
  | _ :: _, 0, _, hl, ha => nodup_cons.2 ⟨mt (mem_cons_of_mem _) ha, (nodup_cons.1 hl).2⟩
  | _ :: _, _ + 1, _, hl, ha =>
    nodup_cons.2
      ⟨fun h =>
        (mem_or_eq_of_mem_set h).elim (nodup_cons.1 hl).1 fun hba => ha (hba ▸ mem_cons_self),
        hl.of_cons.set (mt (mem_cons_of_mem _) ha)⟩
/-
**List.Nodup.map_update** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {β : Type v} [inst : DecidableEq α] {l : List α},   l.Nodup
 →     ∀ (f : α → β) (x : α) (y : β),       List.map (Function.update f x y) l =
 if x ∈ l then (List.map f l).set (List.idxOf x l) y else List.map f l
参数：f : α → β；x : α；y : β；Function.update f x y；List.map f l；List.idxOf x l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.idxOf_cons_self`：∀ {α : Type u_1} {a : α} [inst : BEq α] [ReflBEq α
] {l : List α}, List.idxOf a (a :: l) = 0
· 使用定理 `EquivBEq.toReflBEq`：∀ {α : Type u_1} {inst : BEq α} [self : EquivBEq α],
 ReflBEq α
· 使用定理 `instEquivBEqOfLawfulBEq`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α], 
EquivBEq α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ite.congr_simp`：∀ {α : Sort u} (c c_1 : Prop),   c = c_1 →     ∀ {h : De
cidable c} [h_1 : Decidable c_1] (t t_1 : α),       t = t_1 → ∀ (e e_1 : α), e =
 e_1…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `List.idxOf_cons_ne`：idxOf_cons_ne {a b : α} (l : List α) (h : b != a) : 
idxOf a (b :: l) = succ (idxOf a l)
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
-/
theorem Nodup.map_update [DecidableEq α] {l : List α} (hl : l.Nodup) (f : α → β) (x : α) (y : β) :
    l.map (Function.update f x y) =
      if x ∈ l then (l.map f).set (l.idxOf x) y else l.map f := by
  induction l with | nil => simp | cons hd tl ihl => ?_
  rw [nodup_cons] at hl
  simp only [mem_cons, map, ihl hl.2]
  by_cases H : hd = x
  · subst hd
    simp [hl.1]
  · simp [Ne.symm H, H, ← apply_ite (cons (f hd))]
/-
**List.Nodup.pairwise_of_forall_ne** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} {l : List α} {r : α → α → Prop}, l.Nodup → (∀ a ∈ l, ∀ b ∈ 
l, a ≠ b → r a b) → List.Pairwise r l
参数：∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nodup.pairwise_of_forall_ne {l : List α} {r : α → α → Prop} (hl : l.Nodup)
    (h : ∀ a ∈ l, ∀ b ∈ l, a ≠ b → r a b) : l.Pairwise r := by
  grind [List.pairwise_iff_forall_sublist]
/-
**List.Nodup.take_eq_filter_mem** 是 Mathlib 中的一个定理，位于命名空间 `List.Nodup`。
形式化陈述：∀ {α : Type u} [inst : BEq α] [LawfulBEq α] {l : List α} {n : ℕ},   l.Nodu
p → List.take n l = List.filter (fun a => List.elem a (List.take n l)) l
参数：fun a => List.elem a (List.take n l)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Nodup.take_eq_filter_mem [BEq α] [LawfulBEq α] :
    ∀ {l : List α} {n : ℕ} (_ : l.Nodup), l.take n = l.filter (l.take n).elem
  | [], n, _ => by simp
  | b::l, 0, _ => by simp
  | b::l, n + 1, hl => by
    rw [take_succ_cons, Nodup.take_eq_filter_mem (Nodup.of_cons hl), filter_cons_of_pos (by simp)]
    congr 1
    refine List.filter_congr ?_
    intro x hx
    have : x ≠ b := fun h => (nodup_cons.1 hl).1 (h ▸ hx)
    simp +contextual [List.mem_filter, this, hx]
end List

/-
**Option.toList_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Option`。
形式化陈述：∀ {α : Type u} (o : Option α), o.toList.Nodup
参数：o : Option α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.nodup_nil`：∀ {α : Type u_1}, [].Nodup
· 使用定理 `List.nodup_singleton`：nodup_singleton (a : α) : Nodup [a]
-/
theorem Option.toList_nodup : ∀ o : Option α, o.toList.Nodup
  | none => List.nodup_nil
  | some x => List.nodup_singleton x
