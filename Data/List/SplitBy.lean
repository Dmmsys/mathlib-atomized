/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import Mathlib.Data.List.Chain
public import Mathlib.Data.List.Flatten

/-!
# Split a list into contiguous runs of elements which pairwise satisfy a relation.

This file provides the basic API for `List.splitBy` which is defined in Core.
The main results are the following:

- `List.flatten_splitBy`: the lists in `List.splitBy` join to the original list.
- `List.nil_notMem_splitBy`: the empty list is not contained in `List.splitBy`.
- `List.isChain_of_mem_splitBy`: any two adjacent elements in a list in
  `List.splitBy` are related by the specified relation.
- `List.isChain_getLast_head_splitBy`: the last element of each list in `List.splitBy` is not
  related to the first element of the next list.
-/

public section

namespace List

variable {α : Type*} {m : List α}

@[simp]
/-
**List.splitBy_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_nil (r : α -> α -> Bool) : splitBy r [] = []
参数：r : α -> α -> Bool。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem splitBy_nil (r : α → α → Bool) : splitBy r [] = [] :=
  rfl
/-
**List.splitByLoop_eq_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem splitByLoop_eq_append {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (gs : List (List α)) : splitBy.loop r l a g gs = gs.reverse ++ splitBy.loop r l a g [] := by
  induction l generalizing a g gs with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    simp_rw [splitBy.loop]
    split <;> rw [IH]
    conv_rhs => rw [IH]
    simp
/-
**List.flatten_splitByLoop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem flatten_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    (splitBy.loop r l a g []).flatten = g.reverse ++ a :: l := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop, splitByLoop_eq_append [_]]
    split <;> simp [IH]

@[simp]
/-
**List.flatten_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatten_splitBy (r : α -> α -> Bool) (l : List α) : (l.splitBy r).flatten 
= l
参数：r : α -> α -> Bool；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.List.SplitBy.0.List.flatten_splitByLoop`：∀ {α : Ty
pe u_1} {r : α → α → Bool} {l : List α} {a : α} {g : List α},   (List.splitBy.lo
op r l a g []).flatten = g.reverse ++ a :: l
-/
theorem flatten_splitBy (r : α → α → Bool) (l : List α) : (l.splitBy r).flatten = l :=
  match l with
  | nil => rfl
  | cons _ _ => flatten_splitByLoop

@[simp]
/-
**List.splitBy_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_eq_nil {r : α -> α -> Bool} {l : List α} : l.splitBy r = [] ↔ l = 
[]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.flatten_splitBy`：flatten_splitBy (r : α -> α -> Bool) (l : List α) 
: (l.splitBy r).flatten = l
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem splitBy_eq_nil {r : α → α → Bool} {l : List α} : l.splitBy r = [] ↔ l = [] := by
  have := flatten_splitBy r l
  refine ⟨fun _ ↦ ?_, ?_⟩ <;> simp_all
/-
**List.splitBy_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_ne_nil {r : α -> α -> Bool} {l : List α} : l.splitBy r != [] ↔ l !
= []
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `List.splitBy_eq_nil`：splitBy_eq_nil {r : α -> α -> Bool} {l : List α} : 
l.splitBy r = [] ↔ l = []
-/
theorem splitBy_ne_nil {r : α → α → Bool} {l : List α} : l.splitBy r ≠ [] ↔ l ≠ [] :=
  splitBy_eq_nil.not
/-
**List.nil_notMem_splitByLoop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem nil_notMem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α} :
    [] ∉ splitBy.loop r l a g [] := by
  induction l generalizing a g with
  | nil => simp [splitBy.loop]
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · exact IH
    · rw [splitByLoop_eq_append, mem_append]
      simpa using IH

@[simp]
/-
**List.nil_notMem_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：nil_notMem_splitBy (r : α -> α -> Bool) (l : List α) : [] ∉ l.splitBy r
参数：r : α -> α -> Bool；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `_private.Mathlib.Data.List.SplitBy.0.List.nil_notMem_splitByLoop`：∀ {α :
 Type u_1} {r : α → α → Bool} {l : List α} {a : α} {g : List α}, [] ∉ List.split
By.loop r l a g []
-/
theorem nil_notMem_splitBy (r : α → α → Bool) (l : List α) : [] ∉ l.splitBy r :=
  match l with
  | nil => not_mem_nil
  | cons _ _ => nil_notMem_splitByLoop
/-
**List.ne_nil_of_mem_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：ne_nil_of_mem_splitBy {r : α -> α -> Bool} {l : List α} (h : m in l.splitB
y r) : m != []
参数：h : m in l.splitBy r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem ne_nil_of_mem_splitBy {r : α → α → Bool} {l : List α} (h : m ∈ l.splitBy r) : m ≠ [] :=
  fun _ ↦ by simp_all
/-
**List.head_head_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：head_head_splitBy (r : α -> α -> Bool) {l : List α} (hn : l != []) : ((l.s
plitBy r).head (splitBy_ne_nil.2 hn)).head (ne_nil_of_mem_splitBy (head_mem _)) 
= l.head hn
参数：r : α -> α -> Bool；hn : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.splitBy_ne_nil`：splitBy_ne_nil {r : α -> α -> Bool} {l : List α} : 
l.splitBy r != [] ↔ l != []
· 使用定理 `List.ne_nil_of_mem_splitBy`：ne_nil_of_mem_splitBy {r : α -> α -> Bool} {
l : List α} (h : m in l.splitBy r) : m != []
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.flatten_splitBy`：flatten_splitBy (r : α -> α -> Bool) (l : List α) 
: (l.splitBy r).flatten = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.head_head_eq_head_flatten`：head_head_eq_head_flatten {l : List (Lis
t α)} (hl : l != []) (hl' : l.head hl != []) : (l.head hl).head hl' = l.flatten.
head (flatten_ne_nil…
· 使用定理 `List.head.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = as_
1) (a : as ≠ []), as.head a = as_1.head ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem head_head_splitBy (r : α → α → Bool) {l : List α} (hn : l ≠ []) :
    ((l.splitBy r).head (splitBy_ne_nil.2 hn)).head
      (ne_nil_of_mem_splitBy (head_mem _)) = l.head hn := by
  simp [head_head_eq_head_flatten]
/-
**List.getLast_getLast_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getLast_getLast_splitBy (r : α -> α -> Bool) {l : List α} (hn : l != []) :
 ((l.splitBy r).getLast (splitBy_ne_nil.2 hn)).getLast (ne_nil_of_mem_splitBy (g
etLast_mem _)) = l.getLast hn
参数：r : α -> α -> Bool；hn : l != []。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.splitBy_ne_nil`：splitBy_ne_nil {r : α -> α -> Bool} {l : List α} : 
l.splitBy r != [] ↔ l != []
· 使用定理 `List.ne_nil_of_mem_splitBy`：ne_nil_of_mem_splitBy {r : α -> α -> Bool} {
l : List α} (h : m in l.splitBy r) : m != []
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.flatten_splitBy`：flatten_splitBy (r : α -> α -> Bool) (l : List α) 
: (l.splitBy r).flatten = l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getLast_getLast_eq_getLast_flatten`：getLast_getLast_eq_getLast_flat
ten {l : List (List α)} (hl : l != []) (hl' : l.getLast hl != []) : (l.getLast h
l).getLast hl' = l.flatten.ge…
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getLast_getLast_splitBy (r : α → α → Bool) {l : List α} (hn : l ≠ []) :
    ((l.splitBy r).getLast (splitBy_ne_nil.2 hn)).getLast
      (ne_nil_of_mem_splitBy (getLast_mem _)) = l.getLast hn := by
  simp [getLast_getLast_eq_getLast_flatten]
/-
**List.isChain_of_mem_splitByLoop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isChain_of_mem_splitByLoop {r : α → α → Bool} {l : List α} {a : α} {g : List α}
    (hga : ∀ b ∈ g.head?, r b a) (hg : g.IsChain fun y x ↦ r x y)
    (h : m ∈ splitBy.loop r l a g []) : m.IsChain fun x y ↦ r x y := by
  induction l generalizing a g with
  | nil =>
    rw [splitBy.loop, reverse_cons, mem_append, mem_reverse, mem_singleton] at h
    obtain hm | rfl := h
    · cases not_mem_nil hm
    · apply List.isChain_reverse.1
      rw [reverse_reverse]
      exact isChain_cons.2 ⟨hga, hg⟩
  | cons b l IH =>
    simp only [splitBy.loop, reverse_cons] at h
    split at h
    · apply IH _ (isChain_cons.2 ⟨hga, hg⟩) h
      grind
    · rw [splitByLoop_eq_append, mem_append, reverse_singleton, mem_singleton] at h
      obtain rfl | hm := h
      · apply List.isChain_reverse.1
        rw [reverse_append, reverse_cons, reverse_nil, nil_append, reverse_reverse]
        exact isChain_cons.2 ⟨hga, hg⟩
      · grind
/-
**List.isChain_of_mem_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_of_mem_splitBy {r : α -> α -> Bool} {l : List α} (h : m in l.split
By r) : m.IsChain fun x y => r x y
参数：h : m in l.splitBy r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.List.SplitBy.0.List.isChain_of_mem_splitByLoop`：∀ 
{α : Type u_1} {m : List α} {r : α → α → Bool} {l : List α} {a : α} {g : List α}
,   (∀ b ∈ g.head?, r b a = true) →     List.IsChain (fun …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem isChain_of_mem_splitBy {r : α → α → Bool} {l : List α} (h : m ∈ l.splitBy r) :
    m.IsChain fun x y ↦ r x y := by
  match l, h with
  | a::l, h => apply isChain_of_mem_splitByLoop _ _ h <;> simp
/-
**List.isChain_getLast_head_splitByLoop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem isChain_getLast_head_splitByLoop {r : α → α → Bool} (l : List α) {a : α}
    {g : List α} {gs : List (List α)} (hgs' : [] ∉ gs)
    (hgs : gs.IsChain fun b a ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false)
    (hga : ∀ m ∈ gs.head?, ∃ ha hb, r (m.getLast ha) ((g.reverse ++ [a]).head hb) = false) :
    (splitBy.loop r l a g gs).IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  induction l generalizing a g gs with
  | nil =>
    rw [splitBy.loop, reverse_cons]
    apply List.isChain_reverse.1
    simpa using isChain_cons.2 ⟨hga, hgs⟩
  | cons b l IH =>
    rw [splitBy.loop]
    split
    · refine IH hgs' hgs fun m hm ↦ ?_
      obtain ⟨ha, _, H⟩ := hga m hm
      refine ⟨ha, append_ne_nil_of_right_ne_nil _ (cons_ne_nil _ _), ?_⟩
      rwa [reverse_cons, head_append_of_ne_nil]
    · apply IH
      · simpa using hgs'
      · rw [reverse_cons]
        apply isChain_cons.2 ⟨hga, hgs⟩
      · simpa
/-
**List.isChain_getLast_head_splitBy** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：isChain_getLast_head_splitBy (r : α -> α -> Bool) (l : List α) : (l.splitB
y r).IsChain fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false
参数：r : α -> α -> Bool；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.isChain_nil`：isChain_nil : IsChain R []
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `_private.Mathlib.Data.List.SplitBy.0.List.isChain_getLast_head_splitByLo
op`：∀ {α : Type u_1} {r : α → α → Bool} (l : List α) {a : α} {g : List α} {gs : 
List (List α)},   [] ∉ gs →     List.IsChain (fun b a => ∃ (ha :…
· 使用定理 `List.not_mem_nil`：∀ {α : Type u_1} {a : α}, a ∉ []
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem isChain_getLast_head_splitBy (r : α → α → Bool) (l : List α) :
    (l.splitBy r).IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  cases l with
  | nil => exact isChain_nil
  | cons _ _ =>
    apply isChain_getLast_head_splitByLoop _ not_mem_nil isChain_nil
    rintro _ ⟨⟩
/-
**List.splitByLoop_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem splitByLoop_append {r : α → α → Bool} {l g : List α} {a : α}
    (h : (g.reverse ++ a :: l).IsChain fun x y ↦ r x y)
    (ha : ∀ x ∈ m.head?, r ((a :: l).getLast (cons_ne_nil a l)) x = false) :
    splitBy.loop r (l ++ m) a g [] = (g.reverse ++ a :: l) :: m.splitBy r := by
  induction l generalizing a g with
  | nil =>
    rw [nil_append]
    cases m with
    | nil => simp [splitBy.loop]
    | cons c m => simp_all [splitBy.loop, splitByLoop_eq_append [_], splitBy]
  | cons b l IH => simp_all [splitBy.loop]
/-
**List.splitBy_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_of_isChain {r : α -> α -> Bool} {l : List α} (hn : l != []) (h : l
.IsChain fun x y => r x y) : splitBy r l = [l]
参数：hn : l != []；h : l.IsChain fun x y => r x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.splitBy.eq_2`：∀ {α : Type u} (R : α → α → Bool) (a : α) (as : List 
α), List.splitBy R (a :: as) = List.splitBy.loop R as a [] []
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `_private.Mathlib.Data.List.SplitBy.0.List.splitByLoop_append`：∀ {α : Typ
e u_1} {m : List α} {r : α → α → Bool} {l g : List α} {a : α},   List.IsChain (f
un x y => r x y = true) (g.reverse ++ a :: l) →   …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem splitBy_of_isChain {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.IsChain fun x y ↦ r x y) : splitBy r l = [l] := by
  cases l with
  | nil => contradiction
  | cons a l => rw [splitBy, ← append_nil l, splitByLoop_append] <;> simp [h]
/-
**List.splitBy_append_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem splitBy_append_of_isChain {r : α → α → Bool} {l : List α} (hn : l ≠ [])
    (h : l.IsChain fun x y ↦ r x y) (ha : ∀ x ∈ m.head?, r (l.getLast hn) x = false) :
    (l ++ m).splitBy r = l :: m.splitBy r := by
  cases l with
  | nil => contradiction
  | cons a l => rw [cons_append, splitBy, splitByLoop_append h ha]; simp
/-
**List.splitBy_flatten** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_flatten {r : α -> α -> Bool} {l : List (List α)} (hn : [] ∉ l) (hc
 : forall m in l, m.IsChain fun x y => r x y) (hc' : l.IsChain fun a b => exists
 ha hb, r (a.getLast ha) (b.head hb) = false) : l.flatten.splitBy r = l
参数：List α；hn : [] ∉ l；hc : forall m in l, m.IsChain fun x y => r x y；hc' : l.IsC
hain fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.flatten_cons`：∀ {α : Type u_1} {l : List α} {L : List (List α)}, (l
 :: L).flatten = l ++ L.flatten
· 使用定理 `_private.Mathlib.Data.List.SplitBy.0.List.splitBy_append_of_isChain`：∀ {
α : Type u_1} {m : List α} {r : α → α → Bool} {l : List α} (hn : l ≠ []),   List
.IsChain (fun x y => r x y = true) l →     (∀ x ∈ m.head?…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `List.mem_of_mem_head?`：∀ {α : Type u_1} {l : List α} {a : α}, a ∈ l.head
? → a ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head_of_mem_head?`：∀ {α : Type u_1} {l : List α} {x : α} (hx : x ∈ 
l.head?), l.head ⋯ = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.flatten_ne_nil_iff`：∀ {α : Type u_1} {xss : List (List α)}, xss.fla
tten ≠ [] ↔ ∃ xs ∈ xss, xs ≠ []
· 使用定理 `List.isChain_cons`：isChain_cons {x l} : IsChain R (x :: l) ↔ (forall y i
n head? l, R x y) ∧ IsChain R l
· 使用定理 `List.head_mem_head?`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head 
h ∈ l.head?
· 使用定理 `List.head_flatten_eq_head_head`：head_flatten_eq_head_head {l : List (Lis
t α)} (hl : l.flatten != []) (hl' : l.head (by grind) != []) : l.flatten.head hl
 = (l.head (by grind…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.mem_cons_of_mem`：∀ {α : Type u_1} (y : α) {a : α} {l : List α}, a ∈
 l → a ∈ y :: l
· 使用定理 `List.IsChain.tail`：∀ {α : Type u_1} {R : α → α → Prop} {l : List α}, Lis
t.IsChain R l → List.IsChain R l.tail
-/
theorem splitBy_flatten {r : α → α → Bool} {l : List (List α)} (hn : [] ∉ l)
    (hc : ∀ m ∈ l, m.IsChain fun x y ↦ r x y)
    (hc' : l.IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false) :
    l.flatten.splitBy r = l := by
  induction l with
  | nil => rfl
  | cons a l IH =>
    rw [mem_cons, not_or, eq_comm] at hn
    rw [flatten_cons, splitBy_append_of_isChain hn.1 (hc _ mem_cons_self),
      IH hn.2 (fun m hm ↦ hc _ (mem_cons_of_mem a hm)) hc'.tail]
    intro y hy
    rw [← head_of_mem_head? hy]
    rw [isChain_cons] at hc'
    obtain ⟨x, hx, _⟩ := flatten_ne_nil_iff.1 (ne_nil_of_mem (mem_of_mem_head? hy))
    obtain ⟨_, _, H⟩ := hc'.1 (l.head (ne_nil_of_mem hx)) (head_mem_head? _)
    rwa [head_flatten_eq_head_head]

/-- A characterization of `splitBy m r` as the unique list `l` such that:

* The lists of `l` join to `m`.
* It does not contain the empty list.
* Every list in `l` is `IsChain` of `r`.
* The last element of each list in `l` is not related by `r` to the head of the next.
-/
/-
**List.splitBy_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_eq_iff {r : α -> α -> Bool} {l : List (List α)} : m.splitBy r = l 
↔ m = l.flatten ∧ [] ∉ l ∧ (forall m in l, m.IsChain fun x y => r x y) ∧ l.IsCha
in fun a b => exists ha hb, r (a.getLast ha) (b.head hb) = false
参数：List α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.flatten_splitBy`：flatten_splitBy (r : α -> α -> Bool) (l : List α) 
: (l.splitBy r).flatten = l
· 使用定理 `List.nil_notMem_splitBy`：nil_notMem_splitBy (r : α -> α -> Bool) (l : Li
st α) : [] ∉ l.splitBy r
· 使用定理 `List.isChain_of_mem_splitBy`：isChain_of_mem_splitBy {r : α -> α -> Bool}
 {l : List α} (h : m in l.splitBy r) : m.IsChain fun x y => r x y
· 使用定理 `List.isChain_getLast_head_splitBy`：isChain_getLast_head_splitBy (r : α -
> α -> Bool) (l : List α) : (l.splitBy r).IsChain fun a b => exists ha hb, r (a.
getLast ha) (b.head hb)…
· 使用定理 `List.splitBy_flatten`：splitBy_flatten {r : α -> α -> Bool} {l : List (Li
st α)} (hn : [] ∉ l) (hc : forall m in l, m.IsChain fun x y => r x y) (hc' : l.I
sChain fun…

--- 原说明 ---
A characterization of `splitBy m r` as the unique list `l` such that:

* The lists of `l` join to `m`.
* It does not contain the empty list.
* Every list in `l` is `IsChain` of `r`.
* The last element of each list in `l` is not related by `r` to the head of the 
next.
-/
theorem splitBy_eq_iff {r : α → α → Bool} {l : List (List α)} :
    m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (∀ m ∈ l, m.IsChain fun x y ↦ r x y) ∧
      l.IsChain fun a b ↦ ∃ ha hb, r (a.getLast ha) (b.head hb) = false := by
  constructor
  · rintro rfl
    exact ⟨(flatten_splitBy r m).symm, nil_notMem_splitBy r m, fun _ ↦ isChain_of_mem_splitBy,
      isChain_getLast_head_splitBy r m⟩
  · rintro ⟨rfl, hn, hc, hc'⟩
    exact splitBy_flatten hn hc hc'
/-
**List.splitBy_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_append {r : α -> α -> Bool} {l m : List α} (ha : forall x in l.get
Last?, forall y in m.head?, r x y = false) : (l ++ m).splitBy r = l.splitBy r ++
 m.splitBy r
参数：ha : forall x in l.getLast?, forall y in m.head?, r x y = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.splitBy_eq_iff`：splitBy_eq_iff {r : α -> α -> Bool} {l : List (List
 α)} : m.splitBy r = l ↔ m = l.flatten ∧ [] ∉ l ∧ (forall m in l, m.IsChain fun 
x y => r …
· 使用定理 `List.flatten_append`：∀ {α : Type u_1} {L₁ L₂ : List (List α)}, (L₁ ++ L₂
).flatten = L₁.flatten ++ L₂.flatten
· 使用定理 `List.flatten_splitBy`：flatten_splitBy (r : α -> α -> Bool) (l : List α) 
: (l.splitBy r).flatten = l
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.isChain_of_mem_splitBy`：isChain_of_mem_splitBy {r : α -> α -> Bool}
 {l : List α} (h : m in l.splitBy r) : m.IsChain fun x y => r x y
· 使用定理 `List.isChain_append`：∀ {α : Type u_1} {R : α → α → Prop} {l₁ l₂ : List α
},   List.IsChain R (l₁ ++ l₂) ↔ List.IsChain R l₁ ∧ List.IsChain R l₂ ∧ ∀ x ∈ l
₁.getLast…
· 使用定理 `List.isChain_getLast_head_splitBy`：isChain_getLast_head_splitBy (r : α -
> α -> Bool) (l : List α) : (l.splitBy r).IsChain fun a b => exists ha hb, r (a.
getLast ha) (b.head hb)…
· 使用定理 `List.ne_nil_of_mem_splitBy`：ne_nil_of_mem_splitBy {r : α -> α -> Bool} {
l : List α} (h : m in l.splitBy r) : m != []
· 使用定理 `List.mem_of_mem_getLast?`：∀ {α : Type u_1} {l : List α} {a : α}, a ∈ l.g
etLast? → a ∈ l
· 使用定理 `List.mem_of_mem_head?`：∀ {α : Type u_1} {l : List α} {a : α}, a ∈ l.head
? → a ∈ l
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `List.getLast_of_mem_getLast?`：∀ {α : Type u_1} {x : α} {l : List α} (hx 
: x ∈ l.getLast?), l.getLast ⋯ = x
· 使用定理 `List.getLast.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = 
as_1) (a : as ≠ []), as.getLast a = as_1.getLast ⋯
· 使用定理 `List.getLast_getLast_splitBy`：getLast_getLast_splitBy (r : α -> α -> Boo
l) {l : List α} (hn : l != []) : ((l.splitBy r).getLast (splitBy_ne_nil.2 hn)).g
etLast (ne_nil_of_…
· 使用定理 `List.getLast_mem_getLast?`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l
.getLast h ∈ l.getLast?
· 使用定理 `List.head_of_mem_head?`：∀ {α : Type u_1} {l : List α} {x : α} (hx : x ∈ 
l.head?), l.head ⋯ = x
· 使用定理 `List.head.congr_simp`：∀ {α : Type u} (as as_1 : List α) (e_as : as = as_
1) (a : as ≠ []), as.head a = as_1.head ⋯
· 使用定理 `List.head_head_splitBy`：head_head_splitBy (r : α -> α -> Bool) {l : List
 α} (hn : l != []) : ((l.splitBy r).head (splitBy_ne_nil.2 hn)).head (ne_nil_of_
mem_splitBy …
· 使用定理 `List.head_mem_head?`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head 
h ∈ l.head?
-/
theorem splitBy_append {r : α → α → Bool} {l m : List α}
    (ha : ∀ x ∈ l.getLast?, ∀ y ∈ m.head?, r x y = false) :
    (l ++ m).splitBy r = l.splitBy r ++ m.splitBy r := by
  obtain rfl | hl := eq_or_ne l []
  · simp
  obtain rfl | hm := eq_or_ne m []
  · simp
  rw [splitBy_eq_iff]
  refine ⟨by simp, by simp, ?_, ?_⟩; · aesop (add apply unsafe isChain_of_mem_splitBy)
  rw [isChain_append]
  refine ⟨isChain_getLast_head_splitBy _ _, isChain_getLast_head_splitBy _ _, fun x hx y hy ↦ ?_⟩
  use ne_nil_of_mem_splitBy (mem_of_mem_getLast? hx), ne_nil_of_mem_splitBy (mem_of_mem_head? hy)
  apply ha
  · simp_rw [← getLast_of_mem_getLast? hx, getLast_getLast_splitBy _ hl]
    exact getLast_mem_getLast? _
  · simp_rw [← head_of_mem_head? hy, head_head_splitBy _ hm]
    exact head_mem_head? _
/-
**List.splitBy_append_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitBy_append_cons {r : α -> α -> Bool} {l : List α} {a : α} (m : List α)
 (ha : forall x in l.getLast?, r x a = false) : (l ++ a :: m).splitBy r = l.spli
tBy r ++ (a :: m).splitBy r
参数：m : List α；ha : forall x in l.getLast?, r x a = false。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.splitBy_append`：splitBy_append {r : α -> α -> Bool} {l m : List α} 
(ha : forall x in l.getLast?, forall y in m.head?, r x y = false) : (l ++ m).spl
itBy r = …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
-/
theorem splitBy_append_cons {r : α → α → Bool} {l : List α} {a : α} (m : List α)
    (ha : ∀ x ∈ l.getLast?, r x a = false) :
    (l ++ a :: m).splitBy r = l.splitBy r ++ (a :: m).splitBy r := by
  apply splitBy_append
  simpa

end List

