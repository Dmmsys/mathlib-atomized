/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Wrenna Robson
-/
module

public import Batteries.Data.List.Pairwise
public import Batteries.Data.List.Perm
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Nodup
public import Mathlib.Order.Fin.Basic

/-!
# Sorting algorithms on lists

In this file we define the sorting algorithm `List.insertionSort r` and prove
that we have `(l.insertionSort r l).Pairwise r` under suitable conditions on `r`.

We then define `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`,
predicates which are equivalent to `List.Pairwise` when the relation derives from a
preorder (but which are defined in terms of the monotonicity predicates).
-/

public section

namespace List

section sort

variable {α β : Type*} (r : α → α → Prop) (s : β → β → Prop)

variable [DecidableRel r] [DecidableRel s]

local infixl:50 " ≼ " => r
local infixl:50 " ≼ " => s

/-! ### Insertion sort -/

section InsertionSort

/-- `orderedInsert a l` inserts `a` into `l` at such that
  `orderedInsert a l` is sorted if `l` is. -/
/-
**List.orderedInsert** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → [DecidableRel r] → α → List α → List
 α
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`orderedInsert a l` inserts `a` into `l` at such that
  `orderedInsert a l` is sorted if `l` is.
-/
def orderedInsert (a : α) : List α → List α
  | [] => [a]
  | b :: l => if a ≼ b then a :: b :: l else b :: orderedInsert a l
/-
**List.orderedInsert_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : DecidableRel r] (a : α), List.
orderedInsert r a [] = [a]
参数：r : α → α → Prop；a : α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem orderedInsert_nil (a : α) : [].orderedInsert r a = [a] := .refl _
/-
**List.orderedInsert_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : DecidableRel r] (a b : α) (l :
 List α),   List.orderedInsert r a (b :: l) = if r a b then a :: b :: l else b :
: List.orderedInsert r a l
参数：r : α → α → Prop；a b : α；l : List α；b :: l。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem orderedInsert_cons (a b : α) (l : List α) :
    (b :: l).orderedInsert r a = if r a b then a :: b :: l else b :: l.orderedInsert r a :=
  .refl _
/-
**List.orderedInsert_cons_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：orderedInsert_cons_of_le {a b : α} (l : List α) (h : a ≼ b) : orderedInser
t r a (b :: l) = a :: b :: l
参数：l : List α；h : a ≼ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
-/
theorem orderedInsert_cons_of_le {a b : α} (l : List α) (h : a ≼ b) :
    orderedInsert r a (b :: l) = a :: b :: l :=
  dif_pos h
/-
**List.orderedInsert_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：orderedInsert_of_not_le {a b : α} (l : List α) (h : ¬ a ≼ b) : orderedInse
rt r a (b :: l) = b :: orderedInsert r a l
参数：l : List α；h : ¬ a ≼ b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem orderedInsert_of_not_le {a b : α} (l : List α) (h : ¬ a ≼ b) :
    orderedInsert r a (b :: l) = b :: orderedInsert r a l := dif_neg h

/-- `insertionSort l` returns `l` sorted using the insertion sort algorithm. -/
/-
**List.insertionSort** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：insertionSort : List α -> List α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`insertionSort l` returns `l` sorted using the insertion sort algorithm.
-/
def insertionSort : List α → List α := foldr (orderedInsert r) []

@[simp, grind =]
/-
**List.insertionSort_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertionSort_nil : [].insertionSort r = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem insertionSort_nil : [].insertionSort r = [] := .refl _
/-
**List.insertionSort_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : DecidableRel r] (a : α) (l : L
ist α),   List.insertionSort r (a :: l) = List.orderedInsert r a (List.insertion
Sort r l)
参数：r : α → α → Prop；a : α；l : List α；a :: l；List.insertionSort r l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind =] theorem insertionSort_cons (a : α) (l : List α) :
    (a :: l).insertionSort r = orderedInsert r a (insertionSort r l) := .refl _

-- A quick check that insertionSort is stable:
/-
**List.** 是 Mathlib 中的一个示例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example :
    insertionSort (fun m n => m / 10 ≤ n / 10) [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] =
      [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567] := rfl
/-
**List.orderedInsert_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：orderedInsert_length (L : List α) (a : α) : (L.orderedInsert r a).length =
 L.length + 1
参数：L : List α；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderedInsert_length (L : List α) (a : α) :
    (L.orderedInsert r a).length = L.length + 1 := by
  induction L <;> grind

/-- An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`. -/
/-
**List.orderedInsert_eq_take_drop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：orderedInsert_eq_take_drop (a : α) (l : List α) : l.orderedInsert r a = (l
.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative definition of `orderedInsert` using `takeWhile` and `dropWhile`.
-/
theorem orderedInsert_eq_take_drop (a : α) (l : List α) :
    l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhile fun b => ¬a ≼ b := by
  induction l <;> grind [takeWhile, dropWhile]
/-
**List.insertionSort_cons_eq_take_drop** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertionSort_cons_eq_take_drop (a : α) (l : List α) : insertionSort r (a 
:: l) = ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++ a :: (insertionSort r
 l).dropWhile fun b => ¬a ≼ b
参数：a : α；l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.orderedInsert_eq_take_drop`：orderedInsert_eq_take_drop (a : α) (l :
 List α) : l.orderedInsert r a = (l.takeWhile fun b => ¬a ≼ b) ++ a :: l.dropWhi
le fun b => ¬a ≼ b
-/
theorem insertionSort_cons_eq_take_drop (a : α) (l : List α) :
    insertionSort r (a :: l) =
      ((insertionSort r l).takeWhile fun b => ¬a ≼ b) ++
        a :: (insertionSort r l).dropWhile fun b => ¬a ≼ b :=
  orderedInsert_eq_take_drop r a _

@[simp]
/-
**List.mem_orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_orderedInsert {a b : α} {l : List α} : a in orderedInsert r b l ↔ a = 
b ∨ a in l
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_orderedInsert {a b : α} {l : List α} :
    a ∈ orderedInsert r b l ↔ a = b ∨ a ∈ l := by
  induction l <;> grind
/-
**List.map_orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_orderedInsert (f : α -> β) (l : List α) (x : α) (hl₁ : forall a in l, 
a ≼ x ↔ f a ≼ f x) (hl₂ : forall a in l, x ≼ a ↔ f x ≼ f a) : (l.orderedInsert r
 x).map f = (l.map f).orderedInsert s (f x)
参数：f : α -> β；l : List α；x : α；hl₁ : forall a in l, a ≼ x ↔ f a ≼ f x；hl₂ : fora
ll a in l, x ≼ a ↔ f x ≼ f a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_orderedInsert (f : α → β) (l : List α) (x : α)
    (hl₁ : ∀ a ∈ l, a ≼ x ↔ f a ≼ f x) (hl₂ : ∀ a ∈ l, x ≼ a ↔ f x ≼ f a) :
    (l.orderedInsert r x).map f = (l.map f).orderedInsert s (f x) := by
  induction l <;> grind

section Correctness

/-
**List.perm_orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : DecidableRel r] (a : α) (l : L
ist α),   (List.orderedInsert r a l).Perm (a :: l)
参数：r : α → α → Prop；a : α；l : List α；List.orderedInsert r a l；a :: l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem perm_orderedInsert (a) : ∀ l : List α, orderedInsert r a l ~ a :: l
  | [] => Perm.refl _
  | b :: l => by
    by_cases h : a ≼ b
    · simp [h]
    · simpa [h] using ((perm_orderedInsert a l).cons _).trans (Perm.swap _ _ _)
/-
**List.orderedInsert_count** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：orderedInsert_count [DecidableEq α] (L : List α) (a b : α) : count a (L.or
deredInsert r b) = count a L + if b = a then 1 else 0
参数：L : List α；a b : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.count_eq`：∀ {α : Type u_1} [inst : BEq α] {l₁ l₂ : List α}, l₁
.Perm l₂ → ∀ (a : α), List.count a l₁ = List.count a l₂
· 使用定理 `List.perm_orderedInsert`：∀ {α : Type u_1} (r : α → α → Prop) [inst : Dec
idableRel r] (a : α) (l : List α),   (List.orderedInsert r a l).Perm (a :: l)
· 使用定理 `List.count_cons`：∀ {α : Type u_1} [inst : BEq α] {a b : α} {l : List α},
   List.count a (b :: l) = List.count a l + if (b == a) = true then 1 else 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orderedInsert_count [DecidableEq α] (L : List α) (a b : α) :
    count a (L.orderedInsert r b) = count a L + if b = a then 1 else 0 := by
  rw [(L.perm_orderedInsert r b).count_eq, count_cons]
  simp
/-
**List.perm_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：perm_insertionSort (l : List α) : insertionSort r l ~ l
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem perm_insertionSort (l : List α) : insertionSort r l ~ l := by
  induction l <;> grind [List.Perm, perm_orderedInsert]

@[simp]
/-
**List.mem_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mem_insertionSort {l : List α} {x : α} : x in l.insertionSort r ↔ x in l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.perm_insertionSort`：perm_insertionSort (l : List α) : insertionSort
 r l ~ l
-/
theorem mem_insertionSort {l : List α} {x : α} : x ∈ l.insertionSort r ↔ x ∈ l :=
  (perm_insertionSort r l).mem_iff

@[simp]
/-
**List.length_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_insertionSort (l : List α) : (insertionSort r l).length = l.length
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.length_eq`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₁.
length = l₂.length
· 使用定理 `List.perm_insertionSort`：perm_insertionSort (l : List α) : insertionSort
 r l ~ l
-/
theorem length_insertionSort (l : List α) : (insertionSort r l).length = l.length :=
  (perm_insertionSort r _).length_eq
/-
**List.insertionSort_cons_of_forall_rel** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertionSort_cons_of_forall_rel {a : α} {l : List α} (h : forall b in l, 
r a b) : insertionSort r (a :: l) = a :: insertionSort r l
参数：h : forall b in l, r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insertionSort_cons`：∀ {α : Type u_1} (r : α → α → Prop) [inst : Dec
idableRel r] (a : α) (l : List α),   List.insertionSort r (a :: l) = List.ordere
dInsert r a (…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.orderedInsert_cons_of_le`：orderedInsert_cons_of_le {a b : α} (l : L
ist α) (h : a ≼ b) : orderedInsert r a (b :: l) = a :: b :: l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.mem_insertionSort`：mem_insertionSort {l : List α} {x : α} : x in l.
insertionSort r ↔ x in l
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
-/
theorem insertionSort_cons_of_forall_rel {a : α} {l : List α} (h : ∀ b ∈ l, r a b) :
    insertionSort r (a :: l) = a :: insertionSort r l := by
  rw [insertionSort_cons]
  cases hi : insertionSort r l with
  | nil => rfl
  | cons b m =>
    rw [orderedInsert_cons_of_le]
    apply h b <| (mem_insertionSort r).1 _
    rw [hi]
    exact mem_cons_self
/-
**List.map_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_insertionSort (f : α -> β) (l : List α) (hl : forall a in l, forall b 
in l, a ≼ b ↔ f a ≼ f b) : (l.insertionSort r).map f = (l.map f).insertionSort s
参数：f : α -> β；l : List α；hl : forall a in l, forall b in l, a ≼ b ↔ f a ≼ f b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insertionSort_nil`：insertionSort_nil : [].insertionSort r = []
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `List.insertionSort.congr_simp`：∀ {α : Type u_1} (r r_1 : α → α → Prop), 
  r = r_1 →     ∀ {inst : DecidableRel r} [inst_1 : DecidableRel r_1] (a a_1 : L
ist α),       a = a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.insertionSort_cons`：∀ {α : Type u_1} (r : α → α → Prop) [inst : Dec
idableRel r] (a : α) (l : List α),   List.insertionSort r (a :: l) = List.ordere
dInsert r a (…
· 使用定理 `List.map_orderedInsert`：map_orderedInsert (f : α -> β) (l : List α) (x :
 α) (hl₁ : forall a in l, a ≼ x ↔ f a ≼ f x) (hl₂ : forall a in l, x ≼ a ↔ f x ≼
 f a) : (l.o…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem map_insertionSort (f : α → β) (l : List α) (hl : ∀ a ∈ l, ∀ b ∈ l, a ≼ b ↔ f a ≼ f b) :
    (l.insertionSort r).map f = (l.map f).insertionSort s := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp_rw [List.forall_mem_cons, forall_and] at hl
    simp_rw [List.map, insertionSort_cons]
    rw [List.map_orderedInsert _ s, ih hl.2.2]
    · simpa only [mem_insertionSort] using hl.2.1
    · simpa only [mem_insertionSort] using hl.1.2

variable {r}

/-- If `l` is already `List.Pairwise` with respect to `r`, then `insertionSort` does not change
it. -/
/-
**List.Pairwise.insertionSort_eq** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [inst : DecidableRel r] {l : List α}, 
List.Pairwise r l → List.insertionSort r l = l
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `l` is already `List.Pairwise` with respect to `r`, then `insertionSort` does
 not change
it.
-/
theorem Pairwise.insertionSort_eq {l : List α} : Pairwise r l → insertionSort r l = l := by
  induction l <;> grind [cases List]

/-- For a reflexive relation, insert then erasing is the identity. -/
/-
**List.erase_orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：erase_orderedInsert [DecidableEq α] [Std.Refl r] (x : α) (xs : List α) : (
xs.orderedInsert r x).erase x = xs
参数：x : α；xs : List α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a reflexive relation, insert then erasing is the identity.
-/
theorem erase_orderedInsert [DecidableEq α] [Std.Refl r] (x : α) (xs : List α) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind [Std.Refl]

/-- Inserting then erasing an element that is absent is the identity. -/
/-
**List.erase_orderedInsert_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：erase_orderedInsert_of_notMem [DecidableEq α] {x : α} {xs : List α} (hx : 
x ∉ xs) : (xs.orderedInsert r x).erase x = xs
参数：hx : x ∉ xs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inserting then erasing an element that is absent is the identity.
-/
theorem erase_orderedInsert_of_notMem [DecidableEq α]
    {x : α} {xs : List α} (hx : x ∉ xs) :
    (xs.orderedInsert r x).erase x = xs := by
  induction xs <;> grind

/-- For an antisymmetric relation, erasing then inserting is the identity. -/
/-
**List.orderedInsert_erase** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：orderedInsert_erase [DecidableEq α] [Std.Antisymm r] (x : α) (xs : List α)
 (hx : x in xs) (hxs : Pairwise r xs) : (xs.erase x).orderedInsert r x = xs
参数：x : α；xs : List α；hx : x in xs；hxs : Pairwise r xs。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For an antisymmetric relation, erasing then inserting is the identity.
-/
theorem orderedInsert_erase [DecidableEq α] [Std.Antisymm r] (x : α) (xs : List α) (hx : x ∈ xs)
    (hxs : Pairwise r xs) :
    (xs.erase x).orderedInsert r x = xs := by
  induction xs with grind +splitIndPred
/-
**List.sublist_orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_orderedInsert (x : α) (xs : List α) : xs <+ xs.orderedInsert r x
参数：x : α；xs : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sublist_orderedInsert (x : α) (xs : List α) : xs <+ xs.orderedInsert r x := by
  induction xs <;> grind
/-
**List.cons_sublist_orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：cons_sublist_orderedInsert {l c : List α} {a : α} (hl : c <+ l) (ha : fora
ll a' in c, a ≼ a') : a :: c <+ orderedInsert r a l
参数：hl : c <+ l；ha : forall a' in c, a ≼ a'。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem cons_sublist_orderedInsert {l c : List α} {a : α} (hl : c <+ l) (ha : ∀ a' ∈ c, a ≼ a') :
    a :: c <+ orderedInsert r a l := by
  induction l <;> grind
/-
**List.Sublist.orderedInsert_sublist** 是 Mathlib 中的一个定理，位于命名空间 `List.Sublist`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [inst : DecidableRel r] [IsTrans α r] 
{as bs : List α} (x : α),   as.Sublist bs → List.Pairwise r bs → (List.orderedIn
sert r x as).Sublist (List.orderedInsert r x bs)
参数：x : α；List.orderedInsert r x as；List.orderedInsert r x bs。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Sublist.orderedInsert_sublist [IsTrans α r] {as bs} (x) (hs : as <+ bs)
    (hb : bs.Pairwise r) : orderedInsert r x as <+ orderedInsert r x bs := by
  cases as with
  | nil => simp
  | cons a as =>
    cases bs with
    | nil => contradiction
    | cons b bs =>
      unfold orderedInsert
      cases hs <;> split_ifs with hr
      · exact .cons_cons _ <| .cons _ ‹a :: as <+ bs›
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        simp only [hr, orderedInsert_cons, ite_true] at ih
        exact .trans ih <| .cons _ (.refl _)
      · have hba := pairwise_cons.mp hb |>.left _ (mem_of_cons_sublist ‹a :: as <+ bs›)
        exact absurd (trans_of _ ‹r x b› hba) hr
      · have ih := orderedInsert_sublist x ‹a :: as <+ bs› hb.of_cons
        rw [orderedInsert_cons, if_neg hr] at ih
        exact .cons _ ih
      · simp_all
      · exact .cons_cons _ <| orderedInsert_sublist x ‹as <+ bs› hb.of_cons

section TotalAndTransitive

variable [Std.Total r] [IsTrans α r]

/-
**List.Pairwise.orderedInsert** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [inst : DecidableRel r] [Std.Total r] 
[IsTrans α r] (a : α) (l : List α),   List.Pairwise r l → List.Pairwise r (List.
orderedInsert r a l)
参数：a : α；l : List α；List.orderedInsert r a l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Pairwise.orderedInsert (a : α) : ∀ l, Pairwise r l → Pairwise r (orderedInsert r a l)
  | [], _ => pairwise_singleton _ a
  | b :: l, h => by
    by_cases h' : a ≼ b
    · grind
    · suffices ∀ b' : α, b' ∈ List.orderedInsert r a l → r b b' by
        simpa [orderedInsert_cons, h', h.of_cons.orderedInsert a l]
      intro b' bm
      rcases (mem_orderedInsert r).mp bm with rfl | bm
      · exact (total_of r _ _).resolve_left h'
      · exact rel_of_pairwise_cons h bm

variable (r)

/-- The list `List.insertionSort r l` is `List.Pairwise` with respect to `r`. -/
/-
**List.pairwise_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop) [inst : DecidableRel r] [Std.Total r] 
[IsTrans α r] (l : List α),   List.Pairwise r (List.insertionSort r l)
参数：r : α → α → Prop；l : List α；List.insertionSort r l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The list `List.insertionSort r l` is `List.Pairwise` with respect to `r`.
-/
theorem pairwise_insertionSort : ∀ l, Pairwise r (insertionSort r l)
  | [] => Pairwise.nil
  | a :: l => (pairwise_insertionSort l).orderedInsert a _

end TotalAndTransitive

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
If `c` is a sorted sublist of `l`, then `c` is still a sublist of `insertionSort r l`.
-/
/-
**List.sublist_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_insertionSort {l c : List α} (hr : c.Pairwise r) (hc : c <+ l) : c
 <+ insertionSort r l
参数：hr : c.Pairwise r；hc : c <+ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.sublist_orderedInsert`：sublist_orderedInsert (x : α) (xs : List α) 
: xs <+ xs.orderedInsert r x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.pairwise_cons`：∀ {α : Type u} {R : α → α → Prop} {a : α} {l : List 
α},   List.Pairwise R (a :: l) ↔ (∀ a' ∈ l, R a a') ∧ List.Pairwise R l
· 使用定理 `List.cons_sublist_orderedInsert`：cons_sublist_orderedInsert {l c : List 
α} {a : α} (hl : c <+ l) (ha : forall a' in c, a ≼ a') : a :: c <+ orderedInsert
 r a l

--- 原说明 ---
If `c` is a sorted sublist of `l`, then `c` is still a sublist of `insertionSort
 r l`.
-/
theorem sublist_insertionSort {l c : List α} (hr : c.Pairwise r) (hc : c <+ l) :
    c <+ insertionSort r l := by
  induction l generalizing c with
  | nil         => grind
  | cons _ _ ih =>
    cases hc with
    | cons  _ h => exact ih hr h |>.trans (sublist_orderedInsert ..)
    | cons_cons _ h =>
      obtain ⟨hr, hp⟩ := pairwise_cons.mp hr
      exact cons_sublist_orderedInsert (ih hp h) hr

/--
Another statement of stability of insertion sort.
If a pair `[a, b]` is a sublist of `l` and `r a b`,
then `[a, b]` is still a sublist of `insertionSort r l`.
-/
/-
**List.pair_sublist_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pair_sublist_insertionSort {a b : α} {l : List α} (hab : r a b) (h : [a, b
] <+ l) : [a, b] <+ insertionSort r l
参数：hab : r a b；h : [a, b] <+ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublist_insertionSort`：sublist_insertionSort {l c : List α} (hr : c
.Pairwise r) (hc : c <+ l) : c <+ insertionSort r l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_pair`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α}, List.
Pairwise R [a, b] ↔ R a b

--- 原说明 ---
Another statement of stability of insertion sort.
If a pair `[a, b]` is a sublist of `l` and `r a b`,
then `[a, b]` is still a sublist of `insertionSort r l`.
-/
theorem pair_sublist_insertionSort {a b : α} {l : List α} (hab : r a b) (h : [a, b] <+ l) :
    [a, b] <+ insertionSort r l :=
  sublist_insertionSort (pairwise_pair.mpr hab) h

variable [Std.Antisymm r] [Std.Total r] [IsTrans α r]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/--
A version of `insertionSort_stable` which only assumes `c <+~ l` (instead of `c <+ l`), but
additionally requires `Std.Antisymm r`, `Std.Total r` and `IsTrans α r`.
-/
/-
**List.sublist_insertionSort'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_insertionSort' {l c : List α} (hs : c.Pairwise r) (hc : c <+~ l) :
 c <+ insertionSort r l
参数：hs : c.Pairwise r；hc : c <+~ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.sublist_orderedInsert`：sublist_orderedInsert (x : α) (xs : List α) 
: xs <+ xs.orderedInsert r x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Perm.mem_iff`：∀ {α : Type u_1} {a : α} {l₁ l₂ : List α}, l₁.Perm l₂
 → (a ∈ l₁ ↔ a ∈ l₂)
· 使用定理 `List.mem_cons_self`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ a :: l
· 使用定理 `List.orderedInsert_erase`：orderedInsert_erase [DecidableEq α] [Std.Antis
ymm r] (x : α) (xs : List α) (hx : x in xs) (hxs : Pairwise r xs) : (xs.erase x)
.orderedInsert…
· 使用定理 `List.Sublist.orderedInsert_sublist`：∀ {α : Type u_1} {r : α → α → Prop} 
[inst : DecidableRel r] [IsTrans α r] {as bs : List α} (x : α),   as.Sublist bs 
→ List.Pairwise r bs → (…
· 使用定理 `List.Pairwise.erase`：∀ {α : Type u_1} [inst : BEq α] {p : α → α → Prop} 
[LawfulBEq α] {l : List α} (a : α),   List.Pairwise p l → List.Pairwise p (l.era
se a)
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `List.Perm.erase`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a : α) {
l₁ l₂ : List α}, l₁.Perm l₂ → (l₁.erase a).Perm (l₂.erase a)
· 使用定理 `List.erase_cons_head`：∀ {α : Type u_1} [inst : BEq α] [LawfulBEq α] (a :
 α) (l : List α), (a :: l).erase a = l
· 使用定理 `List.pairwise_insertionSort`：∀ {α : Type u_1} (r : α → α → Prop) [inst :
 DecidableRel r] [Std.Total r] [IsTrans α r] (l : List α),   List.Pairwise r (Li
st.insertionSort …

--- 原说明 ---
A version of `insertionSort_stable` which only assumes `c <+~ l` (instead of `c 
<+ l`), but
additionally requires `Std.Antisymm r`, `Std.Total r` and `IsTrans α r`.
-/
theorem sublist_insertionSort' {l c : List α} (hs : c.Pairwise r) (hc : c <+~ l) :
    c <+ insertionSort r l := by
  classical
  obtain ⟨d, hc, hd⟩ := hc
  induction l generalizing c d with
  | nil         => grind [nil_perm]
  | cons a _ ih =>
    cases hd with
    | cons  _ h => exact ih hs _ hc h |>.trans (sublist_orderedInsert ..)
    | cons_cons _ h =>
      specialize ih (hs.erase _) _ (erase_cons_head a ‹List _› ▸ hc.erase a) h
      have hm := hc.mem_iff.mp <| mem_cons_self ..
      have he := orderedInsert_erase _ _ hm hs
      exact he ▸ Sublist.orderedInsert_sublist _ ih (pairwise_insertionSort ..)

/--
Another statement of stability of insertion sort.
If a pair `[a, b]` is a sublist of a permutation of `l` and `a ≼ b`,
then `[a, b]` is still a sublist of `insertionSort r l`.
-/
/-
**List.pair_sublist_insertionSort'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pair_sublist_insertionSort' {a b : α} {l : List α} (hab : a ≼ b) (h : [a, 
b] <+~ l) : [a, b] <+ insertionSort r l
参数：hab : a ≼ b；h : [a, b] <+~ l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublist_insertionSort'`：sublist_insertionSort' {l c : List α} (hs :
 c.Pairwise r) (hc : c <+~ l) : c <+ insertionSort r l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_pair`：∀ {α : Type u_1} {R : α → α → Prop} {a b : α}, List.
Pairwise R [a, b] ↔ R a b

--- 原说明 ---
Another statement of stability of insertion sort.
If a pair `[a, b]` is a sublist of a permutation of `l` and `a ≼ b`,
then `[a, b]` is still a sublist of `insertionSort r l`.
-/
theorem pair_sublist_insertionSort' {a b : α} {l : List α} (hab : a ≼ b) (h : [a, b] <+~ l) :
    [a, b] <+ insertionSort r l :=
  sublist_insertionSort' (pairwise_pair.mpr hab) h

end Correctness

end InsertionSort

/-! ### Merge sort

We provide some wrapper functions around the theorems for `mergeSort` provided in Lean,
which rather than using explicit hypotheses for transitivity and totality,
use Mathlib order typeclasses instead.
-/

set_option linter.hashCommand false in
#guard mergeSort [5, 27, 221, 95, 17, 43, 7, 2, 98, 567, 23, 12] (fun m n => m / 10 ≤ n / 10) =
  [5, 7, 2, 17, 12, 27, 23, 43, 95, 98, 221, 567]

section MergeSort

section Correctness

section Antisymm

variable {r : α → α → Prop} [Std.Antisymm r]

/-- Variant of `Perm.eq_of_pairwise` using relation typeclasses. -/
/-
**List.Perm.eq_of_pairwise'** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Antisymm r] {l₁ l₂ : List α},   L
ist.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂ → l₁ = l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_pairwise`：∀ {α : Type u_1} {le : α → α → Prop} {l₁ l₂ : 
List α},   (∀ (a b : α), a ∈ l₁ → b ∈ l₂ → le a b → le b a → a = b) →     List.P
airwise le l₁ …
· 使用引理 `antisymm`：antisymm [Std.Antisymm r] : a ≺ b -> b ≺ a -> a = b

--- 原说明 ---
Variant of `Perm.eq_of_pairwise` using relation typeclasses.
-/
theorem Perm.eq_of_pairwise' {l₁ l₂ : List α} :
    Pairwise r l₁ → Pairwise r l₂ → (hl : l₁ ~ l₂) → l₁ = l₂ :=
  eq_of_pairwise (fun _ _ _ _ => antisymm)
/-
**List.sublist_of_subperm_of_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_of_subperm_of_pairwise {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hs₁ : l₁
.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <+ l₂
参数：hp : l₁ <+~ l₂；hs₁ : l₁.Pairwise r；hs₂ : l₂.Pairwise r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `List.Pairwise.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α} {R : α → α → Pr
op}, l₁.Sublist l₂ → List.Pairwise R l₂ → List.Pairwise R l₁
-/
theorem sublist_of_subperm_of_pairwise {l₁ l₂ : List α} (hp : l₁ <+~ l₂)
    (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <+ l₂ := by
  let ⟨_, h, h'⟩ := hp
  exact Sublist.trans (h.eq_of_pairwise' (hs₂.sublist h') hs₁ ▸ Sublist.refl _) h'
/-
**List.Subset.antisymm_of_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List.Subset`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Antisymm r] [Std.Irrefl r] {l₁ l₂
 : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁ ⊆ l₂ → l₂ ⊆ l₁ → l₁ =
 l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `List.Subperm.antisymm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Subperm l₂ 
→ l₂.Subperm l₁ → l₁.Perm l₂
· 使用定理 `List.subperm_of_subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Nodup → l₁
 ⊆ l₂ → l₁.Subperm l₂
· 使用定理 `List.Pairwise.nodup`：∀ {α : Type u} {l : List α} {r : α → α → Prop} [Std
.Irrefl r], List.Pairwise r l → l.Nodup
-/
theorem Subset.antisymm_of_pairwise [Std.Irrefl r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (hl₁₂ : l₁ ⊆ l₂) (hl₁₂' : l₂ ⊆ l₁) : l₁ = l₂ :=
  ((subperm_of_subset h₁.nodup hl₁₂).antisymm
    (subperm_of_subset h₂.nodup hl₁₂')).eq_of_pairwise' h₁ h₂
/-
**List.Pairwise.eq_of_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Antisymm r] [Std.Irrefl r] {l₁ l₂
 : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → (∀ (a : α), a ∈ l₁ ↔ a ∈
 l₂) → l₁ = l₂
参数：∀ (a : α), a ∈ l₁ ↔ a ∈ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Subset.antisymm_of_pairwise`：∀ {α : Type u_1} {r : α → α → Prop} [S
td.Antisymm r] [Std.Irrefl r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pair
wise r l₂ → l₁ ⊆ l₂ → …
-/
theorem Pairwise.eq_of_mem_iff [Std.Irrefl r] {l₁ l₂ : List α}
    (h₁ : Pairwise r l₁) (h₂ : Pairwise r l₂) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  Subset.antisymm_of_pairwise h₁ h₂ (by grind) (by grind)

end Antisymm

section TotalAndTransitive

variable {r} [Std.Total r] [IsTrans α r]

/-
**List.Pairwise.merge** 是 Mathlib 中的一个定理，位于命名空间 `List.Pairwise`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [inst : DecidableRel r] [Std.Total r] 
[IsTrans α r] {l l' : List α},   List.Pairwise r l → List.Pairwise r l' → List.P
airwise r (l.merge l' fun x1 x2 => decide (r x1 x2))
参数：l.merge l' fun x1 x2 => decide (r x1 x2)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.pairwise_merge`：∀ {α : Type u_1} {le : α → α → Bool},   (∀ (a b c :
 α), le a b = true → le b c = true → le a c = true) →     (∀ (a b : α), (le a b 
|| le b a…
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.or_eq_true`：∀ (a b : Bool), ((a || b) = true) = (a = true ∨ b = tru
e)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
theorem Pairwise.merge {l l' : List α} (h : Pairwise r l) (h' : Pairwise r l') :
    Pairwise r (merge l l' (r · ·)) := by
  simpa using pairwise_merge (le := (r · ·))
    (fun a b c h₁ h₂ => by simpa using _root_.trans (by simpa using h₁) (by simpa using h₂))
    (fun a b => by simpa using Std.Total.total a b)
    l l' (by simpa using h) (by simpa using h')

variable (r)

/-- Variant of `pairwise_mergeSort` using relation typeclasses. -/
/-
**List.pairwise_mergeSort'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：pairwise_mergeSort' (l : List α) : Pairwise r (mergeSort l (r · ·))
参数：l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `decide_eq_true_eq`：∀ {p : Prop} [inst : Decidable p], (decide p = true) 
= p
· 使用定理 `List.pairwise_mergeSort`：∀ {α : Type u_1} {le : α → α → Bool},   (∀ (a b
 c : α), le a b = true → le b c = true → le a c = true) →     (∀ (a b : α), (le 
a b || le b a…
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Bool.or_eq_true`：∀ (a b : Bool), ((a || b) = true) = (a = true ∨ b = tru
e)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `total_of`：total_of [Std.Total r] (a b : α) : a ≺ b ∨ b ≺ a

--- 原说明 ---
Variant of `pairwise_mergeSort` using relation typeclasses.
-/
theorem pairwise_mergeSort' (l : List α) : Pairwise r (mergeSort l (r · ·)) := by
  simpa using pairwise_mergeSort (le := (r · ·))
    (fun _ _ _ => by simpa using trans_of r)
    (by simpa using total_of r)
    l

variable [Std.Antisymm r]
/-
**List.mergeSort_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mergeSort_eq_self {l : List α} : Pairwise r l -> mergeSort l (r · ·) = l
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `List.pairwise_mergeSort'`：pairwise_mergeSort' (l : List α) : Pairwise r 
(mergeSort l (r · ·))
· 使用定理 `List.mergeSort_perm`：∀ {α : Type u_1} (l : List α) (le : α → α → Bool), 
(l.mergeSort le).Perm l
-/
theorem mergeSort_eq_self {l : List α} : Pairwise r l → mergeSort l (r · ·) = l :=
  (mergeSort_perm _ _).eq_of_pairwise' (pairwise_mergeSort' _ l)
/-
**List.mergeSort_eq_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：mergeSort_eq_insertionSort (l : List α) : mergeSort l (r · ·) = insertionS
ort r l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `List.pairwise_mergeSort'`：pairwise_mergeSort' (l : List α) : Pairwise r 
(mergeSort l (r · ·))
· 使用定理 `List.pairwise_insertionSort`：∀ {α : Type u_1} (r : α → α → Prop) [inst :
 DecidableRel r] [Std.Total r] [IsTrans α r] (l : List α),   List.Pairwise r (Li
st.insertionSort …
· 使用定理 `List.mergeSort_perm`：∀ {α : Type u_1} (l : List α) (le : α → α → Bool), 
(l.mergeSort le).Perm l
· 使用定理 `List.Perm.symm`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → l₂.Perm 
l₁
· 使用定理 `List.perm_insertionSort`：perm_insertionSort (l : List α) : insertionSort
 r l ~ l
-/
theorem mergeSort_eq_insertionSort (l : List α) :
    mergeSort l (r · ·) = insertionSort r l :=
  ((mergeSort_perm l _).trans (perm_insertionSort r l).symm).eq_of_pairwise'
    (pairwise_mergeSort' r l) (pairwise_insertionSort r l)

end TotalAndTransitive

end Correctness

end MergeSort

end sort

section Sorted

variable {α : Type*} {l : List α}

/-!
### The predicates `List.SortedLE`, `List.SortedGE`, `List.SortedLT` and `List.SortedGT`
-/

section Preorder

variable [Preorder α]

/-!
These predicates are equivalent to `Monotone l.get`, but they are also equivalent to
`IsChain (· < ·)` and `Pairwise (· < ·)`. API is provided to move between these forms.

API has deliberately not been provided for decomposed lists to avoid unneeded API replication.
The provided API should be used to move to and from `IsChain`,
`Pairwise` or `Monotone` as needed.
--/

/-- `l.SortedLE` means that the list is monotonic. -/
/-
**List.SortedLE** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：SortedLE (l : List α)
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`l.SortedLE` means that the list is monotonic.
-/
def SortedLE (l : List α) := Monotone l.get
/-- `l.SortedGE` means that the list is antitonic. -/
/-
**List.SortedGE** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [Preorder α] → List α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`l.SortedGE` means that the list is antitonic.
-/
@[to_dual existing SortedLE] def SortedGE (l : List α) := Antitone l.get
/-- `l.SortedLT` means that the list is strictly monotonic. -/
/-
**List.SortedLT** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：SortedLT (l : List α)
参数：l : List α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`l.SortedLT` means that the list is strictly monotonic.
-/
def SortedLT (l : List α) := StrictMono l.get
/-- `l.SortedGT` means that the list is strictly antitonic. -/
/-
**List.SortedGT** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：{α : Type u_1} → [Preorder α] → List α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`l.SortedGT` means that the list is strictly antitonic.
-/
@[to_dual existing SortedLT] def SortedGT (l : List α) := StrictAnti l.get

section Get

/-
**List.sortedLE_iff_monotone_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_iff_monotone_get : l.SortedLE ↔ Monotone l.get
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sortedLE_iff_monotone_get : l.SortedLE ↔ Monotone l.get := .rfl
/-
**List.sortedGE_iff_antitone_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGE_iff_antitone_get : l.SortedGE ↔ Antitone l.get
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sortedGE_iff_antitone_get : l.SortedGE ↔ Antitone l.get := .rfl
/-
**List.sortedLT_iff_strictMono_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_iff_strictMono_get : l.SortedLT ↔ StrictMono l.get
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sortedLT_iff_strictMono_get : l.SortedLT ↔ StrictMono l.get := .rfl
/-
**List.sortedGT_iff_strictAnti_get** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGT_iff_strictAnti_get : l.SortedGT ↔ StrictAnti l.get
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem sortedGT_iff_strictAnti_get : l.SortedGT ↔ StrictAnti l.get := .rfl

protected alias ⟨SortedLE.monotone_get, _root_.Monotone.sortedLE⟩ := sortedLE_iff_monotone_get
protected alias ⟨SortedGE.antitone_get, _root_.Antitone.sortedGE⟩ := sortedGE_iff_antitone_get
protected alias ⟨SortedLT.strictMono_get, _root_.StrictMono.sortedLT⟩ := sortedLT_iff_strictMono_get
protected alias ⟨SortedGT.strictAnti_get, _root_.StrictAnti.sortedGT⟩ := sortedGT_iff_strictAnti_get

end Get

section Pairwise

/-
**List.sortedLE_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedLE ↔ List.Pairw
ise (fun x1 x2 => x1 ≤ x2) l
参数：fun x1 x2 => x1 ≤ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[grind =] theorem sortedLE_iff_pairwise : l.SortedLE ↔ l.Pairwise (· ≤ ·) := by
  simp only [sortedLE_iff_monotone_get, monotone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
/-
**List.sortedGE_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedGE ↔ List.Pairw
ise (fun x1 x2 => x1 ≥ x2) l
参数：fun x1 x2 => x1 ≥ x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[grind =] theorem sortedGE_iff_pairwise : l.SortedGE ↔ l.Pairwise (· ≥ ·) := by
  simp only [sortedGE_iff_antitone_get, antitone_iff_forall_lt, Fin.forall_iff]
  grind [pairwise_iff_getElem]
/-
**List.sortedLT_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedLT ↔ List.Pairw
ise (fun x1 x2 => x1 < x2) l
参数：fun x1 x2 => x1 < x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[grind =] theorem sortedLT_iff_pairwise : l.SortedLT ↔ l.Pairwise (· < ·) := by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff]
  grind [pairwise_iff_getElem]
/-
**List.sortedGT_iff_pairwise** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedGT ↔ List.Pairw
ise (fun x1 x2 => x1 > x2) l
参数：fun x1 x2 => x1 > x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
-/
@[grind =] theorem sortedGT_iff_pairwise : l.SortedGT ↔ l.Pairwise (· > ·) := by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff]
  grind [pairwise_iff_getElem]

protected alias ⟨SortedLE.pairwise, Pairwise.sortedLE⟩ := sortedLE_iff_pairwise
protected alias ⟨SortedGE.pairwise, Pairwise.sortedGE⟩ := sortedGE_iff_pairwise
protected alias ⟨SortedLT.pairwise, Pairwise.sortedLT⟩ := sortedLT_iff_pairwise
protected alias ⟨SortedGT.pairwise, Pairwise.sortedGT⟩ := sortedGT_iff_pairwise

end Pairwise

section IsChain

/-
**List.sortedLE_iff_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_iff_isChain : l.SortedLE ↔ IsChain (· <= ·) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.sortedLE_iff_pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedLE ↔ List.Pairwise (fun x1 x2 => x1 ≤ x2) l
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
-/
theorem sortedLE_iff_isChain : l.SortedLE ↔ IsChain (· ≤ ·) l :=
  sortedLE_iff_pairwise.trans isChain_iff_pairwise.symm
/-
**List.sortedGE_iff_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGE_iff_isChain : l.SortedGE ↔ IsChain (· >= ·) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.sortedGE_iff_pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedGE ↔ List.Pairwise (fun x1 x2 => x1 ≥ x2) l
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
-/
theorem sortedGE_iff_isChain : l.SortedGE ↔ IsChain (· ≥ ·) l :=
  sortedGE_iff_pairwise.trans isChain_iff_pairwise.symm
/-
**List.sortedLT_iff_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_iff_isChain : l.SortedLT ↔ IsChain (· < ·) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.sortedLT_iff_pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedLT ↔ List.Pairwise (fun x1 x2 => x1 < x2) l
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
-/
theorem sortedLT_iff_isChain : l.SortedLT ↔ IsChain (· < ·) l :=
  sortedLT_iff_pairwise.trans isChain_iff_pairwise.symm
/-
**List.sortedGT_iff_isChain** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGT_iff_isChain : l.SortedGT ↔ IsChain (· > ·) l
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.sortedGT_iff_pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedGT ↔ List.Pairwise (fun x1 x2 => x1 > x2) l
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.isChain_iff_pairwise`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α} [Trans R R R], List.IsChain R l ↔ List.Pairwise R l
-/
theorem sortedGT_iff_isChain : l.SortedGT ↔ IsChain (· > ·) l :=
  sortedGT_iff_pairwise.trans isChain_iff_pairwise.symm

protected alias ⟨SortedLE.isChain, IsChain.sortedLE⟩ := sortedLE_iff_isChain
protected alias ⟨SortedGE.isChain, IsChain.sortedGE⟩ := sortedGE_iff_isChain
protected alias ⟨SortedLT.isChain, IsChain.sortedLT⟩ := sortedLT_iff_isChain
protected alias ⟨SortedGT.isChain, IsChain.sortedGT⟩ := sortedGT_iff_isChain

section Decidable

/-
**List.decidableSortedLE** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：decidableSortedLE [DecidableLE α] : DecidablePred (SortedLE (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sortedLE_iff_isChain`：sortedLE_iff_isChain : l.SortedLE ↔ IsChain (
· <= ·) l
-/
instance decidableSortedLE [DecidableLE α] : DecidablePred (SortedLE (α := α)) :=
  fun _ => decidable_of_iff' _ sortedLE_iff_isChain
/-
**List.decidableSortedGE** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：decidableSortedGE [DecidableLE α] : DecidablePred (SortedGE (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sortedGE_iff_isChain`：sortedGE_iff_isChain : l.SortedGE ↔ IsChain (
· >= ·) l
-/
instance decidableSortedGE [DecidableLE α] : DecidablePred (SortedGE (α := α)) :=
  fun _ => decidable_of_iff' _ sortedGE_iff_isChain
/-
**List.decidableSortedLT** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：decidableSortedLT [DecidableLT α] : DecidablePred (SortedLT (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sortedLT_iff_isChain`：sortedLT_iff_isChain : l.SortedLT ↔ IsChain (
· < ·) l
-/
instance decidableSortedLT [DecidableLT α] : DecidablePred (SortedLT (α := α)) :=
  fun _ => decidable_of_iff' _ sortedLT_iff_isChain
/-
**List.decidableSortedGT** 是 Mathlib 中的一个实例，位于命名空间 `List`。
形式化陈述：decidableSortedGT [DecidableLT α] : DecidablePred (SortedGT (α
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sortedGT_iff_isChain`：sortedGT_iff_isChain : l.SortedGT ↔ IsChain (
· > ·) l
-/
instance decidableSortedGT [DecidableLT α] : DecidablePred (SortedGT (α := α)) :=
  fun _ => decidable_of_iff' _ sortedGT_iff_isChain

end Decidable

end IsChain

section GetElem

/-
**List.sortedLE_iff_getElem_le_getElem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_iff_getElem_le_getElem_of_le : l.SortedLE ↔ forall ⦃i j : Nat⦄ ⦃h
i : i < l.length⦄ ⦃hj : j < l.length⦄, i <= j -> l[i] <= l[j]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLE.monotone_get`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedLE → Monotone l.get
· 使用定理 `Monotone.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], Mo
notone l.get → l.SortedLE
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem sortedLE_iff_getElem_le_getElem_of_le :
    l.SortedLE ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i ≤ j → l[i] ≤ l[j] :=
  ⟨fun h _ _ _ _ hij => h.monotone_get hij, fun h => Monotone.sortedLE <| fun _ _ => (h ·)⟩
/-
**List.sortedGE_iff_getElem_ge_getElem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGE_iff_getElem_ge_getElem_of_le : l.SortedGE ↔ forall ⦃i j : Nat⦄ ⦃h
i : i < l.length⦄ ⦃hj : j < l.length⦄, j <= i -> l[i] <= l[j]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedGE.antitone_get`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedGE → Antitone l.get
· 使用定理 `Antitone.sortedGE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], An
titone l.get → l.SortedGE
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem sortedGE_iff_getElem_ge_getElem_of_le :
    l.SortedGE ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j ≤ i → l[i] ≤ l[j] :=
  ⟨fun h _ _ _ _ hij => h.antitone_get hij, fun h => Antitone.sortedGE <| fun _ _ => (h ·)⟩
/-
**List.sortedLT_iff_getElem_lt_getElem_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_iff_getElem_lt_getElem_of_lt : l.SortedLT ↔ forall ⦃i j : Nat⦄ ⦃h
i : i < l.length⦄ ⦃hj : j < l.length⦄, i < j -> l[i] < l[j]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLT.strictMono_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedLT → StrictMono l.get
· 使用定理 `StrictMono.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
StrictMono l.get → l.SortedLT
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem sortedLT_iff_getElem_lt_getElem_of_lt :
    l.SortedLT ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i < j → l[i] < l[j] :=
  ⟨fun h _ _ _ _ hij => h.strictMono_get hij, fun h => StrictMono.sortedLT <| fun _ _ => (h ·)⟩
/-
**List.sortedGT_iff_getElem_gt_getElem_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGT_iff_getElem_gt_getElem_of_lt : l.SortedGT ↔ forall ⦃i j : Nat⦄ ⦃h
i : i < l.length⦄ ⦃hj : j < l.length⦄, j < i -> l[i] < l[j]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedGT.strictAnti_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedGT → StrictAnti l.get
· 使用定理 `StrictAnti.sortedGT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
StrictAnti l.get → l.SortedGT
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
theorem sortedGT_iff_getElem_gt_getElem_of_lt :
    l.SortedGT ↔ ∀ ⦃i j : Nat⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, j < i → l[i] < l[j] :=
  ⟨fun h _ _ _ _ hij => h.strictAnti_get hij, fun h => StrictAnti.sortedGT <| fun _ _ => (h ·)⟩

alias ⟨SortedLE.getElem_le_getElem_of_le, sortedLE_of_getElem_le_getElem_of_le⟩ :=
  sortedLE_iff_getElem_le_getElem_of_le
alias ⟨SortedGE.getElem_ge_getElem_of_le, sortedGE_of_getElem_ge_getElem_of_le⟩ :=
  sortedGE_iff_getElem_ge_getElem_of_le
alias ⟨SortedLT.getElem_lt_getElem_of_lt, sortedLT_of_getElem_lt_getElem_of_lt⟩ :=
  sortedLT_iff_getElem_lt_getElem_of_lt
alias ⟨SortedGT.getElem_gt_getElem_of_lt, sortedGT_of_getElem_gt_getElem_of_lt⟩ :=
  sortedGT_iff_getElem_gt_getElem_of_lt

end GetElem

section

/-
**List.SortedLT.sortedLE** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List α}, l.SortedLT → l.SortedLE
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], Mo
notone l.get → l.SortedLE
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `List.SortedLT.strictMono_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedLT → StrictMono l.get
-/
protected theorem SortedLT.sortedLE {l : List α} (h : l.SortedLT) : l.SortedLE :=
  h.strictMono_get.monotone.sortedLE
/-
**List.SortedGT.sortedGE** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedGT`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List α}, l.SortedGT → l.SortedGE
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.sortedGE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], An
titone l.get → l.SortedGE
· 使用定理 `StrictAnti.antitone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictAnti f → Antitone f
· 使用定理 `List.SortedGT.strictAnti_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedGT → StrictAnti l.get
-/
protected theorem SortedGT.sortedGE {l : List α} (h : l.SortedGT) : l.SortedGE :=
  h.strictAnti_get.antitone.sortedGE
/-
**List.SortedLT.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedLT → l.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nodup`：∀ {α : Type u} {l : List α}, Function.Injectiv
e l.get → l.Nodup
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `List.SortedLT.strictMono_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedLT → StrictMono l.get
-/
protected theorem SortedLT.nodup (h : l.SortedLT) : l.Nodup := h.strictMono_get.injective.nodup
/-
**List.SortedGT.nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedGT`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.SortedGT → l.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nodup`：∀ {α : Type u} {l : List α}, Function.Injectiv
e l.get → l.Nodup
· 使用定理 `StrictAnti.injective`：StrictAnti.injective (hf : StrictAnti f) : Injecti
ve f
· 使用定理 `List.SortedGT.strictAnti_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedGT → StrictAnti l.get
-/
protected theorem SortedGT.nodup (h : l.SortedGT) : l.Nodup := h.strictAnti_get.injective.nodup
/-
**List.sortedLE_replicate** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_replicate {a : α} (n : Nat) : (replicate n a).SortedLE
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_replicate`：∀ {α : Type u_1} {R : α → α → Prop} {n : ℕ} {a 
: α}, List.Pairwise R (List.replicate n a) ↔ n ≤ 1 ∨ R a a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem sortedLE_replicate {a : α} (n : ℕ) : (replicate n a).SortedLE :=
  (pairwise_replicate.mpr (Or.inr le_rfl)).sortedLE
/-
**List.sortedLT_finRange** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_finRange (n : Nat) : (finRange n).SortedLT
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sortedLT_of_getElem_lt_getElem_of_lt`：∀ {α : Type u_1} {l : List α}
 [inst : Preorder α],   (∀ ⦃i j : ℕ⦄ ⦃hi : i < l.length⦄ ⦃hj : j < l.length⦄, i 
< j → l[i] < l[j]) → l.SortedLT
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_finRange`：∀ {n : ℕ}, (List.finRange n).length = n
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.getElem_finRange`：∀ {n i : ℕ} (h : i < (List.finRange n).length), (
List.finRange n)[i] = Fin.cast ⋯ ⟨i, h⟩
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem sortedLT_finRange (n : ℕ) : (finRange n).SortedLT :=
  sortedLT_of_getElem_lt_getElem_of_lt <| by simp
/-
**List.sortedLT_range** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_range (n : Nat) : (range n).SortedLT
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 < x2) l → l.SortedLT
· 使用定理 `List.pairwise_lt_range`：∀ {n : ℕ}, List.Pairwise (fun x1 x2 => x1 < x2) 
(List.range n)
-/
theorem sortedLT_range (n : ℕ) : (range n).SortedLT := pairwise_lt_range.sortedLT
/-
**List.sortedLT_range'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_range' (a b) {s} (hs : s != 0) : (range' a b s).SortedLT
参数：a b；hs : s != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 < x2) l → l.SortedLT
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `List.pairwise_lt_range'`：∀ {s n : ℕ} (step : optParam ℕ 1),   autoParam 
(0 < step) List.pairwise_lt_range'._auto_1 → List.Pairwise (fun x1 x2 => x1 < x2
) (List.range…
· 使用定理 `Nat.pos_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → 0 < n
-/
theorem sortedLT_range' (a b) {s} (hs : s ≠ 0) :
    (range' a b s).SortedLT := (pairwise_lt_range' _ (Nat.pos_of_ne_zero hs)).sortedLT
/-
**List.sortedLE_range'** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_range' (a b s) : (range' a b s).SortedLE
参数：a b s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用引理 `List.range'`：range'_0 (a b : Nat) : range' a b 0 = replicate b a
· 使用定理 `List.pairwise_le_range'`：∀ {s n : ℕ} (step : optParam ℕ 1), List.Pairwis
e (fun x1 x2 => x1 ≤ x2) (List.range' s n step)
-/
theorem sortedLE_range' (a b s) :
    (range' a b s).SortedLE := (pairwise_le_range' _).sortedLE

end

section OfFn

variable {n : ℕ} {f : Fin n → α}

/-- The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is monotone. -/
/-
**List.sortedLE_ofFn_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f
).SortedLE ↔ Monotone f
参数：List.ofFn f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (F
in.cast (by simp) i)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The list `List.ofFn f` is sorted with respect to `(· ≤ ·)` if and only if `f` is
 monotone.
-/
@[simp] theorem sortedLE_ofFn_iff : (ofFn f).SortedLE ↔ Monotone f := by
  simp only [sortedLE_iff_monotone_get, Monotone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

/-- The list `List.ofFn f` is sorted with respect to `(· ≥ ·)` if and only if `f` is antitone. -/
/-
**List.sortedGE_ofFn_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f
).SortedGE ↔ Antitone f
参数：List.ofFn f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (F
in.cast (by simp) i)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The list `List.ofFn f` is sorted with respect to `(· ≥ ·)` if and only if `f` is
 antitone.
-/
@[simp] theorem sortedGE_ofFn_iff : (ofFn f).SortedGE ↔ Antitone f := by
  simp only [sortedGE_iff_antitone_get, Antitone, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_le_mk]

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only if `f` is
strictly monotone. -/
/-
**List.sortedLT_ofFn_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f
).SortedLT ↔ StrictMono f
参数：List.ofFn f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (F
in.cast (by simp) i)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The list `List.ofFn f` is strictly sorted with respect to `(· ≤ ·)` if and only 
if `f` is
strictly monotone.
-/
@[simp] theorem sortedLT_ofFn_iff : (ofFn f).SortedLT ↔ StrictMono f := by
  simp only [sortedLT_iff_strictMono_get, StrictMono, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

/-- The list `List.ofFn f` is strictly sorted with respect to `(· ≥ ·)` if and only if `f` is
strictly antitone. -/
/-
**List.sortedGT_ofFn_iff** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {n : ℕ} {f : Fin n → α}, (List.ofFn f
).SortedGT ↔ StrictAnti f
参数：List.ofFn f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_ofFn`：∀ {n : ℕ} {α : Type u_1} {f : Fin n → α}, (List.ofFn f
).length = n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `List.get_ofFn`：get_ofFn {n} (f : Fin n -> α) (i) : get (ofFn f) i = f (F
in.cast (by simp) i)
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The list `List.ofFn f` is strictly sorted with respect to `(· ≥ ·)` if and only 
if `f` is
strictly antitone.
-/
@[simp] theorem sortedGT_ofFn_iff : (ofFn f).SortedGT ↔ StrictAnti f := by
  simp only [sortedGT_iff_strictAnti_get, StrictAnti, Fin.forall_iff,
    length_ofFn, get_ofFn, Fin.cast_mk, Fin.mk_lt_mk]

/-- The list obtained from a monotone tuple is sorted. -/
protected alias ⟨SortedLE.monotone, _root_.Monotone.sortedLE_ofFn⟩ := sortedLE_ofFn_iff
/-- The list obtained from an antitone tuple is sorted. -/
protected alias ⟨SortedGE.antitone, _root_.Antitone.sortedGE_ofFn⟩ := sortedGE_ofFn_iff
/-- The list obtained from a strictly monotone tuple is sorted. -/
protected alias ⟨SortedLT.strictMono, _root_.StrictMono.sortedLT_ofFn⟩ := sortedLT_ofFn_iff
/-- The list obtained from a strictly antitone tuple is sorted. -/
protected alias ⟨SortedGT.strictAnti, _root_.StrictAnti.sortedGT_ofFn⟩ := sortedGT_ofFn_iff

end OfFn

section Reverse

/-
**List.sortedLE_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.reverse.SortedLE ↔ l.
SortedGE
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedLE_reverse : l.reverse.SortedLE ↔ l.SortedGE := by grind
/-
**List.sortedGE_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.reverse.SortedGE ↔ l.
SortedLE
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedGE_reverse : l.reverse.SortedGE ↔ l.SortedLE := by grind
/-
**List.sortedLT_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.reverse.SortedLT ↔ l.
SortedGT
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedLT_reverse : l.reverse.SortedLT ↔ l.SortedGT := by grind
/-
**List.sortedGT_reverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : Preorder α], l.reverse.SortedGT ↔ l.
SortedLT
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedGT_reverse : l.reverse.SortedGT ↔ l.SortedLT := by grind

protected alias ⟨SortedLE.of_reverse, SortedGE.reverse⟩ := sortedLE_reverse
protected alias ⟨SortedGE.of_reverse, SortedLE.reverse⟩ := sortedGE_reverse
protected alias ⟨SortedLT.of_reverse, SortedGT.reverse⟩ := sortedLT_reverse
protected alias ⟨SortedGT.of_reverse, SortedLT.reverse⟩ := sortedGT_reverse

end Reverse

section Dual

section OfDual

variable {l : List αᵒᵈ}

/-
**List.sortedLE_map_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List αᵒᵈ}, (List.map (⇑OrderDual
.ofDual) l).SortedLE ↔ l.SortedGE
参数：List.map (⇑OrderDual.ofDual) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedLE_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLE ↔ l.SortedGE := by
  grind [OrderDual.ofDual_le_ofDual]
/-
**List.sortedGE_map_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List αᵒᵈ}, (List.map (⇑OrderDual
.ofDual) l).SortedGE ↔ l.SortedLE
参数：List.map (⇑OrderDual.ofDual) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedGE_map_ofDual :
    (l.map OrderDual.ofDual).SortedGE ↔ l.SortedLE := by
  grind [OrderDual.ofDual_le_ofDual]
/-
**List.sortedLT_map_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List αᵒᵈ}, (List.map (⇑OrderDual
.ofDual) l).SortedLT ↔ l.SortedGT
参数：List.map (⇑OrderDual.ofDual) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedLT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedLT ↔ l.SortedGT := by
  grind [OrderDual.ofDual_lt_ofDual]
/-
**List.sortedGT_map_ofDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {l : List αᵒᵈ}, (List.map (⇑OrderDual
.ofDual) l).SortedGT ↔ l.SortedLT
参数：List.map (⇑OrderDual.ofDual) l。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem sortedGT_map_ofDual {l : List αᵒᵈ} :
    (l.map OrderDual.ofDual).SortedGT ↔ l.SortedLT := by
  grind [OrderDual.ofDual_lt_ofDual]

protected alias ⟨SortedLE.map_ofDual, SortedGE.of_map_ofDual⟩ := sortedLE_map_ofDual
protected alias ⟨SortedGE.map_ofDual, SortedLE.of_map_ofDual⟩ := sortedGE_map_ofDual
protected alias ⟨SortedLT.map_ofDual, SortedGT.of_map_ofDual⟩ := sortedLT_map_ofDual
protected alias ⟨SortedGT.map_ofDual, SortedLT.of_map_ofDual⟩ := sortedGT_map_ofDual

end OfDual

section ToDual

variable {l : List α}

/-
**List.sortedLE_map_toDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_map_toDual {l : List α} : (l.map OrderDual.toDual).SortedLE ↔ l.S
ortedGE
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedLE_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedLE ↔ l.SortedGE := by
  grind [OrderDual.toDual_le_toDual]
/-
**List.sortedGE_map_toDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGE_map_toDual {l : List α} : (l.map OrderDual.toDual).SortedGE ↔ l.S
ortedLE
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedGE_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedGE ↔ l.SortedLE := by
  grind [OrderDual.toDual_le_toDual]
/-
**List.sortedLT_map_toDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_map_toDual {l : List α} : (l.map OrderDual.toDual).SortedLT ↔ l.S
ortedGT
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedLT_map_toDual {l : List α} :
    (l.map OrderDual.toDual).SortedLT ↔ l.SortedGT := by
  grind [OrderDual.toDual_lt_toDual]
/-
**List.sortedGT_map_toDual** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGT_map_toDual {l : List αᵒᵈ} : (l.map OrderDual.toDual).SortedGT ↔ l
.SortedLT
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedGT_map_toDual {l : List αᵒᵈ} :
    (l.map OrderDual.toDual).SortedGT ↔ l.SortedLT := by
  grind [OrderDual.toDual_lt_toDual]

protected alias ⟨SortedLE.map_toDual, SortedGE.of_map_toDual⟩ := sortedLE_map_toDual
protected alias ⟨SortedGE.map_toDual, SortedLE.of_map_toDual⟩ := sortedGE_map_toDual
protected alias ⟨SortedLT.map_toDual, SortedGT.of_map_toDual⟩ := sortedLT_map_toDual
protected alias ⟨SortedGT.map_toDual, SortedLT.of_map_toDual⟩ := sortedGT_map_toDual

end ToDual

end Dual

end Preorder

section PartialOrder

variable [PartialOrder α]

/-
**List.SortedLE.sortedLT_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLE`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l : List α}, l.SortedLE → l.Nodu
p → l.SortedLT
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.sortedLT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
StrictMono l.get → l.SortedLT
· 使用定理 `Monotone.strictMono_of_injective`：Monotone.strictMono_of_injective (h₁ :
 Monotone f) (h₂ : Injective f) : StrictMono f
· 使用定理 `List.SortedLE.monotone_get`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedLE → Monotone l.get
· 使用定理 `List.Nodup.injective_get`：∀ {α : Type u} {l : List α}, l.Nodup → Functio
n.Injective l.get
-/
protected theorem SortedLE.sortedLT_of_nodup {l : List α} (h₁ : l.SortedLE) (h₂ : l.Nodup) :
    l.SortedLT := (h₁.monotone_get.strictMono_of_injective h₂.injective_get).sortedLT
/-
**List.SortedGE.sortedGT_of_nodup** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedGE`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l : List α}, l.SortedGE → l.Nodu
p → l.SortedGT
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.sortedGT`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
StrictAnti l.get → l.SortedGT
· 使用定理 `Antitone.strictAnti_of_injective`：Antitone.strictAnti_of_injective (h₁ :
 Antitone f) (h₂ : Injective f) : StrictAnti f
· 使用定理 `List.SortedGE.antitone_get`：∀ {α : Type u_1} {l : List α} [inst : Preord
er α], l.SortedGE → Antitone l.get
· 使用定理 `List.Nodup.injective_get`：∀ {α : Type u} {l : List α}, l.Nodup → Functio
n.Injective l.get
-/
protected theorem SortedGE.sortedGT_of_nodup {l : List α} (h₁ : l.SortedGE) (h₂ : l.Nodup) :
    l.SortedGT := (h₁.antitone_get.strictAnti_of_injective h₂.injective_get).sortedGT
/-
**List.sortedLT_iff_nodup_and_sortedLE** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLT_iff_nodup_and_sortedLE : l.SortedLT ↔ l.Nodup ∧ l.SortedLE
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLT.nodup`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
l.SortedLT → l.Nodup
· 使用定理 `List.SortedLT.sortedLE`：∀ {α : Type u_1} [inst : Preorder α] {l : List α
}, l.SortedLT → l.SortedLE
· 使用定理 `List.SortedLE.sortedLT_of_nodup`：∀ {α : Type u_1} [inst : PartialOrder α
] {l : List α}, l.SortedLE → l.Nodup → l.SortedLT
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sortedLT_iff_nodup_and_sortedLE : l.SortedLT ↔ l.Nodup ∧ l.SortedLE :=
  ⟨fun h => ⟨h.nodup, h.sortedLE⟩, fun h => h.2.sortedLT_of_nodup h.1⟩
/-
**List.sortedGT_iff_nodup_and_sortedGE** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGT_iff_nodup_and_sortedGE : l.SortedGT ↔ l.Nodup ∧ l.SortedGE
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedGT.nodup`：∀ {α : Type u_1} {l : List α} [inst : Preorder α], 
l.SortedGT → l.Nodup
· 使用定理 `List.SortedGT.sortedGE`：∀ {α : Type u_1} [inst : Preorder α] {l : List α
}, l.SortedGT → l.SortedGE
· 使用定理 `List.SortedGE.sortedGT_of_nodup`：∀ {α : Type u_1} [inst : PartialOrder α
] {l : List α}, l.SortedGE → l.Nodup → l.SortedGT
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem sortedGT_iff_nodup_and_sortedGE : l.SortedGT ↔ l.Nodup ∧ l.SortedGE :=
  ⟨fun h => ⟨h.nodup, h.sortedGE⟩, fun h => h.2.sortedGT_of_nodup h.1⟩
/-
**List.Perm.eq_of_sortedLE** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedLE → l
₂.SortedLE → l₁.Perm l₂ → l₁ = l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
-/
theorem Perm.eq_of_sortedLE {l₁ l₂ : List α} (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : (hl₁₂ : l₁ ~ l₂) → l₁ = l₂ :=
  Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise
/-
**List.Perm.eq_of_sortedGE** 是 Mathlib 中的一个定理，位于命名空间 `List.Perm`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.SortedGE → l
₂.SortedGE → l₁.Perm l₂ → l₁ = l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_pairwise'`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Anti
symm r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise r l₂ → l₁.Perm l₂
 → l₁ = l₂
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `List.SortedGE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGE → List.Pairwise (fun x1 x2 => x1 ≥ x2) l
-/
theorem Perm.eq_of_sortedGE {l₁ l₂ : List α} (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : (hl₁₂ : l₁ ~ l₂) → l₁ = l₂ :=
  Perm.eq_of_pairwise' hl₁.pairwise hl₂.pairwise
/-
**List.Subset.antisymm_of_sortedLT** 是 Mathlib 中的一个定理，位于命名空间 `List.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₂ ⊆ 
l₁ → l₁.SortedLT → l₂.SortedLT → l₁ = l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Subset.antisymm_of_pairwise`：∀ {α : Type u_1} {r : α → α → Prop} [S
td.Antisymm r] [Std.Irrefl r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pair
wise r l₂ → l₁ ⊆ l₂ → …
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
-/
theorem Subset.antisymm_of_sortedLT {l₁ l₂ : List α} (hl₁₂ : l₁ ⊆ l₂) (hl₁₂' : l₂ ⊆ l₁)
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) : l₁ = l₂ :=
  hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'
/-
**List.Subset.antisymm_of_sortedGT** 是 Mathlib 中的一个定理，位于命名空间 `List.Subset`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁ ⊆ l₂ → l₂ ⊆ 
l₁ → l₁.SortedGT → l₂.SortedGT → l₁ = l₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Subset.antisymm_of_pairwise`：∀ {α : Type u_1} {r : α → α → Prop} [S
td.Antisymm r] [Std.Irrefl r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pair
wise r l₂ → l₁ ⊆ l₂ → …
· 使用定理 `instAntisymmGt`：∀ {α : Type u} [inst : Preorder α], Std.Antisymm fun x1 
x2 => x2 < x1
· 使用定理 `instIrreflGt`：∀ {α : Type u} [inst : Preorder α], Std.Irrefl fun x1 x2 =
> x2 < x1
· 使用定理 `List.SortedGT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGT → List.Pairwise (fun x1 x2 => x1 > x2) l
-/
theorem Subset.antisymm_of_sortedGT {l₁ l₂ : List α} (hl₁₂ : l₁ ⊆ l₂) (hl₁₂' : l₂ ⊆ l₁)
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) : l₁ = l₂ :=
  hl₁₂.antisymm_of_pairwise h₁.pairwise h₂.pairwise hl₁₂'
/-
**List.SortedLT.eq_of_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α},   l₁.SortedLT →
 l₂.SortedLT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
参数：∀ (a : α), a ∈ l₁ ↔ a ∈ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.eq_of_mem_iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.An
tisymm r] [Std.Irrefl r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise 
r l₂ → (∀ (a : α)…
· 使用定理 `List.SortedLT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLT → List.Pairwise (fun x1 x2 => x1 < x2) l
-/
theorem SortedLT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedLT) (h₂ : l₂.SortedLT) : (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise
/-
**List.SortedGT.eq_of_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedGT`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α},   l₁.SortedGT →
 l₂.SortedGT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ = l₂
参数：∀ (a : α), a ∈ l₁ ↔ a ∈ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.eq_of_mem_iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.An
tisymm r] [Std.Irrefl r] {l₁ l₂ : List α},   List.Pairwise r l₁ → List.Pairwise 
r l₂ → (∀ (a : α)…
· 使用定理 `instAntisymmGt`：∀ {α : Type u} [inst : Preorder α], Std.Antisymm fun x1 
x2 => x2 < x1
· 使用定理 `instIrreflGt`：∀ {α : Type u} [inst : Preorder α], Std.Irrefl fun x1 x2 =
> x2 < x1
· 使用定理 `List.SortedGT.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGT → List.Pairwise (fun x1 x2 => x1 > x2) l
-/
theorem SortedGT.eq_of_mem_iff {l₁ l₂ : List α}
    (h₁ : l₁.SortedGT) (h₂ : l₂.SortedGT) (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) : l₁ = l₂ :=
  h₁.pairwise.eq_of_mem_iff h₂.pairwise h
/-
**List.Perm.eq_reverse_of_sortedLE_of_sortedGE** 是 Mathlib 中的一个定理，位于命名空间 `List.P
erm`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α}, l₁.Perm l₂ → l₁
.SortedLE → l₂.SortedGE → l₁ = l₂.reverse
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Perm.eq_of_sortedLE`：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l
₂ : List α}, l₁.SortedLE → l₂.SortedLE → l₁.Perm l₂ → l₁ = l₂
· 使用定理 `List.SortedGE.reverse`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, l.SortedGE → l.reverse.SortedLE
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.perm_reverse`：∀ {α : Type u} {l₁ l₂ : List α}, l₁.Perm l₂.reverse ↔
 l₁.Perm l₂
-/
theorem Perm.eq_reverse_of_sortedLE_of_sortedGE {l₁ l₂ : List α} (hp : l₁ ~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedGE) : l₁ = l₂.reverse :=
  (perm_reverse.mpr hp).eq_of_sortedLE hl₁ hl₂.reverse
/-
**List.SortedLT.eq_reverse_of_mem_iff_of_sortedGT** 是 Mathlib 中的一个定理，位于命名空间 `Lis
t.SortedLT`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α},   (∀ (a : α), a
 ∈ l₁ ↔ a ∈ l₂) → l₁.SortedLT → l₂.SortedGT → l₁ = l₂.reverse
参数：∀ (a : α), a ∈ l₁ ↔ a ∈ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedLT.eq_of_mem_iff`：∀ {α : Type u_1} [inst : PartialOrder α] {l
₁ l₂ : List α},   l₁.SortedLT → l₂.SortedLT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ 
= l₂
· 使用定理 `List.SortedGT.reverse`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, l.SortedGT → l.reverse.SortedLT
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem SortedLT.eq_reverse_of_mem_iff_of_sortedGT {l₁ l₂ : List α}
    (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) (hl₁ : l₁.SortedLT)
    (hl₂ : l₂.SortedGT) : l₁ = l₂.reverse := hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)
/-
**List.SortedGT.eq_reverse_of_mem_iff_of_sortedLT** 是 Mathlib 中的一个定理，位于命名空间 `Lis
t.SortedGT`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] {l₁ l₂ : List α},   (∀ (a : α), a
 ∈ l₁ ↔ a ∈ l₂) → l₁.SortedGT → l₂.SortedLT → l₁ = l₂.reverse
参数：∀ (a : α), a ∈ l₁ ↔ a ∈ l₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.SortedGT.eq_of_mem_iff`：∀ {α : Type u_1} [inst : PartialOrder α] {l
₁ l₂ : List α},   l₁.SortedGT → l₂.SortedGT → (∀ (a : α), a ∈ l₁ ↔ a ∈ l₂) → l₁ 
= l₂
· 使用定理 `List.SortedLT.reverse`：∀ {α : Type u_1} {l : List α} [inst : Preorder α]
, l.SortedLT → l.reverse.SortedGT
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem SortedGT.eq_reverse_of_mem_iff_of_sortedLT {l₁ l₂ : List α}
    (h : ∀ a : α, a ∈ l₁ ↔ a ∈ l₂) (hl₁ : l₁.SortedGT)
    (hl₂ : l₂.SortedLT) : l₁ = l₂.reverse :=
  hl₁.eq_of_mem_iff hl₂.reverse (by simpa using h)
/-
**List.sublist_of_subperm_of_sortedLE** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_of_subperm_of_sortedLE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁
.SortedLE) (hl₂ : l₂.SortedLE) : l₁ <+ l₂
参数：hp : l₁ <+~ l₂；hl₁ : l₁.SortedLE；hl₂ : l₂.SortedLE。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublist_of_subperm_of_pairwise`：sublist_of_subperm_of_pairwise {l₁ 
l₂ : List α} (hp : l₁ <+~ l₂) (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <
+ l₂
· 使用定理 `List.SortedLE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedLE → List.Pairwise (fun x1 x2 => x1 ≤ x2) l
-/
theorem sublist_of_subperm_of_sortedLE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedLE)
    (hl₂ : l₂.SortedLE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise
/-
**List.sublist_of_subperm_of_sortedGE** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_of_subperm_of_sortedGE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁
.SortedGE) (hl₂ : l₂.SortedGE) : l₁ <+ l₂
参数：hp : l₁ <+~ l₂；hl₁ : l₁.SortedGE；hl₂ : l₂.SortedGE。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.sublist_of_subperm_of_pairwise`：sublist_of_subperm_of_pairwise {l₁ 
l₂ : List α} (hp : l₁ <+~ l₂) (hs₁ : l₁.Pairwise r) (hs₂ : l₂.Pairwise r) : l₁ <
+ l₂
· 使用定理 `instAntisymmGe`：∀ {α : Type u} [inst : PartialOrder α], Std.Antisymm fun
 x1 x2 => x2 ≤ x1
· 使用定理 `List.SortedGE.pairwise`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], l.SortedGE → List.Pairwise (fun x1 x2 => x1 ≥ x2) l
-/
theorem sublist_of_subperm_of_sortedGE {l₁ l₂ : List α} (hp : l₁ <+~ l₂) (hl₁ : l₁.SortedGE)
    (hl₂ : l₂.SortedGE) : l₁ <+ l₂ := sublist_of_subperm_of_pairwise hp hl₁.pairwise hl₂.pairwise

end PartialOrder

section LinearOrder

variable [LinearOrder α]

/-
**List.sortedLE_mergeSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_mergeSort : (l.mergeSort (· <= ·)).SortedLE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `List.pairwise_mergeSort'`：pairwise_mergeSort' (l : List α) : Pairwise r 
(mergeSort l (r · ·))
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem sortedLE_mergeSort : (l.mergeSort (· ≤ ·)).SortedLE :=
  (pairwise_mergeSort' _ _).sortedLE
/-
**List.sortedGE_mergeSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGE_mergeSort : (l.mergeSort (· >= ·)).SortedGE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedGE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≥ x2) l → l.SortedGE
· 使用定理 `List.pairwise_mergeSort'`：pairwise_mergeSort' (l : List α) : Pairwise r 
(mergeSort l (r · ·))
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
-/
theorem sortedGE_mergeSort : (l.mergeSort (· ≥ ·)).SortedGE :=
  (pairwise_mergeSort' _ _).sortedGE
/-
**List.sortedLE_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedLE_insertionSort : (l.insertionSort (· <= ·)).SortedLE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedLE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≤ x2) l → l.SortedLE
· 使用定理 `List.pairwise_insertionSort`：∀ {α : Type u_1} (r : α → α → Prop) [inst :
 DecidableRel r] [Std.Total r] [IsTrans α r] (l : List α),   List.Pairwise r (Li
st.insertionSort …
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
-/
theorem sortedLE_insertionSort : (l.insertionSort (· ≤ ·)).SortedLE :=
  (pairwise_insertionSort _ _).sortedLE
/-
**List.sortedGE_insertionSort** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sortedGE_insertionSort : (l.insertionSort (· >= ·)).SortedGE
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Pairwise.sortedGE`：∀ {α : Type u_1} {l : List α} [inst : Preorder α
], List.Pairwise (fun x1 x2 => x1 ≥ x2) l → l.SortedGE
· 使用定理 `List.pairwise_insertionSort`：∀ {α : Type u_1} (r : α → α → Prop) [inst :
 DecidableRel r] [Std.Total r] [IsTrans α r] (l : List α),   List.Pairwise r (Li
st.insertionSort …
· 使用定理 `LE.total'`：∀ {α : Type u} [inst : LinearOrder α], Std.Total fun x1 x2 =>
 x2 ≤ x1
· 使用定理 `instIsTransGe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x2 ≤ x1
-/
theorem sortedGE_insertionSort : (l.insertionSort (· ≥ ·)).SortedGE :=
  (pairwise_insertionSort _ _).sortedGE

@[simp]
/-
**List.SortedLT.getElem_le_getElem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`
。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : LinearOrder α],   l.SortedLT → ∀ {i 
j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] ≤ l[j] ↔ i ≤ j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b
· 使用定理 `List.SortedLT.strictMono_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedLT → StrictMono l.get
-/
theorem SortedLT.getElem_le_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] ≤ l[j] ↔ i ≤ j := hl.strictMono_get.le_iff_le

@[simp]
/-
**List.SortedGT.getElem_le_getElem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedGT`
。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : LinearOrder α],   l.SortedGT → ∀ {i 
j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] ≤ l[j] ↔ j ≤ i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `List.SortedGT.strictAnti_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedGT → StrictAnti l.get
-/
theorem SortedGT.getElem_le_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] ≤ l[j] ↔ j ≤ i := hl.strictAnti_get.le_iff_ge

@[simp]
/-
**List.SortedLT.getElem_lt_getElem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedLT`
。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : LinearOrder α],   l.SortedLT → ∀ {i 
j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] < l[j] ↔ i < j
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `List.SortedLT.strictMono_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedLT → StrictMono l.get
-/
theorem SortedLT.getElem_lt_getElem_iff (hl : l.SortedLT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ i < j := hl.strictMono_get.lt_iff_lt

@[simp]
/-
**List.SortedGT.getElem_lt_getElem_iff** 是 Mathlib 中的一个定理，位于命名空间 `List.SortedGT`
。
形式化陈述：∀ {α : Type u_1} {l : List α} [inst : LinearOrder α],   l.SortedGT → ∀ {i 
j : ℕ} {hi : i < l.length} {hj : j < l.length}, l[i] < l[j] ↔ j < i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictAnti.lt_iff_gt`：StrictAnti.lt_iff_gt (hf : StrictAnti f) {a b : α}
 : f a < f b ↔ b < a
· 使用定理 `List.SortedGT.strictAnti_get`：∀ {α : Type u_1} {l : List α} [inst : Preo
rder α], l.SortedGT → StrictAnti l.get
-/
theorem SortedGT.getElem_lt_getElem_iff (hl : l.SortedGT) {i j} {hi : i < l.length}
    {hj : j < l.length} : l[i] < l[j] ↔ j < i := hl.strictAnti_get.lt_iff_gt

end LinearOrder

end Sorted

end List

namespace RelEmbedding

open List

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
/-
**RelEmbedding.pairwise_listMap** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：pairwise_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.P
airwise ra
参数：e : ra ↪r rb。
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
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra := by
  simp [pairwise_map, e.map_rel_iff]

@[simp]
/-
**RelEmbedding.pairwise_swap_listMap** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：pairwise_swap_listMap (e : ra ↪r rb) {l : List α} : (l.map e).Pairwise (Fu
nction.swap rb) ↔ l.Pairwise (Function.swap ra)
参数：e : ra ↪r rb。
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
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pairwise_swap_listMap (e : ra ↪r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) := by
  simp [pairwise_map, e.map_rel_iff]

end RelEmbedding

namespace RelIso

variable {α β : Type*} {ra : α → α → Prop} {rb : β → β → Prop}

@[simp]
/-
**RelIso.pairwise_listMap** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：pairwise_listMap (e : ra ≃r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.P
airwise ra
参数：e : ra ≃r rb。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.pairwise_listMap`：pairwise_listMap (e : ra ↪r rb) {l : List
 α} : (l.map e).Pairwise rb ↔ l.Pairwise ra
-/
theorem pairwise_listMap (e : ra ≃r rb) {l : List α} : (l.map e).Pairwise rb ↔ l.Pairwise ra :=
  e.toRelEmbedding.pairwise_listMap

@[simp]
/-
**RelIso.pairwise_swap_listMap** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：pairwise_swap_listMap (e : ra ≃r rb) {l : List α} : (l.map e).Pairwise (Fu
nction.swap rb) ↔ l.Pairwise (Function.swap ra)
参数：e : ra ≃r rb。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.pairwise_swap_listMap`：pairwise_swap_listMap (e : ra ↪r rb)
 {l : List α} : (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swa
p ra)
-/
theorem pairwise_swap_listMap (e : ra ≃r rb) {l : List α} :
    (l.map e).Pairwise (Function.swap rb) ↔ l.Pairwise (Function.swap ra) :=
  e.toRelEmbedding.pairwise_swap_listMap

end RelIso

namespace OrderEmbedding

open List

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
/-
**OrderEmbedding.sortedLE_listMap** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：sortedLE_listMap (e : α ↪o β) {l : List α} : (l.map e).SortedLE ↔ l.Sorted
LE
参数：e : α ↪o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RelEmbedding.pairwise_listMap`：pairwise_listMap (e : ra ↪r rb) {l : List
 α} : (l.map e).Pairwise rb ↔ l.Pairwise ra
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sortedLE_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedLE ↔ l.SortedLE := by
  simp_rw [sortedLE_iff_pairwise, e.pairwise_listMap]

@[simp]
/-
**OrderEmbedding.sortedLT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：sortedLT_listMap (e : α ↪o β) {l : List α} : (l.map e).SortedLT ↔ l.Sorted
LT
参数：e : α ↪o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelEmbedding.pairwise_listMap`：pairwise_listMap (e : ra ↪r rb) {l : List
 α} : (l.map e).Pairwise rb ↔ l.Pairwise ra
-/
theorem sortedLT_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedLT ↔ l.SortedLT := by
  simp_rw [sortedLT_iff_pairwise]
  exact e.ltEmbedding.pairwise_listMap

@[simp]
/-
**OrderEmbedding.sortedGE_listMap** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：sortedGE_listMap (e : α ↪o β) {l : List α} : (l.map e).SortedGE ↔ l.Sorted
GE
参数：e : α ↪o β。
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
theorem sortedGE_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedGE ↔ l.SortedGE := by
  simp_rw [← sortedLE_reverse, ← map_reverse, sortedLE_listMap]

@[simp]
/-
**OrderEmbedding.sortedGT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：sortedGT_listMap (e : α ↪o β) {l : List α} : (l.map e).SortedGT ↔ l.Sorted
GT
参数：e : α ↪o β。
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
theorem sortedGT_listMap (e : α ↪o β) {l : List α} :
    (l.map e).SortedGT ↔ l.SortedGT := by
  simp_rw [← sortedLT_reverse, ← map_reverse, sortedLT_listMap]

end OrderEmbedding

namespace OrderIso

variable {α β : Type*} [Preorder α] [Preorder β]

@[simp]
/-
**OrderIso.sortedLT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sortedLT_listMap (e : α ≃o β) {l : List α} : (l.map e).SortedLT ↔ l.Sorted
LT
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.sortedLT_listMap`：sortedLT_listMap (e : α ↪o β) {l : List
 α} : (l.map e).SortedLT ↔ l.SortedLT
-/
theorem sortedLT_listMap (e : α ≃o β) {l : List α} :
    (l.map e).SortedLT ↔ l.SortedLT :=
  e.toOrderEmbedding.sortedLT_listMap

@[simp]
/-
**OrderIso.sortedGT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：sortedGT_listMap (e : α ≃o β) {l : List α} : (l.map e).SortedGT ↔ l.Sorted
GT
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.sortedGT_listMap`：sortedGT_listMap (e : α ↪o β) {l : List
 α} : (l.map e).SortedGT ↔ l.SortedGT
-/
theorem sortedGT_listMap (e : α ≃o β) {l : List α} :
    (l.map e).SortedGT ↔ l.SortedGT :=
  e.toOrderEmbedding.sortedGT_listMap

end OrderIso

namespace StrictMono

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

/-
**StrictMono.sortedLE_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：sortedLE_listMap (hf : StrictMono f) : (l.map f).SortedLE ↔ l.SortedLE
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.sortedLE_listMap`：sortedLE_listMap (e : α ↪o β) {l : List
 α} : (l.map e).SortedLE ↔ l.SortedLE
-/
theorem sortedLE_listMap (hf : StrictMono f) :
    (l.map f).SortedLE ↔ l.SortedLE :=
  (OrderEmbedding.ofStrictMono f hf).sortedLE_listMap
/-
**StrictMono.sortedGE_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：sortedGE_listMap (hf : StrictMono f) : (l.map f).SortedGE ↔ l.SortedGE
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.sortedGE_listMap`：sortedGE_listMap (e : α ↪o β) {l : List
 α} : (l.map e).SortedGE ↔ l.SortedGE
-/
theorem sortedGE_listMap (hf : StrictMono f) :
    (l.map f).SortedGE ↔ l.SortedGE :=
  (OrderEmbedding.ofStrictMono f hf).sortedGE_listMap
/-
**StrictMono.sortedLT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：sortedLT_listMap (hf : StrictMono f) : (l.map f).SortedLT ↔ l.SortedLT
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.sortedLT_listMap`：sortedLT_listMap (e : α ↪o β) {l : List
 α} : (l.map e).SortedLT ↔ l.SortedLT
-/
theorem sortedLT_listMap (hf : StrictMono f) :
    (l.map f).SortedLT ↔ l.SortedLT :=
  (OrderEmbedding.ofStrictMono f hf).sortedLT_listMap
/-
**StrictMono.sortedGT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictMono`。
形式化陈述：sortedGT_listMap (hf : StrictMono f) : (l.map f).SortedGT ↔ l.SortedGT
参数：hf : StrictMono f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.sortedGT_listMap`：sortedGT_listMap (e : α ↪o β) {l : List
 α} : (l.map e).SortedGT ↔ l.SortedGT
-/
theorem sortedGT_listMap (hf : StrictMono f) :
    (l.map f).SortedGT ↔ l.SortedGT :=
  (OrderEmbedding.ofStrictMono f hf).sortedGT_listMap

end StrictMono

namespace StrictAnti

open List

variable {α β : Type*} [LinearOrder α] [Preorder β] {f : α → β} {l : List α}

/-
**StrictAnti.sortedLE_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：sortedLE_listMap (hf : StrictAnti f) : (l.map f).SortedLE ↔ l.SortedGE
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedLE_listMap (hf : StrictAnti f) :
    (l.map f).SortedLE ↔ l.SortedGE := by
  grind [hf.le_iff_ge]
/-
**StrictAnti.sortedGE_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：sortedGE_listMap (hf : StrictAnti f) : (l.map f).SortedGE ↔ l.SortedLE
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedGE_listMap (hf : StrictAnti f) :
    (l.map f).SortedGE ↔ l.SortedLE := by
  grind [hf.le_iff_ge]
/-
**StrictAnti.sortedLT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：sortedLT_listMap (hf : StrictAnti f) : (l.map f).SortedLT ↔ l.SortedGT
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedLT_listMap (hf : StrictAnti f) :
    (l.map f).SortedLT ↔ l.SortedGT := by
  grind [hf.lt_iff_gt]
/-
**StrictAnti.sortedGT_listMap** 是 Mathlib 中的一个定理，位于命名空间 `StrictAnti`。
形式化陈述：sortedGT_listMap (hf : StrictAnti f) : (l.map f).SortedGT ↔ l.SortedLT
参数：hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sortedGT_listMap (hf : StrictAnti f) :
    (l.map f).SortedGT ↔ l.SortedLT := by
  grind [hf.lt_iff_gt]

end StrictAnti

