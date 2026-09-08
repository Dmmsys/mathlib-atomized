/-
Copyright (c) 2024 Daniel Weber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Weber
-/
module

public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Order.MinMax

/-!
# Splitting a list to chunks of specified lengths

This file defines splitting a list to chunks of given lengths, and some proofs about that.
-/

@[expose] public section

variable {α : Type*} (l : List α) (sz : List ℕ)

namespace List

/--
Split a list to chunks of given lengths.
-/
/-
**List.splitLengths** 是 Mathlib 中的一个定义，位于命名空间 `List`。
形式化陈述：splitLengths : List Nat -> List α -> List (List α) | [], _ => [] | n::ns, 
x => let (x0, x1)
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split a list to chunks of given lengths.
-/
def splitLengths : List ℕ → List α → List (List α)
  | [], _ => []
  | n::ns, x =>
    let (x0, x1) := x.splitAt n
    x0 :: ns.splitLengths x1

@[simp]
/-
**List.length_splitLengths** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_splitLengths : (sz.splitLengths l).length = sz.length
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
-/
theorem length_splitLengths : (sz.splitLengths l).length = sz.length := by
  induction sz generalizing l <;> simp [splitLengths, *]

@[simp]
/-
**List.splitLengths_nil** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：splitLengths_nil : [].splitLengths l = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma splitLengths_nil : [].splitLengths l = [] := rfl

@[simp]
/-
**List.splitLengths_cons** 是 Mathlib 中的一个引理，位于命名空间 `List`。
形式化陈述：splitLengths_cons (n : Nat) : (n :: sz).splitLengths l = l.take n :: sz.sp
litLengths (l.drop n)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.splitAt_eq`：∀ {α : Type u_1} {i : ℕ} {l : List α}, List.splitAt i l
 = (List.take i l, List.drop i l)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma splitLengths_cons (n : ℕ) :
    (n :: sz).splitLengths l = l.take n :: sz.splitLengths (l.drop n) := by
  simp [splitLengths]
/-
**List.take_splitLength** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：take_splitLength (i : Nat) : (sz.splitLengths l).take i = (sz.take i).spli
tLengths l
参数：i : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.take_nil`：∀ {α : Type u} {i : ℕ}, List.take i [] = []
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `List.splitLengths_cons`：splitLengths_cons (n : Nat) : (n :: sz).splitLen
gths l = l.take n :: sz.splitLengths (l.drop n)
-/
theorem take_splitLength (i : ℕ) : (sz.splitLengths l).take i = (sz.take i).splitLengths l := by
  induction i generalizing sz l
  case zero => simp
  case succ i hi =>
    cases sz
    · simp
    · simp only [splitLengths_cons, take_succ_cons, hi]
/-
**List.length_splitLengths_getElem_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_splitLengths_getElem_le {i : Nat} {hi : i < (sz.splitLengths l).len
gth} : (sz.splitLengths l)[i].length <= sz[i]'(by simpa using hi)
参数：sz.splitLengths l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `List.splitLengths_cons`：splitLengths_cons (n : Nat) : (n :: sz).splitLen
gths l = l.take n :: sz.splitLengths (l.drop n)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_of_succ_lt_succ`：∀ {n m : ℕ}, n.succ < m.succ → n < m
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem length_splitLengths_getElem_le {i : ℕ} {hi : i < (sz.splitLengths l).length} :
    (sz.splitLengths l)[i].length ≤ sz[i]'(by simpa using hi) := by
  induction sz generalizing l i
  · simp at hi
  case cons head tail tail_ih =>
    simp only [splitLengths_cons]
    cases i
    · simp
    · simp only [getElem_cons_succ, tail_ih]
/-
**List.flatten_splitLengths** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：flatten_splitLengths (h : l.length <= sz.sum) : (sz.splitLengths l).flatte
n = l
参数：h : l.length <= sz.sum。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `List.splitLengths_cons`：splitLengths_cons (n : Nat) : (n :: sz).splitLen
gths l = l.take n :: sz.splitLengths (l.drop n)
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `List.take_append_drop`：∀ {α : Type u_1} (i : ℕ) (l : List α), List.take 
i l ++ List.drop i l = l
-/
theorem flatten_splitLengths (h : l.length ≤ sz.sum) : (sz.splitLengths l).flatten = l := by
  induction sz generalizing l
  · simp_all
  case cons head tail ih =>
    simp only [splitLengths_cons, flatten_cons]
    rw [ih, take_append_drop]
    simpa [add_comm] using h
/-
**List.map_splitLengths_length** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_splitLengths_length (h : sz.sum <= l.length) : (sz.splitLengths l).map
 length = sz
参数：h : sz.sum <= l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `List.splitLengths_cons`：splitLengths_cons (n : Nat) : (n :: sz).splitLen
gths l = l.take n :: sz.splitLengths (l.drop n)
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `List.length_drop`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.drop i l)
.length = l.length - i
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.le_sub_of_add_le'`：∀ {n k m : ℕ}, m + n ≤ k → n ≤ k - m
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.le_of_add_right_le`：∀ {n m k : ℕ}, n + k ≤ m → n ≤ m
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem map_splitLengths_length (h : sz.sum ≤ l.length) :
    (sz.splitLengths l).map length = sz := by
  induction sz generalizing l
  · simp
  case cons head tail ih =>
    simp only [sum_cons] at h
    simp only [splitLengths_cons, map_cons, length_take, cons.injEq, min_eq_left_iff]
    rw [ih]
    · simp [Nat.le_of_add_right_le h]
    · simp [Nat.le_sub_of_add_le' h]
/-
**List.length_splitLengths_getElem_eq** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_splitLengths_getElem_eq {i : Nat} (hi : i < sz.length) (h : (sz.tak
e (i + 1)).sum <= l.length) : ((sz.splitLengths l)[i]'(by simpa)).length = sz[i]
参数：hi : i < sz.length；h : (sz.take (i + 1)).sum <= l.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_min`：∀ {a b c : ℕ}, a < min b c ↔ a < b ∧ a < c
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_take`：∀ {α : Type u_1} {i : ℕ} {l : List α}, (List.take i l)
.length = min i l.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_take'`：∀ {α : Type u_1} {xs : List α} {i j : ℕ} (hi : i < x
s.length) (hj : i < j), xs[i] = (List.take j xs)[i]
· 使用定理 `List.take_splitLength`：take_splitLength (i : Nat) : (sz.splitLengths l).
take i = (sz.take i).splitLengths l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `List.map_splitLengths_length`：map_splitLengths_length (h : sz.sum <= l.l
ength) : (sz.splitLengths l).map length = sz
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
-/
theorem length_splitLengths_getElem_eq {i : ℕ} (hi : i < sz.length)
    (h : (sz.take (i + 1)).sum ≤ l.length) :
    ((sz.splitLengths l)[i]'(by simpa)).length = sz[i] := by
  rw [List.getElem_take' (hj := i.lt_add_one)]
  simp only [take_splitLength]
  conv_rhs =>
    rw [List.getElem_take' (hj := i.lt_add_one)]
    simp +singlePass only [← map_splitLengths_length l _ h]
    rw [getElem_map]
/-
**List.splitLengths_length_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：splitLengths_length_getElem {α : Type*} (l : List α) (sz : List Nat) (h : 
sz.sum <= l.length) (i : Nat) (hi : i < (sz.splitLengths l).length) : (sz.splitL
engths l)[i].length = sz[i]'(by simpa using hi)
参数：l : List α；sz : List Nat；h : sz.sum <= l.length；i : Nat；hi : i < (sz.splitLen
gths l).length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.map_splitLengths_length`：map_splitLengths_length (h : sz.sum <= l.l
ength) : (sz.splitLengths l).map length = sz
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `List.length_splitLengths`：length_splitLengths : (sz.splitLengths l).leng
th = sz.length
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem splitLengths_length_getElem {α : Type*} (l : List α) (sz : List ℕ)
    (h : sz.sum ≤ l.length) (i : ℕ) (hi : i < (sz.splitLengths l).length) :
    (sz.splitLengths l)[i].length = sz[i]'(by simpa using hi) := by
  have := map_splitLengths_length l sz h
  rw [← List.getElem_map List.length]
  · simp [this]
  · simpa using hi
/-
**List.length_mem_splitLengths** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：length_mem_splitLengths {α : Type*} (l : List α) (sz : List Nat) (b : Nat)
 (h : forall n in sz, n <= b) : forall l₂ in sz.splitLengths l, l₂.length <= b
参数：l : List α；sz : List Nat；b : Nat；h : forall n in sz, n <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.forall_mem_iff_forall_getElem`：∀ {α : Type u_1} {P : α → Prop} {l :
 List α}, (∀ x ∈ l, P x) ↔ ∀ (i : ℕ) (hi : i < l.length), P l[i]
· 使用定理 `List.length_splitLengths_getElem_le`：length_splitLengths_getElem_le {i :
 Nat} {hi : i < (sz.splitLengths l).length} : (sz.splitLengths l)[i].length <= s
z[i]'(by simpa using hi)
· 使用定理 `List.length_splitLengths`：length_splitLengths : (sz.splitLengths l).leng
th = sz.length
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
-/
theorem length_mem_splitLengths {α : Type*} (l : List α) (sz : List ℕ) (b : ℕ)
    (h : ∀ n ∈ sz, n ≤ b) : ∀ l₂ ∈ sz.splitLengths l, l₂.length ≤ b := by
  rw [List.forall_mem_iff_forall_getElem]
  intro i hi
  have := length_splitLengths_getElem_le l sz (hi := hi)
  have := h (sz[i]'(by simpa using hi)) (getElem_mem ..)
  lia

end List

