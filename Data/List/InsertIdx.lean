/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
module

public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Common
public import Mathlib.Util.CompileInductive

/-!
# insertIdx

Proves various lemmas about `List.insertIdx`.
-/

public section

assert_not_exists Set.range Preorder

open Function

open Nat hiding one_pos

namespace List

universe u v

variable {α : Type u} {β : Type v}

section InsertIdx

variable {a : α}

@[simp]
/-
**List.sublist_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：sublist_insertIdx (l : List α) (n : Nat) (a : α) : l <+ (l.insertIdx n a)
参数：l : List α；n : Nat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.eraseIdx_insertIdx_self`：∀ {α : Type u} {i : ℕ} {l : List α} (a : α
), (l.insertIdx i a).eraseIdx i = l
· 使用定理 `List.eraseIdx_sublist`：∀ {α : Type u_1} (l : List α) (k : ℕ), (l.eraseId
x k).Sublist l
-/
theorem sublist_insertIdx (l : List α) (n : ℕ) (a : α) : l <+ (l.insertIdx n a) := by
  simpa only [eraseIdx_insertIdx_self] using eraseIdx_sublist (l.insertIdx n a) n

@[simp]
/-
**List.subset_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：subset_insertIdx (l : List α) (n : Nat) (a : α) : l subseteq l.insertIdx n
 a
参数：l : List α；n : Nat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `List.sublist_insertIdx`：sublist_insertIdx (l : List α) (n : Nat) (a : α)
 : l <+ (l.insertIdx n a)
-/
theorem subset_insertIdx (l : List α) (n : ℕ) (a : α) : l ⊆ l.insertIdx n a :=
  (sublist_insertIdx ..).subset

/-- Erasing `n`th element of a list, then inserting `a` at the same place
is the same as setting `n`th element to `a`.

We assume that `n ≠ length l`, because otherwise LHS equals `l ++ [a]` while RHS equals `l`. -/
@[simp]
/-
**List.insertIdx_eraseIdx_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertIdx_eraseIdx_self {l : List α} {n : Nat} (hn : n != length l) (a : α
) : (l.eraseIdx n).insertIdx n a = l.set n a
参数：hn : n != length l；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.eraseIdx_zero`：∀ {α : Type u_1} {l : List α}, l.eraseIdx 0 = l.tail
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Erasing `n`th element of a list, then inserting `a` at the same place
is the same as setting `n`th element to `a`.

We assume that `n ≠ length l`, because otherwise LHS equals `l ++ [a]` while RHS
 equals `l`.
-/
theorem insertIdx_eraseIdx_self {l : List α} {n : ℕ} (hn : n ≠ length l) (a : α) :
    (l.eraseIdx n).insertIdx n a = l.set n a := by
  induction n generalizing l <;> cases l <;> simp_all
/-
**List.insertIdx_eraseIdx_getElem** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertIdx_eraseIdx_getElem {l : List α} {n : Nat} (hn : n < length l) : (l
.eraseIdx n).insertIdx n l[n] = l
参数：hn : n < length l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insertIdx_eraseIdx_self`：insertIdx_eraseIdx_self {l : List α} {n : 
Nat} (hn : n != length l) (a : α) : (l.eraseIdx n).insertIdx n a = l.set n a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.ne_of_lt`：∀ {a b : ℕ}, a < b → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.set_getElem_self`：∀ {α : Type u_1} {as : List α} {i : ℕ} (h : i < a
s.length), as.set i as[i] = as
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem insertIdx_eraseIdx_getElem {l : List α} {n : ℕ} (hn : n < length l) :
    (l.eraseIdx n).insertIdx n l[n] = l := by
  simp [Nat.ne_of_lt hn]
/-
**List.eq_or_mem_of_mem_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：eq_or_mem_of_mem_insertIdx {l : List α} {n : Nat} {a b : α} (h : a in l.in
sertIdx n b) : a = b ∨ a in l
参数：h : a in l.insertIdx n b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.lt_or_ge`：∀ (n m : ℕ), n < m ∨ n ≥ m
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.insertIdx_of_length_lt`：∀ {α : Type u} {l : List α} {x : α} {i : ℕ}
, l.length < i → l.insertIdx i x = l
· 使用定理 `List.mem_insertIdx`：∀ {α : Type u} {a b : α} {i : ℕ} {l : List α}, i ≤ l
.length → (a ∈ l.insertIdx i b ↔ a = b ∨ a ∈ l)
-/
theorem eq_or_mem_of_mem_insertIdx {l : List α} {n : ℕ} {a b : α} (h : a ∈ l.insertIdx n b) :
    a = b ∨ a ∈ l := by
  cases Nat.lt_or_ge (length l) n with
  | inl hn =>
    rw [insertIdx_of_length_lt hn] at h
    exact .inr h
  | inr hn =>
    rwa [mem_insertIdx hn] at h
/-
**List.insertIdx_subset_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertIdx_subset_cons (n : Nat) (a : α) (l : List α) : l.insertIdx n a sub
seteq a :: l
参数：n : Nat；a : α；l : List α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eq_or_mem_of_mem_insertIdx`：eq_or_mem_of_mem_insertIdx {l : List α}
 {n : Nat} {a b : α} (h : a in l.insertIdx n b) : a = b ∨ a in l
-/
theorem insertIdx_subset_cons (n : ℕ) (a : α) (l : List α) : l.insertIdx n a ⊆ a :: l := by
  intro b hb
  simpa using eq_or_mem_of_mem_insertIdx hb
/-
**List.insertIdx_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertIdx_pmap {p : α -> Prop} (f : forall a, p a -> β) {l : List α} {a : 
α} {n : Nat} (hl : forall x in l, p x) (ha : p a) : (l.pmap f hl).insertIdx n (f
 a ha) = (l.insertIdx n a).pmap f (fun _ h => (eq_or_mem_of_mem_insertIdx h).eli
m (fun heq => heq ▸ ha) (hl _))
参数：f : forall a, p a -> β；hl : forall x in l, p x；ha : p a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `List.eq_or_mem_of_mem_insertIdx`：eq_or_mem_of_mem_insertIdx {l : List α}
 {n : Nat} {a b : α} (h : a in l.insertIdx n b) : a = b ∨ a in l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.forall_mem_cons`：∀ {α : Type u_1} {p : α → Prop} {a : α} {l : List 
α}, (∀ x ∈ a :: l, p x) ↔ p a ∧ ∀ x ∈ l, p x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem insertIdx_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} {a : α} {n : ℕ}
    (hl : ∀ x ∈ l, p x) (ha : p a) :
    (l.pmap f hl).insertIdx n (f a ha) = (l.insertIdx n a).pmap f
      (fun _ h ↦ (eq_or_mem_of_mem_insertIdx h).elim (fun heq ↦ heq ▸ ha) (hl _)) := by
  induction n generalizing l with
  | zero => cases l <;> simp
  | succ n ihn => cases l <;> simp_all
/-
**List.map_insertIdx** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：map_insertIdx (f : α -> β) (l : List α) (n : Nat) (a : α) : (l.insertIdx n
 a).map f = (l.map f).insertIdx n (f a)
参数：f : α -> β；l : List α；n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `List.eq_or_mem_of_mem_insertIdx`：eq_or_mem_of_mem_insertIdx {l : List α}
 {n : Nat} {a b : α} (h : a in l.insertIdx n b) : a = b ∨ a in l
· 使用定理 `trivial`：True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.pmap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : α 
→ β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap (fun a x => f a) l H = List.ma
p f l
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.insertIdx_pmap`：insertIdx_pmap {p : α -> Prop} (f : forall a, p a -
> β) {l : List α} {a : α} {n : Nat} (hl : forall x in l, p x) (ha : p a) : (l.pm
ap f hl).…
-/
theorem map_insertIdx (f : α → β) (l : List α) (n : ℕ) (a : α) :
    (l.insertIdx n a).map f = (l.map f).insertIdx n (f a) := by
  simpa only [pmap_eq_map] using (insertIdx_pmap (fun a _ ↦ f a) (fun _ _ ↦ trivial) trivial).symm
/-
**List.eraseIdx_pmap** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：eraseIdx_pmap {p : α -> Prop} (f : forall a, p a -> β) {l : List α} (hl : 
forall a in l, p a) (n : Nat) : (pmap f l hl).eraseIdx n = (l.eraseIdx n).pmap f
 fun a ha => hl a (eraseIdx_subset ha)
参数：f : forall a, p a -> β；hl : forall a in l, p a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.eraseIdx_subset`：∀ {α : Type u_1} {l : List α} {k : ℕ}, l.eraseIdx 
k ⊆ l
-/
theorem eraseIdx_pmap {p : α → Prop} (f : ∀ a, p a → β) {l : List α} (hl : ∀ a ∈ l, p a) (n : ℕ) :
    (pmap f l hl).eraseIdx n = (l.eraseIdx n).pmap f fun a ha ↦ hl a (eraseIdx_subset ha) :=
  match l, hl, n with
  | [], _, _ => rfl
  | a :: _, _, 0 => rfl
  | a :: as, h, n + 1 => by rw [forall_mem_cons] at h; simp [eraseIdx_pmap f h.2 n]

/-- Erasing an index commutes with `List.map`. -/
/-
**List.eraseIdx_map** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：eraseIdx_map (f : α -> β) (l : List α) (n : Nat) : (map f l).eraseIdx n = 
(l.eraseIdx n).map f
参数：f : α -> β；l : List α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `List.pmap_eq_map`：∀ {α : Type u_1} {β : Type u_2} {p : α → Prop} {f : α 
→ β} {l : List α} (H : ∀ a ∈ l, p a),   List.pmap (fun a x => f a) l H = List.ma
p f l
· 使用定理 `List.eraseIdx_pmap`：eraseIdx_pmap {p : α -> Prop} (f : forall a, p a -> 
β) {l : List α} (hl : forall a in l, p a) (n : Nat) : (pmap f l hl).eraseIdx n =
 (l.eras…

--- 原说明 ---
Erasing an index commutes with `List.map`.
-/
theorem eraseIdx_map (f : α → β) (l : List α) (n : ℕ) :
    (map f l).eraseIdx n = (l.eraseIdx n).map f := by
  simpa only [pmap_eq_map] using eraseIdx_pmap (fun a _ ↦ f a) (fun _ _ ↦ trivial) n
/-
**List.get_insertIdx_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_insertIdx_of_lt (l : List α) (x : α) (n k : Nat) (hn : k < n) (hk : k 
< l.length) (hk' : k < (l.insertIdx n x).length
参数：l : List α；x : α；n k : Nat；hn : k < n；hk : k < l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_insertIdx_of_lt`：∀ {α : Type u} {l : List α} {x : α} {i j :
 ℕ} (hn : j < i) (hk : j < (l.insertIdx i x).length),   (l.insertIdx i x)[j] = l
[j]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_insertIdx_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (l.insertIdx n x).length := by grind) :
    (l.insertIdx n x).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  simp_all [getElem_insertIdx_of_lt]
/-
**List.get_insertIdx_self** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_insertIdx_self (l : List α) (x : α) (n : Nat) (hn : n <= l.length) (hn
' : n < (l.insertIdx n x).length
参数：l : List α；x : α；n : Nat；hn : n <= l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_insertIdx_self`：∀ {α : Type u} {l : List α} {x : α} {i : ℕ}
 (hi : i < (l.insertIdx i x).length), (l.insertIdx i x)[i] = x
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_insertIdx_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (l.insertIdx n x).length :=
      (by rwa [length_insertIdx_of_le_length hn, Nat.lt_succ_iff])) :
    (l.insertIdx n x).get ⟨n, hn'⟩ = x := by
  simp
/-
**List.getElem_insertIdx_add_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：getElem_insertIdx_add_succ (l : List α) (x : α) (n k : Nat) (hk' : n + k <
 l.length) (hk : n + k + 1 < (l.insertIdx n x).length
参数：l : List α；x : α；n k : Nat；hk' : n + k < l.length。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getElem_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (l.insertIdx n x).length := (by
      rwa [length_insertIdx_of_le_length (by lia), Nat.succ_lt_succ_iff])) :
    (l.insertIdx n x)[n + k + 1] = l[n + k] := by
  grind
/-
**List.get_insertIdx_add_succ** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：get_insertIdx_add_succ (l : List α) (x : α) (n k : Nat) (hk' : n + k < l.l
ength) (hk : n + k + 1 < (l.insertIdx n x).length
参数：l : List α；x : α；n k : Nat；hk' : n + k < l.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_insertIdx_add_succ`：getElem_insertIdx_add_succ (l : List α)
 (x : α) (n k : Nat) (hk' : n + k < l.length) (hk : n + k + 1 < (l.insertIdx n x
).length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem get_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (l.insertIdx n x).length := (by
      rwa [length_insertIdx_of_le_length (by lia), Nat.succ_lt_succ_iff])) :
    (l.insertIdx n x).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  simp [getElem_insertIdx_add_succ, hk']
/-
**List.insertIdx_injective** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：insertIdx_injective (n : Nat) (x : α) : Function.Injective (fun l : List α
 => l.insertIdx n x)
参数：n : Nat；x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.eraseIdx_insertIdx_self`：∀ {α : Type u} {i : ℕ} {l : List α} (a : α
), (l.insertIdx i a).eraseIdx i = l
-/
theorem insertIdx_injective (n : ℕ) (x : α) :
    Function.Injective (fun l : List α => l.insertIdx n x) := by
  intro l₁ l₂ hl
  simpa using congr($hl |>.eraseIdx n)
/-
**List.take_insertIdx_eq_take_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：take_insertIdx_eq_take_of_le (l : List α) x i j (h : i <= j) : (l.insertId
x j x).take i = l.take i
参数：l : List α；h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
-/
theorem take_insertIdx_eq_take_of_le (l : List α) x i j (h : i ≤ j) :
    (l.insertIdx j x).take i = l.take i :=
  ext_getElem (by grind) (by grind)
/-
**List.take_eraseIdx_eq_take_of_le** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：take_eraseIdx_eq_take_of_le (l : List α) i j (h : i <= j) : (l.eraseIdx j)
.take i = l.take i
参数：l : List α；h : i <= j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.ext_getElem`：ext_getElem?' {l₁ l₂ : List α} (h' : forall n < max l₁
.length l₂.length, l₁[n]? = l₂[n]?) : l₁ = l₂
-/
theorem take_eraseIdx_eq_take_of_le (l : List α) i j (h : i ≤ j) :
    (l.eraseIdx j).take i = l.take i :=
  ext_getElem (by grind) (by grind)

end InsertIdx

end List

