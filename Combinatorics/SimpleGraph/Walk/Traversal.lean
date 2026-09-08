/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Daniel Weber
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# Traversing walks

Functions that help access different parts of a walk.

## Main definitions

* `SimpleGraph.Walk.getVert`:
  Get the nth vertex encountered in a walk, or the last one if `n` is too large
* `SimpleGraph.Walk.snd`: The second vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.penultimate`:
  The penultimate vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.firstDart`: The first dart of a non-empty walk
* `SimpleGraph.Walk.lastDart`: The last dart of a non-empty walk

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
/-
**SimpleGraph.Walk.getVert** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → ℕ → V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint
.
-/
def getVert {u v : V} : G.Walk u v → ℕ → V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n

@[simp]
/-
**SimpleGraph.Walk.getVert_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u
参数：w : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by cases w <;> rfl

@[simp]
/-
**SimpleGraph.Walk.getVert_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_nil (u : V) {i : Nat} : (@nil _ G u).getVert i = u
参数：u : V。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getVert_nil (u : V) {i : ℕ} : (@nil _ G u).getVert i = u := rfl
/-
**SimpleGraph.Walk.getVert_of_length_le** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：getVert_of_length_le {u v} (w : G.Walk u v) {i : Nat} (hi : w.length <= i)
 : w.getVert i = v
参数：w : G.Walk u v；hi : w.length <= i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_le_succ_iff`：∀ {a b : ℕ}, a.succ ≤ b.succ ↔ a ≤ b
-/
theorem getVert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) :
    w.getVert i = v := by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]
/-
**SimpleGraph.Walk.getVert_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v
参数：w : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.getVert_of_length_le`：getVert_of_length_le {u v} (w : G
.Walk u v) {i : Nat} (hi : w.length <= i) : w.getVert i = v
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
-/
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_length_le rfl.le
/-
**SimpleGraph.Walk.adj_getVert_succ** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：adj_getVert_succ {u v} (w : G.Walk u v) {i : Nat} (hi : i < w.length) : G.
Adj (w.getVert i) (w.getVert (i + 1))
参数：w : G.Walk u v；hi : i < w.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.succ_lt_succ_iff`：∀ {a b : ℕ}, a.succ < b.succ ↔ a < b
-/
theorem adj_getVert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)

@[simp]
/-
**SimpleGraph.Walk.getVert_cons_succ** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) : (p.cons h).
getVert (n + 1) = p.getVert n
参数：p : G.Walk v w；h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) :
    (p.cons h).getVert (n + 1) = p.getVert n := rfl
/-
**SimpleGraph.Walk.getVert_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getVert_cons {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n != 0) : (p
.cons h).getVert n = p.getVert (n - 1)
参数：p : G.Walk v w；h : G.Adj u v；hn : n != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.exists_eq_add_one_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.getVert_cons_succ`：getVert_cons_succ {u v w n} (p : G.W
alk v w) (h : G.Adj u v) : (p.cons h).getVert (n + 1) = p.getVert n
· 使用定理 `Nat.add_sub_cancel`：∀ (n m : ℕ), n + m - m = n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma getVert_cons {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n ≠ 0) :
    (p.cons h).getVert n = p.getVert (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [getVert_cons_succ, Nat.add_sub_cancel]

@[simp]
/-
**SimpleGraph.Walk.getVert_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：getVert_mem_support {u v : V} (p : G.Walk u v) (i : Nat) : p.getVert i in 
p.support
参数：p : G.Walk u v；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem getVert_mem_support {u v : V} (p : G.Walk u v) (i : ℕ) : p.getVert i ∈ p.support := by
  induction p generalizing i <;> cases i <;> simp [*]

/-- Use `support_getElem_eq_getVert` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.getVert_eq_support_getElem** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：getVert_eq_support_getElem {u v : V} {n : Nat} (p : G.Walk u v) (h : n <= 
p.length) : p.getVert n = p.support[n]'(p.length_support ▸ Nat.lt_add_one_of_le 
h)
参数：p : G.Walk u v；h : n <= p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.getVert_eq_support_getElem._unary`：∀ {V : Type u} {G : 
SimpleGraph V} {v : V} (_x : (u : V) ×' (n : ℕ) ×' (p : G.Walk u v) ×' n ≤ p.len
gth),   _x.2.2.1.getVert _x.2.1 = _x.2.2…

--- 原说明 ---
Use `support_getElem_eq_getVert` to rewrite in the reverse direction.
-/
lemma getVert_eq_support_getElem {u v : V} {n : ℕ} (p : G.Walk u v) (h : n ≤ p.length) :
    p.getVert n = p.support[n]'(p.length_support ▸ Nat.lt_add_one_of_le h) := by
  cases p with
  | nil => simp
  | cons => cases n with
    | zero => simp
    | succ n =>
      simp_rw [support_cons, getVert_cons _ _ n.zero_ne_add_one.symm, List.getElem_cons]
      exact getVert_eq_support_getElem _ (Nat.sub_le_of_le_add h)

/-- Use `getVert_eq_support_getElem` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.support_getElem_eq_getVert** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：support_getElem_eq_getVert {u v : V} {n : Nat} (p : G.Walk u v) (h) : p.su
pport[n]'h = p.getVert n
参数：p : G.Walk u v；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.lt_add_one_of_le`：∀ {n m : ℕ}, n ≤ m → n < m + 1
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用引理 `SimpleGraph.Walk.getVert_eq_support_getElem`：getVert_eq_support_getElem 
{u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length) : p.getVert n = p.suppo
rt[n]'(p.length_support ▸ Nat.lt_…

--- 原说明 ---
Use `getVert_eq_support_getElem` to rewrite in the reverse direction.
-/
lemma support_getElem_eq_getVert {u v : V} {n : ℕ} (p : G.Walk u v) (h) :
    p.support[n]'h = p.getVert n :=
  (p.getVert_eq_support_getElem <| by grind).symm
/-
**SimpleGraph.Walk.getVert_eq_support_getElem** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：getVert_eq_support_getElem {u v : V} {n : Nat} (p : G.Walk u v) (h : n <= 
p.length) : p.getVert n = p.support[n]'(p.length_support ▸ Nat.lt_add_one_of_le 
h)
参数：p : G.Walk u v；h : n <= p.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.getVert_eq_support_getElem._unary`：∀ {V : Type u} {G : 
SimpleGraph V} {v : V} (_x : (u : V) ×' (n : ℕ) ×' (p : G.Walk u v) ×' n ≤ p.len
gth),   _x.2.2.1.getVert _x.2.1 = _x.2.2…
-/
lemma getVert_eq_support_getElem? {u v : V} {n : ℕ} (p : G.Walk u v) (h : n ≤ p.length) :
    some (p.getVert n) = p.support[n]? := by
  rw [getVert_eq_support_getElem p h, ← List.getElem?_eq_getElem]
/-
**SimpleGraph.Walk.getVert_eq_getD_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：getVert_eq_getD_support {u v : V} (p : G.Walk u v) (n : Nat) : p.getVert n
 = p.support.getD n v
参数：p : G.Walk u v；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getD_eq_getElem?_getD`：∀ {α : Type u_1} {l : List α} {i : ℕ} {a : α
}, l.getD i a = l[i]?.getD a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_eq_support_getElem?`：∀ {V : Type u} {G : Simple
Graph V} {u v : V} {n : ℕ} (p : G.Walk u v), n ≤ p.length → some (p.getVert n) =
 p.support[n]?
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma getVert_eq_getD_support {u v : V} (p : G.Walk u v) (n : ℕ) :
    p.getVert n = p.support.getD n v := by
  by_cases h : n ≤ p.length
  · simp [← getVert_eq_support_getElem? p h]
  grind [getVert_of_length_le, length_support]

@[simp]
/-
**SimpleGraph.Walk.getVert_support_idxOf** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：getVert_support_idxOf [DecidableEq V] (p : G.Walk u v) (h : w in p.support
) : p.getVert (p.support.idxOf w) = w
参数：p : G.Walk u v；h : w in p.support。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma getVert_support_idxOf [DecidableEq V] (p : G.Walk u v) (h : w ∈ p.support) :
    p.getVert (p.support.idxOf w) = w := by
  grind [getVert_eq_support_getElem]
/-
**SimpleGraph.Walk.getVert_comp_val_eq_get_support** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Walk`。
形式化陈述：getVert_comp_val_eq_get_support {u v : V} (p : G.Walk u v) : p.getVert ∘ F
in.val = p.support.get
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getVert_comp_val_eq_get_support {u v : V} (p : G.Walk u v) :
    p.getVert ∘ Fin.val = p.support.get := by
  grind [getVert_eq_support_getElem, length_support]
/-
**SimpleGraph.Walk.range_getVert_eq_range_support_getElem** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Walk`。
形式化陈述：range_getVert_eq_range_support_getElem {u v : V} (p : G.Walk u v) : Set.ra
nge p.getVert = Set.range p.support.get
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem range_getVert_eq_range_support_getElem {u v : V} (p : G.Walk u v) :
    Set.range p.getVert = Set.range p.support.get :=
  Set.ext fun _ ↦ ⟨by grind [Set.range_list_get, getVert_mem_support],
    fun ⟨n, _⟩ ↦ ⟨n, by grind [getVert_eq_support_getElem, length_support]⟩⟩
/-
**SimpleGraph.Walk.darts_getElem_eq_getVert** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：darts_getElem_eq_getVert {u v : V} {p : G.Walk u v} (n : Nat) (h : n < p.d
arts.length) : p.darts[n] = ⟨⟨p.getVert n, p.getVert (n + 1)⟩, p.adj_getVert_suc
c (p.length_darts ▸ h)⟩
参数：n : Nat；h : n < p.darts.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Dart.ext`：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Da
rt), d₁.toProd = d₂.toProd → d₁ = d₂
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.lt_of_lt_of_le`：∀ {n m k : ℕ}, n < m → m ≤ k → n < k
· 使用定理 `Nat.pred_le`：∀ (n : ℕ), n.pred ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_dropLast`：∀ {α : Type u_1} {xs : List α}, xs.dropLast.length
 = xs.length - 1
· 使用定理 `Nat.lt_add_one_of_le`：∀ {n m : ℕ}, n ≤ m → n < m + 1
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.fst_darts_getElem`：fst_darts_getElem {p : G.Walk u v} {
i : Nat} (hi : i < p.darts.length) : p.darts[i].fst = p.support.dropLast[i]'(by 
grind)
· 使用定理 `List.getElem_dropLast`：∀ {α : Type u_1} {xs : List α} {i : ℕ} (h : i < x
s.dropLast.length), xs.dropLast[i] = xs[i]
· 使用引理 `SimpleGraph.Walk.getVert_eq_support_getElem`：getVert_eq_support_getElem 
{u v : V} {n : Nat} (p : G.Walk u v) (h : n <= p.length) : p.getVert n = p.suppo
rt[n]'(p.length_support ▸ Nat.lt_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Nat.add_lt_of_lt_sub`：∀ {a b c : ℕ}, a < c - b → a + b < c
· 使用定理 `SimpleGraph.Walk.snd_darts_getElem`：snd_darts_getElem {p : G.Walk u v} {
i : Nat} (hi : i < p.darts.length) : p.darts[i].snd = p.support.tail[i]'(by grin
d)
· 使用定理 `List.getElem_tail`：∀ {α : Type u_1} {l : List α} {i : ℕ} (h : i < l.tail
.length), l.tail[i] = l[i + 1]
-/
theorem darts_getElem_eq_getVert {u v : V} {p : G.Walk u v} (n : ℕ) (h : n < p.darts.length) :
    p.darts[n] = ⟨⟨p.getVert n, p.getVert (n + 1)⟩, p.adj_getVert_succ (p.length_darts ▸ h)⟩ := by
  rw [p.length_darts] at h
  ext <;> simp [p.getVert_eq_support_getElem (le_of_lt h), p.getVert_eq_support_getElem h]
/-
**SimpleGraph.Walk.getElem_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getElem_edges {p : G.Walk u v} {i : Nat} (h : i < p.edges.length) : p.edge
s[i] = s(p.getVert i, p.getVert (i + 1))
参数：h : i < p.edges.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `SimpleGraph.Walk.getElem_edges_eq_edge_getElem_darts`：getElem_edges_eq_e
dge_getElem_darts {p : G.Walk u v} {i : Nat} (h : i < p.edges.length) : p.edges[
i] = (p.darts[i]'(by grind)).edge
· 使用定理 `SimpleGraph.Walk.darts_getElem_eq_getVert`：darts_getElem_eq_getVert {u v
 : V} {p : G.Walk u v} (n : Nat) (h : n < p.darts.length) : p.darts[n] = ⟨⟨p.get
Vert n, p.getVert (n + 1)⟩, p.a…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem getElem_edges {p : G.Walk u v} {i : ℕ} (h : i < p.edges.length) :
    p.edges[i] = s(p.getVert i, p.getVert (i + 1)) := by
  simp [getElem_edges_eq_edge_getElem_darts, darts_getElem_eq_getVert]
/-
**SimpleGraph.Walk.mk_mem_edges_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：mk_mem_edges_iff_exists {u' v' : V} (p : G.Walk u v) : s(u', v') in p.edge
s ↔ exists i < p.length, s(p.getVert i, p.getVert (i + 1)) = s(u', v')
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_mem_edges_iff_exists {u' v' : V} (p : G.Walk u v) :
    s(u', v') ∈ p.edges ↔ ∃ i < p.length, s(p.getVert i, p.getVert (i + 1)) = s(u', v') := by
  constructor <;> grind [getElem_edges, List.mem_iff_getElem]
/-
**SimpleGraph.Walk.adj_of_infix_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：adj_of_infix_support {u v u' v'} {p : G.Walk u v} (h : [u', v'] <:+: p.sup
port) : G.Adj u' v'
参数：h : [u', v'] <:+: p.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.infix_iff_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁ <:+: l₂
 ↔ ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ (i : ℕ) (h : i < l₁.length), l₂[i + k]? = 
some l₁[i]
· 使用定理 `Nat.zero_lt_two`：0 < 2
· 使用定理 `Nat.zero_add`：∀ (n : ℕ), 0 + n = n
· 使用定理 `Nat.one_lt_two`：1 < 2
· 使用定理 `Nat.add_comm`：∀ (n m : ℕ), n + m = m + n
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Option.some.injEq`：∀ {α : Type u} (val val_1 : α), (some val = some val_
1) = (val = val_1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_eq_support_getElem?`：∀ {V : Type u} {G : Simple
Graph V} {u v : V} {n : ℕ} (p : G.Walk u v), n ≤ p.length → some (p.getVert n) =
 p.support[n]?
-/
theorem adj_of_infix_support {u v u' v'} {p : G.Walk u v} (h : [u', v'] <:+: p.support) :
    G.Adj u' v' := by
  have ⟨k, hk, h⟩ := List.infix_iff_getElem?.mp h
  have h₀ := Nat.zero_add _ ▸ h 0 Nat.zero_lt_two
  have h₁ := Nat.add_comm .. ▸ h 1 Nat.one_lt_two
  rw [← getVert_eq_support_getElem? _ <| by grind, Option.some.injEq] at h₀ h₁
  exact h₀ ▸ h₁ ▸ p.adj_getVert_succ (i := k) <| by grind

/-- The second vertex of a walk, or the only vertex in a nil walk. -/
/-
**SimpleGraph.Walk.snd** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：snd (p : G.Walk u v) : V
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The second vertex of a walk, or the only vertex in a nil walk.
-/
abbrev snd (p : G.Walk u v) : V := p.getVert 1
/-
**SimpleGraph.Walk.adj_snd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p : G.Walk v w}, ¬p.Nil → G.
Adj v p.snd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
-/
@[simp] lemma adj_snd {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v p.snd := by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)
/-
**SimpleGraph.Walk.snd_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：snd_cons {u v w} (q : G.Walk v w) (hadj : G.Adj u v) : (q.cons hadj).snd =
 v
参数：q : G.Walk v w；hadj : G.Adj u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma snd_cons {u v w} (q : G.Walk v w) (hadj : G.Adj u v) :
    (q.cons hadj).snd = v := by simp
/-
**SimpleGraph.Walk.snd_mem_tail_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：snd_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬p.Nil) : p.snd in p.
support.tail
参数：h : ¬p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma snd_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬p.Nil) : p.snd ∈ p.support.tail :=
  p.notNilRec (by simp) h

/-- Use `snd_eq_support_getElem_one` to rewrite in the reverse direction. -/
@[simp]
/-
**SimpleGraph.Walk.support_getElem_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：support_getElem_one {p : G.Walk u v} (hp) : p.support[1]'hp = p.snd
参数：hp。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `snd_eq_support_getElem_one` to rewrite in the reverse direction.
-/
lemma support_getElem_one {p : G.Walk u v} (hp) : p.support[1]'hp = p.snd := by
  grind [getVert_eq_support_getElem]

/-- Use `support_getElem_one` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.snd_eq_support_getElem_one** 是 Mathlib 中的一个引理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：snd_eq_support_getElem_one {p : G.Walk u v} (hnil : ¬p.Nil) : p.snd = p.su
pport[1]'(by grind [not_nil_iff_lt_length])
参数：hnil : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.support_getElem_one`：support_getElem_one {p : G.Walk u 
v} (hp) : p.support[1]'hp = p.snd

--- 原说明 ---
Use `support_getElem_one` to rewrite in the reverse direction.
-/
lemma snd_eq_support_getElem_one {p : G.Walk u v} (hnil : ¬p.Nil) :
    p.snd = p.support[1]'(by grind [not_nil_iff_lt_length]) :=
  support_getElem_one _ |>.symm

/-- The penultimate vertex of a walk, or the only vertex in a nil walk. -/
/-
**SimpleGraph.Walk.penultimate** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：penultimate (p : G.Walk u v) : V
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The penultimate vertex of a walk, or the only vertex in a nil walk.
-/
abbrev penultimate (p : G.Walk u v) : V := p.getVert (p.length - 1)

@[simp]
/-
**SimpleGraph.Walk.penultimate_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：penultimate_nil : (@nil _ G v).penultimate = v
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma penultimate_nil : (@nil _ G v).penultimate = v := rfl

@[simp]
/-
**SimpleGraph.Walk.penultimate_cons_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：penultimate_cons_nil (h : G.Adj u v) : (cons h nil).penultimate = u
参数：h : G.Adj u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma penultimate_cons_nil (h : G.Adj u v) : (cons h nil).penultimate = u := rfl

@[simp]
/-
**SimpleGraph.Walk.penultimate_cons_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：penultimate_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w 
w') : (cons h (cons h₂ p)).penultimate = (cons h₂ p).penultimate
参数：h : G.Adj u v；h₂ : G.Adj v w；p : G.Walk w w'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma penultimate_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).penultimate = (cons h₂ p).penultimate := rfl
/-
**SimpleGraph.Walk.penultimate_cons_of_not_nil** 是 Mathlib 中的一个引理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：penultimate_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil
) : (cons h p).penultimate = p.penultimate
参数：h : G.Adj u v；p : G.Walk v w；hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma penultimate_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).penultimate = p.penultimate :=
  p.notNilRec (by simp) hp h

@[simp]
/-
**SimpleGraph.Walk.adj_penultimate** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：adj_penultimate {p : G.Walk v w} (hp : ¬ p.Nil) : G.Adj p.penultimate w
参数：hp : ¬ p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma adj_penultimate {p : G.Walk v w} (hp : ¬ p.Nil) : G.Adj p.penultimate w := by
  grind [getVert_length, adj_getVert_succ]
/-
**SimpleGraph.Walk.penultimate_mem_dropLast_support** 是 Mathlib 中的一个引理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：penultimate_mem_dropLast_support {p : G.Walk u v} (h : ¬p.Nil) : p.penulti
mate in p.support.dropLast
参数：h : ¬p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w
-/
lemma penultimate_mem_dropLast_support {p : G.Walk u v} (h : ¬p.Nil) :
    p.penultimate ∈ p.support.dropLast := by
  have := adj_penultimate h |>.ne
  grind [getVert_mem_support, List.dropLast_concat_getLast, getLast_support]

@[simp]
/-
**SimpleGraph.Walk.support_getElem_length_sub_one_eq_penultimate** 是 Mathlib 中的一
个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_getElem_length_sub_one_eq_penultimate {p : G.Walk u v} : p.support
[p.length - 1] = p.penultimate
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma support_getElem_length_sub_one_eq_penultimate {p : G.Walk u v} :
    p.support[p.length - 1] = p.penultimate := by
  grind [getVert_eq_support_getElem]

/-- The first dart of a walk. -/
@[simps]
/-
**SimpleGraph.Walk.firstDart** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where fst
参数：p : G.Walk v w；hp : ¬ p.Nil。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd

--- 原说明 ---
The first dart of a walk.
-/
def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := v
  snd := p.snd
  adj := p.adj_snd hp

/-- The last dart of a walk. -/
@[simps]
/-
**SimpleGraph.Walk.lastDart** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：lastDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where fst
参数：p : G.Walk v w；hp : ¬ p.Nil。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.adj_penultimate`：adj_penultimate {p : G.Walk v w} (hp :
 ¬ p.Nil) : G.Adj p.penultimate w

--- 原说明 ---
The last dart of a walk.
-/
def lastDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := p.penultimate
  snd := w
  adj := p.adj_penultimate hp
/-
**SimpleGraph.Walk.edge_firstDart** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : (p.firstDart hp).edge = s
(v, p.snd)
参数：p : G.Walk v w；hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.firstDart hp).edge = s(v, p.snd) := rfl
/-
**SimpleGraph.Walk.edge_lastDart** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edge_lastDart (p : G.Walk v w) (hp : ¬ p.Nil) : (p.lastDart hp).edge = s(p
.penultimate, w)
参数：p : G.Walk v w；hp : ¬ p.Nil。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma edge_lastDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.lastDart hp).edge = s(p.penultimate, w) := rfl
/-
**SimpleGraph.Walk.firstDart_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：firstDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) : p
.firstDart h₁ = p.darts[0]
参数：h₁ : ¬ p.Nil；h₂ : 0 < p.darts.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `SimpleGraph.Walk.darts_getElem_eq_getVert`：darts_getElem_eq_getVert {u v
 : V} {p : G.Walk u v} (n : Nat) (h : n < p.darts.length) : p.darts[n] = ⟨⟨p.get
Vert n, p.getVert (n + 1)⟩, p.a…
· 使用定理 `SimpleGraph.Dart.mk.congr_simp`：∀ {V : Type u_1} {G : SimpleGraph V} (to
Prod toProd_1 : V × V) (e_toProd : toProd = toProd_1)   (adj : G.Adj toProd.1 to
Prod.2), { toProd :=…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.firstDart_toProd`：∀ {V : Type u} {G : SimpleGraph V} {v
 w : V} (p : G.Walk v w) (hp : ¬p.Nil), (p.firstDart hp).toProd = (v, p.snd)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem firstDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) :
    p.firstDart h₁ = p.darts[0] := by
  simp [Dart.ext_iff, firstDart_toProd, darts_getElem_eq_getVert]
/-
**SimpleGraph.Walk.lastDart_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：lastDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) : p.
lastDart h₁ = p.darts[p.darts.length - 1]
参数：h₁ : ¬ p.Nil；h₂ : 0 < p.darts.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.adj_getVert_succ`：adj_getVert_succ {u v} (w : G.Walk u 
v) {i : Nat} (hi : i < w.length) : G.Adj (w.getVert i) (w.getVert (i + 1))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `SimpleGraph.Walk.getVert_of_length_le`：getVert_of_length_le {u v} (w : G
.Walk u v) {i : Nat} (hi : w.length <= i) : w.getVert i = v
· 使用定理 `GetElem.getElem.congr_simp`：∀ {coll : Type u} {idx : Type v} {elem : Typ
e w} {valid : coll → idx → Prop} [self : GetElem coll idx elem valid]   (xs xs_1
 : coll) (e_xs :…
· 使用定理 `SimpleGraph.Walk.darts_getElem_eq_getVert`：darts_getElem_eq_getVert {u v
 : V} {p : G.Walk u v} (n : Nat) (h : n < p.darts.length) : p.darts[n] = ⟨⟨p.get
Vert n, p.getVert (n + 1)⟩, p.a…
· 使用定理 `SimpleGraph.Dart.mk.congr_simp`：∀ {V : Type u_1} {G : SimpleGraph V} (to
Prod toProd_1 : V × V) (e_toProd : toProd = toProd_1)   (adj : G.Adj toProd.1 to
Prod.2), { toProd :=…
· 使用定理 `SimpleGraph.Walk.lastDart_toProd`：∀ {V : Type u} {G : SimpleGraph V} {v 
w : V} (p : G.Walk v w) (hp : ¬p.Nil), (p.lastDart hp).toProd = (p.penultimate, 
w)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lastDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) :
    p.lastDart h₁ = p.darts[p.darts.length - 1] := by
  simp (disch := grind) [Dart.ext_iff, lastDart_toProd, darts_getElem_eq_getVert,
    p.getVert_of_length_le]

/-- Use `firstDart_eq_head_darts` to rewrite in the reverse direction. -/
@[simp]
/-
**SimpleGraph.Walk.head_darts_eq_firstDart** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：head_darts_eq_firstDart {p : G.Walk v w} (hnil : p.darts != []) : p.darts.
head hnil = p.firstDart (darts_eq_nil.not.mp hnil)
参数：hnil : p.darts != []。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Use `firstDart_eq_head_darts` to rewrite in the reverse direction.
-/
theorem head_darts_eq_firstDart {p : G.Walk v w} (hnil : p.darts ≠ []) :
    p.darts.head hnil = p.firstDart (darts_eq_nil.not.mp hnil) := by
  grind [firstDart_eq]

/-- Use `head_darts_eq_firstDart` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.firstDart_eq_head_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：firstDart_eq_head_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.firstDart hni
l = p.darts.head (darts_eq_nil.not.mpr hnil)
参数：hnil : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.darts_eq_nil`：darts_eq_nil {p : G.Walk v w} : p.darts =
 [] ↔ p.Nil
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.head_darts_eq_firstDart`：head_darts_eq_firstDart {p : G
.Walk v w} (hnil : p.darts != []) : p.darts.head hnil = p.firstDart (darts_eq_ni
l.not.mp hnil)

--- 原说明 ---
Use `head_darts_eq_firstDart` to rewrite in the reverse direction.
-/
theorem firstDart_eq_head_darts {p : G.Walk v w} (hnil : ¬p.Nil) :
    p.firstDart hnil = p.darts.head (darts_eq_nil.not.mpr hnil) :=
  head_darts_eq_firstDart _ |>.symm

@[simp]
/-
**SimpleGraph.Walk.firstDart_mem_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：firstDart_mem_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.firstDart hnil in
 p.darts
参数：hnil : ¬p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.darts_eq_nil`：darts_eq_nil {p : G.Walk v w} : p.darts =
 [] ↔ p.Nil
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.firstDart_eq_head_darts`：firstDart_eq_head_darts {p : G
.Walk v w} (hnil : ¬p.Nil) : p.firstDart hnil = p.darts.head (darts_eq_nil.not.m
pr hnil)
-/
theorem firstDart_mem_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.firstDart hnil ∈ p.darts :=
  p.firstDart_eq_head_darts _ ▸ List.head_mem _

@[simp]
/-
**SimpleGraph.Walk.getLast_darts_eq_lastDart** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：getLast_darts_eq_lastDart {p : G.Walk v w} (hnil : p.darts != []) : p.dart
s.getLast hnil = p.lastDart (darts_eq_nil.not.mp hnil)
参数：hnil : p.darts != []。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem getLast_darts_eq_lastDart {p : G.Walk v w} (hnil : p.darts ≠ []) :
    p.darts.getLast hnil = p.lastDart (darts_eq_nil.not.mp hnil) := by
  grind [lastDart_eq, not_nil_iff_lt_length]
/-
**SimpleGraph.Walk.lastDart_eq_getLast_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：lastDart_eq_getLast_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.lastDart hn
il = p.darts.getLast (darts_eq_nil.not.mpr hnil)
参数：hnil : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastDart_eq_getLast_darts {p : G.Walk v w} (hnil : ¬p.Nil) :
    p.lastDart hnil = p.darts.getLast (darts_eq_nil.not.mpr hnil) := by
  grind [lastDart_eq, not_nil_iff_lt_length]

@[simp]
/-
**SimpleGraph.Walk.lastDart_mem_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：lastDart_mem_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.lastDart hnil in p
.darts
参数：hnil : ¬p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.darts_eq_nil`：darts_eq_nil {p : G.Walk v w} : p.darts =
 [] ↔ p.Nil
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.lastDart_eq_getLast_darts`：lastDart_eq_getLast_darts {p
 : G.Walk v w} (hnil : ¬p.Nil) : p.lastDart hnil = p.darts.getLast (darts_eq_nil
.not.mpr hnil)
-/
theorem lastDart_mem_darts {p : G.Walk v w} (hnil : ¬p.Nil) : p.lastDart hnil ∈ p.darts :=
  p.lastDart_eq_getLast_darts _ ▸ List.getLast_mem _

/-- Use `mk_start_snd_eq_head_edges` to rewrite in the reverse direction. -/
@[simp]
/-
**SimpleGraph.Walk.head_edges_eq_mk_start_snd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：head_edges_eq_mk_start_snd {p : G.Walk v w} (hp) : p.edges.head hp = s(v, 
p.snd)
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.darts_eq_nil`：darts_eq_nil {p : G.Walk v w} : p.darts =
 [] ↔ p.Nil
· 使用定理 `List.head_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α} 
(w : List.map f l ≠ []), (List.map f l).head w = f (l.head ⋯)
· 使用定理 `SimpleGraph.Walk.head_darts_eq_firstDart`：head_darts_eq_firstDart {p : G
.Walk v w} (hnil : p.darts != []) : p.darts.head hnil = p.firstDart (darts_eq_ni
l.not.mp hnil)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Use `mk_start_snd_eq_head_edges` to rewrite in the reverse direction.
-/
theorem head_edges_eq_mk_start_snd {p : G.Walk v w} (hp) : p.edges.head hp = s(v, p.snd) := by
  simp [p.edge_firstDart, Walk.edges]

/-- Use `head_edges_eq_mk_start_snd` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.mk_start_snd_eq_head_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：mk_start_snd_eq_head_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(v, p.snd) 
= p.edges.head (edges_eq_nil.not.mpr hnil)
参数：hnil : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.edges_eq_nil`：edges_eq_nil {p : G.Walk v w} : p.edges =
 [] ↔ p.Nil
· 使用定理 `SimpleGraph.Walk.head_edges_eq_mk_start_snd`：head_edges_eq_mk_start_snd 
{p : G.Walk v w} (hp) : p.edges.head hp = s(v, p.snd)

--- 原说明 ---
Use `head_edges_eq_mk_start_snd` to rewrite in the reverse direction.
-/
theorem mk_start_snd_eq_head_edges {p : G.Walk v w} (hnil : ¬p.Nil) :
    s(v, p.snd) = p.edges.head (edges_eq_nil.not.mpr hnil) :=
  head_edges_eq_mk_start_snd _ |>.symm
/-
**SimpleGraph.Walk.mk_start_snd_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：mk_start_snd_mem_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(v, p.snd) in p
.edges
参数：hnil : ¬p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.edges_eq_nil`：edges_eq_nil {p : G.Walk v w} : p.edges =
 [] ↔ p.Nil
· 使用定理 `List.head_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head h ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.mk_start_snd_eq_head_edges`：mk_start_snd_eq_head_edges 
{p : G.Walk v w} (hnil : ¬p.Nil) : s(v, p.snd) = p.edges.head (edges_eq_nil.not.
mpr hnil)
-/
theorem mk_start_snd_mem_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(v, p.snd) ∈ p.edges :=
  p.mk_start_snd_eq_head_edges hnil ▸ List.head_mem _

/-- Use `mk_penultimate_end_eq_getLast_edges` to rewrite in the reverse direction. -/
@[simp]
/-
**SimpleGraph.Walk.getLast_edges_eq_mk_penultimate_end** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
形式化陈述：getLast_edges_eq_mk_penultimate_end {p : G.Walk v w} (hp) : p.edges.getLas
t hp = s(p.penultimate, w)
参数：hp。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.darts_eq_nil`：darts_eq_nil {p : G.Walk v w} : p.darts =
 [] ↔ p.Nil
· 使用定理 `List.getLast_map`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List 
α} (h : List.map f l ≠ []),   (List.map f l).getLast h = f (l.getLast ⋯)
· 使用定理 `SimpleGraph.Walk.getLast_darts_eq_lastDart`：getLast_darts_eq_lastDart {p
 : G.Walk v w} (hnil : p.darts != []) : p.darts.getLast hnil = p.lastDart (darts
_eq_nil.not.mp hnil)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Use `mk_penultimate_end_eq_getLast_edges` to rewrite in the reverse direction.
-/
theorem getLast_edges_eq_mk_penultimate_end {p : G.Walk v w} (hp) :
    p.edges.getLast hp = s(p.penultimate, w) := by
  simp [p.edge_lastDart, Walk.edges]

/-- Use `getLast_edges_eq_mk_penultimate_end` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.mk_penultimate_end_eq_getLast_edges** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
形式化陈述：mk_penultimate_end_eq_getLast_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(p
.penultimate, w) = p.edges.getLast (edges_eq_nil.not.mpr hnil)
参数：hnil : ¬p.Nil。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.edges_eq_nil`：edges_eq_nil {p : G.Walk v w} : p.edges =
 [] ↔ p.Nil
· 使用定理 `SimpleGraph.Walk.getLast_edges_eq_mk_penultimate_end`：getLast_edges_eq_m
k_penultimate_end {p : G.Walk v w} (hp) : p.edges.getLast hp = s(p.penultimate, 
w)

--- 原说明 ---
Use `getLast_edges_eq_mk_penultimate_end` to rewrite in the reverse direction.
-/
theorem mk_penultimate_end_eq_getLast_edges {p : G.Walk v w} (hnil : ¬p.Nil) :
    s(p.penultimate, w) = p.edges.getLast (edges_eq_nil.not.mpr hnil) :=
  getLast_edges_eq_mk_penultimate_end _ |>.symm
/-
**SimpleGraph.Walk.mk_penultimate_end_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：mk_penultimate_end_mem_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(p.penult
imate, w) in p.edges
参数：hnil : ¬p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.edges_eq_nil`：edges_eq_nil {p : G.Walk v w} : p.edges =
 [] ↔ p.Nil
· 使用定理 `List.getLast_mem`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.getLast 
h ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.mk_penultimate_end_eq_getLast_edges`：mk_penultimate_end
_eq_getLast_edges {p : G.Walk v w} (hnil : ¬p.Nil) : s(p.penultimate, w) = p.edg
es.getLast (edges_eq_nil.not.mpr hnil)
-/
theorem mk_penultimate_end_mem_edges {p : G.Walk v w} (hnil : ¬p.Nil) :
    s(p.penultimate, w) ∈ p.edges :=
  p.mk_penultimate_end_eq_getLast_edges hnil ▸ List.getLast_mem _

end Walk

end SimpleGraph

