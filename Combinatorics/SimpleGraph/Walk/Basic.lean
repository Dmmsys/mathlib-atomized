/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Peter Nelson
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Dart

/-!
# Walks

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions
  `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'`)
* `SimpleGraph.Walk.Nil`: A predicate for the empty walk
* `SimpleGraph.Walk.length`: The length of a walk
* `SimpleGraph.Walk.support`: The list of vertices a walk visits in order
* `SimpleGraph.Walk.darts`: The list of darts a walk visits in order
* `SimpleGraph.Walk.edges`: The list of edges a walk visits in order
* `SimpleGraph.Walk.edgeSet`: The set of edges of a walk visits

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

universe u
variable {V : Type u} (G : SimpleGraph V) {u v w : V}

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
/-
**SimpleGraph.Walk** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u} → SimpleGraph V → V → V → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit.
-/
inductive Walk : V → V → Type u
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq

attribute [refl] Walk.nil

@[simps]
/-
**SimpleGraph.Walk.instInhabited** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → (G : SimpleGraph V) → (v : V) → Inhabited (G.Walk v v)
参数：G : SimpleGraph V；v : V；G.Walk v v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Walk.instInhabited (v : V) : Inhabited (G.Walk v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
/-
**SimpleGraph.Adj.toWalk** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Adj`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Adj u v → G.Walk u v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The one-edge walk associated to a pair of adjacent vertices.
-/
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil

namespace Walk

variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
/-
**SimpleGraph.Walk.nil'** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil' (u : V) : G.Walk u u
参数：u : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pattern to get `Walk.nil` with the vertex as an explicit argument.
-/
abbrev nil' (u : V) : G.Walk u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
/-
**SimpleGraph.Walk.cons'** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w
参数：u v w : V；h : G.Adj u v；p : G.Walk v w。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Pattern to get `Walk.cons` with the vertices as explicit arguments.
-/
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w := Walk.cons h p
/-
**SimpleGraph.Walk.exists_eq_cons_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V},   u ≠ v → ∀ (p : G.Walk u v)
, ∃ w, ∃ (h : G.Adj u w), ∃ p', p = SimpleGraph.Walk.cons h p'
参数：p : G.Walk u v；h : G.Adj u w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem exists_eq_cons_of_ne {u v : V} (hne : u ≠ v) :
    ∀ (p : G.Walk u v), ∃ (w : V) (h : G.Adj u w) (p' : G.Walk w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
/-
**SimpleGraph.Walk.length** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length of a walk is the number of edges/darts along it.
-/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

@[simp]
/-
**SimpleGraph.Walk.length_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_nil {u : V} : (nil : G.Walk u u).length = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 := rfl

@[simp]
/-
**SimpleGraph.Walk.length_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).leng
th = p.length + 1
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 := rfl
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.length_toWalk** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.length_toWalk (h : G.Adj u v) : h.toWalk.length = 1 := by
  simp
/-
**SimpleGraph.Walk.eq_of_length_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.length = 
0 → u = v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_length_eq_zero {u v : V} : ∀ {p : G.Walk u v}, p.length = 0 → u = v
  | nil, _ => rfl
/-
**SimpleGraph.Walk.adj_of_length_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.length = 
1 → G.Adj u v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adj_of_length_eq_one {u v : V} : ∀ {p : G.Walk u v}, p.length = 1 → G.Adj u v
  | cons h nil, _ => h
/-
**SimpleGraph.Walk.exists_length_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：exists_length_eq_zero_iff {u v : V} : (exists p : G.Walk u v, p.length = 0
) ↔ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.eq_of_length_eq_zero`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.length = 0 → u = v
-/
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v :=
  ⟨fun ⟨_, h⟩ ↦ (eq_of_length_eq_zero h), (· ▸ ⟨nil, rfl⟩)⟩

@[simp]
/-
**SimpleGraph.Walk.exists_length_eq_one_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：exists_length_eq_one_iff {u v : V} : (exists (p : G.Walk u v), p.length = 
1) ↔ G.Adj u v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.adj_of_length_eq_one`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.length = 1 → G.Adj u v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma exists_length_eq_one_iff {u v : V} : (∃ (p : G.Walk u v), p.length = 1) ↔ G.Adj u v :=
  ⟨fun ⟨_, hp⟩ ↦ adj_of_length_eq_one hp, (⟨·.toWalk, by simp⟩)⟩
/-
**SimpleGraph.Walk.eq_of_length_le_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：eq_of_length_le_one {p q : G.Walk u v} (hp : p.length <= 1) (hq : q.length
 <= 1) : p = q
参数：hp : p.length <= 1；hq : q.length <= 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eq_of_length_le_one {p q : G.Walk u v} (hp : p.length ≤ 1) (hq : q.length ≤ 1) : p = q := by
  grind [cases Walk, length_cons, Adj.ne]

/-- The `support` of a walk is the list of vertices it visits in order. -/
/-
**SimpleGraph.Walk.support** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → List V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `support` of a walk is the list of vertices it visits in order.
-/
def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
/-
**SimpleGraph.Walk.darts** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → List G.Dart
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `darts` of a walk is the list of darts it visits in order.
-/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
/-
**SimpleGraph.Walk.edges** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges {u v : V} (p : G.Walk u v) : List (Sym2 V)
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`.
-/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge
/-
**SimpleGraph.Walk.edges_eq_map_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：edges_eq_map_darts (p : G.Walk u v) : p.edges = p.darts.map Dart.edge
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edges_eq_map_darts (p : G.Walk u v) : p.edges = p.darts.map Dart.edge :=
  rfl

@[simp]
/-
**SimpleGraph.Walk.support_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_nil {u : V} : (nil : G.Walk u u).support = [u]
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_nil {u : V} : (nil : G.Walk u u).support = [u] := rfl

@[simp, grind =]
/-
**SimpleGraph.Walk.support_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).sup
port = u :: p.support
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u :: p.support := rfl
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.support_toWalk** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.support_toWalk (h : G.Adj u v) : h.toWalk.support = [u, v] :=
  rfl

@[simp]
/-
**SimpleGraph.Walk.support_ne_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_ne_nil {u v : V} (p : G.Walk u v) : p.support != []
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.support ≠ [] := by cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.head_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：head_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : p.support.he
ad (by simp) = a
参数：p : G.Walk a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem head_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.head (by simp) = a := by cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.getLast_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：getLast_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) : p.support
.getLast (by simp) = b
参数：p : G.Walk a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.getLast_cons`：∀ {α : Type u_1} {a : α} {l : List α} (h : l ≠ []), (
a :: l).getLast ⋯ = l.getLast h
-/
theorem getLast_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.getLast (by simp) = b := by
  induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.cons_tail_support** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：cons_tail_support (p : G.Walk u v) : u :: p.support.tail = p.support
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma cons_tail_support (p : G.Walk u v) : u :: p.support.tail = p.support := by
  cases p <;> simp

@[deprecated cons_tail_support (since := "2026-03-16")]
/-
**SimpleGraph.Walk.support_eq_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.ta
il
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.start_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：start_mem_support {u v : V} (p : G.Walk u v) : u in p.support
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
-/
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.end_mem_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：end_mem_support {u v : V} (p : G.Walk u v) : v in p.support
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]

@[simp]
/-
**SimpleGraph.Walk.support_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：support_nonempty {u v : V} (p : G.Walk u v) : { w | w in p.support }.Nonem
pty
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩
/-
**SimpleGraph.Walk.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：mem_support_iff {u v w : V} (p : G.Walk u v) : w in p.support ↔ w = u ∨ w 
in p.support.tail
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem mem_support_iff {u v w : V} (p : G.Walk u v) :
    w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by cases p <;> simp
/-
**SimpleGraph.Walk.mem_support_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：mem_support_nil_iff {u v : V} : u in (nil : G.Walk v v).support ↔ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).support ↔ u = v := by simp

@[simp]
/-
**SimpleGraph.Walk.end_mem_tail_support_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：end_mem_tail_support_of_ne {u v : V} (h : u != v) (p : G.Walk u v) : v in 
p.support.tail
参数：h : u != v；p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.exists_eq_cons_of_ne`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V},   u ≠ v → ∀ (p : G.Walk u v), ∃ w, ∃ (h : G.Adj u w), ∃ p', p = Sim
pleGraph.Walk.cons h p'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp
/-
**SimpleGraph.Walk.support_suffix_support_cons** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：support_suffix_support_cons (p : G.Walk v w) (hadj : G.Adj u v) : p.suppor
t <:+ (p.cons hadj).support
参数：p : G.Walk v w；hadj : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem support_suffix_support_cons (p : G.Walk v w) (hadj : G.Adj u v) :
    p.support <:+ (p.cons hadj).support := by
  simp
/-
**SimpleGraph.Walk.support_subset_support_cons** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：support_subset_support_cons {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v
) : p.support subseteq (p.cons hadj).support
参数：p : G.Walk v w；hadj : G.Adj u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem support_subset_support_cons {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v) :
    p.support ⊆ (p.cons hadj).support := by
  simp
/-
**SimpleGraph.Walk.coe_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：coe_support {u v : V} (p : G.Walk u v) : (p.support : Multiset V) = {u} + 
p.support.tail
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem coe_support {u v : V} (p : G.Walk u v) :
    (p.support : Multiset V) = {u} + p.support.tail := by cases p <;> rfl
/-
**SimpleGraph.Walk.isChain_adj_cons_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V}, G.Adj u v → ∀ (p : G.Walk 
v w), List.IsChain G.Adj (u :: p.support)
参数：p : G.Walk v w；u :: p.support。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_adj_cons_support {u v w : V} (h : G.Adj u v) :
    ∀ (p : G.Walk v w), List.IsChain G.Adj (u :: p.support)
  | nil => .cons_cons h (.singleton _)
  | cons h' p => .cons_cons h (isChain_adj_cons_support h' p)
/-
**SimpleGraph.Walk.isChain_adj_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), List.IsChai
n G.Adj p.support
参数：p : G.Walk u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isChain_adj_cons_support`：∀ {V : Type u} {G : SimpleGra
ph V} {u v w : V}, G.Adj u v → ∀ (p : G.Walk v w), List.IsChain G.Adj (u :: p.su
pport)
-/
theorem isChain_adj_support {u v : V} : ∀ (p : G.Walk u v), List.IsChain G.Adj p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p
/-
**SimpleGraph.Walk.isChain_dartAdj_cons_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：isChain_dartAdj_cons_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.W
alk v w) : List.IsChain G.DartAdj (d :: p.darts)
参数：h : d.snd = v；p : G.Walk v w。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isChain_dartAdj_cons_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) :
    List.IsChain G.DartAdj (d :: p.darts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)
/-
**SimpleGraph.Walk.isChain_dartAdj_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), List.IsChai
n G.DartAdj p.darts
参数：p : G.Walk u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isChain_dartAdj_cons_darts`：isChain_dartAdj_cons_darts 
{d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) : List.IsChain G.DartAdj
 (d :: p.darts)
-/
theorem isChain_dartAdj_darts {u v : V} : ∀ (p : G.Walk u v), List.IsChain G.DartAdj p.darts
  | nil => .nil
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => isChain_dartAdj_cons_darts (by rfl) p

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
/-
**SimpleGraph.Walk.edges_subset_edgeSet** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄
, e ∈ p.edges → e ∈ G.edgeSet
参数：p : G.Walk u v。
该定理/引理表达了一个蕴含关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions.
-/
theorem edges_subset_edgeSet {u v : V} :
    ∀ (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
  | cons h' p', e, h => by
    cases h
    · exact h'
    next h' => exact edges_subset_edgeSet p' h'
/-
**SimpleGraph.Walk.adj_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : s(x, y) in p.edges) :
 G.Adj x y
参数：p : G.Walk u v；h : s(x, y) in p.edges。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
-/
theorem adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y :=
  p.edges_subset_edgeSet h

@[simp]
/-
**SimpleGraph.Walk.darts_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_nil {u : V} : (nil : G.Walk u u).darts = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] := rfl

@[simp]
/-
**SimpleGraph.Walk.darts_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).darts
 = ⟨(u, v), h⟩ :: p.darts
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.darts_toWalk** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.darts_toWalk (h : G.Adj u v) : h.toWalk.darts = [⟨(u, v), h⟩] :=
  rfl
/-
**SimpleGraph.Walk.cons_map_snd_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u :: p.darts.map (·.snd))
 = p.support
参数：p : G.Walk u v。
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
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u :: p.darts.map (·.snd)) = p.support := by
  induction p <;> simp [*]
/-
**SimpleGraph.Walk.map_snd_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.snd) = p.support
.tail
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.cons_map_snd_darts`：cons_map_snd_darts {u v : V} (p : G
.Walk u v) : (u :: p.darts.map (·.snd)) = p.support
-/
theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)
/-
**SimpleGraph.Walk.map_fst_darts_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：map_fst_darts_append {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) ++ [
v] = p.support
参数：p : G.Walk u v。
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
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
-/
theorem map_fst_darts_append {u v : V} (p : G.Walk u v) :
    p.darts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp [*]
/-
**SimpleGraph.Walk.map_fst_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) = p.support
.dropLast
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `List.dropLast_append_of_ne_nil`：∀ {α : Type u} {l l' : List α}, l ≠ [] →
 (l' ++ l).dropLast = l' ++ l.dropLast
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.append_nil`：∀ {α : Type u} (as : List α), as ++ [] = as
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.map_fst_darts_append`：map_fst_darts_append {u v : V} (p
 : G.Walk u v) : p.darts.map (·.fst) ++ [v] = p.support
-/
theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) = p.support.dropLast := by
  simpa! using! congr_arg List.dropLast (map_fst_darts_append p)

@[simp]
/-
**SimpleGraph.Walk.edges_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_nil {u : V} : (nil : G.Walk u u).edges = []
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] := rfl

@[simp]
/-
**SimpleGraph.Walk.edges_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).edges
 = s(u, v) :: p.edges
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edges = s(u, v) :: p.edges := rfl
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.edges_toWalk** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.edges_toWalk (h : G.Adj u v) : h.toWalk.edges = [s(u, v)] :=
  rfl

@[simp, grind =]
/-
**SimpleGraph.Walk.length_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 
1
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp, grind =]
/-
**SimpleGraph.Walk.length_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp, grind =]
/-
**SimpleGraph.Walk.length_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by simp [edges]

/-- Use `edge_getElem_darts` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.getElem_edges_eq_edge_getElem_darts** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
形式化陈述：getElem_edges_eq_edge_getElem_darts {p : G.Walk u v} {i : Nat} (h : i < p.
edges.length) : p.edges[i] = (p.darts[i]'(by grind)).edge
参数：h : i < p.edges.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]

--- 原说明 ---
Use `edge_getElem_darts` to rewrite in the reverse direction.
-/
theorem getElem_edges_eq_edge_getElem_darts {p : G.Walk u v} {i : ℕ} (h : i < p.edges.length) :
    p.edges[i] = (p.darts[i]'(by grind)).edge :=
  List.getElem_map ..

/-- Use `getElem_edges_eq_edge_getElem_darts` to rewrite in the reverse direction. -/
/-
**SimpleGraph.Walk.edge_getElem_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：edge_getElem_darts {p : G.Walk u v} {i : Nat} (h : i < p.darts.length) : p
.darts[i].edge = p.edges[i]'(by grind)
参数：h : i < p.darts.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.getElem_edges_eq_edge_getElem_darts`：getElem_edges_eq_e
dge_getElem_darts {p : G.Walk u v} {i : Nat} (h : i < p.edges.length) : p.edges[
i] = (p.darts[i]'(by grind)).edge

--- 原说明 ---
Use `getElem_edges_eq_edge_getElem_darts` to rewrite in the reverse direction.
-/
theorem edge_getElem_darts {p : G.Walk u v} {i : ℕ} (h : i < p.darts.length) :
    p.darts[i].edge = p.edges[i]'(by grind) := by
  rw [getElem_edges_eq_edge_getElem_darts]

@[simp]
/-
**SimpleGraph.Walk.fst_darts_getElem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：fst_darts_getElem {p : G.Walk u v} {i : Nat} (hi : i < p.darts.length) : p
.darts[i].fst = p.support.dropLast[i]'(by grind)
参数：hi : i < p.darts.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fst_darts_getElem {p : G.Walk u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i].fst = p.support.dropLast[i]'(by grind) := by
  grind [map_fst_darts]

@[simp]
/-
**SimpleGraph.Walk.snd_darts_getElem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：snd_darts_getElem {p : G.Walk u v} {i : Nat} (hi : i < p.darts.length) : p
.darts[i].snd = p.support.tail[i]'(by grind)
参数：hi : i < p.darts.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem snd_darts_getElem {p : G.Walk u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i].snd = p.support.tail[i]'(by grind) := by
  grind [map_snd_darts]

@[simp]
/-
**SimpleGraph.Walk.support_getElem_zero** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：support_getElem_zero (p : G.Walk u v) : p.support[0] = u
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma support_getElem_zero (p : G.Walk u v) : p.support[0] = u := by cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.support_getElem_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph
.Walk`。
形式化陈述：support_getElem_length (p : G.Walk u v) : p.support[p.length] = v
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma support_getElem_length (p : G.Walk u v) : p.support[p.length] = v := by
  induction p <;> simp_all
/-
**SimpleGraph.Walk.mem_darts_iff_infix_support** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：mem_darts_iff_infix_support {u' v'} {p : G.Walk u v} (h : G.Adj u' v') : ⟨
⟨u', v'⟩, h⟩ in p.darts ↔ [u', v'] <:+: p.support
参数：h : G.Adj u' v'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `List.getElem_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ i,
 ∃ (h : i < l.length), l[i] = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
· 使用定理 `List.getElem_mem`：∀ {α : Type u_1} {l : List α} {n : ℕ} (h : n < l.lengt
h), l[n] ∈ l
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `List.infix_iff_getElem?`：∀ {α : Type u_1} {l₁ l₂ : List α},   l₁ <:+: l₂
 ↔ ∃ k, l₁.length + k ≤ l₂.length ∧ ∀ (i : ℕ) (h : i < l₁.length), l₂[i + k]? = 
some l₁[i]
-/
theorem mem_darts_iff_infix_support {u' v'} {p : G.Walk u v} (h : G.Adj u' v') :
    ⟨⟨u', v'⟩, h⟩ ∈ p.darts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h ↦ ?_, fun ⟨i, hi, h⟩ ↦ ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj ↦ by grind [fst_darts_getElem, snd_darts_getElem]⟩
  · have := h 0
    have := h 1
    convert! p.darts.getElem_mem (n := i) (by grind)
      <;> grind [fst_darts_getElem, snd_darts_getElem]
/-
**SimpleGraph.Walk.mem_darts_iff_fst_snd_infix_support** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
形式化陈述：mem_darts_iff_fst_snd_infix_support {p : G.Walk u v} {d : G.Dart} : d in p
.darts ↔ [d.fst, d.snd] <:+: p.support
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.mem_darts_iff_infix_support`：mem_darts_iff_infix_suppor
t {u' v'} {p : G.Walk u v} (h : G.Adj u' v') : ⟨⟨u', v'⟩, h⟩ in p.darts ↔ [u', v
'] <:+: p.support
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
theorem mem_darts_iff_fst_snd_infix_support {p : G.Walk u v} {d : G.Dart} :
    d ∈ p.darts ↔ [d.fst, d.snd] <:+: p.support :=
  mem_darts_iff_infix_support ..
/-
**SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) {d : G.Dart}
, d ∈ p.darts → d.toProd.1 ∈ p.support
参数：p : G.Walk u v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dart_fst_mem_support_of_mem_darts {u v : V} :
    ∀ (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.fst ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with rfl | hd
    · exact .inl rfl
    · exact .inr (dart_fst_mem_support_of_mem_darts _ hd)
/-
**SimpleGraph.Walk.mem_support_iff_exists_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：mem_support_iff_exists_mem_edges {u v w : V} {p : G.Walk u v} : w in p.sup
port ↔ w = v ∨ exists e in p.edges, w in e
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
theorem mem_support_iff_exists_mem_edges {u v w : V} {p : G.Walk u v} :
    w ∈ p.support ↔ w = v ∨ ∃ e ∈ p.edges, w ∈ e := by
  induction p <;> aesop
/-
**SimpleGraph.Walk.darts_nodup_of_support_nodup** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nod
up) : p.darts.Nodup
参数：h : p.support.Nodup。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts`：∀ {V : Type u} {G : 
SimpleGraph V} {u v : V} (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.toProd.1
 ∈ p.support
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨(h.1 <| dart_fst_mem_support_of_mem_darts p' ·), ih h.2⟩
/-
**SimpleGraph.Walk.edges_eq_zipWith_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk`。
形式化陈述：edges_eq_zipWith_support {u v : V} {p : G.Walk u v} : p.edges = List.zipWi
th (s(·, ·)) p.support p.support.tail
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.zipWith_nil_right`：∀ {α : Type u} {β : Type v} {γ : Type w} {l : Li
st α} {f : α → β → γ}, List.zipWith f l [] = []
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem edges_eq_zipWith_support {u v : V} {p : G.Walk u v} :
    p.edges = List.zipWith (s(·, ·)) p.support p.support.tail := by
  induction p with
  | nil => simp
  | cons _ p' ih => cases p' <;> simp [edges_cons, ih]
/-
**SimpleGraph.Walk.edges_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_injective {u v : V} : Function.Injective (Walk.edges : G.Walk u v ->
 List (Sym2 V)) | .nil, .nil, _ => rfl | .nil, .cons _ _, h => by simp at h | .c
ons _ _, .nil, h => by simp at h | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h =>
 by obtain ⟨rfl, h₃⟩ : v = v' ∧ w₁.edges = w₂.edges
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem edges_injective {u v : V} : Function.Injective (Walk.edges : G.Walk u v → List (Sym2 V))
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    obtain ⟨rfl, h₃⟩ : v = v' ∧ w₁.edges = w₂.edges := by simpa [h₁, h₂.ne] using h
    rw [edges_injective h₃]
/-
**SimpleGraph.Walk.darts_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_injective {u v : V} : Function.Injective (Walk.darts : G.Walk u v ->
 List G.Dart)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `SimpleGraph.Walk.edges_injective`：edges_injective {u v : V} : Function.I
njective (Walk.edges : G.Walk u v -> List (Sym2 V)) | .nil, .nil, _ => rfl | .ni
l, .cons _ _, h => by …
-/
theorem darts_injective {u v : V} : Function.Injective (Walk.darts : G.Walk u v → List G.Dart) :=
  edges_injective.of_comp

/-- The `Set` of edges of a walk. -/
/-
**SimpleGraph.Walk.edgeSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet {u v : V} (p : G.Walk u v) : Set (Sym2 V)
参数：p : G.Walk u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Set` of edges of a walk.
-/
def edgeSet {u v : V} (p : G.Walk u v) : Set (Sym2 V) := {e | e ∈ p.edges}

@[simp]
/-
**SimpleGraph.Walk.mem_edgeSet** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：mem_edgeSet {u v : V} {p : G.Walk u v} {e : Sym2 V} : e in p.edgeSet ↔ e i
n p.edges
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_edgeSet {u v : V} {p : G.Walk u v} {e : Sym2 V} : e ∈ p.edgeSet ↔ e ∈ p.edges := Iff.rfl

@[simp]
/-
**SimpleGraph.Walk.edgeSet_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_nil (u : V) : (nil : G.Walk u u).edgeSet = ∅
参数：u : V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma edgeSet_nil (u : V) : (nil : G.Walk u u).edgeSet = ∅ := by ext; simp

@[simp]
/-
**SimpleGraph.Walk.edgeSet_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edgeSet_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).edg
eSet = insert s(u, v) p.edgeSet
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem edgeSet_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edgeSet = insert s(u, v) p.edgeSet := by ext; simp
/-
**SimpleGraph.Walk.coe_edges_toFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：coe_edges_toFinset [DecidableEq V] {u v : V} (p : G.Walk u v) : (p.edges.t
oFinset : Set (Sym2 V)) = p.edgeSet
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.coe_toFinset`：coe_toFinset (l : List α) : (l.toFinset : Set α) = { 
a | a in l }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coe_edges_toFinset [DecidableEq V] {u v : V} (p : G.Walk u v) :
    (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet := by
  simp [edgeSet]

/-- Predicate for the empty walk.

Solves the dependent type problem where `p = G.Walk.nil` typechecks
only if `p` has defeq endpoints. -/
/-
**SimpleGraph.Walk.Nil** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {v w : V} → G.Walk v w → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Predicate for the empty walk.

Solves the dependent type problem where `p = G.Walk.nil` typechecks
only if `p` has defeq endpoints.
-/
inductive Nil : {v w : V} → G.Walk v w → Prop
  | nil {u : V} : Nil (nil : G.Walk u u)
/-
**SimpleGraph.Walk.nil_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V}, SimpleGraph.Walk.nil.Nil
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp, grind .] lemma nil_nil : (nil : G.Walk u u).Nil := Nil.nil
/-
**SimpleGraph.Walk.not_nil_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {h : G.Adj u v} {p : G.Walk
 v w}, ¬(SimpleGraph.Walk.cons h p).Nil
参数：SimpleGraph.Walk.cons h p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma not_nil_cons {h : G.Adj u v} {p : G.Walk v w} : ¬ (cons h p).Nil := nofun
/-
**SimpleGraph.Walk.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (p : G.Walk v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

@[grind .]
/-
**SimpleGraph.Walk.Nil.eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Nil`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p : G.Walk v w}, p.Nil → v =
 w
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma Nil.eq {p : G.Walk v w} : p.Nil → v = w | .nil => rfl
/-
**SimpleGraph.Walk.not_nil_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：not_nil_of_ne {p : G.Walk v w} : v != w -> ¬ p.Nil
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `SimpleGraph.Walk.Nil.eq`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p
 : G.Walk v w}, p.Nil → v = w
-/
lemma not_nil_of_ne {p : G.Walk v w} : v ≠ w → ¬ p.Nil := mt Nil.eq
/-
**SimpleGraph.Walk.nil_iff_support_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
lemma nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.darts_eq_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_eq_nil {p : G.Walk v w} : p.darts = [] ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma darts_eq_nil {p : G.Walk v w} : p.darts = [] ↔ p.Nil := by
  cases p <;> simp

@[simp]
/-
**SimpleGraph.Walk.edges_eq_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_eq_nil {p : G.Walk v w} : p.edges = [] ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
lemma edges_eq_nil {p : G.Walk v w} : p.edges = [] ↔ p.Nil := by
  cases p <;> simp

@[simp, grind .]
/-
**SimpleGraph.Walk.length_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：length_eq_zero_iff {p : G.Walk u v} : p.length = 0 ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem length_eq_zero_iff {p : G.Walk u v} : p.length = 0 ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.length_eq_zero⟩ := length_eq_zero_iff

@[deprecated length_eq_zero_iff (since := "2026-05-11")]
/-
**SimpleGraph.Walk.nil_iff_length_eq** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SimpleGraph.Walk.length_eq_zero_iff`：length_eq_zero_iff {p : G.Walk u v}
 : p.length = 0 ↔ p.Nil
-/
lemma nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0 :=
  length_eq_zero_iff.symm
/-
**SimpleGraph.Walk.not_nil_iff_lt_length** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.
Walk`。
形式化陈述：not_nil_iff_lt_length {p : G.Walk v w} : ¬ p.Nil ↔ 0 < p.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma not_nil_iff_lt_length {p : G.Walk v w} : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp
/-
**SimpleGraph.Walk.not_nil_iff** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：not_nil_iff {p : G.Walk v w} : ¬ p.Nil ↔ exists (u : V) (h : G.Adj v u) (q
 : G.Walk u w), p = cons h q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.Walk.cons.injEq`：∀ {V : Type u} {G : SimpleGraph V} {u v w :
 V} (h : G.Adj u v) (p : G.Walk v w) (v_1 : V) (h_1 : G.Adj u v_1)   (p_1 : G.Wa
lk v_1 w), (Simpl…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
lemma not_nil_iff {p : G.Walk v w} :
    ¬ p.Nil ↔ ∃ (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
@[simp]
/-
**SimpleGraph.Walk.eq_nil_iff_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：eq_nil_iff_nil {p : G.Walk v v} : p = nil ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`.
-/
theorem eq_nil_iff_nil {p : G.Walk v v} : p = nil ↔ p.Nil := by
  cases p <;> simp

alias ⟨_, Nil.eq_nil⟩ := eq_nil_iff_nil

@[deprecated eq_nil_iff_nil (since := "2026-05-11")]
/-
**SimpleGraph.Walk.nil_iff_eq_nil** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：nil_iff_eq_nil : forall {p : G.Walk v v}, p.Nil ↔ p = nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SimpleGraph.Walk.eq_nil_iff_nil`：eq_nil_iff_nil {p : G.Walk v v} : p = n
il ↔ p.Nil
-/
lemma nil_iff_eq_nil : ∀ {p : G.Walk v v}, p.Nil ↔ p = nil :=
  eq_nil_iff_nil.symm
/-
**SimpleGraph.Walk.nil_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：nil_of_subsingleton [Subsingleton V] (p : G.Walk v w) : p.Nil
参数：p : G.Walk v w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
-/
lemma nil_of_subsingleton [Subsingleton V] (p : G.Walk v w) : p.Nil :=
  match p with
  | nil => Nil.nil
  | cons h w => Unique.eq_default G ▸ h |>.elim

@[simp]
/-
**SimpleGraph.Walk.exists_nil_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：exists_nil_iff {u v : V} : (exists p : G.Walk u v, p.Nil) ↔ u = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.Nil.eq`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {p
 : G.Walk v w}, p.Nil → v = w
-/
theorem exists_nil_iff {u v : V} : (∃ p : G.Walk u v, p.Nil) ↔ u = v :=
  ⟨fun ⟨_, h⟩ ↦ h.eq, (· ▸ ⟨nil, .nil⟩)⟩

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
/-
**SimpleGraph.Walk.notNilRec** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：notNilRec {motive : {u w : V} -> (p : G.Walk u w) -> (h : ¬ p.Nil) -> Sort
*} (cons : {u v w : V} -> (h : G.Adj u v) -> (q : G.Walk v w) -> motive (cons h 
q) not_nil_cons) (p : G.Walk u w) : (hp : ¬ p.Nil) -> motive p hp
参数：p : G.Walk u w；h : ¬ p.Nil；cons : {u v w : V} -> (h : G.Adj u v) -> (q : G.Wa
lk v w) -> motive (cons h q) not_nil_cons；p : G.Walk u w。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.not_nil_cons`：∀ {V : Type u} {G : SimpleGraph V} {u v w
 : V} {h : G.Adj u v} {p : G.Walk v w}, ¬(SimpleGraph.Walk.cons h p).Nil

--- 原说明 ---
The recursion principle for nonempty walks
-/
def notNilRec {motive : {u w : V} → (p : G.Walk u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) → motive (cons h q) not_nil_cons)
    (p : G.Walk u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
/-
**SimpleGraph.Walk.notNilRec_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：notNilRec_cons {motive : {u w : V} -> (p : G.Walk u w) -> ¬ p.Nil -> Sort*
} (cons : {u v w : V} -> (h : G.Adj u v) -> (q : G.Walk v w) -> motive (q.cons h
) Walk.not_nil_cons) (h' : G.Adj u v) (q' : G.Walk v w) : @Walk.notNilRec _ _ _ 
_ _ cons _ _ = cons h' q'
参数：p : G.Walk u w；cons : {u v w : V} -> (h : G.Adj u v) -> (q : G.Walk v w) -> m
otive (q.cons h) Walk.not_nil_cons；h' : G.Adj u v；q' : G.Walk v w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.not_nil_cons`：∀ {V : Type u} {G : SimpleGraph V} {u v w
 : V} {h : G.Adj u v} {p : G.Walk v w}, ¬(SimpleGraph.Walk.cons h p).Nil
-/
lemma notNilRec_cons {motive : {u w : V} → (p : G.Walk u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : G.Adj u v) (q' : G.Walk v w) :
    @Walk.notNilRec _ _ _ _ _ cons _ _ = cons h' q' := by rfl
/-
**SimpleGraph.Walk.end_mem_tail_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：end_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) : v in p.sup
port.tail
参数：h : ¬ p.Nil。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem end_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) h
/-
**SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil** 是 Mathlib 中的一个定
理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：mem_support_iff_exists_mem_edges_of_not_nil {u v w : V} {p : G.Walk u v} (
hnil : ¬p.Nil) : w in p.support ↔ exists e in p.edges, w in e
参数：hnil : ¬p.Nil。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem mem_support_iff_exists_mem_edges_of_not_nil {u v w : V} {p : G.Walk u v} (hnil : ¬p.Nil) :
    w ∈ p.support ↔ ∃ e ∈ p.edges, w ∈ e := by
  induction p with
  | nil => simp at hnil
  | cons h p ih => cases p <;> aesop

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not. -/
/-
**SimpleGraph.Walk.exists_boundary_dart** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u in S) 
(vS : v ∉ S) : exists d : G.Dart, d in p.darts ∧ d.fst in S ∧ d.snd ∉ S
参数：p : G.Walk u v；S : Set V；uS : u in S；vS : v ∉ S。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not.
-/
theorem exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x _
    by_cases h : x ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨_, a⟩, List.Mem.head _, uS, h⟩

/-- Construct a walk from a list of vertices where adjacent vertices in the list are also adjacent
in the graph -/
/-
**SimpleGraph.Walk.ofSupport** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：ofSupport (l : List V) (hne : l != []) (hchain : l.IsChain G.Adj) : G.Walk
 (l.head hne) (l.getLast hne)
参数：l : List V；hne : l != []；hchain : l.IsChain G.Adj。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?

--- 原说明 ---
Construct a walk from a list of vertices where adjacent vertices in the list are
 also adjacent
in the graph
-/
def ofSupport (l : List V) (hne : l ≠ []) (hchain : l.IsChain G.Adj) :
    G.Walk (l.head hne) (l.getLast hne) :=
  match l with
  | [_] => .nil
  | _ :: v :: l => .cons hchain.rel <| .ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons

variable (G v) in
@[simp]
/-
**SimpleGraph.Walk.ofSupport_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：ofSupport_singleton : ofSupport [v] ([].cons_ne_nil v) (.singleton v) = .n
il (G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem ofSupport_singleton :
    ofSupport [v] ([].cons_ne_nil v) (.singleton v) = .nil (G := G) (u := v) :=
  rfl

@[simp]
/-
**SimpleGraph.Walk.ofSupport_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：ofSupport_cons_cons {l : List V} (hchain : u :: v :: l |>.IsChain G.Adj) :
 ofSupport (u :: v :: l) ((v :: l).cons_ne_nil u) hchain = .cons hchain.rel (.of
Support (v :: l) (l.cons_ne_nil v) hchain.of_cons)
参数：hchain : u :: v :: l |>.IsChain G.Adj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem ofSupport_cons_cons {l : List V} (hchain : u :: v :: l |>.IsChain G.Adj) :
    ofSupport (u :: v :: l) ((v :: l).cons_ne_nil u) hchain =
      .cons hchain.rel (.ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.support_ofSupport** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：support_ofSupport {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj) 
: (ofSupport l hne hchain).support = l
参数：hne : l != []；hchain : l.IsChain G.Adj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem support_ofSupport {l : List V} (hne : l ≠ []) (hchain : l.IsChain G.Adj) :
    (ofSupport l hne hchain).support = l := by
  match l with
  | [_] => rfl
  | _ :: v :: l =>
    simpa using support_ofSupport (l.cons_ne_nil v) hchain.of_cons

@[simp, grind =]
/-
**SimpleGraph.Walk.length_ofSupport** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：length_ofSupport {l : List V} (hne : l != []) (hchain : l.IsChain G.Adj) :
 (ofSupport l hne hchain).length = l.length - 1
参数：hne : l != []；hchain : l.IsChain G.Adj。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_ofSupport {l : List V} (hne : l ≠ []) (hchain : l.IsChain G.Adj) :
    (ofSupport l hne hchain).length = l.length - 1 := by
  grind [support_ofSupport]

/-- Construct a walk from a list of darts where adjacent darts in the list are also adjacent
in the graph -/
/-
**SimpleGraph.Walk.ofDarts** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：ofDarts (l : List G.Dart) (hne : l != []) (hchain : l.IsChain G.DartAdj) :
 G.Walk (l.head hne).fst (l.getLast hne).snd
参数：l : List G.Dart；hne : l != []；hchain : l.IsChain G.DartAdj。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?

--- 原说明 ---
Construct a walk from a list of darts where adjacent darts in the list are also 
adjacent
in the graph
-/
def ofDarts (l : List G.Dart) (hne : l ≠ []) (hchain : l.IsChain G.DartAdj) :
    G.Walk (l.head hne).fst (l.getLast hne).snd :=
  match l with
  | [d] => .cons d.adj .nil
  | d₁ :: d₂ :: l =>
    .cons (hchain.rel ▸ d₁.adj) <| ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.of_cons

@[simp]
/-
**SimpleGraph.Walk.ofDarts_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：ofDarts_singleton (d : G.Dart) : ofDarts [d] (by simp) (by simp) = .cons d
.adj .nil
参数：d : G.Dart。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem ofDarts_singleton (d : G.Dart) : ofDarts [d] (by simp) (by simp) = .cons d.adj .nil :=
  rfl
/-
**SimpleGraph.Walk.ofDarts_singleton'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：ofDarts_singleton' (d : G.Dart) : ofDarts [d] (by simp) (by simp) = d.adj.
toWalk
参数：d : G.Dart。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem ofDarts_singleton' (d : G.Dart) : ofDarts [d] (by simp) (by simp) = d.adj.toWalk :=
  rfl

@[simp]
/-
**SimpleGraph.Walk.ofDarts_cons_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：ofDarts_cons_cons {d₁ d₂ : G.Dart} {l : List G.Dart} (hchain : d₁ :: d₂ ::
 l |>.IsChain G.DartAdj) : ofDarts (d₁ :: d₂ :: l) ((d₂ :: l).cons_ne_nil d₁) hc
hain = .cons (hchain.rel ▸ d₁.adj) (ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.
of_cons)
参数：hchain : d₁ :: d₂ :: l |>.IsChain G.DartAdj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.cons_ne_nil`：∀ {α : Type u_1} (a : α) (l : List α), a :: l ≠ []
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem ofDarts_cons_cons {d₁ d₂ : G.Dart} {l : List G.Dart}
    (hchain : d₁ :: d₂ :: l |>.IsChain G.DartAdj) :
    ofDarts (d₁ :: d₂ :: l) ((d₂ :: l).cons_ne_nil d₁) hchain =
      .cons (hchain.rel ▸ d₁.adj) (ofDarts (d₂ :: l) (l.cons_ne_nil d₂) hchain.of_cons) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.darts_ofDarts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：darts_ofDarts {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.Dart
Adj) : (ofDarts l hne hchain).darts = l
参数：hne : l != []；hchain : l.IsChain G.DartAdj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
-/
theorem darts_ofDarts {l : List G.Dart} (hne : l ≠ []) (hchain : l.IsChain G.DartAdj) :
    (ofDarts l hne hchain).darts = l := by
  match l with
  | [_] => rfl
  | d₁ :: d₂ :: l =>
    simpa [hchain.rel.symm] using darts_ofDarts (l.cons_ne_nil d₂) hchain.of_cons

@[simp]
/-
**SimpleGraph.Walk.edges_ofDarts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：edges_ofDarts {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.Dart
Adj) : (ofDarts l hne hchain).edges = l.map Dart.edge
参数：hne : l != []；hchain : l.IsChain G.DartAdj。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.getLast`：getLast?_flatten_replicate {n : Nat} (h : n != 0) (l : Lis
t α) : (List.replicate n l).flatten.getLast? = l.getLast?
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.darts_ofDarts`：darts_ofDarts {l : List G.Dart} (hne : l
 != []) (hchain : l.IsChain G.DartAdj) : (ofDarts l hne hchain).darts = l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem edges_ofDarts {l : List G.Dart} (hne : l ≠ []) (hchain : l.IsChain G.DartAdj) :
    (ofDarts l hne hchain).edges = l.map Dart.edge := by
  simp [edges]

@[simp, grind =]
/-
**SimpleGraph.Walk.length_ofDarts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_ofDarts {l : List G.Dart} (hne : l != []) (hchain : l.IsChain G.Dar
tAdj) : (ofDarts l hne hchain).length = l.length
参数：hne : l != []；hchain : l.IsChain G.DartAdj。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem length_ofDarts {l : List G.Dart} (hne : l ≠ []) (hchain : l.IsChain G.DartAdj) :
    (ofDarts l hne hchain).length = l.length := by
  grind [darts_ofDarts]

end Walk

end SimpleGraph

