/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
public import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks
public import Mathlib.Order.Preorder.Finite

/-!

# Trail, Path, and Cycle

In a simple graph,

* A *trail* is a walk whose edges each appear no more than once.

* A *circuit* is a nonempty trail whose first and last vertices are the
  same.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`, and `SimpleGraph.Walk.IsCycle`.

* `SimpleGraph.Path`

* `SimpleGraph.Path.map` for the induced map on paths,
  given an (injective) graph homomorphism.

## Tags
trails, paths, circuits, cycles
-/

@[expose] public section

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v}
variable (G : SimpleGraph V) (G' : SimpleGraph V')

namespace Walk

variable {G G'} {u u' v w : V} {p : G.Walk u v} {f : G →g G'}

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
/-
**SimpleGraph.Walk.IsTrail** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *trail* is a walk with no repeating edges.
-/
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup

/-- A *path* is a walk with no repeating vertices.
Use `SimpleGraph.Walk.IsPath.mk'` for a simpler constructor. -/
/-
**SimpleGraph.Walk.IsPath** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u v : V} → G.Walk u v → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *path* is a walk with no repeating vertices.
Use `SimpleGraph.Walk.IsPath.mk'` for a simpler constructor.
-/
structure IsPath {u v : V} (p : G.Walk u v) : Prop extends isTrail : IsTrail p where
  support_nodup : p.support.Nodup

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
/-
**SimpleGraph.Walk.IsCircuit** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u : V} → G.Walk u u → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`.
-/
structure IsCircuit {u : V} (p : G.Walk u u) : Prop extends isTrail : IsTrail p where
  ne_nil : p ≠ nil

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
/-
**SimpleGraph.Walk.IsCycle** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u : V} → G.Walk u u → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice).
-/
structure IsCycle {u : V} (p : G.Walk u u) : Prop extends isCircuit : IsCircuit p where
  support_nodup : p.support.tail.Nodup

@[simp]
/-
**SimpleGraph.Walk.isTrail_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p
.copy hu hv).IsTrail ↔ p.IsTrail
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.IsPath.mk'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsPath
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.support.N
odup → p.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.edges_nodup_of_support_nodup`：edges_nodup_of_support_no
dup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.edges.Nodup
-/
theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩
/-
**SimpleGraph.Walk.isPath_def** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
· 使用定理 `SimpleGraph.Walk.IsPath.mk'`：∀ {V : Type u} {G : SimpleGraph V} {u v : V
} {p : G.Walk u v}, p.support.Nodup → p.IsPath
-/
theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩
/-
**SimpleGraph.Walk.isPath_iff_injective_get_support** 是 Mathlib 中的一个定理，位于命名空间 `S
impleGraph.Walk`。
形式化陈述：isPath_iff_injective_get_support {u v : V} (p : G.Walk u v) : p.IsPath ↔ (
p.support.get ·).Injective
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `SimpleGraph.Walk.isPath_def`：isPath_def {u v : V} (p : G.Walk u v) : p.I
sPath ↔ p.support.Nodup
· 使用定理 `List.nodup_iff_injective_get`：nodup_iff_injective_get {l : List α} : Nod
up l ↔ Function.Injective l.get
-/
theorem isPath_iff_injective_get_support {u v : V} (p : G.Walk u v) :
    p.IsPath ↔ (p.support.get ·).Injective :=
  p.isPath_def.trans List.nodup_iff_injective_get

@[simp]
/-
**SimpleGraph.Walk.isPath_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.
copy hu hv).IsPath ↔ p.IsPath
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl

@[simp]
/-
**SimpleGraph.Walk.isCircuit_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') : (p.copy hu hu).IsCi
rcuit ↔ p.IsCircuit
参数：p : G.Walk u u；hu : u = u'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.IsCircuit.not_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
.IsCircuit`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} {p : G.Walk v v}, p.IsCircuit →
 ¬p.Nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_nil`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → p ≠ SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.Nil.eq_nil`：∀ {V : Type u} {G : SimpleGraph V} {v : V} 
{p : G.Walk v v}, p.Nil → p = SimpleGraph.Walk.nil
-/
lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)
/-
**SimpleGraph.Walk.isCycle_def** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isCycle_def {u : V} (p : G.Walk u u) : p.IsCycle ↔ p.IsTrail ∧ p != nil ∧ 
p.support.tail.Nodup
参数：p : G.Walk u u。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCircuit → p.IsTrail
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_nil`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → p ≠ SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩

@[simp]
/-
**SimpleGraph.Walk.isCycle_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') : (p.copy hu hu).IsCycl
e ↔ p.IsCycle
参数：p : G.Walk u u；hu : u = u'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.IsCycle.not_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} {p : G.Walk v v}, p.IsCycle → ¬
p.Nil
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_nil`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → p ≠ SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `SimpleGraph.Walk.Nil.eq_nil`：∀ {V : Type u} {G : SimpleGraph V} {v : V} 
{p : G.Walk v v}, p.Nil → p = SimpleGraph.Walk.nil
-/
lemma IsCycle.not_nil {p : G.Walk v v} (hp : IsCycle p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

@[simp]
/-
**SimpleGraph.Walk.IsTrail.nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsTra
il`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V}, SimpleGraph.Walk.nil.IsTrail
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
-/
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩
/-
**SimpleGraph.Walk.IsTrail.of_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {h : G.Adj u v} {p : G.Walk
 v w},   (SimpleGraph.Walk.cons h p).IsTrail → p.IsTrail
参数：SimpleGraph.Walk.cons h p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by simp [isTrail_def]

@[simp]
/-
**SimpleGraph.Walk.isTrail_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isTrail_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).IsT
rail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isTrail_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges := by simp [isTrail_def, and_comm]
/-
**SimpleGraph.Walk.IsTrail.cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsTr
ail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u u' v : V} {w : G.Walk u' v},   w.IsT
rail → ∀ (hu : G.Adj u u'), s(u, u') ∉ w.edges → (SimpleGraph.Walk.cons hu w).Is
Trail
参数：hu : G.Adj u u'；u, u'；SimpleGraph.Walk.cons hu w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
protected lemma IsTrail.cons {w : G.Walk u' v} (hw : w.IsTrail) (hu : G.Adj u u')
    (hu' : s(u, u') ∉ w.edges) : (w.cons hu).IsTrail := by simp [*]
/-
**SimpleGraph.Walk.IsTrail.reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), p.IsTrail →
 p.reverse.IsTrail
参数：p : G.Walk u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.edges_reverse`：edges_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.edges = p.edges.reverse
-/
theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [isTrail_def] using h

@[simp]
/-
**SimpleGraph.Walk.reverse_isTrail_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsT
rail
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p
· 使用定理 `SimpleGraph.Walk.IsTrail.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} (p : G.Walk u v), p.IsTrail → p.reverse.IsTrail
-/
theorem reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert! h.reverse _
      try rw [reverse_reverse]

@[simp]
/-
**SimpleGraph.Walk.isTrail_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isTrail_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) : (p.append q
).IsTrail ↔ p.IsTrail ∧ q.IsTrail ∧ p.edges.Disjoint q.edges
参数：p : G.Walk u v；q : G.Walk v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.edges_append`：edges_append {u v w : V} (p : G.Walk u v)
 (p' : G.Walk v w) : (p.append p').edges = p.edges ++ p'.edges
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isTrail_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).IsTrail ↔ p.IsTrail ∧ q.IsTrail ∧ p.edges.Disjoint q.edges := by
  simp [Walk.isTrail_def, List.nodup_append']
/-
**SimpleGraph.Walk.IsTrail.of_append_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w}, (p.append q).IsTrail → p.IsTrail
参数：p.append q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  simp_all
/-
**SimpleGraph.Walk.IsTrail.of_append_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w}, (p.append q).IsTrail → q.IsTrail
参数：p.append q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  simp_all
/-
**SimpleGraph.Walk.IsTrail.count_edges_le_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p : G
.Walk u v},   p.IsTrail → ∀ (e : Sym2 V), List.count e p.edges ≤ 1
参数：e : Sym2 V。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_count_le_one`：nodup_iff_count_le_one [BEq α] [LawfulBEq α
] {l : List α} : Nodup l ↔ forall a, count a l <= 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
-/
theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e
/-
**SimpleGraph.Walk.IsTrail.count_edges_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v : V} {p : G
.Walk u v},   p.IsTrail → ∀ {e : Sym2 V}, e ∈ p.edges → List.count e p.edges = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
-/
theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he
/-
**SimpleGraph.Walk.IsTrail.length_le_card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Fintype ↑G.edgeSet] {u v : V} {
w : G.Walk u v},   w.IsTrail → w.length ≤ G.edgeFinset.card
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.toFinset_card_of_nodup`：List.toFinset_card_of_nodup {l : List α} (h
 : l.Nodup) : #l.toFinset = l.length
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
· 使用定理 `SimpleGraph.Walk.length_edges`：length_edges {u v : V} (p : G.Walk u v) :
 p.edges.length = p.length
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.mem_edgeFinset`：mem_edgeFinset : e in G.edgeFinset ↔ e in G.
edgeSet
· 使用定理 `SimpleGraph.Walk.edges_subset_edgeSet`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
-/
theorem IsTrail.length_le_card_edgeFinset [Fintype G.edgeSet] {u v : V}
    {w : G.Walk u v} (h : w.IsTrail) : w.length ≤ G.edgeFinset.card := by
  classical
  let edges := w.edges.toFinset
  have : edges.card = w.length := length_edges _ ▸ List.toFinset_card_of_nodup h.edges_nodup
  rw [← this]
  have : edges ⊆ G.edgeFinset := by
    intro e h
    refine mem_edgeFinset.mpr ?_
    apply w.edges_subset_edgeSet
    simpa [edges] using h
  exact Finset.card_le_card this
/-
**SimpleGraph.Walk.IsPath.nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsPath
`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V}, SimpleGraph.Walk.nil.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by constructor <;> simp
/-
**SimpleGraph.Walk.IsPath.of_cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Path`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {h : G.Adj u v} {p : G.Walk
 v w},   (SimpleGraph.Walk.cons h p).IsPath → p.IsPath
参数：SimpleGraph.Walk.cons h p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath → p.IsPath := by simp [isPath_def]

@[simp]
/-
**SimpleGraph.Walk.cons_isPath_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) : (cons h p).
IsPath ↔ p.IsPath ∧ u ∉ p.support
参数：h : G.Adj u v；p : G.Walk v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp +contextual [isPath_def]
/-
**SimpleGraph.Walk.IsPath.cons** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsPat
h`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk v w},   p.IsPat
h → u ∉ p.support → ∀ {h : G.Adj u v}, (SimpleGraph.Walk.cons h p).IsPath
参数：SimpleGraph.Walk.cons h p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.cons_isPath_iff`：cons_isPath_iff {u v w : V} (h : G.Adj
 u v) (p : G.Walk v w) : (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support
-/
protected lemma IsPath.cons {p : Walk G v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v} :
    (cons h p).IsPath :=
  (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
/-
**SimpleGraph.Walk.isPath_iff_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isPath_iff_nil {u : V} {p : G.Walk u u} : p.IsPath ↔ p.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem isPath_iff_nil {u : V} {p : G.Walk u u} : p.IsPath ↔ p.Nil := by
  cases p <;> simp [IsPath.nil]

@[deprecated isPath_iff_nil (since := "2026-06-01")]
/-
**SimpleGraph.Walk.isPath_iff_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：isPath_iff_eq_nil {u : V} {p : G.Walk u u} : p.IsPath ↔ p = nil
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
theorem isPath_iff_eq_nil {u : V} {p : G.Walk u u} : p.IsPath ↔ p = nil := by
  simp
/-
**SimpleGraph.Walk.IsPath.nil_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
(p.Nil ↔ u = v)
参数：p.Nil ↔ u = v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_iff_nil`：isPath_iff_nil {u : V} {p : G.Walk u u}
 : p.IsPath ↔ p.Nil
-/
theorem IsPath.nil_iff_eq {u v : V} {p : G.Walk u v} (hp : p.IsPath) : p.Nil ↔ u = v := by
  refine ⟨fun ⟨⟩ ↦ rfl, ?_⟩
  rintro rfl
  exact isPath_iff_nil.mp hp
/-
**SimpleGraph.Walk._root_.SimpleGraph.Adj.isPath_toWalk** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.Adj.isPath_toWalk (h : G.Adj u v) : h.toWalk.IsPath := by
  simp [h.ne]
/-
**SimpleGraph.Walk.IsPath.reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Path`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
p.reverse.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
-/
theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [isPath_def] using h

@[simp]
/-
**SimpleGraph.Walk.isPath_reverse_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPat
h
参数：p : G.Walk u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `SimpleGraph.Walk.IsPath.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.reverse.IsPath
-/
theorem isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert! h.reverse; simp
/-
**SimpleGraph.Walk.IsPath.of_append_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w}, (p.append q).IsPath → p.IsPath
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `List.Nodup.of_append_left`：∀ {α : Type u} {l₁ l₂ : List α}, (l₁ ++ l₂).N
odup → l₁.Nodup
-/
theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath → p.IsPath := by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left
/-
**SimpleGraph.Walk.IsPath.of_append_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w}, (p.append q).IsPath → q.IsPath
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.isPath_reverse_iff`：isPath_reverse_iff {u v : V} (p : G
.Walk u v) : p.reverse.IsPath ↔ p.IsPath
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_left`：∀ {V : Type u} {G : SimpleGraph 
V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → p.IsPath
· 使用定理 `SimpleGraph.Walk.reverse_append`：reverse_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) : (p.append q).reverse = q.reverse.append p.reverse
-/
theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left
/-
**SimpleGraph.Walk.isTrail_of_isSubwalk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk`。
形式化陈述：isTrail_of_isSubwalk {v w v' w'} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} (h 
: p₁.IsSubwalk p₂) (h₂ : p₂.IsTrail) : p₁.IsTrail
参数：h : p₁.IsSubwalk p₂；h₂ : p₂.IsTrail。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.of_append_right`：∀ {V : Type u} {G : SimpleGrap
h V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsTrail → q.IsT
rail
· 使用定理 `SimpleGraph.Walk.IsTrail.of_append_left`：∀ {V : Type u} {G : SimpleGraph
 V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsTrail → p.IsTr
ail
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isTrail_of_isSubwalk {v w v' w'} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
    (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsTrail) : p₁.IsTrail := by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right
/-
**SimpleGraph.Walk.isPath_of_isSubwalk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk`。
形式化陈述：isPath_of_isSubwalk {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} 
(h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) : p₁.IsPath
参数：h : p₁.IsSubwalk p₂；h₂ : p₂.IsPath。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_right`：∀ {V : Type u} {G : SimpleGraph
 V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → q.IsPat
h
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_left`：∀ {V : Type u} {G : SimpleGraph 
V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → p.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isPath_of_isSubwalk {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'}
    (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) : p₁.IsPath := by
  obtain ⟨_, _, h⟩ := h
  rw [h] at h₂
  exact h₂.of_append_left.of_append_right
/-
**SimpleGraph.Walk.IsPath.of_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsP
ath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (h : G.Adj u v), h.toWalk.IsP
ath
参数：h : G.Adj u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
-/
lemma IsPath.of_adj {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : h.toWalk.IsPath := by
  aesop
/-
**SimpleGraph.Walk.concat_isPath_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：concat_isPath_iff {p : G.Walk u v} (h : G.Adj v w) : (p.concat h).IsPath ↔
 p.IsPath ∧ w ∉ p.support
参数：h : G.Adj v w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.isPath_reverse_iff`：isPath_reverse_iff {u v : V} (p : G
.Walk u v) : p.reverse.IsPath ↔ p.IsPath
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `SimpleGraph.Walk.reverse_concat`：reverse_concat {u v w : V} (p : G.Walk 
u v) (h : G.Adj v w) : (p.concat h).reverse = cons h.symm p.reverse
· 使用定理 `List.mem_reverse`：∀ {α : Type u_1} {x : α} {as : List α}, x ∈ as.reverse
 ↔ x ∈ as
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
· 使用定理 `SimpleGraph.Walk.cons_isPath_iff`：cons_isPath_iff {u v w : V} (h : G.Adj
 u v) (p : G.Walk v w) : (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support
-/
theorem concat_isPath_iff {p : G.Walk u v} (h : G.Adj v w) :
    (p.concat h).IsPath ↔ p.IsPath ∧ w ∉ p.support := by
  rw [← (p.concat h).isPath_reverse_iff, ← p.isPath_reverse_iff, reverse_concat, ← List.mem_reverse,
    ← support_reverse]
  exact cons_isPath_iff h.symm p.reverse
/-
**SimpleGraph.Walk.IsPath.concat** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsP
ath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v},   p.IsPat
h → w ∉ p.support → ∀ (h : G.Adj v w), (p.concat h).IsPath
参数：h : G.Adj v w；p.concat h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.concat_isPath_iff`：concat_isPath_iff {p : G.Walk u v} (
h : G.Adj v w) : (p.concat h).IsPath ↔ p.IsPath ∧ w ∉ p.support
-/
theorem IsPath.concat {p : G.Walk u v} (hp : p.IsPath) (hw : w ∉ p.support)
    (h : G.Adj v w) : (p.concat h).IsPath :=
  (concat_isPath_iff h).mpr ⟨hp, hw⟩
/-
**SimpleGraph.Walk.IsPath.take_of_take** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {n k : ℕ} {p : G.Walk u v}, (
p.take k).IsPath → n ≤ k → (p.take n).IsPath
参数：p.take k；p.take n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isPath_of_isSubwalk`：isPath_of_isSubwalk {v w v' w' : V
} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) :
 p₁.IsPath
· 使用定理 `SimpleGraph.Walk.take_isSubwalk_take`：take_isSubwalk_take {u v n k} (p :
 G.Walk u v) (h : n <= k) : (p.take n).IsSubwalk (p.take k)
-/
lemma IsPath.take_of_take {n k} {p : G.Walk u v} (h : (p.take k).IsPath) (hle : n ≤ k) :
    (p.take n).IsPath :=
  isPath_of_isSubwalk (p.take_isSubwalk_take hle) h
/-
**SimpleGraph.Walk.IsPath.drop_of_drop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {n k : ℕ} {p : G.Walk u v}, (
p.drop k).IsPath → k ≤ n → (p.drop n).IsPath
参数：p.drop k；p.drop n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isPath_of_isSubwalk`：isPath_of_isSubwalk {v w v' w' : V
} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) :
 p₁.IsPath
· 使用定理 `SimpleGraph.Walk.drop_isSubwalk_drop`：drop_isSubwalk_drop {u v n k} (p :
 G.Walk u v) (h : n <= k) : (p.drop k).IsSubwalk (p.drop n)
-/
lemma IsPath.drop_of_drop {n k} {p : G.Walk u v} (h : (p.drop k).IsPath) (hle : k ≤ n) :
    (p.drop n).IsPath :=
  isPath_of_isSubwalk (p.drop_isSubwalk_drop hle) h
/-
**SimpleGraph.Walk.IsPath.take** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsPat
h`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
∀ (n : ℕ), (p.take n).IsPath
参数：n : ℕ；p.take n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isPath_of_isSubwalk`：isPath_of_isSubwalk {v w v' w' : V
} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) :
 p₁.IsPath
· 使用定理 `SimpleGraph.Walk.isSubwalk_take`：isSubwalk_take {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.take n).IsSubwalk p
-/
lemma IsPath.take {p : G.Walk u v} (h : p.IsPath) (n : ℕ) :
    (p.take n).IsPath :=
  isPath_of_isSubwalk (p.isSubwalk_take n) h
/-
**SimpleGraph.Walk.IsPath.drop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsPat
h`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
∀ (n : ℕ), (p.drop n).IsPath
参数：n : ℕ；p.drop n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isPath_of_isSubwalk`：isPath_of_isSubwalk {v w v' w' : V
} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) :
 p₁.IsPath
· 使用定理 `SimpleGraph.Walk.isSubwalk_drop`：isSubwalk_drop {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.drop n).IsSubwalk p
-/
lemma IsPath.drop {p : G.Walk u v} (h : p.IsPath) (n : ℕ) :
    (p.drop n).IsPath :=
  isPath_of_isSubwalk (p.isSubwalk_drop n) h
/-
**SimpleGraph.Walk.IsPath.mem_support_iff_exists_append** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v},   p.IsPat
h → (w ∈ p.support ↔ ∃ q r, q.IsPath ∧ r.IsPath ∧ p = q.append r)
参数：w ∈ p.support ↔ ∃ q r, q.IsPath ∧ r.IsPath ∧ p = q.append r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.mem_support_iff_exists_append`：mem_support_iff_exists_a
ppend {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} : w in p.sup
port ↔ exists (q : G.Walk u w) (r : …
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_left`：∀ {V : Type u} {G : SimpleGraph 
V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → p.IsPath
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_right`：∀ {V : Type u} {G : SimpleGraph
 V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → q.IsPat
h
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma IsPath.mem_support_iff_exists_append {p : G.Walk u v} (hp : p.IsPath) :
    w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), q.IsPath ∧ r.IsPath ∧ p = q.append r := by
  refine ⟨fun hw ↦ ?_, fun ⟨q, r, hq, hr, hqr⟩ ↦ p.mem_support_iff_exists_append.mpr ⟨q, r, hqr⟩⟩
  obtain ⟨q, r, hqr⟩ := p.mem_support_iff_exists_append.mp hw
  have : (q.append r).IsPath := hqr ▸ hp
  exact ⟨q, r, this.of_append_left, this.of_append_right, hqr⟩
/-
**SimpleGraph.Walk.IsPath.disjoint_support_of_append** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w},   (p.append q).IsPath → ¬q.Nil → p.support.Disjoint q.tail.support
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `List.disjoint_of_nodup_append`：disjoint_of_nodup_append {l₁ l₂ : List α}
 (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
-/
lemma IsPath.disjoint_support_of_append {p : G.Walk u v} {q : G.Walk v w}
    (hpq : (p.append q).IsPath) (hq : ¬q.Nil) : p.support.Disjoint q.tail.support := by
  have hpq' := hpq.support_nodup
  rw [support_append] at hpq'
  rw [support_tail_of_not_nil q hq]
  exact List.disjoint_of_nodup_append hpq'
/-
**SimpleGraph.Walk.IsPath.ne_of_mem_support_of_append** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Wal
k v w},   (p.append q).IsPath → ∀ {x y : V}, y ≠ v → x ∈ p.support → y ∈ q.suppo
rt → x ≠ y
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `SimpleGraph.Walk.nil_iff_support_eq`：nil_iff_support_eq {p : G.Walk v w}
 : p.Nil ↔ p.support = [v]
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `SimpleGraph.Walk.mem_support_iff`：mem_support_iff {u v w : V} (p : G.Wal
k u v) : w in p.support ↔ w = u ∨ w in p.support.tail
· 使用定理 `SimpleGraph.Walk.IsPath.disjoint_support_of_append`：∀ {V : Type u} {G : 
SimpleGraph V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w},   (p.append q).IsP
ath → ¬q.Nil → p.support.Disjoint q.tail…
-/
lemma IsPath.ne_of_mem_support_of_append {p : G.Walk u v} {q : G.Walk v w}
    (hpq : (p.append q).IsPath) {x y : V} (hyv : y ≠ v) (hx : x ∈ p.support) (hy : y ∈ q.support) :
    x ≠ y := by
  rintro rfl
  have hq : ¬q.Nil := by
    intro hq
    simp [nil_iff_support_eq.mp hq, hyv] at hy
  have hx' : x ∈ q.tail.support := by
    rw [support_tail_of_not_nil q hq]
    rw [mem_support_iff] at hy
    exact hy.resolve_left hyv
  exact IsPath.disjoint_support_of_append hpq hq hx hx'

@[simp]
/-
**SimpleGraph.Walk.not_isCircuit_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
`。
形式化陈述：not_isCircuit_nil {u : V} : ¬(nil : G.Walk u u).IsCircuit
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_nil`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → p ≠ SimpleGraph.Walk.nil
-/
theorem not_isCircuit_nil {u : V} : ¬(nil : G.Walk u u).IsCircuit :=
  (·.ne_nil rfl)

@[simp]
/-
**SimpleGraph.Walk.not_isCycle_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：not_isCycle_nil {u : V} : ¬(nil : G.Walk u u).IsCycle
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.ne_nil`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {p : G.Walk u u}, p.IsCircuit → p ≠ SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
-/
theorem not_isCycle_nil {u : V} : ¬(nil : G.Walk u u).IsCycle :=
  (·.ne_nil rfl)

@[deprecated (since := "2026-06-16")] alias IsCycle.not_of_nil := not_isCycle_nil
/-
**SimpleGraph.Walk.IsCircuit.ne_bot** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsCircuit`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCircuit →
 G ≠ ⊥
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma IsCircuit.ne_bot : ∀ {p : G.Walk u u}, p.IsCircuit → G ≠ ⊥
  | cons h _, hp => by rintro rfl; exact h
/-
**SimpleGraph.Walk.IsCircuit.three_le_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk.IsCircuit`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} {p : G.Walk v v}, p.IsCircuit →
 3 ≤ p.length
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `SimpleGraph.Walk.IsCircuit.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCircuit → p.IsTrail
-/
lemma IsCircuit.three_le_length {p : G.Walk v v} (hp : p.IsCircuit) : 3 ≤ p.length := by
  match p with
  | .cons hadj .nil => simp at hadj
  | .cons _ <| .cons _ .nil => simpa using hp.isTrail
  | .cons _ <| .cons _ <| .cons _ _ => grind [length_cons]
/-
**SimpleGraph.Walk.not_nil_of_isCycle_cons** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：not_nil_of_isCycle_cons {p : G.Walk u v} {h : G.Adj v u} (hc : (Walk.cons 
h p).IsCycle) : ¬ p.Nil
参数：hc : (Walk.cons h p).IsCycle。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma not_nil_of_isCycle_cons {p : G.Walk u v} {h : G.Adj v u} (hc : (Walk.cons h p).IsCycle) :
    ¬ p.Nil := by
  grind [not_nil_iff_lt_length, hc.three_le_length, length_cons]
/-
**SimpleGraph.Walk.cons_isCycle_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) : (Walk.cons h
 p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges
参数：p : G.Walk v u；h : G.Adj u v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_nodup_of_support_nodup`：edges_nodup_of_support_no
dup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.edges.Nodup
· 使用定理 `Decidable.not_or_of_imp`：∀ {a b : Prop} [Decidable a], (a → b) → ¬a ∨ b
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges := by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup → p.edges.Nodup := edges_nodup_of_support_nodup
  tauto
/-
**SimpleGraph.Walk.IsCycle.nodup_dropLast_support** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → p
.support.dropLast.Nodup
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `SimpleGraph.Walk.tail_support_perm_dropLast_support`：tail_support_perm_d
ropLast_support (p : G.Walk u u) : p.support.tail ~ p.support.dropLast
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
-/
theorem IsCycle.nodup_dropLast_support {p : G.Walk u u} (h : p.IsCycle) :
    p.support.dropLast.Nodup :=
  p.tail_support_perm_dropLast_support.nodup_iff.mp h.support_nodup
/-
**SimpleGraph.Walk.IsCycle.reverse** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → p
.reverse.IsCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.IsTrail.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} (p : G.Walk u v), p.IsTrail → p.reverse.IsTrail
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
-/
protected lemma IsCycle.reverse {p : G.Walk u u} (h : p.IsCycle) : p.reverse.IsCycle := by
  simp only [Walk.isCycle_def, nodup_tail_support_reverse] at h ⊢
  exact ⟨h.1.reverse, fun h' ↦ h.2.1 (by simp_all [← Walk.length_eq_zero_iff]), h.2.2⟩

@[simp]
/-
**SimpleGraph.Walk.isCycle_reverse** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isCycle_reverse {p : G.Walk u u} : p.reverse.IsCycle ↔ p.IsCycle where mp 
h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.reverse_reverse`：reverse_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.reverse = p
· 使用定理 `SimpleGraph.Walk.IsCycle.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V} {p : G.Walk u u}, p.IsCycle → p.reverse.IsCycle
-/
lemma isCycle_reverse {p : G.Walk u u} : p.reverse.IsCycle ↔ p.IsCycle where
  mp h := by simpa using h.reverse
  mpr := .reverse
/-
**SimpleGraph.Walk.IsCycle.isPath_of_append_right** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk 
v u}, ¬p.Nil → (p.append q).IsCycle → q.IsPath
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isPath_def`：isPath_def {u v : V} (p : G.Walk u v) : p.I
sPath ↔ p.support.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.cons_tail_support`：cons_tail_support (p : G.Walk u v) :
 u :: p.support.tail = p.support
· 使用定理 `List.nodup_cons`：∀ {α : Type u_1} {a : α} {l : List α}, (a :: l).Nodup ↔
 a ∉ l ∧ l.Nodup
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `List.nodup_append'`：nodup_append' {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ 
Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂
· 使用定理 `SimpleGraph.Walk.tail_support_append`：tail_support_append {u v w : V} (p
 : G.Walk u v) (p' : G.Walk v w) : (p.append p').support.tail = p.support.tail +
+ p'.support.tail
· 使用定理 `SimpleGraph.Walk.end_mem_tail_support`：end_mem_tail_support {u v : V} {p
 : G.Walk u v} (h : ¬ p.Nil) : v in p.support.tail
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma IsCycle.isPath_of_append_right {p : G.Walk u v} {q : G.Walk v u} (h : ¬ p.Nil)
    (hcyc : (p.append q).IsCycle) : q.IsPath := by
  have := hcyc.2
  rw [tail_support_append, List.nodup_append'] at this
  rw [isPath_def, ← cons_tail_support, List.nodup_cons]
  exact ⟨this.2.2 (p.end_mem_tail_support h), this.2.1⟩
/-
**SimpleGraph.Walk.IsCycle.isPath_of_append_left** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk 
v u}, ¬q.Nil → (p.append q).IsCycle → p.IsPath
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_reverse_iff`：isPath_reverse_iff {u v : V} (p : G
.Walk u v) : p.reverse.IsPath ↔ p.IsPath
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_of_append_right`：∀ {V : Type u} {G : Sim
pleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk v u}, ¬p.Nil → (p.append q).I
sCycle → q.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.IsCycle.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V} {p : G.Walk u u}, p.IsCycle → p.reverse.IsCycle
· 使用定理 `SimpleGraph.Walk.reverse_append`：reverse_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) : (p.append q).reverse = q.reverse.append p.reverse
-/
lemma IsCycle.isPath_of_append_left {p : G.Walk u v} {q : G.Walk v u} (h : ¬ q.Nil)
    (hcyc : (p.append q).IsCycle) : p.IsPath :=
  p.isPath_reverse_iff.mp ((reverse_append _ _ ▸ hcyc.reverse).isPath_of_append_right (by simpa))
/-
**SimpleGraph.Walk.IsCycle.isPath_tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → p
.tail.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.mk'`：∀ {V : Type u} {G : SimpleGraph V} {u v : V
} {p : G.Walk u v}, p.support.Nodup → p.IsPath
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.support_tail_of_not_nil`：support_tail_of_not_nil (p : G
.Walk u v) (hp : ¬ p.Nil) : p.tail.support = p.support.tail
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
-/
theorem IsCycle.isPath_tail {p : G.Walk u u} (h : p.IsCycle) : p.tail.IsPath :=
  IsPath.mk' <| p.support_tail_of_not_nil h.not_nil ▸ h.support_nodup
/-
**SimpleGraph.Walk.IsPath.tail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsPat
h`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
p.tail.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma IsPath.tail {p : G.Walk u v} (hp : p.IsPath) : p.tail.IsPath := by
  cases p with
  | nil => simp
  | cons hadj p =>
    simp_all [Walk.isPath_def]
/-
**SimpleGraph.Walk.IsCycle.isPath_dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → p
.dropLast.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.mk'`：∀ {V : Type u} {G : SimpleGraph V} {u v : V
} {p : G.Walk u v}, p.support.Nodup → p.IsPath
· 使用定理 `SimpleGraph.Walk.IsCycle.nodup_dropLast_support`：∀ {V : Type u} {G : Sim
pleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.dropLast.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.support_dropLast`：support_dropLast {p : G.Walk u v} (hp
 : ¬p.Nil) : p.dropLast.support = p.support.dropLast
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
-/
theorem IsCycle.isPath_dropLast {p : G.Walk u u} (h : p.IsCycle) : p.dropLast.IsPath :=
  .mk' <| p.support_dropLast h.not_nil ▸ h.nodup_dropLast_support
/-
**SimpleGraph.Walk.IsPath.dropLast** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
p.dropLast.IsPath
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.take`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} {p : G.Walk u v}, p.IsPath → ∀ (n : ℕ), (p.take n).IsPath
-/
theorem IsPath.dropLast (hp : p.IsPath) : p.dropLast.IsPath :=
  hp.take _
/-
**SimpleGraph.Walk.IsCycle.isPath_drop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {n : ℕ} {p : G.Walk u u}, p.IsC
ycle → 0 < n → (p.drop n).IsPath
参数：p.drop n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_tail`：∀ {V : Type u} {G : SimpleGraph V}
 {u : V} {p : G.Walk u u}, p.IsCycle → p.tail.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用引理 `SimpleGraph.Walk.drop_getVert`：drop_getVert (p : G.Walk u v) (n m : Nat)
 : (p.drop n).getVert m = p.getVert (n + m)
· 使用引理 `SimpleGraph.Walk.drop_add_eq`：drop_add_eq (p : G.Walk u v) (n m : Nat) :
 p.drop (n + m) = ((p.drop n).drop m).copy (drop_getVert ..) rfl
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `SimpleGraph.Walk.IsPath.drop`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} {p : G.Walk u v}, p.IsPath → ∀ (n : ℕ), (p.drop n).IsPath
-/
theorem IsCycle.isPath_drop {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : 0 < n) :
    (p.drop n).IsPath := by
  replace h : (p.drop 1).IsPath := h.isPath_tail
  rw [← Nat.add_sub_of_le hn, drop_add_eq]
  simp [h.drop (n - 1), -drop_drop]
/-
**SimpleGraph.Walk.IsCycle.isPath_take** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wa
lk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {n : ℕ} {p : G.Walk u u}, p.IsC
ycle → n < p.length → (p.take n).IsPath
参数：p.take n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_dropLast`：∀ {V : Type u} {G : SimpleGrap
h V} {u : V} {p : G.Walk u u}, p.IsCycle → p.dropLast.IsPath
· 使用定理 `SimpleGraph.Walk.IsPath.take`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} {p : G.Walk u v}, p.IsPath → ∀ (n : ℕ), (p.take n).IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.take_getVert`：take_getVert (p : G.Walk u v) (n m : Nat)
 : (p.take n).getVert m = p.getVert (n ⊓ m)
· 使用定理 `SimpleGraph.Walk.isPath_copy`：isPath_copy {u v u' v'} (p : G.Walk u v) (
hu : u = u') (hv : v = v') : (p.copy hu hv).IsPath ↔ p.IsPath
· 使用引理 `SimpleGraph.Walk.take_take`：take_take (p : G.Walk u v) (n m : Nat) : (p.
take n).take m = (p.take (min n m)).copy rfl (p.take_getVert n m).symm
-/
theorem IsCycle.isPath_take {u n} {p : G.Walk u u} (h : p.IsCycle) (hn : n < p.length) :
    (p.take n).IsPath := by
  replace h : (p.take (p.length - 1)).IsPath := h.isPath_dropLast
  suffices ((p.take (p.length - 1)).take n).IsPath by
    rwa [take_take, isPath_copy, show min (p.length - 1) n = n by omega] at this
  exact h.take n

/-- There exists a trail of maximal length in a non-empty graph on finite edges. -/
/-
**SimpleGraph.Walk.exists_isTrail_forall_isTrail_length_le_length** 是 Mathlib 中的
一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：exists_isTrail_forall_isTrail_length_le_length (G : SimpleGraph V) [N : No
nempty V] [Finite G.edgeSet] : exists (u v : V) (p : G.Walk u v) (_ : p.IsTrail)
, forall (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsTrail), p'.length <= p.length
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `SimpleGraph.Walk.IsTrail.length_le_card_edgeFinset`：∀ {V : Type u} {G : 
SimpleGraph V} [inst : Fintype ↑G.edgeSet] {u v : V} {w : G.Walk u v},   w.IsTra
il → w.length ≤ G.edgeFinset.card
· 使用定理 `Set.Finite.exists_maximal`：∀ {α : Type u_2} [inst : LE α] [IsTrans α LE.
le] {s : Set α}, s.Finite → s.Nonempty → ∃ i, Maximal (fun x => x ∈ s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
There exists a trail of maximal length in a non-empty graph on finite edges.
-/
lemma exists_isTrail_forall_isTrail_length_le_length (G : SimpleGraph V) [N : Nonempty V]
    [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v) (_ : p.IsTrail),
      ∀ (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsTrail), p'.length ≤ p.length := by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | ∃ (u v : V) (p : G.Walk u v), p.IsTrail ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ ↦ hn ▸ hp.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ := this.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' ↦ ?_⟩
  have := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  lia

/-- There exists a path of maximal length in a non-empty graph on finite edges. -/
/-
**SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length** 是 Mathlib 中的一个
引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：exists_isPath_forall_isPath_length_le_length (G : SimpleGraph V) [N : None
mpty V] [Finite G.edgeSet] : exists (u v : V) (p : G.Walk u v) (_ : p.IsPath), f
orall (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsPath), p'.length <= p.length
参数：G : SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `SimpleGraph.Walk.IsTrail.length_le_card_edgeFinset`：∀ {V : Type u} {G : 
SimpleGraph V} [inst : Fintype ↑G.edgeSet] {u v : V} {w : G.Walk u v},   w.IsTra
il → w.length ≤ G.edgeFinset.card
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `Set.Finite.exists_maximal`：∀ {α : Type u_2} [inst : LE α] [IsTrans α LE.
le] {s : Set α}, s.Finite → s.Nonempty → ∃ i, Maximal (fun x => x ∈ s) i
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
There exists a path of maximal length in a non-empty graph on finite edges.
-/
lemma exists_isPath_forall_isPath_length_le_length (G : SimpleGraph V) [N : Nonempty V]
    [Finite G.edgeSet] :
    ∃ (u v : V) (p : G.Walk u v) (_ : p.IsPath),
      ∀ (u' v' : V) (p' : G.Walk u' v') (_ : p'.IsPath), p'.length ≤ p.length := by
  have := Fintype.ofFinite G.edgeSet
  let s := {n | ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ p.length = n}
  have : s.Finite := Set.Finite.subset (Set.finite_le_nat G.edgeFinset.card)
    fun n ⟨_, _, _, hp, hn⟩ ↦ hn ▸ hp.isTrail.length_le_card_edgeFinset
  obtain ⟨x⟩ := N
  obtain ⟨_, ⟨⟨u, v, p, hp, _⟩, hn⟩⟩ := this.exists_maximal ⟨0, ⟨x, x, Walk.nil, by simp⟩⟩
  refine ⟨u, v, p, hp, fun u' v' p' hp' ↦ ?_⟩
  have := hn ⟨u', v', p', hp', Eq.refl p'.length⟩
  lia

/-! ### About paths -/

/-
**SimpleGraph.Walk.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph.Walk`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### About paths
-/
instance [DecidableEq V] {u v : V} (p : G.Walk u v) : Decidable p.IsPath := by
  rw [isPath_def]
  infer_instance
/-
**SimpleGraph.Walk.IsPath.length_lt** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : Fintype V] {u v : V} {p : G.Wal
k u v}, p.IsPath → p.length < Fintype.card V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_iff_add_one_le`：∀ {m n : ℕ}, m < n ↔ m + 1 ≤ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `List.Nodup.length_le_card`：List.Nodup.length_le_card {α : Type*} [Fintyp
e α] {l : List α} (h : l.Nodup) : l.length <= Fintype.card α
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
-/
theorem IsPath.length_lt [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  rw [Nat.lt_iff_add_one_le, ← length_support]
  exact hp.support_nodup.length_le_card
/-
**SimpleGraph.Walk.IsPath.getVert_injOn** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
Set.InjOn p.getVert {i | i ≤ p.length}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.getVert_cons`：getVert_cons {u v w n} (p : G.Walk v w) (
h : G.Adj u v) (hn : n != 0) : (p.cons h).getVert n = p.getVert (n - 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.mem_support_iff_exists_getVert`：mem_support_iff_exists_
getVert {u v w : V} {p : G.Walk v w} : u in p.support ↔ exists n, p.getVert n = 
u ∧ n <= p.length
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `SimpleGraph.Walk.IsPath.of_cons`：∀ {V : Type u} {G : SimpleGraph V} {u v
 w : V} {h : G.Adj u v} {p : G.Walk v w},   (SimpleGraph.Walk.cons h p).IsPath →
 p.IsPath
-/
lemma IsPath.getVert_injOn {p : G.Walk u v} (hp : p.IsPath) :
    Set.InjOn p.getVert {i | i ≤ p.length} := by
  intro n hn m hm hnm
  induction p generalizing n m with
  | nil => simp_all
  | @cons v w u h p ihp =>
    simp only [length_cons, Set.mem_ofPred_eq] at hn hm hnm
    by_cases hn0 : n = 0 <;> by_cases hm0 : m = 0
    · lia
    · simp only [hn0, getVert_zero, Walk.getVert_cons p h hm0] at hnm
      have hvp : v ∉ p.support := by aesop
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(m - 1), ⟨hnm.symm, by lia⟩⟩)).elim
    · simp only [hm0, Walk.getVert_cons p h hn0] at hnm
      have hvp : v ∉ p.support := by simp_all
      exact (hvp (Walk.mem_support_iff_exists_getVert.mpr ⟨(n - 1), ⟨hnm, by lia⟩⟩)).elim
    · simp only [Walk.getVert_cons _ _ hn0, Walk.getVert_cons _ _ hm0] at hnm
      have := ihp hp.of_cons (by lia : (n - 1) ≤ p.length)
        (by lia : (m - 1) ≤ p.length) hnm
      lia
/-
**SimpleGraph.Walk.IsPath.getVert_eq_start_iff_of_not_nil** 是 Mathlib 中的一个定理，位于命
名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u w : V} {i : ℕ} {p : G.Walk u w}, p.I
sPath → ¬p.Nil → (p.getVert i = u ↔ i = 0)
参数：p.getVert i = u ↔ i = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Walk.getVert_of_length_le`：getVert_of_length_le {u v} (w : G
.Walk u v) {i : Nat} (hi : w.length <= i) : w.getVert i = v
· 使用定理 `le_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b 
→ b ≤ a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma IsPath.getVert_eq_start_iff_of_not_nil {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (h : ¬p.Nil) :
    p.getVert i = u ↔ i = 0 := by
  refine ⟨fun h ↦ ?_, by simp_all⟩
  by_cases h' : i ≤ p.length
  · apply hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by rw [Set.mem_ofPred]; lia)
    simp [h]
  · rw [p.getVert_of_length_le (le_of_not_ge h')] at h
    subst h
    simp_all
/-
**SimpleGraph.Walk.IsPath.getVert_eq_start_iff** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u w : V} {i : ℕ} {p : G.Walk u w},   p
.IsPath → i ≤ p.length → (p.getVert i = u ↔ i = 0)
参数：p.getVert i = u ↔ i = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_eq_start_iff_of_not_nil`：∀ {V : Type u} 
{G : SimpleGraph V} {u w : V} {i : ℕ} {p : G.Walk u w}, p.IsPath → ¬p.Nil → (p.g
etVert i = u ↔ i = 0)
· 使用定理 `SimpleGraph.Walk.not_nil_cons`：∀ {V : Type u} {G : SimpleGraph V} {u v w
 : V} {h : G.Adj u v} {p : G.Walk v w}, ¬(SimpleGraph.Walk.cons h p).Nil
-/
lemma IsPath.getVert_eq_start_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 := by
  cases p
  · simpa using hi
  · exact hp.getVert_eq_start_iff_of_not_nil not_nil_cons
/-
**SimpleGraph.Walk.IsPath.getVert_eq_end_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u w : V} {i : ℕ} {p : G.Walk u w},   p
.IsPath → i ≤ p.length → (p.getVert i = w ↔ i = p.length)
参数：p.getVert i = w ↔ i = p.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_eq_start_iff`：∀ {V : Type u} {G : Simple
Graph V} {u w : V} {i : ℕ} {p : G.Walk u w},   p.IsPath → i ≤ p.length → (p.getV
ert i = u ↔ i = 0)
· 使用定理 `SimpleGraph.Walk.IsPath.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.reverse.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `SimpleGraph.Walk.getVert_reverse`：getVert_reverse {u v : V} (p : G.Walk 
u v) (i : Nat) : p.reverse.getVert i = p.getVert (p.length - i)
-/
lemma IsPath.getVert_eq_end_iff {i : ℕ} {p : G.Walk u w} (hp : p.IsPath) (hi : i ≤ p.length) :
    p.getVert i = w ↔ i = p.length := by
  have := hp.reverse.getVert_eq_start_iff (by lia : p.reverse.length - i ≤ p.reverse.length)
  simp only [length_reverse, getVert_reverse, show p.length - (p.length - i) = i by lia] at this
  rw [this]
  lia
/-
**SimpleGraph.Walk.IsPath.getVert_injOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Walk u v), Set.InjOn p
.getVert {i | i ≤ p.length} ↔ p.IsPath
参数：p : G.Walk u v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `SimpleGraph.Walk.cons_isPath_iff`：cons_isPath_iff {u v w : V} (h : G.Adj
 u v) (p : G.Walk v w) : (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support
· 使用定理 `SimpleGraph.Walk.length_cons`：length_cons {u v w : V} (h : G.Adj u v) (p
 : G.Walk v w) : (cons h p).length = p.length + 1
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.mem_support_iff_exists_getVert`：mem_support_iff_exists_
getVert {u v w : V} {p : G.Walk v w} : u in p.support ↔ exists n, p.getVert n = 
u ∧ n <= p.length
· 使用引理 `SimpleGraph.Walk.getVert_cons`：getVert_cons {u v w n} (p : G.Walk v w) (
h : G.Adj u v) (hn : n != 0) : (p.cons h).getVert n = p.getVert (n - 1)
· 使用定理 `Nat.add_one_ne_zero`：∀ (n : ℕ), n + 1 ≠ 0
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
-/
lemma IsPath.getVert_injOn_iff (p : G.Walk u v) : Set.InjOn p.getVert {i | i ≤ p.length} ↔
    p.IsPath := by
  refine ⟨?_, fun a => a.getVert_injOn⟩
  induction p with
  | nil => simp
  | cons h q ih =>
    intro hinj
    rw [cons_isPath_iff]
    refine ⟨ih (by
      intro n hn m hm hnm
      simp only [Set.mem_ofPred_eq] at hn hm
      have := hinj
        (by rw [length_cons]; lia : n + 1 ≤ (q.cons h).length)
        (by rw [length_cons]; lia : m + 1 ≤ (q.cons h).length)
        (by simpa [getVert_cons] using hnm)
      lia), fun h' => ?_⟩
    obtain ⟨n, ⟨hn, hnl⟩⟩ := mem_support_iff_exists_getVert.mp h'
    have := hinj
      (by rw [length_cons]; lia : (n + 1) ≤ (q.cons h).length)
      (by lia : 0 ≤ (q.cons h).length)
      (by rwa [getVert_cons _ _ n.add_one_ne_zero, getVert_zero])
    lia
/-
**SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v}, p.IsPath 
→ s(u, w) ∈ p.edges → w = p.snd
参数：u, w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用引理 `SimpleGraph.Walk.edges_eq_nil`：edges_eq_nil {p : G.Walk v w} : p.edges =
 [] ↔ p.Nil
· 使用定理 `List.ne_nil_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → l ≠ [
]
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `SimpleGraph.Walk.support_copy`：support_copy {u v u' v'} (p : G.Walk u v)
 (hu : u = u') (hv : v = v') : (p.copy hu hv).support = p.support
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Sym2.rel_iff'`：rel_iff' {p q : α × α} : Rel α p q ↔ p = q ∨ p = q.swap
· 使用定理 `Sym2.eq`：∀ {α : Type u_1} {a b c d : α}, s(a, b) = s(c, d) ↔ Sym2.Rel α 
(a, b) (c, d)
· 使用定理 `List.mem_cons`：∀ {α : Type u_1} {b : α} {l : List α} {a : α}, a ∈ b :: l
 ↔ a = b ∨ a ∈ l
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Walk.edges_cons`：edges_cons {u v w : V} (h : G.Adj u v) (p :
 G.Walk v w) : (cons h p).edges = s(u, v) :: p.edges
· 使用引理 `SimpleGraph.Walk.cons_tail_eq`：cons_tail_eq (p : G.Walk u v) (hp : ¬ p.N
il) : cons (p.adj_snd hp) p.tail = p
-/
theorem IsPath.eq_snd_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (hmem : s(u, w) ∈ p.edges) :
    w = p.snd := by
  have hnil := edges_eq_nil.not.mp <| List.ne_nil_of_mem hmem
  rw [← cons_tail_eq _ hnil, edges_cons, List.mem_cons, Sym2.eq, Sym2.rel_iff'] at hmem
  have : u ∉ p.tail.support := by induction p <;> simp_all
  grind [fst_mem_support_of_mem_edges]
/-
**SimpleGraph.Walk.IsPath.eq_penultimate_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v w : V} {p : G.Walk u v}, p.IsPath 
→ s(v, w) ∈ p.edges → w = p.penultimate
参数：v, w。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.edges_reverse`：edges_reverse {u v : V} (p : G.Walk u v)
 : p.reverse.edges = p.edges.reverse
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `SimpleGraph.Walk.snd_reverse`：snd_reverse (p : G.Walk u v) : p.reverse.s
nd = p.penultimate
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SimpleGraph.Walk.IsPath.eq_snd_of_mem_edges`：∀ {V : Type u} {G : SimpleG
raph V} {u v w : V} {p : G.Walk u v}, p.IsPath → s(u, w) ∈ p.edges → w = p.snd
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.isPath_reverse_iff`：isPath_reverse_iff {u v : V} (p : G
.Walk u v) : p.reverse.IsPath ↔ p.IsPath
-/
theorem IsPath.eq_penultimate_of_mem_edges {p : G.Walk u v} (hp : p.IsPath)
    (hmem : s(v, w) ∈ p.edges) : w = p.penultimate := by
  simpa [hmem] using isPath_reverse_iff p |>.mpr hp |>.eq_snd_of_mem_edges (w := w)
/-
**SimpleGraph.Walk.IsPath.injOn_support_of_isPath_map** 是 Mathlib 中的一个定理，位于命名空间 
`SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {u 
v : V} {p : G.Walk u v} {f : G →g G'},   (SimpleGraph.Walk.map f p).IsPath → Set
.InjOn ⇑f {w | w ∈ p.support}
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.get_of_mem`：∀ {α : Type u_1} {a : α} {l : List α}, a ∈ l → ∃ n, l.g
et n = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `List.nodup_iff_injective_getElem`：nodup_iff_injective_getElem {l : List 
α} : Nodup l ↔ Function.Injective (fun i : Fin l.length => l[i.1])
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.length_map`：∀ {α : Type u_1} {β : Type u_2} {as : List α} (f : α → 
β), (List.map f as).length = as.length
· 使用定理 `Mathlib.Tactic.DepRewrite.eq_of_heq`：eq_of_heq.{u} {α : Sort u} {a a' : 
α} (h : a ≍ a') : a = a'
· 使用定理 `Mathlib.Tactic.DepRewrite.hdcongrArg`：hdcongrArg.{u, v} {α : Sort u} {a 
a' : α} {β : (a' : α) -> a = a' -> Sort v} (h : a = a') (f : (a' : α) -> (h : a 
= a') -> β a' h) : f a rfl…
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.getElem_map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l : List 
α} {i : ℕ} {h : i < (List.map f l).length},   (List.map f l)[i] = f l[i]
-/
theorem IsPath.injOn_support_of_isPath_map (h : (p.map f).IsPath) :
    Set.InjOn f {w | w ∈ p.support} := by
  intro u hu v hv hf
  obtain ⟨u, rfl⟩ := List.get_of_mem hu
  obtain ⟨v, rfl⟩ := List.get_of_mem hv
  congr
  have := List.nodup_iff_injective_getElem.mp h.support_nodup
  rw! (castMode := .all) [support_map, List.length_map] at this
  apply this
  simpa

/-! ### About cycles -/

-- TODO: These results could possibly be less laborious with a periodic function getCycleVert
/-
**SimpleGraph.Walk.IsCycle.getVert_injOn** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → S
et.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.length}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.adj_snd`：∀ {V : Type u} {G : SimpleGraph V} {v w : V} {
p : G.Walk v w}, ¬p.Nil → G.Adj v p.snd
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `SimpleGraph.Walk.cons_isCycle_iff`：cons_isCycle_iff {u v : V} (p : G.Wal
k v u) (h : G.Adj u v) : (Walk.cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SimpleGraph.Walk.cons_tail_eq`：cons_tail_eq (p : G.Walk u v) (hp : ¬ p.N
il) : cons (p.adj_snd hp) p.tail = p
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用引理 `SimpleGraph.Walk.length_tail_add_one`：length_tail_add_one {p : G.Walk u 
v} (hp : ¬ p.Nil) : p.tail.length + 1 = p.length
· 使用引理 `SimpleGraph.Walk.not_nil_of_tail_not_nil`：not_nil_of_tail_not_nil {p : G
.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil
· 使用引理 `SimpleGraph.Walk.not_nil_of_isCycle_cons`：not_nil_of_isCycle_cons {p : G
.Walk u v} {h : G.Adj v u} (hc : (Walk.cons h p).IsCycle) : ¬ p.Nil
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SimpleGraph.Walk.getVert_tail`：∀ {V : Type u} {G : SimpleGraph V} {u v :
 V} {n : ℕ} (p : G.Walk u v), p.tail.getVert n = p.getVert (n + 1)
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.length_tail`：length_tail (p : G.Walk u v) : p.tail.leng
th = p.length - 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCycle.getVert_injOn {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.length} := by
  rw [← p.cons_tail_eq hpc.not_nil] at hpc
  intro n hn m hm hnm
  rw [← SimpleGraph.Walk.length_tail_add_one
    (p.not_nil_of_tail_not_nil (not_nil_of_isCycle_cons hpc)), Set.mem_ofPred] at hn hm
  have := ((Walk.cons_isCycle_iff _ _).mp hpc).1.getVert_injOn
    (by lia : n - 1 ≤ p.tail.length) (by lia : m - 1 ≤ p.tail.length)
    (by simp_all)
  lia
/-
**SimpleGraph.Walk.IsCycle.getVert_injOn'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → S
et.InjOn p.getVert {i | i ≤ p.length - 1}
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.
length}
· 使用定理 `SimpleGraph.Walk.IsCycle.reverse`：∀ {V : Type u} {G : SimpleGraph V} {u 
: V} {p : G.Walk u u}, p.IsCycle → p.reverse.IsCycle
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Walk.length_reverse`：length_reverse {u v : V} (p : G.Walk u 
v) : p.reverse.length = p.length
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.getVert_reverse`：getVert_reverse {u v : V} (p : G.Walk 
u v) (i : Nat) : p.reverse.getVert i = p.getVert (p.length - i)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCycle.getVert_injOn' {p : G.Walk u u} (hpc : p.IsCycle) :
    Set.InjOn p.getVert {i |  i ≤ p.length - 1} := by
  intro n hn m hm hnm
  simp only [Set.mem_ofPred_eq] at *
  have := hpc.three_le_length
  have : p.length - n = p.length - m := Walk.length_reverse _ ▸ hpc.reverse.getVert_injOn
    (by simp only [Walk.length_reverse, Set.mem_ofPred_eq]; lia)
    (by simp only [Walk.length_reverse, Set.mem_ofPred_eq]; lia)
    (by simp [Walk.getVert_reverse, show p.length - (p.length - n) = n by lia, hnm,
      show p.length - (p.length - m) = m by lia])
  lia
/-
**SimpleGraph.Walk.IsCycle.snd_ne_penultimate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {p : G.Walk u u}, p.IsCycle → p
.snd ≠ p.penultimate
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.
length}
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma IsCycle.snd_ne_penultimate {p : G.Walk u u} (hp : p.IsCycle) : p.snd ≠ p.penultimate := by
  intro h
  have := hp.three_le_length
  apply hp.getVert_injOn (by simp; lia) (by simp; lia) at h
  lia
/-
**SimpleGraph.Walk.IsCycle.getVert_endpoint_iff** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {i : ℕ} {p : G.Walk u u},   p.I
sCycle → i ≤ p.length → (p.getVert i = u ↔ i = 0 ∨ i = p.length)
参数：p.getVert i = u ↔ i = 0 ∨ i = p.length。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → Set.InjOn p.getVert {i | 1 ≤ i ∧ i ≤ p.
length}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsCycle.getVert_endpoint_iff {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle) (hl : i ≤ p.length) :
    p.getVert i = u ↔ i = 0 ∨ i = p.length := by
  refine ⟨?_, by aesop⟩
  rw [or_iff_not_imp_left]
  intro h hi
  exact hpc.getVert_injOn (by simp only [Set.mem_ofPred_eq]; lia)
    (by simp only [Set.mem_ofPred_eq]; lia) (h.symm ▸ (Walk.getVert_length p).symm)
/-
**SimpleGraph.Walk.IsCycle.getVert_sub_one_ne_getVert_add_one** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {i : ℕ} {p : G.Walk u u},   p.I
sCycle → i ≤ p.length → p.getVert (i - 1) ≠ p.getVert (i + 1)
参数：i - 1；i + 1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_endpoint_iff`：∀ {V : Type u} {G : Simpl
eGraph V} {u : V} {i : ℕ} {p : G.Walk u u},   p.IsCycle → i ≤ p.length → (p.getV
ert i = u ↔ i = 0 ∨ i = p.length)
· 使用定理 `SimpleGraph.Walk.getVert_of_length_le`：getVert_of_length_le {u v} (w : G
.Walk u v) {i : Nat} (hi : w.length <= i) : w.getVert i = v
· 使用定理 `SimpleGraph.Walk.IsCycle.getVert_injOn'`：∀ {V : Type u} {G : SimpleGraph
 V} {u : V} {p : G.Walk u u}, p.IsCycle → Set.InjOn p.getVert {i | i ≤ p.length 
- 1}
-/
lemma IsCycle.getVert_sub_one_ne_getVert_add_one {i : ℕ} {p : G.Walk u u} (hpc : p.IsCycle)
    (h : i ≤ p.length) : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
  intro h'
  have hl := hpc.three_le_length
  by_cases hi' : i ≥ p.length - 1
  · rw [p.getVert_of_length_le (by lia : p.length ≤ i + 1),
      hpc.getVert_endpoint_iff (by lia)] at h'
    lia
  have := hpc.getVert_injOn' (by simp only [Set.mem_ofPred_eq, Nat.sub_le_iff_le_add]; lia)
    (by simp only [Set.mem_ofPred_eq]; lia) h'
  lia
/-
**SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length** 是 Mathlib 中的一个定理，位于命名
空间 `SimpleGraph.Walk`。
形式化陈述：isCycle_iff_isPath_tail_and_le_length {p : G.Walk u u} : p.IsCycle ↔ p.tai
l.IsPath ∧ 3 <= p.length
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_tail`：∀ {V : Type u} {G : SimpleGraph V}
 {u : V} {p : G.Walk u u}, p.IsCycle → p.tail.IsPath
· 使用定理 `SimpleGraph.Walk.IsCircuit.three_le_length`：∀ {V : Type u} {G : SimpleGr
aph V} {v : V} {p : G.Walk v v}, p.IsCircuit → 3 ≤ p.length
· 使用定理 `SimpleGraph.Walk.IsCycle.isCircuit`：∀ {V : Type u} {G : SimpleGraph V} {
u : V} {p : G.Walk u u}, p.IsCycle → p.IsCircuit
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.le_zero_eq`：∀ (a : ℕ), (a ≤ 0) = (a = 0)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.cons_isCycle_iff`：cons_isCycle_iff {u v : V} (p : G.Wal
k v u) (h : G.Adj u v) : (Walk.cons h p).IsCycle ↔ p.IsPath ∧ s(u, v) ∉ p.edges
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.tail_cons`：tail_cons (h : G.Adj u v) (p : G.Walk v w) :
 (p.cons h).tail = p.copy (getVert_zero p).symm rfl
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
· 使用定理 `Nat.Internal.Linear.ExprCnstr.eq_of_toNormPoly_eq`：∀ (ctx : Nat.Internal
.Linear.Context) (c d : Nat.Internal.Linear.ExprCnstr),   (c.toNormPoly == d.toP
oly) = true →     Nat.Internal.Linear.E…
· 使用定理 `List.length_pos_iff`：∀ {α : Type u_1} {l : List α}, 0 < l.length ↔ l ≠ [
]
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `SimpleGraph.Walk.head_support`：head_support {G : SimpleGraph V} {a b : V
} (p : G.Walk a b) : p.support.head (by simp) = a
· 使用定理 `SimpleGraph.Walk.IsPath.eq_penultimate_of_mem_edges`：∀ {V : Type u} {G :
 SimpleGraph V} {u v w : V} {p : G.Walk u v}, p.IsPath → s(v, w) ∈ p.edges → w =
 p.penultimate
· 使用引理 `SimpleGraph.Walk.support_getElem_length_sub_one_eq_penultimate`：support_
getElem_length_sub_one_eq_penultimate {p : G.Walk u v} : p.support[p.length - 1]
 = p.penultimate
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_iff_injective_get_support`：isPath_iff_injective_
get_support {u v : V} (p : G.Walk u v) : p.IsPath ↔ (p.support.get ·).Injective
-/
theorem isCycle_iff_isPath_tail_and_le_length {p : G.Walk u u} :
    p.IsCycle ↔ p.tail.IsPath ∧ 3 ≤ p.length := by
  refine ⟨fun h ↦ ⟨h.isPath_tail, h.three_le_length⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  cases p with
  | nil => simp_all
  | cons h' p =>
    simp only [getVert_cons_succ, tail_cons, isPath_copy, length_cons] at h₁ h₂
    refine p.cons_isCycle_iff h' |>.mpr ⟨h₁, fun hh ↦ ?_⟩
    have : p.support[0] = p.support[p.length - 1] := by
      simp [← List.head_eq_getElem_zero, h₁.eq_penultimate_of_mem_edges hh]
    have := p.isPath_iff_injective_get_support.mp h₁ this
    lia

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-
**SimpleGraph.Walk.IsTrail.takeUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v w : V} {p :
 G.Walk v w},   p.IsTrail → ∀ (h : u ∈ p.support), (p.takeUntil u h).IsTrail
参数：h : u ∈ p.support；p.takeUntil u h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.of_append_left`：∀ {V : Type u} {G : SimpleGraph
 V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsTrail → p.IsTr
ail
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
-/
protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)
/-
**SimpleGraph.Walk.IsTrail.dropUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk
.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v w : V} {p :
 G.Walk v w},   p.IsTrail → ∀ (h : u ∈ p.support), (p.dropUntil u h).IsTrail
参数：h : u ∈ p.support；p.dropUntil u h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.of_append_right`：∀ {V : Type u} {G : SimpleGrap
h V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsTrail → q.IsT
rail
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
-/
protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)
/-
**SimpleGraph.Walk.IsPath.takeUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v w : V} {p :
 G.Walk v w},   p.IsPath → ∀ (h : u ∈ p.support), (p.takeUntil u h).IsPath
参数：h : u ∈ p.support；p.takeUntil u h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_left`：∀ {V : Type u} {G : SimpleGraph 
V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → p.IsPath
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
-/
protected theorem IsPath.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (q := p.dropUntil u h) (by rwa [← take_spec _ h] at hc)
/-
**SimpleGraph.Walk.IsPath.dropUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} [inst : DecidableEq V] {u v w : V} {p :
 G.Walk v w},   p.IsPath → ∀ (h : u ∈ p.support), (p.dropUntil u h).IsPath
参数：h : u ∈ p.support；p.dropUntil u h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.of_append_right`：∀ {V : Type u} {G : SimpleGraph
 V} {u v w : V} {p : G.Walk u v} {q : G.Walk v w}, (p.append q).IsPath → q.IsPat
h
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
-/
protected theorem IsPath.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (p := p.takeUntil u h) (q := p.dropUntil u h)
    (by rwa [← take_spec _ h] at hc)
/-
**SimpleGraph.Walk.IsTrail.disjoint_edges_takeUntil_dropUntil** 是 Mathlib 中的一个定理
，位于命名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {x : V
} {w : G.Walk u v},   w.IsTrail → ∀ (hx : x ∈ w.support), (w.takeUntil x hx).edg
es.Disjoint (w.dropUntil x hx).edges
参数：hx : x ∈ w.support；w.takeUntil x hx；w.dropUntil x hx。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.disjoint_of_nodup_append`：disjoint_of_nodup_append {l₁ l₂ : List α}
 (d : Nodup (l₁ ++ l₂)) : Disjoint l₁ l₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
-/
lemma IsTrail.disjoint_edges_takeUntil_dropUntil {x : V} {w : G.Walk u v} (hw : w.IsTrail)
    (hx : x ∈ w.support) : (w.takeUntil x hx).edges.Disjoint (w.dropUntil x hx).edges :=
  List.disjoint_of_nodup_append <| by simpa [← edges_append] using hw.edges_nodup
/-
**SimpleGraph.Walk.isTrail_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {c : G
.Walk v v} (hu : u ∈ c.support),   (c.rotate u hu).IsTrail ↔ c.IsTrail
参数：hu : u ∈ c.support；c.rotate u hu。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isTrail_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v), p.IsTrail ↔ p.edges.Nodup
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.IsRotated.perm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
· 使用定理 `SimpleGraph.Walk.rotate_edges`：rotate_edges (c : G.Walk v v) (u : V) (h)
 : (c.rotate u h).edges ~r c.edges
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isTrail_rotate {c : G.Walk v v} (hu : u ∈ c.support) :
    (c.rotate u hu).IsTrail ↔ c.IsTrail := by
  rw [isTrail_def, isTrail_def, (c.rotate_edges u hu).perm.nodup_iff]
/-
**SimpleGraph.Walk.isCircuit_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`
。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {c : G
.Walk v v} (hu : u ∈ c.support),   (c.rotate u hu).IsCircuit ↔ c.IsCircuit
参数：hu : u ∈ c.support；c.rotate u hu。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isCircuit_rotate {c : G.Walk v v} (hu : u ∈ c.support) :
    (c.rotate u hu).IsCircuit ↔ c.IsCircuit := by simp [isCircuit_def]
/-
**SimpleGraph.Walk.isCycle_rotate** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {c : G
.Walk v v} (hu : u ∈ c.support),   (c.rotate u hu).IsCycle ↔ c.IsCycle
参数：hu : u ∈ c.support；c.rotate u hu。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `List.Perm.nodup_iff`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Perm l₂ → (l₁
.Nodup ↔ l₂.Nodup)
· 使用定理 `List.IsRotated.perm`：∀ {α : Type u} {l l' : List α}, l ~r l' → l.Perm l'
· 使用定理 `SimpleGraph.Walk.support_rotate`：support_rotate (c : G.Walk v v) (u : V)
 (h) : (c.rotate u h).support.tail ~r c.support.tail
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isCycle_rotate {c : G.Walk v v} (hu : u ∈ c.support) :
    (c.rotate u hu).IsCycle ↔ c.IsCycle := by simp [isCycle_def, (support_rotate ..).perm.nodup_iff]

protected alias ⟨IsTrail.of_rotate, IsTrail.rotate⟩ := isTrail_rotate
protected alias ⟨IsCircuit.of_rotate, IsCircuit.rotate⟩ := isCircuit_rotate
protected alias ⟨IsCycle.of_rotate, IsCycle.rotate⟩ := isCycle_rotate
/-
**SimpleGraph.Walk.IsCycle.isPath_takeUntil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGra
ph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v w : V} [inst : DecidableEq V] {c : G
.Walk v v},   c.IsCycle → ∀ (h : w ∈ c.support), (c.takeUntil w h).IsPath
参数：h : w ∈ c.support；c.takeUntil w h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.Walk.takeUntil_first`：takeUntil_first (p : G.Walk u v) : p.t
akeUntil u p.start_mem_support = .nil
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_reverse_iff`：isPath_reverse_iff {u v : V} (p : G
.Walk u v) : p.reverse.IsPath ↔ p.IsPath
· 使用定理 `SimpleGraph.Walk.IsCycle.isPath_of_append_right`：∀ {V : Type u} {G : Sim
pleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk v u}, ¬p.Nil → (p.append q).I
sCycle → q.IsPath
· 使用引理 `SimpleGraph.Walk.not_nil_of_ne`：not_nil_of_ne {p : G.Walk v w} : v != w 
-> ¬ p.Nil
· 使用定理 `SimpleGraph.Walk.reverse_append`：reverse_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) : (p.append q).reverse = q.reverse.append p.reverse
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.take_spec`：take_spec {u v w : V} (p : G.Walk v w) (h : 
u in p.support) : (p.takeUntil u h).append (p.dropUntil u h) = p
· 使用引理 `SimpleGraph.Walk.isCycle_reverse`：isCycle_reverse {p : G.Walk u u} : p.r
everse.IsCycle ↔ p.IsCycle where mp h
-/
lemma IsCycle.isPath_takeUntil {c : G.Walk v v} (hc : c.IsCycle) (h : w ∈ c.support) :
    (c.takeUntil w h).IsPath := by
  by_cases hvw : v = w
  · subst hvw
    simp
  rw [← isCycle_reverse, ← take_spec c h, reverse_append] at hc
  exact (c.takeUntil w h).isPath_reverse_iff.mp (hc.isPath_of_append_right (not_nil_of_ne hvw))
/-
**SimpleGraph.Walk.IsCycle.count_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] {c : G.W
alk v v},   c.IsCycle → List.count v c.support = 2
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
· 使用定理 `SimpleGraph.Walk.end_mem_tail_support`：end_mem_tail_support {u v : V} {p
 : G.Walk u v} (h : ¬ p.Nil) : v in p.support.tail
· 使用定理 `SimpleGraph.Walk.IsCycle.not_nil`：∀ {V : Type u} {G : SimpleGraph V} {v 
: V} {p : G.Walk v v}, p.IsCycle → ¬p.Nil
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `List.head?_eq_some_head`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.h
ead? = some (l.head h)
· 使用定理 `SimpleGraph.Walk.support_ne_nil`：support_ne_nil {u v : V} (p : G.Walk u 
v) : p.support != []
· 使用定理 `SimpleGraph.Walk.head_support`：head_support {G : SimpleGraph V} {a b : V
} (p : G.Walk a b) : p.support.head (by simp) = a
-/
theorem IsCycle.count_support {c : G.Walk v v} (hc : c.IsCycle) : c.support.count v = 2 := by
  have := List.count_eq_one_of_mem hc.support_nodup <| c.end_mem_tail_support hc.not_nil
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind
/-
**SimpleGraph.Walk.IsCycle.count_support_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk.IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {c : G
.Walk v v},   c.IsCycle → u ∈ c.support → u ≠ v → List.count u c.support = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.head`：head?_flatten_replicate {n : Nat} (h : n != 0) (l : List α) :
 (List.replicate n l).flatten.head? = l.head?
· 使用定理 `SimpleGraph.Walk.support_ne_nil`：support_ne_nil {u v : V} (p : G.Walk u 
v) : p.support != []
· 使用定理 `List.eq_or_mem_of_mem_cons`：∀ {α : Type u_1} {a b : α} {l : List α}, a ∈
 b :: l → a = b ∨ a ∈ l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.cons_head_tail`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.head 
h :: l.tail = l
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsCycle.support_nodup`：∀ {V : Type u} {G : SimpleGraph 
V} {u : V} {p : G.Walk u u}, p.IsCycle → p.support.tail.Nodup
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `SimpleGraph.Walk.head_support`：head_support {G : SimpleGraph V} {a b : V
} (p : G.Walk a b) : p.support.head (by simp) = a
· 使用定理 `List.head?_eq_some_head`：∀ {α : Type u_1} {l : List α} (h : l ≠ []), l.h
ead? = some (l.head h)
-/
theorem IsCycle.count_support_of_mem {c : G.Walk v v} (hc : c.IsCycle) (hu : u ∈ c.support)
    (hv : u ≠ v) : c.support.count u = 1 := by
  have := List.eq_or_mem_of_mem_cons <| List.cons_head_tail c.support_ne_nil ▸ hu
  have := List.count_eq_one_of_mem hc.support_nodup <| this.resolve_left <| head_support _ ▸ hv
  have := c.head_support ▸ List.head?_eq_some_head c.support_ne_nil
  grind

/-- Taking a strict initial segment of a path removes the end vertex from the support. -/
/-
**SimpleGraph.Walk.endpoint_notMem_support_takeUntil** 是 Mathlib 中的一个引理，位于命名空间 `
SimpleGraph.Walk`。
形式化陈述：endpoint_notMem_support_takeUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w
 in p.support) (h : v != w) : v ∉ (p.takeUntil w hw).support
参数：hp : p.IsPath；hw : w in p.support；h : v != w。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.mem_support_iff_exists_getVert`：mem_support_iff_exists_
getVert {u v w : V} {p : G.Walk v w} : u in p.support ↔ exists n, p.getVert n = 
u ∧ n <= p.length
· 使用引理 `SimpleGraph.Walk.length_takeUntil_lt_length`：length_takeUntil_lt_length 
{u v w : V} {p : G.Walk v w} (h : u in p.support) (huw : u != w) : (p.takeUntil 
u h).length < p.length
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_injOn`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → Set.InjOn p.getVert {i | i ≤ p.length}
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
· 使用引理 `SimpleGraph.Walk.getVert_takeUntil`：getVert_takeUntil {u v : V} {n : Nat
} {p : G.Walk u v} (hw : w in p.support) (hn : n <= (p.takeUntil w hw).length) :
 (p.takeUntil w hw).getV…

--- 原说明 ---
Taking a strict initial segment of a path removes the end vertex from the suppor
t.
-/
lemma endpoint_notMem_support_takeUntil {p : G.Walk u v} (hp : p.IsPath) (hw : w ∈ p.support)
    (h : v ≠ w) : v ∉ (p.takeUntil w hw).support := by
  intro hv
  rw [Walk.mem_support_iff_exists_getVert] at hv
  obtain ⟨n, ⟨hn, hnl⟩⟩ := hv
  rw [getVert_takeUntil hw hnl] at hn
  have := p.length_takeUntil_lt_length hw h.symm
  have : n = p.length := hp.getVert_injOn (by rw [Set.mem_ofPred]; lia) (by simp)
    (hn.symm ▸ p.getVert_length.symm)
  lia

end WalkDecomp

/-
**SimpleGraph.Walk.isPath_iff_isSubwalk_imp_nil** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：isPath_iff_isSubwalk_imp_nil {u v} {p : G.Walk u v} : p.IsPath ↔ forall (v
 : V) (w : G.Walk v v), w.IsSubwalk p -> w.Nil
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_iff_nil`：isPath_iff_nil {u : V} {p : G.Walk u u}
 : p.IsPath ↔ p.Nil
· 使用定理 `SimpleGraph.Walk.isPath_of_isSubwalk`：isPath_of_isSubwalk {v w v' w' : V
} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} (h : p₁.IsSubwalk p₂) (h₂ : p₂.IsPath) :
 p₁.IsPath
· 使用定理 `SimpleGraph.Walk.IsPath.mk'`：∀ {V : Type u} {G : SimpleGraph V} {u v : V
} {p : G.Walk u v}, p.support.Nodup → p.IsPath
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `List.pairwise_iff_getElem`：∀ {α : Type u_1} {R : α → α → Prop} {l : List
 α},   List.Pairwise R l ↔ ∀ (i j : ℕ) (_hi : i < l.length) (_hj : j < l.length)
, i < j → R l[i…
· 使用定理 `SimpleGraph.Walk.IsSubwalk.trans`：∀ {V : Type u_1} {G : SimpleGraph V} {
u₁ v₁ u₂ v₂ u₃ v₃ : V} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}   {p₃ : G.Walk u₃
 v₃}, p₁.IsSubwalk p₂ …
· 使用定理 `SimpleGraph.Walk.isSubwalk_drop`：isSubwalk_drop {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.drop n).IsSubwalk p
· 使用定理 `SimpleGraph.Walk.isSubwalk_take`：isSubwalk_take {u v : V} (p : G.Walk u 
v) (n : Nat) : (p.take n).IsSubwalk p
-/
theorem isPath_iff_isSubwalk_imp_nil {u v} {p : G.Walk u v} :
    p.IsPath ↔ ∀ (v : V) (w : G.Walk v v), w.IsSubwalk p → w.Nil := by
  refine ⟨fun hp v w hwp ↦ ?_, fun h ↦ .mk' ?_⟩
  · simp [w.isPath_iff_nil.mp <| isPath_of_isSubwalk hwp hp]
  · refine List.pairwise_iff_getElem.mpr fun i j _ _ _ _ ↦ ?_
    let p' := p.take j |>.drop i
    have : ¬p'.Nil := by grind [nil_drop_iff, take_length]
    have : p'.IsSubwalk p := isSubwalk_drop _ i |>.trans <| p.isSubwalk_take j
    grind [take_getVert, getVert_eq_support_getElem]
/-
**SimpleGraph.Walk.IsTrail.isPath_iff_isSubwalk_imp_not_isCycle** 是 Mathlib 中的一个
定理，位于命名空间 `SimpleGraph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v},   p.IsTrail
 → (p.IsPath ↔ ∀ (v_1 : V) (w : G.Walk v_1 v_1), w.IsSubwalk p → ¬w.IsCycle)
参数：p.IsPath ↔ ∀ (v_1 : V) (w : G.Walk v_1 v_1), w.IsSubwalk p → ¬w.IsCycle。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsTrail.isPath_iff_isSubwalk_imp_not_isCycle {u v} {p : G.Walk u v} (ht : p.IsTrail) :
    p.IsPath ↔ ∀ (v : V) (w : G.Walk v v), w.IsSubwalk p → ¬w.IsCycle := by
  refine ⟨by grind [isPath_iff_isSubwalk_imp_nil, IsCycle.not_nil], fun h ↦ ?_⟩
  classical
  match p with
  | .nil => simp
  | .cons hadj p =>
    have hp := isPath_iff_isSubwalk_imp_not_isCycle ht.of_cons |>.mpr (h · · <| ·.cons hadj)
    refine cons_isPath_iff .. |>.mpr ⟨hp, fun hup ↦ h u (p.takeUntil u hup |>.cons hadj) ?_ ?_⟩
    · rw [isSubwalk_iff_support_isInfix, support_cons, support_cons]
      exact (List.prefix_cons_inj u |>.mpr <| p.support_takeUntil_prefix_support hup).isInfix
    · refine cons_isCycle_iff .. |>.mpr ⟨hp.takeUntil hup, fun he ↦ ?_⟩
      exact ht.edges_nodup.notMem <| p.edges_takeUntil_subset_edges hup he

end Walk

/-! ### Type of paths -/

/-- The type for paths between two vertices. -/
/-
**SimpleGraph.Path** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：Path (u v : V)
参数：u v : V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type for paths between two vertices.
-/
abbrev Path (u v : V) := { p : G.Walk u v // p.IsPath }

namespace Path

variable {G G'}

@[simp]
/-
**SimpleGraph.Path.isPath** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Path`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Path u v), (↑p).IsPath
参数：p : G.Path u v；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem isPath {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property

@[simp]
/-
**SimpleGraph.Path.isTrail** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Path`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (p : G.Path u v), (↑p).IsTrai
l
参数：p : G.Path u v；↑p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
protected theorem isTrail {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail

/-- The length-0 path at a vertex. -/
@[refl, simps]
/-
**SimpleGraph.Path.nil** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Path`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {u : V} → G.Path u u
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.nil`：∀ {V : Type u} {G : SimpleGraph V} {u : V},
 SimpleGraph.Walk.nil.IsPath

--- 原说明 ---
The length-0 path at a vertex.
-/
protected def nil {u : V} : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
/-
**SimpleGraph.Path.singleton** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Path`。
形式化陈述：singleton {u v : V} (h : G.Adj u v) : G.Path u v
参数：h : G.Adj u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The length-1 path between a pair of adjacent vertices.
-/
def singleton {u v : V} (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩
/-
**SimpleGraph.Path.mk'_mem_edges_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Path`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} (h : G.Adj u v), s(u, v) ∈ (↑
(SimpleGraph.Path.singleton h)).edges
参数：h : G.Adj u v；u, v；↑(SimpleGraph.Path.singleton h)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
-/
theorem mk'_mem_edges_singleton {u v : V} (h : G.Adj u v) :
    s(u, v) ∈ (singleton h : G.Walk u v).edges := by simp [singleton]

/-- The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
/-
**SimpleGraph.Path.reverse** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Path`。
形式化陈述：reverse {u v : V} (p : G.Path u v) : G.Path v u
参数：p : G.Path u v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`.
-/
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩
/-
**SimpleGraph.Path.count_support_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.P
ath`。
形式化陈述：count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v} (hw : w 
in (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1
参数：hw : w in (p : G.Walk u v).support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v}
    (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw
/-
**SimpleGraph.Path.count_edges_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Pat
h`。
形式化陈述：count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
 (hw : e in (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1
参数：e : Sym2 V；hw : e in (p : G.Walk u v).edges。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.count_eq_one_of_mem`：count_eq_one_of_mem [BEq α] [LawfulBEq α] {a :
 α} {l : List α} (d : Nodup l) (h : a in l) : count a l = 1
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `SimpleGraph.Walk.IsTrail.edges_nodup`：∀ {V : Type u} {G : SimpleGraph V}
 {u v : V} {p : G.Walk u v}, p.IsTrail → p.edges.Nodup
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
    (hw : e ∈ (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw

@[simp]
/-
**SimpleGraph.Path.nodup_support** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Path`。
形式化陈述：nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup
参数：p : G.Path u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isPath_def`：isPath_def {u v : V} (p : G.Walk u v) : p.I
sPath ↔ p.support.Nodup
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property
/-
**SimpleGraph.Path.loop_eq** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Path`。
形式化陈述：loop_eq {v : V} (p : G.Path v v) : p = Path.nil
参数：p : G.Path v v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem loop_eq {v : V} (p : G.Path v v) : p = Path.nil := by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h
/-
**SimpleGraph.Path.notMem_edges_of_loop** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.P
ath`。
形式化陈述：notMem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} : e ∉ (p : G.Wa
lk v v).edges
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Path.loop_eq`：loop_eq {v : V} (p : G.Path v v) : p = Path.ni
l
· 使用定理 `SimpleGraph.Path.nil_coe`：∀ {V : Type u} {G : SimpleGraph V} {u : V}, ↑S
impleGraph.Path.nil = SimpleGraph.Walk.nil
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem notMem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} :
    e ∉ (p : G.Walk v v).edges := by simp [p.loop_eq]
/-
**SimpleGraph.Path.cons_isCycle** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Path`。
形式化陈述：cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v) (he : s(u, v) ∉ (p
 : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle
参数：p : G.Path v u；h : G.Adj u v；he : s(u, v) ∉ (p : G.Walk v u).edges。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : s(u, v) ∉ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.isTrail_cons, he]

end Path


/-! ### Walks to paths -/

namespace Walk

variable {G} {u v : V}

/-
**SimpleGraph.Walk.IsPath.length_eq_one_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
s(u, v) ∈ p.edges → p.length = 1
参数：u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.IsPath.getVert_eq_start_iff`：∀ {V : Type u} {G : Simple
Graph V} {u w : V} {i : ℕ} {p : G.Walk u w},   p.IsPath → i ≤ p.length → (p.getV
ert i = u ↔ i = 0)
· 使用定理 `Nat.sub_le`：∀ (n m : ℕ), n - m ≤ n
· 使用定理 `SimpleGraph.Walk.IsPath.eq_penultimate_of_mem_edges`：∀ {V : Type u} {G :
 SimpleGraph V} {u v w : V} {p : G.Walk u v}, p.IsPath → s(v, w) ∈ p.edges → w =
 p.penultimate
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem IsPath.length_eq_one_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) ∈ p.edges) :
    p.length = 1 := by
  suffices p.length - 1 = 0 by grind [length_edges]
  rw [← hp.getVert_eq_start_iff <| p.length.sub_le 1]
  exact (hp.eq_penultimate_of_mem_edges <| Sym2.eq_swap ▸ h).symm
/-
**SimpleGraph.Walk.IsPath.eq_adj_toWalk_of_mem_edges** 是 Mathlib 中的一个定理，位于命名空间 `
SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → 
∀ (h : s(u, v) ∈ p.edges), p = ⋯.toWalk
参数：h : s(u, v) ∈ p.edges。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_getVert_le_length`：ext_getVert_le_length {u v} {p q
 : G.Walk u v} (hl : p.length = q.length) (h : forall k <= p.length, p.getVert k
 = q.getVert k) : p = q
· 使用定理 `SimpleGraph.Walk.adj_of_mem_edges`：adj_of_mem_edges {u v x y : V} (p : G
.Walk u v) (h : s(x, y) in p.edges) : G.Adj x y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.IsPath.length_eq_one_of_mem_edges`：∀ {V : Type u} {G : 
SimpleGraph V} {u v : V} {p : G.Walk u v}, p.IsPath → s(u, v) ∈ p.edges → p.leng
th = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.le_one_iff_eq_zero_or_eq_one`：∀ {n : ℕ}, n ≤ 1 ↔ n = 0 ∨ n = 1
· 使用定理 `SimpleGraph.Walk.getVert_zero`：getVert_zero {u v} (w : G.Walk u v) : w.g
etVert 0 = u
· 使用引理 `SimpleGraph.Walk.getVert_cons_succ`：getVert_cons_succ {u v w n} (p : G.W
alk v w) (h : G.Adj u v) : (p.cons h).getVert (n + 1) = p.getVert n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SimpleGraph.Walk.getVert_length`：getVert_length {u v} (w : G.Walk u v) :
 w.getVert w.length = v
-/
theorem IsPath.eq_adj_toWalk_of_mem_edges {p : G.Walk u v} (hp : p.IsPath) (h : s(u, v) ∈ p.edges) :
    p = (p.adj_of_mem_edges h).toWalk := by
  apply p.ext_getVert_le_length <| by simp [hp.length_eq_one_of_mem_edges h]
  intro _ hl
  cases Nat.le_one_iff_eq_zero_or_eq_one.mp (hp.length_eq_one_of_mem_edges h ▸ hl) with
  | inl hl => simp [hl]
  | inr hl =>
    rw [hl, getVert_cons_succ, getVert_zero, ← hp.length_eq_one_of_mem_edges h, getVert_length]
/-
**SimpleGraph.Walk.IsPath.disjoint_edges_of_disjoint_support** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk 
v u},   p.IsPath → p.support.tail.Disjoint q.support.tail → p.length ≠ 1 → p.edg
es.Disjoint q.edges
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.mem_support_iff`：mem_support_iff {u v w : V} (p : G.Wal
k u v) : w in p.support ↔ w = u ∨ w in p.support.tail
· 使用定理 `SimpleGraph.Walk.fst_mem_support_of_mem_edges`：fst_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : t in p.support
· 使用定理 `SimpleGraph.Walk.snd_mem_support_of_mem_edges`：snd_mem_support_of_mem_ed
ges {t u v w : V} (p : G.Walk v w) (he : s(t, u) in p.edges) : u in p.support
-/
theorem IsPath.disjoint_edges_of_disjoint_support {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath)
    (hd : p.support.tail.Disjoint q.support.tail) (hl : p.length ≠ 1) :
    p.edges.Disjoint q.edges := by
  simp only [List.disjoint_left] at hd ⊢
  contrapose! hd
  obtain ⟨⟨a, b⟩, hep, heq⟩ := hd
  have := p.mem_support_iff.mp <| p.fst_mem_support_of_mem_edges hep
  have := p.mem_support_iff.mp <| p.snd_mem_support_of_mem_edges hep
  have := q.mem_support_iff.mp <| q.fst_mem_support_of_mem_edges heq
  have := q.mem_support_iff.mp <| q.snd_mem_support_of_mem_edges heq
  grind [p.adj_of_mem_edges hep |>.ne, length_eq_one_of_mem_edges]
/-
**SimpleGraph.Walk.IsPath.isCycle_append** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p : G.Walk u v} {q : G.Walk 
v u},   p.IsPath → q.IsPath → p.support.tail.Disjoint q.support.tail → 1 < p.len
gth ∨ 1 < q.length → (p.append q).IsCycle
参数：p.append q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isCycle_def`：isCycle_def {u : V} (p : G.Walk u u) : p.I
sCycle ↔ p.IsTrail ∧ p != nil ∧ p.support.tail.Nodup
· 使用定理 `SimpleGraph.Walk.isTrail_append`：isTrail_append {u v w : V} (p : G.Walk 
u v) (q : G.Walk v w) : (p.append q).IsTrail ↔ p.IsTrail ∧ q.IsTrail ∧ p.edges.D
isjoint q.edges
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `SimpleGraph.Walk.tail_support_append`：tail_support_append {u v w : V} (p
 : G.Walk u v) (p' : G.Walk v w) : (p.append p').support.tail = p.support.tail +
+ p'.support.tail
· 使用定理 `List.nodup_append'`：nodup_append' {l₁ l₂ : List α} : Nodup (l₁ ++ l₂) ↔ 
Nodup l₁ ∧ Nodup l₂ ∧ Disjoint l₁ l₂
· 使用定理 `List.Nodup.tail`：∀ {α : Type u} {l : List α}, l.Nodup → l.tail.Nodup
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
-/
lemma IsPath.isCycle_append {p : G.Walk u v} {q : G.Walk v u} (hp : p.IsPath) (hq : q.IsPath)
    (h : p.support.tail.Disjoint q.support.tail) (hn : 1 < p.length ∨ 1 < q.length) :
    (p.append q).IsCycle := by
  rw [isCycle_def, isTrail_append]
  refine ⟨⟨hp.isTrail, hq.isTrail, ?_⟩, ?_, ?_⟩
  · grind [IsPath.disjoint_edges_of_disjoint_support, List.Disjoint.symm]
  · grind [nil_append_iff]
  · rw [tail_support_append, List.nodup_append']
    exact ⟨hp.support_nodup.tail, hq.support_nodup.tail, h⟩

/--
Given two distinct paths with the same endpoints, we can extract a subwalk from each such that their
concatenation, with one reversed, forms a cycle.
-/
/-
**SimpleGraph.Walk.IsPath.exists_isCycle_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p q : G.Walk u v},   p.IsPat
h → q.IsPath → p ≠ q → ∃ u' v' p' q', p'.IsSubwalk p ∧ q'.IsSubwalk q ∧ (p'.appe
nd q'.reverse).IsCycle
参数：p'.append q'.reverse。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用引理 `SimpleGraph.Walk.length_takeUntil_lt_length`：length_takeUntil_lt_length 
{u v w : V} {p : G.Walk v w} (h : u in p.support) (huw : u != w) : (p.takeUntil 
u h).length < p.length
· 使用定理 `SimpleGraph.Walk.IsPath.takeUntil`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : DecidableEq V] {u v w : V} {p : G.Walk v w},   p.IsPath → ∀ (h : u ∈ p.sup
port), (p.takeUntil u h…
· 使用引理 `SimpleGraph.Walk.length_dropUntil_lt_length`：length_dropUntil_lt_length 
{u v w : V} {p : G.Walk v w} (h : u in p.support) (huv : u != v) : (p.dropUntil 
u h).length < p.length
· 使用定理 `SimpleGraph.Walk.IsPath.dropUntil`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : DecidableEq V] {u v w : V} {p : G.Walk v w},   p.IsPath → ∀ (h : u ∈ p.sup
port), (p.dropUntil u h…
· 使用引理 `SimpleGraph.Walk.isSubwalk_rfl`：isSubwalk_rfl {u v} (p : G.Walk u v) : p
.IsSubwalk p
· 使用定理 `SimpleGraph.Walk.IsPath.isCycle_append`：∀ {V : Type u} {G : SimpleGraph 
V} {u v : V} {p : G.Walk u v} {q : G.Walk v u},   p.IsPath → q.IsPath → p.suppor
t.tail.Disjoint q.support.ta…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.isPath_reverse_iff`：isPath_reverse_iff {u v : V} (p : G
.Walk u v) : p.reverse.IsPath ↔ p.IsPath
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)

--- 原说明 ---
Given two distinct paths with the same endpoints, we can extract a subwalk from 
each such that their
concatenation, with one reversed, forms a cycle.
-/
theorem IsPath.exists_isCycle_of_ne {p q : G.Walk u v} (hp : p.IsPath) (hq : q.IsPath)
    (h : p ≠ q) :
    ∃ (u' v' : V) (p' q' : G.Walk u' v'),
      p'.IsSubwalk p ∧ q'.IsSubwalk q ∧ (p'.append q'.reverse).IsCycle := by
  induction hs : p.length using Nat.strongRec generalizing u v with | ind s ih =>
  by_cases! hw : ∃ w, w ∈ p.support ∧ w ∈ q.support ∧ w ≠ u ∧ w ≠ v
  · classical
    have ⟨w, hwp, hwq, hwu, hwv⟩ := hw
    by_cases! p.takeUntil w hwp ≠ q.takeUntil w hwq
    · have := ih _ (hs ▸ length_takeUntil_lt_length hwp hwv) (hp.takeUntil hwp) (hq.takeUntil hwq)
      grind [isSubwalk_takeUntil, IsSubwalk.trans]
    · have := ih _ (hs ▸ length_dropUntil_lt_length hwp hwu) (hp.dropUntil hwp) (hq.dropUntil hwq)
        <| by grind [take_spec]
      grind [isSubwalk_dropUntil, IsSubwalk.trans]
  · refine ⟨u, v, p, q, p.isSubwalk_rfl, q.isSubwalk_rfl, ?_⟩
    refine hp.isCycle_append (isPath_reverse_iff q |>.mpr hq) (fun _ ↦ ?_) ?_
    · grind [dropLast_support_concat, IsPath.support_nodup, support_reverse, cons_tail_support]
    · grind [length_reverse, eq_of_length_le_one]

open List in
/--
Given two distinct paths, `p` and `q`, with same endpoints, we can extract a cycle whose support
is a sublist of `p.support ++ q.support.reverse.tail`.
-/
/-
**SimpleGraph.Walk.IsPath.exists_isCycle_sublist_of_ne** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p q : G.Walk u v},   p.IsPat
h →     q.IsPath →       p ≠ q → ∃ w ∈ p.support, w ∈ q.support ∧ ∃ c, c.IsCycle
 ∧ c.support.Sublist (p.support ++ q.support.reverse.tail)
参数：p.support ++ q.support.reverse.tail。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.exists_isCycle_of_ne`：∀ {V : Type u} {G : Simple
Graph V} {u v : V} {p q : G.Walk u v},   p.IsPath → q.IsPath → p ≠ q → ∃ u' v' p
' q', p'.IsSubwalk p ∧ q'.IsSubwal…
· 使用定理 `SimpleGraph.Walk.IsSubwalk.support_subset`：∀ {V : Type u_1} {G : SimpleG
raph V} {u v u' v' : V} {p₁ : G.Walk u v} {p₂ : G.Walk u' v'},   p₂.IsSubwalk p₁
 → p₂.support ⊆ p₁.support
· 使用定理 `SimpleGraph.Walk.start_mem_support`：start_mem_support {u v : V} (p : G.W
alk u v) : u in p.support
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.support_append`：support_append {u v w : V} (p : G.Walk 
u v) (p' : G.Walk v w) : (p.append p').support = p.support ++ p'.support.tail
· 使用定理 `SimpleGraph.Walk.support_reverse`：support_reverse {u v : V} (p : G.Walk 
u v) : p.reverse.support = p.support.reverse
· 使用定理 `List.Sublist.append`：∀ {α : Type u_1} {l₁ l₂ r₁ r₂ : List α}, l₁.Sublist
 l₂ → r₁.Sublist r₂ → (l₁ ++ r₁).Sublist (l₂ ++ r₂)
· 使用定理 `List.IsInfix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+: l₂ → l₁
.Sublist l₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SimpleGraph.Walk.isSubwalk_iff_support_isInfix`：isSubwalk_iff_support_is
Infix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} : p₁.IsSubwalk p₂ ↔ 
p₁.support <:+: p₂.support
· 使用定理 `List.Sublist.tail`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → l₁
.tail.Sublist l₂.tail
· 使用定理 `List.Sublist.reverse`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ →
 l₁.reverse.Sublist l₂.reverse

--- 原说明 ---
Given two distinct paths, `p` and `q`, with same endpoints, we can extract a cyc
le whose support
is a sublist of `p.support ++ q.support.reverse.tail`.
-/
theorem IsPath.exists_isCycle_sublist_of_ne {p q : G.Walk u v} (hp : p.IsPath)
    (hq : q.IsPath) (h : p ≠ q) :
    ∃ w, w ∈ p.support ∧ w ∈ q.support ∧
      ∃ c : G.Walk w w, c.IsCycle ∧ c.support <+ (p.support ++ q.support.reverse.tail) := by
  have ⟨u', v', p', q', hp', hq', hcyc⟩ := hp.exists_isCycle_of_ne hq h
  use u', hp'.support_subset p'.start_mem_support, hq'.support_subset q'.start_mem_support
  refine ⟨_, hcyc, ?_⟩
  rw [support_append, support_reverse]
  refine .append ?_ <| .tail <| .reverse ?_
  · exact isSubwalk_iff_support_isInfix.mp hp' |>.sublist
  · exact isSubwalk_iff_support_isInfix.mp hq' |>.sublist

/--
Given two distinct paths with same endpoints, we can extract a cycle whose length is less than or
equal to the sum of their lengths.
-/
/-
**SimpleGraph.Walk.IsPath.exists_isCycle_length_le_add_of_ne** 是 Mathlib 中的一个定理，
位于命名空间 `SimpleGraph.Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {p q : G.Walk u v},   p.IsPat
h → q.IsPath → p ≠ q → ∃ w ∈ p.support, w ∈ q.support ∧ ∃ c, c.IsCycle ∧ c.lengt
h ≤ p.length + q.length
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.exists_isCycle_sublist_of_ne`：∀ {V : Type u} {G 
: SimpleGraph V} {u v : V} {p q : G.Walk u v},   p.IsPath →     q.IsPath →      
 p ≠ q → ∃ w ∈ p.support, w ∈ q.support ∧ …

--- 原说明 ---
Given two distinct paths with same endpoints, we can extract a cycle whose lengt
h is less than or
equal to the sum of their lengths.
-/
theorem IsPath.exists_isCycle_length_le_add_of_ne {p q : G.Walk u v} (hp : p.IsPath)
    (hq : q.IsPath) (h : p ≠ q) :
    ∃ w, w ∈ p.support ∧ w ∈ q.support ∧
      ∃ c : G.Walk w w, c.IsCycle ∧ c.length ≤ p.length + q.length := by
  obtain ⟨w, hw₁, hw₂, c, hc₁, hc₂⟩ := hp.exists_isCycle_sublist_of_ne hq h
  use w, hw₁, hw₂, c, hc₁, by grind [hc₂.length_le]

variable [DecidableEq V] {u' v' : V}

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`. -/
/-
**SimpleGraph.Walk.bypass** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：bypass {u v : V} : G.Walk u v -> G.Walk u v | nil => nil | cons ha p => le
t p'
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a walk, produces a walk from it by bypassing subwalks between repeated ver
tices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`.
-/
def bypass {u v : V} : G.Walk u v → G.Walk u v
  | nil => nil
  | cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then
      p'.dropUntil u hs
    else
      cons ha p'

@[simp]
/-
**SimpleGraph.Walk.bypass_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：bypass_copy (p : G.Walk u v) (hu : u = u') (hv : v = v') : (p.copy hu hv).
bypass = p.bypass.copy hu hv
参数：p : G.Walk u v；hu : u = u'；hv : v = v'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem bypass_copy (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv := by
  subst_vars
  rfl
/-
**SimpleGraph.Walk.bypass_isPath** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：bypass_isPath (p : G.Walk u v) : p.bypass.IsPath
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `SimpleGraph.Walk.IsPath.dropUntil`：∀ {V : Type u} {G : SimpleGraph V} [i
nst : DecidableEq V] {u v w : V} {p : G.Walk v w},   p.IsPath → ∀ (h : u ∈ p.sup
port), (p.dropUntil u h…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem bypass_isPath (p : G.Walk u v) : p.bypass.IsPath := by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]

/-- Given a walk, produces a path with the same endpoints using `SimpleGraph.Walk.bypass`. -/
/-
**SimpleGraph.Walk.toPath** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：toPath (p : G.Walk u v) : G.Path u v
参数：p : G.Walk u v。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.bypass_isPath`：bypass_isPath (p : G.Walk u v) : p.bypas
s.IsPath

--- 原说明 ---
Given a walk, produces a path with the same endpoints using `SimpleGraph.Walk.by
pass`.
-/
def toPath (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩

open List in
/-
**SimpleGraph.Walk.support_bypass_sublist_support** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：support_bypass_sublist_support (p : G.Walk u v) : p.bypass.support <+ p.su
pport
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.IsSuffix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
.Sublist l₂
· 使用定理 `SimpleGraph.Walk.support_dropUntil_suffix_support`：support_dropUntil_suf
fix_support (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).support <:
+ p.support
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem support_bypass_sublist_support (p : G.Walk u v) : p.bypass.support <+ p.support := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
    · exact support_dropUntil_suffix_support .. |>.sublist.trans ih |>.cons _
    · simpa
/-
**SimpleGraph.Walk.support_bypass_subset_support** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：support_bypass_subset_support (p : G.Walk u v) : p.bypass.support subseteq
 p.support
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `SimpleGraph.Walk.support_bypass_sublist_support`：support_bypass_sublist_
support (p : G.Walk u v) : p.bypass.support <+ p.support
-/
theorem support_bypass_subset_support (p : G.Walk u v) : p.bypass.support ⊆ p.support :=
  p.support_bypass_sublist_support.subset

@[deprecated (since := "2026-05-25")] alias support_bypass_subset := support_bypass_subset_support
/-
**SimpleGraph.Walk.support_toPath_subset_support** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk`。
形式化陈述：support_toPath_subset_support (p : G.Walk u v) : (p.toPath : G.Walk u v).s
upport subseteq p.support
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.support_bypass_subset_support`：support_bypass_subset_su
pport (p : G.Walk u v) : p.bypass.support subseteq p.support
-/
theorem support_toPath_subset_support (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support ⊆ p.support :=
  p.support_bypass_subset_support

@[deprecated (since := "2026-05-25")] alias support_toPath_subset := support_toPath_subset_support

open List in
/-
**SimpleGraph.Walk.darts_bypass_sublist_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：darts_bypass_sublist_darts (p : G.Walk u v) : p.bypass.darts <+ p.darts
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `List.Sublist.trans`：∀ {α : Type u_1} {l₁ l₂ l₃ : List α}, l₁.Sublist l₂ 
→ l₂.Sublist l₃ → l₁.Sublist l₃
· 使用定理 `List.IsSuffix.sublist`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁ <:+ l₂ → l₁
.Sublist l₂
· 使用定理 `SimpleGraph.Walk.darts_dropUntil_suffix_darts`：darts_dropUntil_suffix_da
rts (p : G.Walk v w) (h : u in p.support) : (p.dropUntil u h).darts <:+ p.darts
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
-/
theorem darts_bypass_sublist_darts (p : G.Walk u v) : p.bypass.darts <+ p.darts := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    dsimp! only
    split_ifs
    · exact darts_dropUntil_suffix_darts .. |>.sublist.trans ih |>.cons _
    · simpa
/-
**SimpleGraph.Walk.darts_bypass_subset_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：darts_bypass_subset_darts (p : G.Walk u v) : p.bypass.darts subseteq p.dar
ts
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `SimpleGraph.Walk.darts_bypass_sublist_darts`：darts_bypass_sublist_darts 
(p : G.Walk u v) : p.bypass.darts <+ p.darts
-/
theorem darts_bypass_subset_darts (p : G.Walk u v) : p.bypass.darts ⊆ p.darts :=
  p.darts_bypass_sublist_darts.subset

@[deprecated (since := "2026-05-25")] alias darts_bypass_subset := darts_bypass_subset_darts

open List in
/-
**SimpleGraph.Walk.edges_bypass_sublist_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleG
raph.Walk`。
形式化陈述：edges_bypass_sublist_edges (p : G.Walk u v) : p.bypass.edges <+ p.edges
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.map`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {l₁ l₂ : L
ist α}, l₁.Sublist l₂ → (List.map f l₁).Sublist (List.map f l₂)
· 使用定理 `SimpleGraph.Walk.darts_bypass_sublist_darts`：darts_bypass_sublist_darts 
(p : G.Walk u v) : p.bypass.darts <+ p.darts
-/
theorem edges_bypass_sublist_edges (p : G.Walk u v) : p.bypass.edges <+ p.edges :=
  p.darts_bypass_sublist_darts.map _
/-
**SimpleGraph.Walk.edges_bypass_subset_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：edges_bypass_subset_edges (p : G.Walk u v) : p.bypass.edges subseteq p.edg
es
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `SimpleGraph.Walk.edges_bypass_sublist_edges`：edges_bypass_sublist_edges 
(p : G.Walk u v) : p.bypass.edges <+ p.edges
-/
theorem edges_bypass_subset_edges (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  p.edges_bypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")] alias edges_bypass_subset := edges_bypass_subset_edges
/-
**SimpleGraph.Walk.length_bypass_le_length** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGrap
h.Walk`。
形式化陈述：length_bypass_le_length (p : G.Walk u v) : p.bypass.length <= p.length
参数：p : G.Walk u v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `List.Sublist.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂
 → l₁.length ≤ l₂.length
· 使用定理 `SimpleGraph.Walk.darts_bypass_sublist_darts`：darts_bypass_sublist_darts 
(p : G.Walk u v) : p.bypass.darts <+ p.darts
-/
theorem length_bypass_le_length (p : G.Walk u v) : p.bypass.length ≤ p.length := by
  simpa using p.darts_bypass_sublist_darts.length_le

@[deprecated (since := "2026-05-25")] alias length_bypass_le := length_bypass_le_length
/-
**SimpleGraph.Walk.bypass_eq_self_of_length_le_length_bypass** 是 Mathlib 中的一个引理，
位于命名空间 `SimpleGraph.Walk`。
形式化陈述：bypass_eq_self_of_length_le_length_bypass (p : G.Walk u v) (h : p.length <
= p.bypass.length) : p.bypass = p
参数：p : G.Walk u v；h : p.length <= p.bypass.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SimpleGraph.Walk.ext_support`：ext_support {u v} {p q : G.Walk u v} (h : 
p.support = q.support) : p = q
· 使用定理 `List.Sublist.eq_of_length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Subl
ist l₂ → l₂.length ≤ l₁.length → l₁ = l₂
· 使用定理 `SimpleGraph.Walk.support_bypass_sublist_support`：support_bypass_sublist_
support (p : G.Walk u v) : p.bypass.support <+ p.support
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_support`：length_support {u v : V} (p : G.Walk u 
v) : p.support.length = p.length + 1
-/
lemma bypass_eq_self_of_length_le_length_bypass (p : G.Walk u v) (h : p.length ≤ p.bypass.length) :
    p.bypass = p :=
  ext_support <| p.support_bypass_sublist_support.eq_of_length_le <| by simpa using h

@[deprecated (since := "2026-05-25")]
alias bypass_eq_self_of_length_le := bypass_eq_self_of_length_le_length_bypass

@[grind →]
/-
**SimpleGraph.Walk.IsPath.bypass_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} [inst : DecidableEq V] {p : G
.Walk u v}, p.IsPath → p.bypass = p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instLawfulBEq`：∀ {α : Type u_1} [inst : DecidableEq α], LawfulBEq α
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `SimpleGraph.Walk.cons.congr_simp`：∀ {V : Type u} {G : SimpleGraph V} {u 
v w : V} (h : G.Adj u v) (p p_1 : G.Walk v w),   p = p_1 → SimpleGraph.Walk.cons
 h p = SimpleGraph.Wal…
-/
lemma IsPath.bypass_eq_self {p : G.Walk u v} (hp : p.IsPath) : p.bypass = p := by
  induction p <;> simp_all [cons_isPath_iff, bypass]
/-
**SimpleGraph.Walk.darts_toPath_subset_darts** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：darts_toPath_subset_darts (p : G.Walk u v) : (p.toPath : G.Walk u v).darts
 subseteq p.darts
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.darts_bypass_subset_darts`：darts_bypass_subset_darts (p
 : G.Walk u v) : p.bypass.darts subseteq p.darts
-/
theorem darts_toPath_subset_darts (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  p.darts_bypass_subset_darts

@[deprecated (since := "2026-05-25")] alias darts_toPath_subset := darts_toPath_subset_darts
/-
**SimpleGraph.Walk.edges_toPath_subset_edges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：edges_toPath_subset_edges (p : G.Walk u v) : (p.toPath : G.Walk u v).edges
 subseteq p.edges
参数：p : G.Walk u v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.edges_bypass_subset_edges`：edges_bypass_subset_edges (p
 : G.Walk u v) : p.bypass.edges subseteq p.edges
-/
theorem edges_toPath_subset_edges (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  p.edges_bypass_subset_edges

@[deprecated (since := "2026-05-25")] alias edges_toPath_subset := edges_toPath_subset_edges

/-- Bypass repeated vertices like `Walk.bypass`, except the starting vertex.

This is intended to be used for closed walks, for which `Walk.bypass` unhelpfully returns the empty
walk. -/
/-
**SimpleGraph.Walk.cycleBypass** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{V : Type u} → {G : SimpleGraph V} → {v : V} → [DecidableEq V] → G.Walk v 
v → G.Walk v v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bypass repeated vertices like `Walk.bypass`, except the starting vertex.

This is intended to be used for closed walks, for which `Walk.bypass` unhelpfull
y returns the empty
walk.
-/
def cycleBypass : G.Walk v v → G.Walk v v
  | .nil => .nil
  | .cons hvv' w => .cons hvv' w.bypass
/-
**SimpleGraph.Walk.cycleBypass_nil** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V],   Simpl
eGraph.Walk.nil.cycleBypass = SimpleGraph.Walk.nil
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma cycleBypass_nil : (.nil : G.Walk v v).cycleBypass = .nil := rfl

open List in
/-
**SimpleGraph.Walk.support_cycleBypass_sublist_support** 是 Mathlib 中的一个定理，位于命名空间
 `SimpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] (w : G.W
alk v v),   w.cycleBypass.support.Sublist w.support
参数：w : G.Walk v v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `SimpleGraph.Walk.support_bypass_sublist_support`：support_bypass_sublist_
support (p : G.Walk u v) : p.bypass.support <+ p.support
-/
theorem support_cycleBypass_sublist_support : ∀ (w : G.Walk v v), w.cycleBypass.support <+ w.support
  | .nil => .refl _
  | .cons _ w => w.support_bypass_sublist_support.cons_cons _

open List in
/-
**SimpleGraph.Walk.darts_cycleBypass_sublist_darts** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] (w : G.W
alk v v), w.cycleBypass.darts.Sublist w.darts
参数：w : G.Walk v v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `SimpleGraph.Walk.darts_bypass_sublist_darts`：darts_bypass_sublist_darts 
(p : G.Walk u v) : p.bypass.darts <+ p.darts
-/
theorem darts_cycleBypass_sublist_darts : ∀ (w : G.Walk v v), w.cycleBypass.darts <+ w.darts
  | .nil => .refl _
  | .cons _ w => w.darts_bypass_sublist_darts.cons_cons _

open List in
/-
**SimpleGraph.Walk.edges_cycleBypass_sublist_edges** 是 Mathlib 中的一个定理，位于命名空间 `Si
mpleGraph.Walk`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] (w : G.W
alk v v), w.cycleBypass.edges.Sublist w.edges
参数：w : G.Walk v v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.refl`：∀ {α : Type u_1} (l : List α), l.Sublist l
· 使用定理 `SimpleGraph.Walk.edges_bypass_sublist_edges`：edges_bypass_sublist_edges 
(p : G.Walk u v) : p.bypass.edges <+ p.edges
-/
theorem edges_cycleBypass_sublist_edges : ∀ (w : G.Walk v v), w.cycleBypass.edges <+ w.edges
  | .nil => .refl _
  | .cons _ w => w.edges_bypass_sublist_edges.cons_cons _
/-
**SimpleGraph.Walk.edges_cycleBypass_subset_edges** 是 Mathlib 中的一个引理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：edges_cycleBypass_subset_edges (w : G.Walk v v) : w.cycleBypass.edges subs
eteq w.edges
参数：w : G.Walk v v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `List.Sublist.subset`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂ → 
l₁ ⊆ l₂
· 使用定理 `SimpleGraph.Walk.edges_cycleBypass_sublist_edges`：∀ {V : Type u} {G : Si
mpleGraph V} {v : V} [inst : DecidableEq V] (w : G.Walk v v), w.cycleBypass.edge
s.Sublist w.edges
-/
lemma edges_cycleBypass_subset_edges (w : G.Walk v v) : w.cycleBypass.edges ⊆ w.edges :=
  w.edges_cycleBypass_sublist_edges.subset

@[deprecated (since := "2026-05-25")]
alias edges_cycleBypass_subset := edges_cycleBypass_subset_edges
/-
**SimpleGraph.Walk.length_cycleBypass_le_length** 是 Mathlib 中的一个引理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：length_cycleBypass_le_length (w : G.Walk v v) : w.cycleBypass.length <= w.
length
参数：w : G.Walk v v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.length_darts`：length_darts {u v : V} (p : G.Walk u v) :
 p.darts.length = p.length
· 使用定理 `List.Sublist.length_le`：∀ {α : Type u_1} {l₁ l₂ : List α}, l₁.Sublist l₂
 → l₁.length ≤ l₂.length
· 使用定理 `SimpleGraph.Walk.darts_cycleBypass_sublist_darts`：∀ {V : Type u} {G : Si
mpleGraph V} {v : V} [inst : DecidableEq V] (w : G.Walk v v), w.cycleBypass.dart
s.Sublist w.darts
-/
lemma length_cycleBypass_le_length (w : G.Walk v v) : w.cycleBypass.length ≤ w.length := by
  simpa using w.darts_cycleBypass_sublist_darts.length_le
/-
**SimpleGraph.Walk.IsCircuit.isCycle_cycleBypass** 是 Mathlib 中的一个定理，位于命名空间 `Simp
leGraph.Walk.IsCircuit`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] {w : G.W
alk v v}, w.IsCircuit → w.cycleBypass.IsCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsTrail.cons`：∀ {V : Type u} {G : SimpleGraph V} {u u' 
v : V} {w : G.Walk u' v},   w.IsTrail → ∀ (hu : G.Adj u u'), s(u, u') ∉ w.edges 
→ (SimpleGraph.Walk…
· 使用定理 `SimpleGraph.Walk.IsPath.isTrail`：∀ {V : Type u} {G : SimpleGraph V} {u v
 : V} {p : G.Walk u v}, p.IsPath → p.IsTrail
· 使用定理 `SimpleGraph.Walk.bypass_isPath`：bypass_isPath (p : G.Walk u v) : p.bypas
s.IsPath
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `SimpleGraph.Walk.edges_bypass_subset_edges`：edges_bypass_subset_edges (p
 : G.Walk u v) : p.bypass.edges subseteq p.edges
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SimpleGraph.Walk.IsPath.support_nodup`：∀ {V : Type u} {G : SimpleGraph V
} {u v : V} {p : G.Walk u v}, p.IsPath → p.support.Nodup
-/
lemma IsCircuit.isCycle_cycleBypass : ∀ {w : G.Walk v v}, w.IsCircuit → w.cycleBypass.IsCycle
  | .cons (v := v') hvv' w, hw => by
    dsimp [cycleBypass]
    refine ⟨⟨(bypass_isPath _).isTrail.cons _ fun hvv' ↦ ?_, by simp⟩, ?_⟩
    · simp only [isCircuit_def, isTrail_cons, ne_eq, reduceCtorEq, not_false_eq_true,
        and_true] at hw
      exact hw.2 <| edges_bypass_subset_edges _ hvv'
    · simpa using (bypass_isPath _).support_nodup
/-
**SimpleGraph.Walk.IsTrail.isCycle_cycleBypass** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk.IsTrail`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {v : V} [inst : DecidableEq V] {w : G.W
alk v v},   w ≠ SimpleGraph.Walk.nil → w.IsTrail → w.cycleBypass.IsCycle
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCircuit.isCycle_cycleBypass`：∀ {V : Type u} {G : Simp
leGraph V} {v : V} [inst : DecidableEq V] {w : G.Walk v v}, w.IsCircuit → w.cycl
eBypass.IsCycle
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Walk.isCircuit_def`：∀ {V : Type u} {G : SimpleGraph V} {u : 
V} (p : G.Walk u u), p.IsCircuit ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil
-/
lemma IsTrail.isCycle_cycleBypass {w : G.Walk v v} (hw : w ≠ .nil) (hw' : w.IsTrail) :
    w.cycleBypass.IsCycle :=
  (w.isCircuit_def.mpr ⟨hw', hw⟩).isCycle_cycleBypass

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G'} {f : G →g G'} {u v : V} {p : G.Walk u v}

/-
**SimpleGraph.Walk.IsTrail.of_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Trail`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {f 
: G →g G'} {u v : V} {p : G.Walk u v},   (SimpleGraph.Walk.map f p).IsTrail → p.
IsTrail
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isTrail_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v), p.IsTrail ↔ p.edges.Nodup
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `SimpleGraph.Walk.edges_map`：edges_map : (p.map f).edges = p.edges.map (S
ym2.map f)
-/
protected theorem IsTrail.of_map (hp : (p.map f).IsTrail) : p.IsTrail := by
  rw [isTrail_def]
  rw [isTrail_def, edges_map] at hp
  exact hp.of_map
/-
**SimpleGraph.Walk.isTrail_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：isTrail_map_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsT
rail ↔ p.IsTrail
参数：hinj : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isTrail_def`：∀ {V : Type u} {G : SimpleGraph V} {u v : 
V} (p : G.Walk u v), p.IsTrail ↔ p.edges.Nodup
· 使用定理 `SimpleGraph.Walk.edges_map`：edges_map : (p.map f).edges = p.edges.map (S
ym2.map f)
· 使用定理 `List.nodup_map_iff`：nodup_map_iff {f : α -> β} {l : List α} (hf : Inject
ive f) : Nodup (map f l) ↔ Nodup l
· 使用定理 `Sym2.map.injective`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Functio
n.Injective f → Function.Injective (Sym2.map f)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isTrail_map_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  rw [isTrail_def, isTrail_def, edges_map, List.nodup_map_iff <| Sym2.map.injective hinj]

@[deprecated (since := "2026-06-16")]
alias map_isTrail_iff_of_injective := isTrail_map_iff_of_injective

alias ⟨_, IsTrail.map⟩ := isTrail_map_iff_of_injective

@[deprecated (since := "2026-06-16")] alias map_isTrail_of_injective := IsTrail.map
/-
**SimpleGraph.Walk.IsPath.of_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.IsP
ath`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {f 
: G →g G'} {u v : V} {p : G.Walk u v},   (SimpleGraph.Walk.map f p).IsPath → p.I
sPath
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isPath_def`：isPath_def {u v : V} (p : G.Walk u v) : p.I
sPath ↔ p.support.Nodup
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
-/
protected theorem IsPath.of_map (hp : (p.map f).IsPath) : p.IsPath := by
  rw [isPath_def]
  rw [isPath_def, support_map] at hp
  exact hp.of_map
/-
**SimpleGraph.Walk.isPath_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：isPath_map_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPa
th ↔ p.IsPath
参数：hinj : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isPath_def`：isPath_def {u v : V} (p : G.Walk u v) : p.I
sPath ↔ p.support.Nodup
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `List.nodup_map_iff`：nodup_map_iff {f : α -> β} {l : List α} (hf : Inject
ive f) : Nodup (map f l) ↔ Nodup l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPath_map_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsPath ↔ p.IsPath := by
  rw [isPath_def, isPath_def, support_map, List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isPath_iff_of_injective := isPath_map_iff_of_injective

alias ⟨_, IsPath.map⟩ := isPath_map_iff_of_injective

@[deprecated (since := "2026-06-16")] alias map_isPath_of_injective := IsPath.map
/-
**SimpleGraph.Walk.IsCircuit.of_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsCircuit`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {f 
: G →g G'} {u : V} {p : G.Walk u u},   (SimpleGraph.Walk.map f p).IsCircuit → p.
IsCircuit
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isCircuit_def`：∀ {V : Type u} {G : SimpleGraph V} {u : 
V} (p : G.Walk u u), p.IsCircuit ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `SimpleGraph.Walk.eq_nil_iff_nil`：eq_nil_iff_nil {p : G.Walk v v} : p = n
il ↔ p.Nil
· 使用定理 `And.imp_left`：∀ {a b c : Prop}, (a → b) → a ∧ c → b ∧ c
· 使用定理 `SimpleGraph.Walk.IsTrail.of_map`：∀ {V : Type u} {V' : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph V'} {f : G →g G'} {u v : V} {p : G.Walk u v},   (Sim
pleGraph.Walk.map f p…
· 使用定理 `SimpleGraph.Walk.nil_map_iff`：nil_map_iff : (p.map f).Nil ↔ p.Nil
-/
protected theorem IsCircuit.of_map {p : G.Walk u u} (hp : (p.map f).IsCircuit) : p.IsCircuit := by
  rw [isCircuit_def, ne_eq, eq_nil_iff_nil]
  rw [isCircuit_def, ne_eq, eq_nil_iff_nil, nil_map_iff] at hp
  exact hp.imp_left .of_map
/-
**SimpleGraph.Walk.isCircuit_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Sim
pleGraph.Walk`。
形式化陈述：isCircuit_map_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective
 f) : (p.map f).IsCircuit ↔ p.IsCircuit
参数：hinj : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isCircuit_def`：∀ {V : Type u} {G : SimpleGraph V} {u : 
V} (p : G.Walk u u), p.IsCircuit ↔ p.IsTrail ∧ p ≠ SimpleGraph.Walk.nil
· 使用定理 `SimpleGraph.Walk.isTrail_map_iff_of_injective`：isTrail_map_iff_of_inject
ive (hinj : Function.Injective f) : (p.map f).IsTrail ↔ p.IsTrail
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `SimpleGraph.Walk.eq_nil_iff_nil`：eq_nil_iff_nil {p : G.Walk v v} : p = n
il ↔ p.Nil
· 使用定理 `SimpleGraph.Walk.nil_map_iff`：nil_map_iff : (p.map f).Nil ↔ p.Nil
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCircuit_map_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCircuit ↔ p.IsCircuit := by
  rw [isCircuit_def, isCircuit_def, isTrail_map_iff_of_injective hinj, ne_eq, ne_eq, eq_nil_iff_nil,
    eq_nil_iff_nil, nil_map_iff]

alias ⟨_, IsCircuit.map⟩ := isCircuit_map_iff_of_injective
/-
**SimpleGraph.Walk.IsCycle.of_map** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.Is
Cycle`。
形式化陈述：∀ {V : Type u} {V' : Type v} {G : SimpleGraph V} {G' : SimpleGraph V'} {f 
: G →g G'} {u : V} {p : G.Walk u u},   (SimpleGraph.Walk.map f p).IsCycle → p.Is
Cycle
参数：SimpleGraph.Walk.map f p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isCycle_def`：isCycle_def {u : V} (p : G.Walk u u) : p.I
sCycle ↔ p.IsTrail ∧ p != nil ∧ p.support.tail.Nodup
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `SimpleGraph.Walk.eq_nil_iff_nil`：eq_nil_iff_nil {p : G.Walk v v} : p = n
il ↔ p.Nil
· 使用定理 `And.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∧ b → c ∧ d
· 使用定理 `SimpleGraph.Walk.IsTrail.of_map`：∀ {V : Type u} {V' : Type v} {G : Simpl
eGraph V} {G' : SimpleGraph V'} {f : G →g G'} {u v : V} {p : G.Walk u v},   (Sim
pleGraph.Walk.map f p…
· 使用定理 `And.imp_right`：∀ {a b c : Prop}, (a → b) → c ∧ a → c ∧ b
· 使用定理 `List.Nodup.of_map`：∀ {α : Type u} {β : Type v} (f : α → β) {l : List α},
 (List.map f l).Nodup → l.Nodup
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_tail`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α},
 List.map f l.tail = (List.map f l).tail
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `SimpleGraph.Walk.nil_map_iff`：nil_map_iff : (p.map f).Nil ↔ p.Nil
-/
protected theorem IsCycle.of_map {p : G.Walk u u} (hp : (p.map f).IsCycle) : p.IsCycle := by
  rw [isCycle_def, ne_eq, eq_nil_iff_nil]
  rw [isCycle_def, ne_eq, eq_nil_iff_nil, nil_map_iff, support_map, ← List.map_tail] at hp
  exact hp.imp .of_map <| .imp_right <| .of_map f
/-
**SimpleGraph.Walk.isCycle_map_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `Simpl
eGraph.Walk`。
形式化陈述：isCycle_map_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f
) : (p.map f).IsCycle ↔ p.IsCycle
参数：hinj : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Walk.isCycle_def`：isCycle_def {u : V} (p : G.Walk u u) : p.I
sCycle ↔ p.IsTrail ∧ p != nil ∧ p.support.tail.Nodup
· 使用定理 `SimpleGraph.Walk.isTrail_map_iff_of_injective`：isTrail_map_iff_of_inject
ive (hinj : Function.Injective f) : (p.map f).IsTrail ↔ p.IsTrail
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `SimpleGraph.Walk.eq_nil_iff_nil`：eq_nil_iff_nil {p : G.Walk v v} : p = n
il ↔ p.Nil
· 使用定理 `SimpleGraph.Walk.nil_map_iff`：nil_map_iff : (p.map f).Nil ↔ p.Nil
· 使用定理 `SimpleGraph.Walk.support_map`：support_map : (p.map f).support = p.suppor
t.map f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `List.map_tail`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l : List α},
 List.map f l.tail = (List.map f l).tail
· 使用定理 `List.nodup_map_iff`：nodup_map_iff {f : α -> β} {l : List α} (hf : Inject
ive f) : Nodup (map f l) ↔ Nodup l
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isCycle_map_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def, isCycle_def, isTrail_map_iff_of_injective hinj, ne_eq, ne_eq, eq_nil_iff_nil,
    eq_nil_iff_nil, nil_map_iff, support_map, ← List.map_tail, List.nodup_map_iff hinj]

@[deprecated (since := "2026-06-16")]
alias map_isCycle_iff_of_injective := isCycle_map_iff_of_injective

alias ⟨_, IsCycle.map⟩ := isCycle_map_iff_of_injective

@[simp]
/-
**SimpleGraph.Walk.isTrail_mapLe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isTrail_mapLe {G G' : SimpleGraph V} (h : G <= G') {u v : V} {p : G.Walk u
 v} : (p.mapLe h).IsTrail ↔ p.IsTrail
参数：h : G <= G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isTrail_map_iff_of_injective`：isTrail_map_iff_of_inject
ive (hinj : Function.Injective f) : (p.map f).IsTrail ↔ p.IsTrail
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem isTrail_mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  isTrail_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isTrail := isTrail_mapLe

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := isTrail_mapLe

@[simp]
/-
**SimpleGraph.Walk.isPath_mapLe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isPath_mapLe {G G' : SimpleGraph V} (h : G <= G') {u v : V} {p : G.Walk u 
v} : (p.mapLe h).IsPath ↔ p.IsPath
参数：h : G <= G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isPath_map_iff_of_injective`：isPath_map_iff_of_injectiv
e (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem isPath_mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  isPath_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isPath := isPath_mapLe

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := isPath_mapLe

@[simp]
/-
**SimpleGraph.Walk.isCircuit_mapLe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isCircuit_mapLe {G G' : SimpleGraph V} (h : G <= G') {u : V} {p : G.Walk u
 u} : (p.mapLe h).IsCircuit ↔ p.IsCircuit
参数：h : G <= G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isCircuit_map_iff_of_injective`：isCircuit_map_iff_of_in
jective {p : G.Walk u u} (hinj : Function.Injective f) : (p.map f).IsCircuit ↔ p
.IsCircuit
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem isCircuit_mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCircuit ↔ p.IsCircuit :=
  isCircuit_map_iff_of_injective Function.injective_id

alias ⟨IsCircuit.of_mapLe, IsCircuit.mapLe⟩ := isCircuit_mapLe

@[simp]
/-
**SimpleGraph.Walk.isCycle_mapLe** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：isCycle_mapLe {G G' : SimpleGraph V} (h : G <= G') {u : V} {p : G.Walk u u
} : (p.mapLe h).IsCycle ↔ p.IsCycle
参数：h : G <= G'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.isCycle_map_iff_of_injective`：isCycle_map_iff_of_inject
ive {p : G.Walk u u} (hinj : Function.Injective f) : (p.map f).IsCycle ↔ p.IsCyc
le
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
-/
theorem isCycle_mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  isCycle_map_iff_of_injective Function.injective_id

@[deprecated (since := "2026-06-16")] alias mapLe_isCycle := isCycle_mapLe

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := isCycle_mapLe

end Walk

namespace Path

variable {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
/-
**SimpleGraph.Path.map** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Path`。
形式化陈述：{V : Type u} →   {V' : Type v} →     {G : SimpleGraph V} →       {G' : Sim
pleGraph V'} → (f : G →g G') → Function.Injective ⇑f → {u v : V} → G.Path u v → 
G'.Path (f u) (f v)
参数：f : G →g G'；f u；f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an injective graph homomorphism, map paths to paths.
-/
protected def map (f : G →g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, p.isPath.map hinj⟩
/-
**SimpleGraph.Path.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Path`。
形式化陈述：map_injective {f : G ->g G'} (hinj : Function.Injective f) (u v : V) : Fun
ction.Injective (Path.map f hinj : G.Path u v -> G'.Path (f u) (f v))
参数：hinj : Function.Injective f；u v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SimpleGraph.Walk.map_injective_of_injective`：map_injective_of_injective 
{f : G ->g G'} (hinj : Function.Injective f) (u v : V) : Function.Injective (Wal
k.map f : G.Walk u v -> G'.Walk (…
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]

/-- Given a graph embedding, map paths to paths. -/
@[simps!]
/-
**SimpleGraph.Path.mapEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Path`。
形式化陈述：{V : Type u} →   {V' : Type v} →     {G : SimpleGraph V} → {G' : SimpleGra
ph V'} → (f : G ↪g G') → {u v : V} → G.Path u v → G'.Path (f u) (f v)
参数：f : G ↪g G'；f u；f v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graph embedding, map paths to paths.
-/
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.injective p
/-
**SimpleGraph.Path.mapEmbedding_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Path`。
形式化陈述：mapEmbedding_injective (f : G ↪g G') (u v : V) : Function.Injective (Path.
mapEmbedding f : G.Path u v -> G'.Path (f u) (f v))
参数：f : G ↪g G'；u v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Path.map_injective`：map_injective {f : G ->g G'} (hinj : Fun
ction.Injective f) (u v : V) : Function.Injective (Path.map f hinj : G.Path u v 
-> G'.Path (f u) (f …
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.injective u v

end Path

/-! ### Transferring between graphs -/

namespace Walk

variable {G} {u v : V} {H : SimpleGraph V}
variable {p : G.Walk u v}

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.IsPath.transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.I
sPath`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u v : V} {H : SimpleGraph V} {p : G.Wa
lk u v} (hp : ∀ e ∈ p.edges, e ∈ H.edgeSet),   p.IsPath → (p.transfer H hp).IsPa
th
参数：hp : ∀ e ∈ p.edges, e ∈ H.edgeSet；p.transfer H hp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.support_transfer`：support_transfer (hp) : (p.transfer H
 hp).support = p.support
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem IsPath.transfer (hp) (pp : p.IsPath) :
    (p.transfer H hp).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩

set_option backward.isDefEq.respectTransparency.types false in
/-
**SimpleGraph.Walk.IsCycle.transfer** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Walk.
IsCycle`。
形式化陈述：∀ {V : Type u} {G : SimpleGraph V} {u : V} {H : SimpleGraph V} {q : G.Walk
 u u},   q.IsCycle → ∀ (hq : ∀ e ∈ q.edges, e ∈ H.edgeSet), (q.transfer H hq).Is
Cycle
参数：hq : ∀ e ∈ q.edges, e ∈ H.edgeSet；q.transfer H hq。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SimpleGraph.Walk.edges_transfer`：edges_transfer (hp) : (p.transfer H hp)
.edges = p.edges
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `SimpleGraph.Walk.IsPath.transfer`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} {H : SimpleGraph V} {p : G.Walk u v} (hp : ∀ e ∈ p.edges, e ∈ H.edgeSet),
   p.IsPath → (p.trans…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
protected theorem IsCycle.transfer {q : G.Walk u u} (qc : q.IsCycle) (hq) :
    (q.transfer H hq).IsCycle := by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.mem_cons, forall_eq_or_imp] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩

end Walk

/-! ## Deleting edges -/

namespace Walk

variable {v w : V}

/-
**SimpleGraph.Walk.IsPath.toDeleteEdges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.W
alk.IsPath`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {v w : V} (s : Set (Sym2 V)) {p : G.Wal
k v w},   p.IsPath → ∀ (hp : ∀ e ∈ p.edges, e ∉ s), (SimpleGraph.Walk.toDeleteEd
ges s p hp).IsPath
参数：G : SimpleGraph V；s : Set (Sym2 V)；hp : ∀ e ∈ p.edges, e ∉ s；SimpleGraph.Walk
.toDeleteEdges s p hp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsPath.transfer`：∀ {V : Type u} {G : SimpleGraph V} {u 
v : V} {H : SimpleGraph V} {p : G.Walk u v} (hp : ∀ e ∈ p.edges, e ∈ H.edgeSet),
   p.IsPath → (p.trans…
-/
protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v w} (h : p.IsPath) (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _
/-
**SimpleGraph.Walk.IsCycle.toDeleteEdges** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Walk.IsCycle`。
形式化陈述：∀ {V : Type u} (G : SimpleGraph V) {v : V} (s : Set (Sym2 V)) {p : G.Walk 
v v},   p.IsCycle → ∀ (hp : ∀ e ∈ p.edges, e ∉ s), (SimpleGraph.Walk.toDeleteEdg
es s p hp).IsCycle
参数：G : SimpleGraph V；s : Set (Sym2 V)；hp : ∀ e ∈ p.edges, e ∉ s；SimpleGraph.Walk
.toDeleteEdges s p hp。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.IsCycle.transfer`：∀ {V : Type u} {G : SimpleGraph V} {u
 : V} {H : SimpleGraph V} {q : G.Walk u u},   q.IsCycle → ∀ (hq : ∀ e ∈ q.edges,
 e ∈ H.edgeSet), (q.tra…
-/
protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _

@[simp]
/-
**SimpleGraph.Walk.toDeleteEdges_copy** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Wal
k`。
形式化陈述：toDeleteEdges_copy {v u u' v' : V} (s : Set (Sym2 V)) (p : G.Walk u v) (hu
 : u = u') (hv : v = v') (h) : (p.copy hu hv).toDeleteEdges s h = (p.toDeleteEdg
es s (by subst_vars; exact h)).copy hu hv
参数：s : Set (Sym2 V)；p : G.Walk u v；hu : u = u'；hv : v = v'；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem toDeleteEdges_copy {v u u' v' : V} (s : Set (Sym2 V))
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s (by subst_vars; exact h)).copy hu hv := by
  subst_vars
  rfl

end Walk

end SimpleGraph

