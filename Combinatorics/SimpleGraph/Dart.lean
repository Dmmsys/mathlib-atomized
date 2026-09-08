/-
Copyright (c) 2020 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Sigma

/-!
# Darts in graphs

A `Dart` or half-edge or bond in a graph is an ordered pair of adjacent vertices, regarded as an
oriented edge. This file defines darts and proves some of their basic properties.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertices.
This terminology comes from combinatorial maps, and they are also known as "half-edges"
or "bonds." -/
/-
**SimpleGraph.Dart** 是 Mathlib 中的一个归纳类型，位于命名空间 `SimpleGraph`。
形式化陈述：{V : Type u_1} → SimpleGraph V → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Dart` is an oriented edge, implemented as an ordered pair of adjacent vertice
s.
This terminology comes from combinatorial maps, and they are also known as "half
-edges"
or "bonds."
-/
structure Dart extends V × V where
  adj : G.Adj fst snd
  deriving DecidableEq

initialize_simps_projections Dart (+toProd, -fst, -snd)

attribute [simp] Dart.adj

variable {G}
/-
**SimpleGraph.Dart.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Dart), d₁ = d₂ ↔ d₁.toProd
 = d₂.toProd
参数：d₁ d₂ : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Dart.mk.injEq`：∀ {V : Type u_1} {G : SimpleGraph V} (toProd 
: V × V) (adj : G.Adj toProd.1 toProd.2) (toProd_1 : V × V)   (adj_1 : G.Adj toP
rod_1.1 toProd_…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Dart.ext_iff (d₁ d₂ : G.Dart) : d₁ = d₂ ↔ d₁.toProd = d₂.toProd := by
  cases d₁; cases d₂; simp

@[ext]
/-
**SimpleGraph.Dart.ext** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Dart), d₁.toProd = d₂.toPr
od → d₁ = d₂
参数：d₁ d₂ : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SimpleGraph.Dart.ext_iff`：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : 
G.Dart), d₁ = d₂ ↔ d₁.toProd = d₂.toProd
-/
theorem Dart.ext (d₁ d₂ : G.Dart) (h : d₁.toProd = d₂.toProd) : d₁ = d₂ :=
  (Dart.ext_iff d₁ d₂).mpr h

@[simp]
/-
**SimpleGraph.Dart.fst_ne_snd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Dart), d.toProd.1 ≠ d.toProd.2
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
theorem Dart.fst_ne_snd (d : G.Dart) : d.fst ≠ d.snd :=
  fun h ↦ G.irrefl (h ▸ d.adj)

@[simp]
/-
**SimpleGraph.Dart.snd_ne_fst** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Dart), d.toProd.2 ≠ d.toProd.1
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.irrefl`：∀ {V : Type u} (G : SimpleGraph V) {v : V}, ¬G.Adj v
 v
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
theorem Dart.snd_ne_fst (d : G.Dart) : d.snd ≠ d.fst :=
  fun h ↦ G.irrefl (h ▸ d.adj)
/-
**SimpleGraph.Dart.toProd_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`
。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, Function.Injective SimpleGraph.Dart.
toProd
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Dart.ext`：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Da
rt), d₁.toProd = d₂.toProd → d₁ = d₂
-/
theorem Dart.toProd_injective : Function.Injective (Dart.toProd : G.Dart → V × V) :=
  Dart.ext
/-
**SimpleGraph.Dart.fintype** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → [Fintype V] → [DecidableRel G.Adj] 
→ Fintype G.Dart
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
instance Dart.fintype [Fintype V] [DecidableRel G.Adj] : Fintype G.Dart :=
  Fintype.ofEquiv (Σ v, G.neighborSet v)
    { toFun := fun s => ⟨(s.fst, s.snd), s.snd.property⟩
      invFun := fun d => ⟨d.fst, d.snd, d.adj⟩ }

/-- The edge associated to the dart. -/
/-
**SimpleGraph.Dart.edge** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → G.Dart → Sym2 V
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge associated to the dart.
-/
def Dart.edge (d : G.Dart) : Sym2 V := s(d.fst, d.snd)

@[simp]
/-
**SimpleGraph.Dart.edge_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {p : V × V} (h : G.Adj p.1 p.2), { to
Prod := p, adj := h }.edge = s(p.1, p.2)
参数：h : G.Adj p.1 p.2；p.1, p.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Dart.edge_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).edge = s(p.1, p.2) :=
  rfl

@[simp]
/-
**SimpleGraph.Dart.edge_mem** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Dart), d.edge ∈ G.edgeSet
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
theorem Dart.edge_mem (d : G.Dart) : d.edge ∈ G.edgeSet :=
  d.adj

/-- The dart with reversed orientation from a given dart. -/
@[simps]
/-
**SimpleGraph.Dart.symm** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：{V : Type u_1} → {G : SimpleGraph V} → G.Dart → G.Dart
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The dart with reversed orientation from a given dart.
-/
def Dart.symm (d : G.Dart) : G.Dart :=
  ⟨d.toProd.swap, d.adj.symm⟩

@[simp]
/-
**SimpleGraph.Dart.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {p : V × V} (h : G.Adj p.1 p.2),   { 
toProd := p, adj := h }.symm = { toProd := p.swap, adj := ⋯ }
参数：h : G.Adj p.1 p.2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Dart.symm_mk {p : V × V} (h : G.Adj p.1 p.2) : (Dart.mk p h).symm = Dart.mk p.swap h.symm :=
  rfl

@[simp]
/-
**SimpleGraph.Dart.edge_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Dart), d.symm.edge = d.edge
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Sym2.eq_swap`：eq_swap {a b : α} : s(a, b) = s(b, a)
-/
theorem Dart.edge_symm (d : G.Dart) : d.symm.edge = d.edge :=
  Sym2.eq_swap

@[simp]
/-
**SimpleGraph.Dart.edge_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, SimpleGraph.Dart.edge ∘ SimpleGraph.
Dart.symm = SimpleGraph.Dart.edge
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SimpleGraph.Dart.edge_symm`：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.
Dart), d.symm.edge = d.edge
-/
theorem Dart.edge_comp_symm : Dart.edge ∘ Dart.symm = (Dart.edge : G.Dart → Sym2 V) :=
  funext Dart.edge_symm

@[simp]
/-
**SimpleGraph.Dart.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Dart), d.symm.symm = d
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Dart.ext`：∀ {V : Type u_1} {G : SimpleGraph V} (d₁ d₂ : G.Da
rt), d₁.toProd = d₂.toProd → d₁ = d₂
· 使用定理 `Prod.swap_swap`：∀ {α : Type u_1} {β : Type u_2} (x : α × β), x.swap.swap
 = x
-/
theorem Dart.symm_symm (d : G.Dart) : d.symm.symm = d :=
  Dart.ext _ _ <| Prod.swap_swap _

@[simp]
/-
**SimpleGraph.Dart.symm_involutive** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V}, Function.Involutive SimpleGraph.Dart
.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Dart.symm_symm`：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.
Dart), d.symm.symm = d
-/
theorem Dart.symm_involutive : Function.Involutive (Dart.symm : G.Dart → G.Dart) :=
  Dart.symm_symm
/-
**SimpleGraph.Dart.symm_ne** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Dart`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} (d : G.Dart), d.symm ≠ d
参数：d : G.Dart。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `SimpleGraph.Adj.ne`：∀ {V : Type u} {G : SimpleGraph V} {a b : V}, G.Adj 
a b → a ≠ b
· 使用定理 `SimpleGraph.Dart.adj`：∀ {V : Type u_1} {G : SimpleGraph V} (self : G.Dar
t), G.Adj self.toProd.1 self.toProd.2
-/
theorem Dart.symm_ne (d : G.Dart) : d.symm ≠ d :=
  ne_of_apply_ne (Prod.snd ∘ Dart.toProd) d.adj.ne

set_option backward.isDefEq.respectTransparency false in
/-
**SimpleGraph.dart_edge_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：dart_edge_eq_iff : forall d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁
 = d₂.symm
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `SimpleGraph.Dart.mk.injEq`：∀ {V : Type u_1} {G : SimpleGraph V} (toProd 
: V × V) (adj : G.Adj toProd.1 toProd.2) (toProd_1 : V × V)   (adj_1 : G.Adj toP
rod_1.1 toProd_…
· 使用定理 `SimpleGraph.Adj.symm`：∀ {V : Type u} {G : SimpleGraph V} {u v : V}, G.Ad
j u v → G.Adj v u
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dart_edge_eq_iff : ∀ d₁ d₂ : G.Dart, d₁.edge = d₂.edge ↔ d₁ = d₂ ∨ d₁ = d₂.symm := by
  rintro ⟨p, hp⟩ ⟨q, hq⟩
  simp
/-
**SimpleGraph.dart_edge_eq_mk'_iff** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {d : G.Dart} {u v : V}, d.edge = s(u,
 v) ↔ d.toProd = (u, v) ∨ d.toProd = (v, u)
参数：u, v；u, v；v, u。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Prod.mk.eta`：∀ {α : Type u_1} {β : Type u_2} {p : α × β}, (p.1, p.2) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dart_edge_eq_mk'_iff :
    ∀ {d : G.Dart} {u v : V}, d.edge = s(u, v) ↔ d.toProd = (u, v) ∨ d.toProd = (v, u) := by
  rintro ⟨p, h⟩ _ _
  simp
/-
**SimpleGraph.dart_edge_eq_mk'_iff'** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} {G : SimpleGraph V} {d : G.Dart} {u v : V},   d.edge = s(
u, v) ↔ d.toProd.1 = u ∧ d.toProd.2 = v ∨ d.toProd.1 = v ∧ d.toProd.2 = u
参数：u, v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.dart_edge_eq_mk'_iff`：∀ {V : Type u_1} {G : SimpleGraph V} {
d : G.Dart} {u v : V}, d.edge = s(u, v) ↔ d.toProd = (u, v) ∨ d.toProd = (v, u)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem dart_edge_eq_mk'_iff' :
    ∀ {d : G.Dart} {u v : V},
      d.edge = s(u, v) ↔ d.fst = u ∧ d.snd = v ∨ d.fst = v ∧ d.snd = u := by
  rintro ⟨⟨a, b⟩, h⟩ u v
  rw [dart_edge_eq_mk'_iff]
  simp

variable (G)

/-- Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex. -/
/-
**SimpleGraph.DartAdj** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：DartAdj (d d' : G.Dart) : Prop
参数：d d' : G.Dart。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two darts are said to be adjacent if they could be consecutive
darts in a walk -- that is, the first dart's second vertex is equal to
the second dart's first vertex.
-/
def DartAdj (d d' : G.Dart) : Prop :=
  d.snd = d'.fst

/-- For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`. -/
@[simps]
/-
**SimpleGraph.dartOfNeighborSet** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart
参数：v : V；w : G.neighborSet v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a given vertex `v`, this is the bijective map from the neighbor set at `v`
to the darts `d` with `d.fst = v`.
-/
def dartOfNeighborSet (v : V) (w : G.neighborSet v) : G.Dart :=
  ⟨(v, w), w.property⟩
/-
**SimpleGraph.dartOfNeighborSet_injective** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighbor
Set v)
参数：v : V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem dartOfNeighborSet_injective (v : V) : Function.Injective (G.dartOfNeighborSet v) :=
  fun e₁ e₂ h =>
  Subtype.ext <| by
    injection h with h'
    convert! congr_arg Prod.snd h'
/-
**SimpleGraph.nonempty_dart_top** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
-/
instance nonempty_dart_top [Nontrivial V] : Nonempty (⊤ : SimpleGraph V).Dart := by
  obtain ⟨v, w, h⟩ := exists_pair_ne V
  exact ⟨⟨(v, w), h⟩⟩

end SimpleGraph

