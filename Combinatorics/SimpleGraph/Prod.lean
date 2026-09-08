/-
Copyright (c) 2022 George Peter Banyard, Yaël Dillies, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Peter Banyard, Yaël Dillies, Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Sum

/-!
# Graph products

This file defines the box product of graphs and other product constructions. The box product of `G`
and `H` is the graph on the product of the vertices such that `x` and `y` are related iff they agree
on one component and the other one is related via either `G` or `H`. For example, the box product of
two edges is a square.

## Main declarations

* `SimpleGraph.boxProd`: The box product.

## Notation

* `G □ H`: The box product of `G` and `H`.

## TODO

Define all other graph products!
-/

@[expose] public section

variable {α β γ V V₁ V₂ W W₁ W₂ : Type*}

namespace SimpleGraph

variable {G : SimpleGraph α} {H : SimpleGraph β}

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
/-
**SimpleGraph.boxProd** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) wher
e Adj x y
参数：G : SimpleGraph α；H : SimpleGraph β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates 
`a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`.
-/
def boxProd (G : SimpleGraph α) (H : SimpleGraph β) : SimpleGraph (α × β) where
  Adj x y := G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1
  symm.symm x y := by simp [eq_comm, adj_comm]

/-- Box product of simple graphs. It relates `(a₁, b)` and `(a₂, b)` if `G` relates `a₁` and `a₂`,
and `(a, b₁)` and `(a, b₂)` if `H` relates `b₁` and `b₂`. -/
infixl:70 " □ " => boxProd

@[simp]
/-
**SimpleGraph.boxProd_adj** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：boxProd_adj {x y : α × β} : (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ 
H.Adj x.2 y.2 ∧ x.1 = y.1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem boxProd_adj {x y : α × β} :
    (G □ H).Adj x y ↔ G.Adj x.1 y.1 ∧ x.2 = y.2 ∨ H.Adj x.2 y.2 ∧ x.1 = y.1 :=
  Iff.rfl
/-
**SimpleGraph.boxProd_adj_left** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：boxProd_adj_left {a₁ : α} {b : β} {a₂ : α} : (G □ H).Adj (a₁, b) (a₂, b) ↔
 G.Adj a₁ a₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem boxProd_adj_left {a₁ : α} {b : β} {a₂ : α} :
    (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂ := by
  simp only [boxProd_adj, and_true, SimpleGraph.irrefl, false_and, or_false]
/-
**SimpleGraph.boxProd_adj_right** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：boxProd_adj_right {a : α} {b₁ b₂ : β} : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Ad
j b₁ b₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem boxProd_adj_right {a : α} {b₁ b₂ : β} : (G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂ := by
  simp only [boxProd_adj, SimpleGraph.irrefl, false_and, and_true, false_or]
/-
**SimpleGraph.neighborSet_boxProd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborSet_boxProd (x : α × β) : (G □ H).neighborSet x = G.neighborSet x.
1 ×ˢ {x.2} union {x.1} ×ˢ H.neighborSet x.2
参数：x : α × β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem neighborSet_boxProd (x : α × β) :
    (G □ H).neighborSet x = G.neighborSet x.1 ×ˢ {x.2} ∪ {x.1} ×ˢ H.neighborSet x.2 := by
  ext ⟨a', b'⟩
  simp only [mem_neighborSet, Set.mem_union, boxProd_adj, Set.mem_prod, Set.mem_singleton_iff]
  simp only [eq_comm, and_comm]

variable (G H)

/-- The box product is commutative up to isomorphism. `Equiv.prodComm` as a graph isomorphism. -/
@[simps!]
/-
**SimpleGraph.boxProdComm** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：boxProdComm : G □ H ≃g H □ G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The box product is commutative up to isomorphism. `Equiv.prodComm` as a graph is
omorphism.
-/
def boxProdComm : G □ H ≃g H □ G := ⟨Equiv.prodComm _ _, or_comm⟩

/-- The box product is associative up to isomorphism. `Equiv.prodAssoc` as a graph isomorphism. -/
@[simps!]
/-
**SimpleGraph.boxProdAssoc** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：boxProdAssoc (I : SimpleGraph γ) : G □ H □ I ≃g G □ (H □ I)
参数：I : SimpleGraph γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The box product is associative up to isomorphism. `Equiv.prodAssoc` as a graph i
somorphism.
-/
def boxProdAssoc (I : SimpleGraph γ) : G □ H □ I ≃g G □ (H □ I) :=
  ⟨Equiv.prodAssoc _ _ _, fun {x y} => by
    simp only [boxProd_adj, Equiv.prodAssoc_apply, or_and_right, or_assoc, Prod.ext_iff,
      and_assoc, @and_comm (x.fst.fst = _)]⟩

/-- The embedding of `G` into `G □ H` given by `b`. -/
@[simps]
/-
**SimpleGraph.boxProdLeft** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：boxProdLeft (b : β) : G ↪g G □ H where toFun a
参数：b : β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.boxProd_adj_left`：boxProd_adj_left {a₁ : α} {b : β} {a₂ : α}
 : (G □ H).Adj (a₁, b) (a₂, b) ↔ G.Adj a₁ a₂

--- 原说明 ---
The embedding of `G` into `G □ H` given by `b`.
-/
def boxProdLeft (b : β) : G ↪g G □ H where
  toFun a := (a, b)
  inj' _ _ := congr_arg Prod.fst
  map_rel_iff' {_ _} := boxProd_adj_left

/-- The embedding of `H` into `G □ H` given by `a`. -/
@[simps]
/-
**SimpleGraph.boxProdRight** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：boxProdRight (a : α) : H ↪g G □ H where toFun
参数：a : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.boxProd_adj_right`：boxProd_adj_right {a : α} {b₁ b₂ : β} : (
G □ H).Adj (a, b₁) (a, b₂) ↔ H.Adj b₁ b₂

--- 原说明 ---
The embedding of `H` into `G □ H` given by `a`.
-/
def boxProdRight (a : α) : H ↪g G □ H where
  toFun := Prod.mk a
  inj' _ _ := congr_arg Prod.snd
  map_rel_iff' {_ _} := boxProd_adj_right

namespace Iso

/-- The box product distributes over the disjoint sum of graphs. -/
@[simps!, simps toEquiv]
/-
**SimpleGraph.Iso.boxProdSumDistrib** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：boxProdSumDistrib (G : SimpleGraph V) (H₁ : SimpleGraph W₁) (H₂ : SimpleGr
aph W₂) : G □ (H₁ oplusg H₂) ≃g G □ H₁ oplusg G □ H₂ where toEquiv
参数：G : SimpleGraph V；H₁ : SimpleGraph W₁；H₂ : SimpleGraph W₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The box product distributes over the disjoint sum of graphs.
-/
def boxProdSumDistrib (G : SimpleGraph V) (H₁ : SimpleGraph W₁) (H₂ : SimpleGraph W₂) :
    G □ (H₁ ⊕g H₂) ≃g G □ H₁ ⊕g G □ H₂ where
  toEquiv := .prodSumDistrib ..
  map_rel_iff' := by simp

/-- The box product distributes over the disjoint sum of graphs. -/
@[simps!, simps toEquiv]
/-
**SimpleGraph.Iso.sumBoxProdDistrib** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Iso`。
形式化陈述：sumBoxProdDistrib (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (H : SimpleG
raph W) : (G₁ oplusg G₂) □ H ≃g G₁ □ H oplusg G₂ □ H where toEquiv
参数：G₁ : SimpleGraph V₁；G₂ : SimpleGraph V₂；H : SimpleGraph W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The box product distributes over the disjoint sum of graphs.
-/
def sumBoxProdDistrib (G₁ : SimpleGraph V₁) (G₂ : SimpleGraph V₂) (H : SimpleGraph W) :
    (G₁ ⊕g G₂) □ H ≃g G₁ □ H ⊕g G₂ □ H where
  toEquiv := .sumProdDistrib ..
  map_rel_iff' := by simp

end Iso

namespace Walk

variable {G}

/-- Turn a walk on `G` into a walk on `G □ H`. -/
/-
**SimpleGraph.Walk.boxProdLeft** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {G : SimpleGraph α} → (H : SimpleG
raph β) → {a₁ a₂ : α} → (b : β) → G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b)
参数：H : SimpleGraph β；b : β；G □ H；a₁, b；a₂, b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a walk on `G` into a walk on `G □ H`.
-/
protected def boxProdLeft {a₁ a₂ : α} (b : β) : G.Walk a₁ a₂ → (G □ H).Walk (a₁, b) (a₂, b) :=
  Walk.map (G.boxProdLeft H b).toHom

variable (G) {H}

/-- Turn a walk on `H` into a walk on `G □ H`. -/
/-
**SimpleGraph.Walk.boxProdRight** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     (G : SimpleGraph α) → {H : SimpleG
raph β} → {b₁ b₂ : β} → (a : α) → H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂)
参数：G : SimpleGraph α；a : α；G □ H；a, b₁；a, b₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Turn a walk on `H` into a walk on `G □ H`.
-/
protected def boxProdRight {b₁ b₂ : β} (a : α) : H.Walk b₁ b₂ → (G □ H).Walk (a, b₁) (a, b₂) :=
  Walk.map (G.boxProdRight H a).toHom

variable {G}

/-- Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direction of `H`. -/
/-
**SimpleGraph.Walk.ofBoxProdLeft** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {G : SimpleGraph α} →       {H : S
impleGraph β} → [DecidableEq β] → [DecidableRel G.Adj] → {x y : α × β} → (G □ H)
.Walk x y → G.Walk x.1 y.1
参数：G □ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Project a walk on `G □ H` to a walk on `G` by discarding the moves in the direct
ion of `H`.
-/
def ofBoxProdLeft [DecidableEq β] [DecidableRel G.Adj] {x y : α × β} :
    (G □ H).Walk x y → G.Walk x.1 y.1
  | nil => nil
  | cons h w =>
    Or.by_cases h
      (fun hG => w.ofBoxProdLeft.cons hG.1)
      (fun hH => hH.2 ▸ w.ofBoxProdLeft)

/-- Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direction of `G`. -/
/-
**SimpleGraph.Walk.ofBoxProdRight** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {G : SimpleGraph α} →       {H : S
impleGraph β} → [DecidableEq α] → [DecidableRel H.Adj] → {x y : α × β} → (G □ H)
.Walk x y → H.Walk x.2 y.2
参数：G □ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Project a walk on `G □ H` to a walk on `H` by discarding the moves in the direct
ion of `G`.
-/
def ofBoxProdRight [DecidableEq α] [DecidableRel H.Adj] {x y : α × β} :
    (G □ H).Walk x y → H.Walk x.2 y.2
  | nil => nil
  | cons h w =>
    (Or.symm h).by_cases
      (fun hH => w.ofBoxProdRight.cons hH.1)
      (fun hG => hG.2 ▸ w.ofBoxProdRight)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.ofBoxProdLeft_boxProdLeft** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph.Walk`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β} [i
nst : DecidableEq β]   [inst_1 : DecidableRel G.Adj] {a₁ a₂ : α} {b : β} (w : G.
Walk a₁ a₂),   (SimpleGraph.Walk.boxProdLeft H b w).ofBoxProdLeft = w
参数：w : G.Walk a₁ a₂；SimpleGraph.Walk.boxProdLeft H b w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoxProdLeft_boxProdLeft [DecidableEq β] [DecidableRel G.Adj] {a₁ a₂ : α} {b : β} :
    ∀ (w : G.Walk a₁ a₂), (w.boxProdLeft H b).ofBoxProdLeft = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdLeft, map_cons, ofBoxProdLeft, Or.by_cases, dif_pos, ← Walk.boxProdLeft]
    · simp [ofBoxProdLeft_boxProdLeft]
    · exact ⟨h, rfl⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.Walk.ofBoxProdRight_boxProdRight** 是 Mathlib 中的一个定理，位于命名空间 `Simple
Graph.Walk`。
形式化陈述：∀ {α : Type u_1} {G : SimpleGraph α} [inst : DecidableEq α] [inst_1 : Deci
dableRel G.Adj] {a b₁ b₂ : α}   (w : G.Walk b₁ b₂), (SimpleGraph.Walk.boxProdRig
ht G a w).ofBoxProdRight = w
参数：w : G.Walk b₁ b₂；SimpleGraph.Walk.boxProdRight G a w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofBoxProdRight_boxProdRight [DecidableEq α] [DecidableRel G.Adj] {a b₁ b₂ : α} :
    ∀ (w : G.Walk b₁ b₂), (w.boxProdRight G a).ofBoxProdRight = w
  | nil => rfl
  | cons' x y z h w => by
    rw [Walk.boxProdRight, map_cons, ofBoxProdRight, Or.by_cases, dif_pos, ←
      Walk.boxProdRight]
    · simp [ofBoxProdRight_boxProdRight]
    · exact ⟨h, rfl⟩
/-
**SimpleGraph.Walk.length_boxProd** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph.Walk`。
形式化陈述：length_boxProd {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β] [De
cidableRel G.Adj] [DecidableRel H.Adj] (w : (G □ H).Walk (a₁, b₁) (a₂, b₂)) : w.
length = w.ofBoxProdLeft.length + w.ofBoxProdRight.length
参数：w : (G □ H).Walk (a₁, b₁) (a₂, b₂)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Walk.length_boxProd._unary`：∀ {α : Type u_1} {β : Type u_2} 
{G : SimpleGraph α} {H : SimpleGraph β} [inst : DecidableEq α] [inst_1 : Decidab
leEq β]   [inst_2 : Decidabl…
-/
lemma length_boxProd {a₁ a₂ : α} {b₁ b₂ : β} [DecidableEq α] [DecidableEq β]
    [DecidableRel G.Adj] [DecidableRel H.Adj] (w : (G □ H).Walk (a₁, b₁) (a₂, b₂)) :
    w.length = w.ofBoxProdLeft.length + w.ofBoxProdRight.length := by
  match w with
  | .nil => simp [ofBoxProdLeft, ofBoxProdRight]
  | .cons x w' => next c =>
    unfold ofBoxProdLeft ofBoxProdRight
    rw [length_cons, length_boxProd w']
    have disj : (G.Adj a₁ c.1 ∧ b₁ = c.2) ∨ (H.Adj b₁ c.2 ∧ a₁ = c.1) := by simp_all
    rcases disj with h₁ | h₂
    · simp only [h₁, and_self, ↓reduceDIte, length_cons, Or.by_cases]
      rw [add_comm, add_comm w'.ofBoxProdLeft.length 1, add_assoc]
      congr <;> simp [h₁.2.symm]
    · simp only [h₂, add_assoc, Or.by_cases]
      congr <;> simp [h₂.2.symm]

end Walk

variable {G H}

/-
**SimpleGraph.Preconnected.boxProd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Precon
nected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β},  
 G.Preconnected → H.Preconnected → (G □ H).Preconnected
参数：G □ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Preconnected.boxProd (hG : G.Preconnected) (hH : H.Preconnected) :
    (G □ H).Preconnected := by
  rintro x y
  obtain ⟨w₁⟩ := hG x.1 y.1
  obtain ⟨w₂⟩ := hH x.2 y.2
  exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩
/-
**SimpleGraph.Preconnected.ofBoxProdLeft** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.
Preconnected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β} [N
onempty β],   (G □ H).Preconnected → G.Preconnected
参数：G □ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Preconnected.ofBoxProdLeft [Nonempty β] (h : (G □ H).Preconnected) :
    G.Preconnected := by
  classical
  rintro a₁ a₂
  obtain ⟨w⟩ := h (a₁, Classical.arbitrary _) (a₂, Classical.arbitrary _)
  exact ⟨w.ofBoxProdLeft⟩
/-
**SimpleGraph.Preconnected.ofBoxProdRight** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
.Preconnected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β} [N
onempty α],   (G □ H).Preconnected → H.Preconnected
参数：G □ H。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem Preconnected.ofBoxProdRight [Nonempty α] (h : (G □ H).Preconnected) :
    H.Preconnected := by
  classical
  rintro b₁ b₂
  obtain ⟨w⟩ := h (Classical.arbitrary _, b₁) (Classical.arbitrary _, b₂)
  exact ⟨w.ofBoxProdRight⟩
/-
**SimpleGraph.Connected.boxProd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Connected
`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β}, G
.Connected → H.Connected → (G □ H).Connected
参数：G □ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `SimpleGraph.Preconnected.boxProd`：∀ {α : Type u_1} {β : Type u_2} {G : S
impleGraph α} {H : SimpleGraph β},   G.Preconnected → H.Preconnected → (G □ H).P
reconnected
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
-/
protected theorem Connected.boxProd (hG : G.Connected) (hH : H.Connected) : (G □ H).Connected := by
  have := hG.nonempty
  have := hH.nonempty
  exact ⟨hG.preconnected.boxProd hH.preconnected⟩
/-
**SimpleGraph.Connected.ofBoxProdLeft** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Con
nected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β}, (
G □ H).Connected → G.Connected
参数：G □ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_prod`：nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty 
β
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Preconnected.ofBoxProdLeft`：∀ {α : Type u_1} {β : Type u_2} 
{G : SimpleGraph α} {H : SimpleGraph β} [Nonempty β],   (G □ H).Preconnected → G
.Preconnected
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
protected theorem Connected.ofBoxProdLeft (h : (G □ H).Connected) : G.Connected := by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdLeft⟩
/-
**SimpleGraph.Connected.ofBoxProdRight** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph.Co
nnected`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {G : SimpleGraph α} {H : SimpleGraph β}, (
G □ H).Connected → H.Connected
参数：G □ H。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_prod`：nonempty_prod : Nonempty (α × β) ↔ Nonempty α ∧ Nonempty 
β
· 使用定理 `SimpleGraph.Connected.nonempty`：∀ {V : Type u} {G : SimpleGraph V}, G.Co
nnected → Nonempty V
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Preconnected.ofBoxProdRight`：∀ {α : Type u_1} {β : Type u_2}
 {G : SimpleGraph α} {H : SimpleGraph β} [Nonempty α],   (G □ H).Preconnected → 
H.Preconnected
· 使用定理 `SimpleGraph.Connected.preconnected`：∀ {V : Type u} {G : SimpleGraph V}, 
G.Connected → G.Preconnected
-/
protected theorem Connected.ofBoxProdRight (h : (G □ H).Connected) : H.Connected := by
  have := (nonempty_prod.1 h.nonempty).1
  have := (nonempty_prod.1 h.nonempty).2
  exact ⟨h.preconnected.ofBoxProdRight⟩

@[simp]
/-
**SimpleGraph.connected_boxProd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：connected_boxProd : (G □ H).Connected ↔ G.Connected ∧ H.Connected
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.Connected.ofBoxProdLeft`：∀ {α : Type u_1} {β : Type u_2} {G 
: SimpleGraph α} {H : SimpleGraph β}, (G □ H).Connected → G.Connected
· 使用定理 `SimpleGraph.Connected.ofBoxProdRight`：∀ {α : Type u_1} {β : Type u_2} {G
 : SimpleGraph α} {H : SimpleGraph β}, (G □ H).Connected → H.Connected
· 使用定理 `SimpleGraph.Connected.boxProd`：∀ {α : Type u_1} {β : Type u_2} {G : Simp
leGraph α} {H : SimpleGraph β}, G.Connected → H.Connected → (G □ H).Connected
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem connected_boxProd : (G □ H).Connected ↔ G.Connected ∧ H.Connected :=
  ⟨fun h => ⟨h.ofBoxProdLeft, h.ofBoxProdRight⟩, fun h => h.1.boxProd h.2⟩
/-
**SimpleGraph.boxProdFintypeNeighborSet** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
形式化陈述：boxProdFintypeNeighborSet (x : α × β) [Fintype (G.neighborSet x.1)] [Finty
pe (H.neighborSet x.2)] : Fintype ((G □ H).neighborSet x)
参数：x : α × β；G.neighborSet x.1；H.neighborSet x.2。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
instance boxProdFintypeNeighborSet (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] :
    Fintype ((G □ H).neighborSet x) :=
  Fintype.ofEquiv
    ((G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) <|
        Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _)
    ((Equiv.refl _).subtypeEquiv fun y => by
      simp_rw [Finset.mem_disjUnion, Finset.mem_product, Finset.mem_singleton, mem_neighborFinset,
        mem_neighborSet, Equiv.refl_apply, boxProd_adj]
      simp only [eq_comm, and_comm])
/-
**SimpleGraph.neighborFinset_boxProd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：neighborFinset_boxProd (x : α × β) [Fintype (G.neighborSet x.1)] [Fintype 
(H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] : (G □ H).neighborFinset 
x = (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2) (F
inset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _)
参数：x : α × β；G.neighborSet x.1；H.neighborSet x.2；(G □ H).neighborSet x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_product`：disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t')
 ↔ Disjoint s s' ∨ Disjoint t t'
· 使用定理 `SimpleGraph.neighborFinset_disjoint_singleton`：neighborFinset_disjoint_s
ingleton : Disjoint (G.neighborFinset v) {v}
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
· 使用定理 `Finset.map_map`：map_map (f : α ↪ β) (g : β ↪ γ) (s : Finset α) : (s.map 
f).map g = s.map (f.trans g)
· 使用定理 `Finset.attach_map_val`：attach_map_val {s : Finset α} : s.attach.map (Emb
edding.subtype _) = s
-/
theorem neighborFinset_boxProd (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).neighborFinset x =
      (G.neighborFinset x.1 ×ˢ {x.2}).disjUnion ({x.1} ×ˢ H.neighborFinset x.2)
        (Finset.disjoint_product.mpr <| Or.inl <| neighborFinset_disjoint_singleton _ _) := by
  -- swap out the fintype instance for the canonical one
  let : Fintype ((G □ H).neighborSet x) := SimpleGraph.boxProdFintypeNeighborSet _
  convert_to (G □ H).neighborFinset x = _ using 2
  exact Eq.trans (Finset.map_map _ _ _) Finset.attach_map_val
/-
**SimpleGraph.degree_boxProd** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：degree_boxProd (x : α × β) [Fintype (G.neighborSet x.1)] [Fintype (H.neigh
borSet x.2)] [Fintype ((G □ H).neighborSet x)] : (G □ H).degree x = G.degree x.1
 + H.degree x.2
参数：x : α × β；G.neighborSet x.1；H.neighborSet x.2；(G □ H).neighborSet x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.degree.eq_1`：∀ {V : Type u_1} (G : SimpleGraph V) (v : V) [i
nst : Fintype ↑(G.neighborSet v)], G.degree v = (G.neighborFinset v).card
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_product`：disjoint_product : Disjoint (s ×ˢ t) (s' ×ˢ t')
 ↔ Disjoint s s' ∨ Disjoint t t'
· 使用定理 `SimpleGraph.neighborFinset_disjoint_singleton`：neighborFinset_disjoint_s
ingleton : Disjoint (G.neighborFinset v) {v}
· 使用定理 `SimpleGraph.neighborFinset_boxProd`：neighborFinset_boxProd (x : α × β) [
Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).nei
ghborSet x)] : (G □ H).n…
· 使用定理 `Finset.card_disjUnion`：card_disjUnion (s t : Finset α) (h) : #(s.disjUni
on t h) = #s + #t
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.card_product`：card_product (s : Finset α) (t : Finset β) : card (
s ×ˢ t) = card s * card t
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_boxProd (x : α × β)
    [Fintype (G.neighborSet x.1)] [Fintype (H.neighborSet x.2)] [Fintype ((G □ H).neighborSet x)] :
    (G □ H).degree x = G.degree x.1 + H.degree x.2 := by
  rw [degree, degree, degree, neighborFinset_boxProd, Finset.card_disjUnion]
  simp_rw [Finset.card_product, Finset.card_singleton, mul_one, one_mul]
/-
**SimpleGraph.reachable_boxProd** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：reachable_boxProd {x y : α × β} : (G □ H).Reachable x y ↔ G.Reachable x.1 
y.1 ∧ H.Reachable x.2 y.2
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reachable_boxProd {x y : α × β} :
    (G □ H).Reachable x y ↔ G.Reachable x.1 y.1 ∧ H.Reachable x.2 y.2 := by
  classical
  constructor
  · intro ⟨w⟩
    exact ⟨⟨w.ofBoxProdLeft⟩, ⟨w.ofBoxProdRight⟩⟩
  · intro ⟨⟨w₁⟩, ⟨w₂⟩⟩
    exact ⟨(w₁.boxProdLeft _ _).append (w₂.boxProdRight _ _)⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**SimpleGraph.edist_boxProd** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：edist_boxProd (x y : α × β) : (G □ H).edist x y = G.edist x.1 y.1 + H.edis
t x.2 y.2
参数：x y : α × β。
该定理/引理给出了一组等式。
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
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `top_add`：top_add (a : α) : ⊤ + a = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `add_top`：add_top (a : α) : a + ⊤ = ⊤
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用引理 `SimpleGraph.exists_walk_of_edist_ne_top`：exists_walk_of_edist_ne_top (h 
: G.edist u v != ⊤) : exists p : G.Walk u v, p.length = G.edist u v
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `SimpleGraph.Walk.length_append`：length_append {u v w : V} (p : G.Walk u 
v) (q : G.Walk v w) : (p.append q).length = p.length + q.length
· 使用定理 `SimpleGraph.Walk.length_map`：length_map : (p.map f).length = p.length
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `SimpleGraph.edist_le`：edist_le (p : G.Walk u v) : G.edist u v <= p.lengt
h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `SimpleGraph.Walk.length_boxProd`：length_boxProd {a₁ a₂ : α} {b₁ b₂ : β} 
[DecidableEq α] [DecidableEq β] [DecidableRel G.Adj] [DecidableRel H.Adj] (w : (
G □ H).Walk (a₁, b₁) …
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
lemma edist_boxProd (x y : α × β) :
    (G □ H).edist x y = G.edist x.1 y.1 + H.edist x.2 y.2 := by
  classical
  -- The case `(G □ H).edist x y = ⊤` is used twice, so better to factor it out.
  have top_case : (G □ H).edist x y = ⊤ ↔ G.edist x.1 y.1 = ⊤ ∨ H.edist x.2 y.2 = ⊤ := by
    simp_rw [← not_ne_iff, edist_ne_top_iff_reachable, reachable_boxProd, not_and_or]
  by_cases h : (G □ H).edist x y = ⊤
  · rw [top_case] at h
    aesop
  · have rGH : G.edist x.1 y.1 ≠ ⊤ ∧ H.edist x.2 y.2 ≠ ⊤ := by rw [top_case] at h; aesop
    have ⟨wG, hwG⟩ := exists_walk_of_edist_ne_top rGH.1
    have ⟨wH, hwH⟩ := exists_walk_of_edist_ne_top rGH.2
    let w_app := (wG.boxProdLeft _ _).append (wH.boxProdRight _ _)
    have w_len : w_app.length = wG.length + wH.length := by
      unfold w_app Walk.boxProdLeft Walk.boxProdRight; simp
    refine le_antisymm ?_ ?_
    · calc (G □ H).edist x y ≤ w_app.length := by exact edist_le _
          _ = wG.length + wH.length := by exact_mod_cast w_len
          _ = G.edist x.1 y.1 + H.edist x.2 y.2 := by simp only [hwG, hwH]
    · have ⟨w, hw⟩ := exists_walk_of_edist_ne_top h
      rw [← hw, Walk.length_boxProd]
      exact add_le_add (edist_le w.ofBoxProdLeft) (edist_le w.ofBoxProdRight)

end SimpleGraph

