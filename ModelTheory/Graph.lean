/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.ModelTheory.Satisfiability
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# First-Order Structures in Graph Theory

This file defines first-order languages, structures, and theories in graph theory.

## Main Definitions

- `FirstOrder.Language.graph` is the language consisting of a single relation representing
  adjacency.
- `SimpleGraph.structure` is the first-order structure corresponding to a given simple graph.
- `FirstOrder.Language.Theory.simpleGraph` is the theory of simple graphs.
- `FirstOrder.Language.simpleGraphOfStructure` gives the simple graph corresponding to a model
  of the theory of simple graphs.
-/

@[expose] public section

universe u

namespace FirstOrder

namespace Language

open FirstOrder

open Structure

variable {V : Type u} {n : ℕ}

/-! ### Simple Graphs -/

/-- The type of relations for the language of graphs, consisting of a single binary relation `adj`.
-/
/-
**FirstOrder.Language.graphRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Language`
。
形式化陈述：graphRel : Nat -> Type | adj : graphRel 2 deriving DecidableEq  /-- The la
nguage consisting of a single relation representing adjacency. -/ protected def 
graph : Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of relations for the language of graphs, consisting of a single binary 
relation `adj`.
-/
inductive graphRel : ℕ → Type
  | adj : graphRel 2
  deriving DecidableEq

/-- The language consisting of a single relation representing adjacency. -/
/-
**FirstOrder.Language.graph** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：FirstOrder.Language
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The language consisting of a single relation representing adjacency.
-/
protected def graph : Language := ⟨fun _ => Empty, graphRel⟩
  deriving IsRelational

/-- The symbol representing the adjacency relation. -/
/-
**FirstOrder.Language.adj** 是 Mathlib 中的一个缩写定义，位于命名空间 `FirstOrder.Language`。
形式化陈述：adj : Language.graph.Relations 2
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symbol representing the adjacency relation.
-/
abbrev adj : Language.graph.Relations 2 := .adj

/-- Any simple graph can be thought of as a structure in the language of graphs. -/
@[instance_reducible]
/-
**FirstOrder.Language._root_.SimpleGraph.structure** 是 Mathlib 中的一个定义，位于命名空间 `Fi
rstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any simple graph can be thought of as a structure in the language of graphs.
-/
def _root_.SimpleGraph.structure (G : SimpleGraph V) : Language.graph.Structure V where
  RelMap | .adj => (fun x => G.Adj (x 0) (x 1))

namespace graph

/-
**FirstOrder.Language.graph.instSubsingleton** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrd
er.Language.graph`。
形式化陈述：instSubsingleton : Subsingleton (Language.graph.Relations n)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
instance instSubsingleton : Subsingleton (Language.graph.Relations n) :=
  ⟨by rintro ⟨⟩ ⟨⟩; rfl⟩

end graph

/-- The theory of simple graphs. -/
/-
**FirstOrder.Language.Theory.simpleGraph** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.L
anguage.Theory`。
形式化陈述：FirstOrder.Language.graph.Theory
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The theory of simple graphs.
-/
protected def Theory.simpleGraph : Language.graph.Theory :=
  {adj.irreflexive, adj.symmetric}

@[simp]
/-
**FirstOrder.Language.Theory.simpleGraph_model_iff** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Language.Theory`。
形式化陈述：∀ {V : Type u} [inst : FirstOrder.Language.graph.Structure V],   V ⊨ First
Order.Language.Theory.simpleGraph ↔     (Std.Irrefl fun x y => FirstOrder.Langua
ge.Structure.RelMap FirstOrder.Language.adj ![x, y]) ∧       Std.Symm fun x y =>
 FirstOrder.Language.Structure.RelMap FirstOrder.Language.adj ![x, y]
参数：Std.Irrefl fun x y => FirstOrder.Language.Structure.RelMap FirstOrder.Languag
e.adj ![x, y]。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem Theory.simpleGraph_model_iff [Language.graph.Structure V] :
    V ⊨ Theory.simpleGraph ↔
      (Std.Irrefl fun x y : V ↦ RelMap adj ![x, y]) ∧
        Std.Symm fun x y : V ↦ RelMap adj ![x, y] := by
  simp [Theory.simpleGraph]
/-
**FirstOrder.Language.simpleGraph_model** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：simpleGraph_model (G : SimpleGraph V) : @Theory.Model _ V G.structure Theo
ry.simpleGraph
参数：G : SimpleGraph V。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FirstOrder.Language.Theory.simpleGraph_model_iff`：∀ {V : Type u} [inst :
 FirstOrder.Language.graph.Structure V],   V ⊨ FirstOrder.Language.Theory.simple
Graph ↔     (Std.Irrefl fun x y => Fir…
· 使用定理 `SimpleGraph.loopless`：∀ {V : Type u} (self : SimpleGraph V), Std.Irrefl 
self.Adj
· 使用定理 `SimpleGraph.symm`：∀ {V : Type u} (self : SimpleGraph V), Std.Symm self.A
dj
-/
instance simpleGraph_model (G : SimpleGraph V) :
    @Theory.Model _ V G.structure Theory.simpleGraph := by
  let := G.structure
  rw [Theory.simpleGraph_model_iff]
  exact ⟨G.loopless, G.symm⟩

variable (V) in
/-- Any model of the theory of simple graphs represents a simple graph. -/
@[simps]
/-
**FirstOrder.Language.simpleGraphOfStructure** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Language`。
形式化陈述：simpleGraphOfStructure [Language.graph.Structure V] [V ⊨ Theory.simpleGrap
h] : SimpleGraph V where Adj x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any model of the theory of simple graphs represents a simple graph.
-/
def simpleGraphOfStructure [Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    SimpleGraph V where
  Adj x y := RelMap adj ![x, y]

@[simp]
/-
**FirstOrder.Language._root_.SimpleGraph.simpleGraphOfStructure** 是 Mathlib 中的一个
定理，位于命名空间 `FirstOrder.Language`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.SimpleGraph.simpleGraphOfStructure (G : SimpleGraph V) :
    @simpleGraphOfStructure V G.structure _ = G := by
  ext
  rfl

@[simp]
/-
**FirstOrder.Language.structure_simpleGraphOfStructure** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language`。
形式化陈述：structure_simpleGraphOfStructure [S : Language.graph.Structure V] [V ⊨ The
ory.simpleGraph] : (simpleGraphOfStructure V).structure = S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Structure.ext`：∀ {L : FirstOrder.Language} {M : Type
 w} {x y : L.Structure M},   @FirstOrder.Language.Structure.funMap L M x = @Firs
tOrder.Language.Structu…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.instIsRelationalGraph`：FirstOrder.Language.graph.IsR
elational
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `iff_eq_eq`：iff_eq_eq {a b : Prop} : (a ↔ b) = (a = b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem structure_simpleGraphOfStructure [S : Language.graph.Structure V] [V ⊨ Theory.simpleGraph] :
    (simpleGraphOfStructure V).structure = S := by
  ext
  case funMap n f xs =>
    exact isEmptyElim f
  case RelMap n r xs =>
    match n, r with
    | 2, .adj =>
      rw [iff_eq_eq]
      change RelMap adj ![xs 0, xs 1] = _
      refine congr rfl (funext ?_)
      simp [Fin.forall_fin_two]
/-
**FirstOrder.Language.Theory.simpleGraph_isSatisfiable** 是 Mathlib 中的一个定理，位于命名空间
 `FirstOrder.Language.Theory`。
形式化陈述：FirstOrder.Language.Theory.simpleGraph.IsSatisfiable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem Theory.simpleGraph_isSatisfiable : Theory.IsSatisfiable Theory.simpleGraph :=
  ⟨@Theory.ModelType.of _ _ Unit (SimpleGraph.structure ⊥) _ _⟩

end Language

end FirstOrder

