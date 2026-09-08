/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.Topology.Algebra.Module.Basic
public import Mathlib.Topology.Algebra.Module.Equiv

/-!
# Partially defined linear operators over topological vector spaces

We define basic notions of partially defined linear operators, which we call unbounded operators
for short.
In this file we prove all elementary properties of unbounded operators that do not assume that the
underlying spaces are normed.

## Main definitions

* `LinearPMap.IsClosed`: An unbounded operator is closed iff its graph is closed.
* `LinearPMap.IsClosable`: An unbounded operator is closable iff the closure of its graph is a
  graph.
* `LinearPMap.closure`: For a closable unbounded operator `f : LinearPMap R E F` the closure is
  the smallest closed extension of `f`. If `f` is not closable, then `f.closure` is defined as `f`.
* `LinearPMap.HasCore`: a submodule contained in the domain is a core if restricting to the core
  does not lose information about the unbounded operator.

## Main statements

* `LinearPMap.isClosable_iff_exists_closed_extension`: an unbounded operator is closable iff it has
  a closed extension.
* `LinearPMap.IsClosable.existsUnique`: there exists a unique closure
* `LinearPMap.closureHasCore`: the domain of `f` is a core of its closure

## References

* [J. Weidmann, *Linear Operators in Hilbert Spaces*][weidmann_linear]

## Tags

Unbounded operators, closed operators
-/

@[expose] public section


open Topology

variable {R E F : Type*}
variable [CommRing R] [AddCommGroup E] [AddCommGroup F]
variable [Module R E] [Module R F]
variable [TopologicalSpace E] [TopologicalSpace F]

namespace LinearPMap

/-! ### Closed and closable operators -/

section Basic

/-- An unbounded operator is closed iff its graph is closed. -/
/-
**LinearPMap.IsClosed** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：IsClosed (f : E ->ₗ.[R] F) : Prop
参数：f : E ->ₗ.[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unbounded operator is closed iff its graph is closed.
-/
def IsClosed (f : E →ₗ.[R] F) : Prop :=
  _root_.IsClosed (f.graph : Set (E × F))

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/-- An unbounded operator is closable iff the closure of its graph is a graph. -/
/-
**LinearPMap.IsClosable** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：IsClosable (f : E ->ₗ.[R] F) : Prop
参数：f : E ->ₗ.[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An unbounded operator is closable iff the closure of its graph is a graph.
-/
def IsClosable (f : E →ₗ.[R] F) : Prop :=
  ∃ f' : E →ₗ.[R] F, f.graph.topologicalClosure = f'.graph

/-- A closed operator is trivially closable. -/
/-
**LinearPMap.IsClosed.isClosable** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.IsClosed`
。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f : 
E →ₗ.[R] F}, f.IsClosed → f.IsClosable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.submodule_topologicalClosure_eq`：IsClosed.submodule_topological
Closure_eq {s : Submodule R M} (hs : IsClosed (s : Set M)) : s.topologicalClosur
e = s
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…

--- 原说明 ---
A closed operator is trivially closable.
-/
theorem IsClosed.isClosable {f : E →ₗ.[R] F} (hf : f.IsClosed) : f.IsClosable :=
  ⟨f, hf.submodule_topologicalClosure_eq⟩

/-- If `g` has a closable extension `f`, then `g` itself is closable. -/
/-
**LinearPMap.IsClosable.leIsClosable** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.IsClo
sable`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f g 
: E →ₗ.[R] F}, f.IsClosable → g ≤ f → g.IsClosable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.topologicalClosure_mono`：Submodule.topologicalClosure_mono {s 
: Submodule R M} {t : Submodule R M} (h : s <= t) : s.topologicalClosure <= t.to
pologicalClosure
· 使用定理 `LinearPMap.le_graph_of_le`：le_graph_of_le {f g : E ->ₗ.[R] F} (h : f <= 
g) : f.graph <= g.graph
· 使用定理 `Submodule.toLinearPMap_graph_eq`：toLinearPMap_graph_eq (g : Submodule R 
(E × F)) (hg : forall (x : E × F) (_hx : x in g) (_hx' : x.fst = 0), x.snd = 0) 
: g.toLinearPMap.grap…
· 使用定理 `LinearPMap.graph_fst_eq_zero_snd`：graph_fst_eq_zero_snd (f : E ->ₗ.[R] F
) {x : E} {x' : F} (h : (x, x') in f.graph) (hx : x = 0) : x' = 0

--- 原说明 ---
If `g` has a closable extension `f`, then `g` itself is closable.
-/
theorem IsClosable.leIsClosable {f g : E →ₗ.[R] F} (hf : f.IsClosable) (hfg : g ≤ f) :
    g.IsClosable := by
  obtain ⟨f', hf⟩ := hf
  have : g.graph.topologicalClosure ≤ f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this hx) hx'

/-- The closure is unique. -/
/-
**LinearPMap.IsClosable.existsUnique** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.IsClo
sable`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f : 
E →ₗ.[R] F}, f.IsClosable → ∃! f', f.graph.topologicalClosure = f'.graph
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `LinearPMap.eq_of_eq_graph`：eq_of_eq_graph {f g : E ->ₗ.[R] F} (h : f.gra
ph = g.graph) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The closure is unique.
-/
theorem IsClosable.existsUnique {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    ∃! f' : E →ₗ.[R] F, f.graph.topologicalClosure = f'.graph := by
  refine existsUnique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph ?_
  rw [← hy₁, ← hy₂]

open scoped Classical in
/-- If `f` is closable, then `f.closure` is the closure. Otherwise it is defined
as `f.closure = f`. -/
/-
**LinearPMap.closure** 是 Mathlib 中的一个定义，位于命名空间 `LinearPMap`。
形式化陈述：closure (f : E ->ₗ.[R] F) : E ->ₗ.[R] F
参数：f : E ->ₗ.[R] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is closable, then `f.closure` is the closure. Otherwise it is defined
as `f.closure = f`.
-/
noncomputable def closure (f : E →ₗ.[R] F) : E →ₗ.[R] F :=
  if hf : f.IsClosable then hf.choose else f
/-
**LinearPMap.closure_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：closure_def {f : E ->ₗ.[R] F} (hf : f.IsClosable) : f.closure = hf.choose
参数：hf : f.IsClosable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_def {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure = hf.choose := by
  simp [closure, hf]
/-
**LinearPMap.closure_def'** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：closure_def' {f : E ->ₗ.[R] F} (hf : ¬f.IsClosable) : f.closure = f
参数：hf : ¬f.IsClosable。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem closure_def' {f : E →ₗ.[R] F} (hf : ¬f.IsClosable) : f.closure = f := by simp [closure, hf]

/-- The closure (as a submodule) of the graph is equal to the graph of the closure
  (as a `LinearPMap`). -/
/-
**LinearPMap.IsClosable.graph_closure_eq_closure_graph** 是 Mathlib 中的一个定理，位于命名空间
 `LinearPMap.IsClosable`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f : 
E →ₗ.[R] F}, f.IsClosable → f.graph.topologicalClosure = f.closure.graph
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.closure_def`：closure_def {f : E ->ₗ.[R] F} (hf : f.IsClosable
) : f.closure = hf.choose
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
The closure (as a submodule) of the graph is equal to the graph of the closure
  (as a `LinearPMap`).
-/
theorem IsClosable.graph_closure_eq_closure_graph {f : E →ₗ.[R] F} (hf : f.IsClosable) :
    f.graph.topologicalClosure = f.closure.graph := by
  rw [closure_def hf]
  exact hf.choose_spec

/-- A `LinearPMap` is contained in its closure. -/
/-
**LinearPMap.le_closure** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：le_closure (f : E ->ₗ.[R] F) : f <= f.closure
参数：f : E ->ₗ.[R] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.le_of_le_graph`：le_of_le_graph {f g : E ->ₗ.[R] F} (h : f.gra
ph <= g.graph) : f <= g
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.IsClosable.graph_closure_eq_closure_graph`：∀ {R : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst
_2 : AddCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `Submodule.le_topologicalClosure`：Submodule.le_topologicalClosure (s : Su
bmodule R M) : s <= s.topologicalClosure
· 使用定理 `LinearPMap.closure_def'`：closure_def' {f : E ->ₗ.[R] F} (hf : ¬f.IsClosa
ble) : f.closure = f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
A `LinearPMap` is contained in its closure.
-/
theorem le_closure (f : E →ₗ.[R] F) : f ≤ f.closure := by
  by_cases hf : f.IsClosable
  · refine le_of_le_graph ?_
    rw [← hf.graph_closure_eq_closure_graph]
    exact (graph f).le_topologicalClosure
  rw [closure_def' hf]
/-
**LinearPMap.IsClosable.closure_mono** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.IsClo
sable`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f g 
: E →ₗ.[R] F}, g.IsClosable → f ≤ g → f.closure ≤ g.closure
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.le_of_le_graph`：le_of_le_graph {f g : E ->ₗ.[R] F} (h : f.gra
ph <= g.graph) : f <= g
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.IsClosable.graph_closure_eq_closure_graph`：∀ {R : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst
_2 : AddCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `LinearPMap.IsClosable.leIsClosable`：∀ {R : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup 
F]   [inst_3 : _root_.Mo…
· 使用定理 `Submodule.topologicalClosure_mono`：Submodule.topologicalClosure_mono {s 
: Submodule R M} {t : Submodule R M} (h : s <= t) : s.topologicalClosure <= t.to
pologicalClosure
· 使用定理 `LinearPMap.le_graph_of_le`：le_graph_of_le {f g : E ->ₗ.[R] F} (h : f <= 
g) : f.graph <= g.graph
-/
theorem IsClosable.closure_mono {f g : E →ₗ.[R] F} (hg : g.IsClosable) (h : f ≤ g) :
    f.closure ≤ g.closure := by
  refine le_of_le_graph ?_
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  rw [← hg.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)

/-- If `f` is closable, then the closure is closed. -/
/-
**LinearPMap.IsClosable.closure_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.I
sClosable`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f : 
E →ₗ.[R] F}, f.IsClosable → f.closure.IsClosed
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.IsClosed.eq_1`：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst
_3 : _root_.Mo…
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.IsClosable.graph_closure_eq_closure_graph`：∀ {R : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst
_2 : AddCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `Submodule.isClosed_topologicalClosure`：Submodule.isClosed_topologicalClo
sure (s : Submodule R M) : IsClosed (s.topologicalClosure : Set M)

--- 原说明 ---
If `f` is closable, then the closure is closed.
-/
theorem IsClosable.closure_isClosed {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosed := by
  rw [IsClosed, ← hf.graph_closure_eq_closure_graph]
  exact f.graph.isClosed_topologicalClosure

/-- If `f` is closable, then the closure is closable. -/
/-
**LinearPMap.IsClosable.closureIsClosable** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap.
IsClosable`。
形式化陈述：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst_3 : _root_.Module R E] [ins
t_4 : _root_.Module R F] [inst_5 : TopologicalSpace E] [inst_6 : TopologicalSpac
e F]   [inst_7 : ContinuousAdd E] [inst_8 : ContinuousAdd F] [inst_9 : Topologic
alSpace R] [inst_10 : ContinuousSMul R E]   [inst_11 : ContinuousSMul R F] {f : 
E →ₗ.[R] F}, f.IsClosable → f.closure.IsClosable
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.IsClosed.isClosable`：∀ {R : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup F]  
 [inst_3 : _root_.Mo…
· 使用定理 `LinearPMap.IsClosable.closure_isClosed`：∀ {R : Type u_1} {E : Type u_2} 
{F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGr
oup F]   [inst_3 : _root_.Mo…

--- 原说明 ---
If `f` is closable, then the closure is closable.
-/
theorem IsClosable.closureIsClosable {f : E →ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosable :=
  hf.closure_isClosed.isClosable
/-
**LinearPMap.isClosable_iff_exists_closed_extension** 是 Mathlib 中的一个定理，位于命名空间 `L
inearPMap`。
形式化陈述：isClosable_iff_exists_closed_extension {f : E ->ₗ.[R] F} : f.IsClosable ↔ 
exists g : E ->ₗ.[R] F, g.IsClosed ∧ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.IsClosable.closure_isClosed`：∀ {R : Type u_1} {E : Type u_2} 
{F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGr
oup F]   [inst_3 : _root_.Mo…
· 使用定理 `LinearPMap.le_closure`：le_closure (f : E ->ₗ.[R] F) : f <= f.closure
· 使用定理 `LinearPMap.IsClosable.leIsClosable`：∀ {R : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup 
F]   [inst_3 : _root_.Mo…
· 使用定理 `LinearPMap.IsClosed.isClosable`：∀ {R : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup F]  
 [inst_3 : _root_.Mo…
-/
theorem isClosable_iff_exists_closed_extension {f : E →ₗ.[R] F} :
    f.IsClosable ↔ ∃ g : E →ₗ.[R] F, g.IsClosed ∧ f ≤ g :=
  ⟨fun h => ⟨f.closure, h.closure_isClosed, f.le_closure⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩

/-! ### The core of a linear operator -/


/-- A submodule `S` is a core of `f` if the closure of the restriction of `f` to `S` is `f`. -/
/-
**LinearPMap.HasCore** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearPMap`。
形式化陈述：{R : Type u_1} →   {E : Type u_2} →     {F : Type u_3} →       [inst : Com
mRing R] →         [inst_1 : AddCommGroup E] →           [inst_2 : AddCommGroup 
F] →             [inst_3 : _root_.Module R E] →               [inst_4 : _root_.M
odule R F] →                 [inst_5 : TopologicalSpace E] →                   [
inst_6 : TopologicalSpace F] →                     [ContinuousAdd E] →          
             [ContinuousAdd F] →                         [inst_9 : TopologicalSp
ace R] →                           [ContinuousSMul R E] → [ContinuousSMul R F] →
 (E →ₗ.[R] F) → Submodule R E → Prop
参数：E →ₗ.[R] F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule `S` is a core of `f` if the closure of the restriction of `f` to `S`
 is `f`.
-/
structure HasCore (f : E →ₗ.[R] F) (S : Submodule R E) : Prop where
  le_domain : S ≤ f.domain
  closure_eq : (f.domRestrict S).closure = f
/-
**LinearPMap.hasCore_def** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：hasCore_def {f : E ->ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S) : (f.d
omRestrict S).closure = f
参数：h : f.HasCore S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.HasCore.closure_eq`：∀ {R : Type u_1} {E : Type u_2} {F : Type
 u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup F]   
[inst_3 : _root_.Mo…
-/
theorem hasCore_def {f : E →ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S) :
    (f.domRestrict S).closure = f :=
  h.2

/-- For every unbounded operator `f` the submodule `f.domain` is a core of its closure.

Note that we don't require that `f` is closable, due to the definition of the closure. -/
/-
**LinearPMap.closureHasCore** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：closureHasCore (f : E ->ₗ.[R] F) : f.closure.HasCore f.domain
参数：f : E ->ₗ.[R] F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LinearPMap.le_closure`：le_closure (f : E ->ₗ.[R] F) : f <= f.closure
· 使用定理 `LinearPMap.ext`：ext {f g : E ->ₛₗ.[σ] F} (h : f.domain = g.domain) (h' :
 forall ⦃x : E⦄ ⦃hf : x in f.domain⦄ ⦃hg : x in g.domain⦄, f ⟨x, hf⟩ = g ⟨x, hg⟩
) : …
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearPMap.domRestrict_apply`：domRestrict_apply {f : E ->ₛₗ.[σ] F} {S : 
Submodule R E} ⦃x : ↥(S ⊓ f.domain)⦄ ⦃y : f.domain⦄ (h : (x : E) = y) : f.domRes
trict S x = f y

--- 原说明 ---
For every unbounded operator `f` the submodule `f.domain` is a core of its closu
re.

Note that we don't require that `f` is closable, due to the definition of the cl
osure.
-/
theorem closureHasCore (f : E →ₗ.[R] F) : f.closure.HasCore f.domain := by
  refine ⟨f.le_closure.1, ?_⟩
  congr
  ext x h1 h2
  · simp only [domRestrict_domain, Submodule.mem_inf, and_iff_left_iff_imp]
    intro hx
    exact f.le_closure.1 hx
  let z : f.closure.domain := ⟨x, f.le_closure.1 h2⟩
  have hyz : x = z := rfl
  rw [f.le_closure.2 hyz]
  exact domRestrict_apply hyz

end Basic

/-! ### Topological properties of the inverse -/

section Inverse

variable {f : E →ₗ.[R] F}

/-- The inverse of `f : LinearPMap` is closed if and only if `f` is closed. -/
/-
**LinearPMap.inverse_closed_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_closed_iff (hf : LinearMap.ker f.toFun = ⊥) : f.inverse.IsClosed ↔
 f.IsClosed
参数：hf : LinearMap.ker f.toFun = ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.IsClosed.eq_1`：∀ {R : Type u_1} {E : Type u_2} {F : Type u_3}
 [inst : CommRing R] [inst_1 : AddCommGroup E] [inst_2 : AddCommGroup F]   [inst
_3 : _root_.Mo…
· 使用定理 `LinearPMap.inverse_graph`：inverse_graph : (inverse f).graph = f.graph.ma
p (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))
· 使用定理 `ContinuousLinearEquiv.isClosed_image`：isClosed_image (e : M₁ ≃SL[σ₁₂] M₂
) {s : Set M₁} : IsClosed (e '' s) ↔ IsClosed s

--- 原说明 ---
The inverse of `f : LinearPMap` is closed if and only if `f` is closed.
-/
theorem inverse_closed_iff (hf : LinearMap.ker f.toFun = ⊥) : f.inverse.IsClosed ↔ f.IsClosed := by
  rw [IsClosed, inverse_graph hf]
  exact (ContinuousLinearEquiv.prodComm R E F).isClosed_image

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

set_option backward.isDefEq.respectTransparency false in
/-- If `f` is invertible and closable as well as its closure being invertible, then
the graph of the inverse of the closure is given by the closure of the graph of the inverse. -/
/-
**LinearPMap.closure_inverse_graph** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：closure_inverse_graph (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable
) (hcf : LinearMap.ker f.closure.toFun = ⊥) : f.closure.inverse.graph = f.invers
e.graph.topologicalClosure
参数：hf : LinearMap.ker f.toFun = ⊥；hf' : f.IsClosable；hcf : LinearMap.ker f.closu
re.toFun = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.inverse_graph`：inverse_graph : (inverse f).graph = f.graph.ma
p (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.IsClosable.graph_closure_eq_closure_graph`：∀ {R : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst
_2 : AddCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `LinearEquiv.prodComm_apply`：∀ (R : Type u_3) (M : Type u_4) (N : Type u_
5) [inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : AddCommMonoid N]   [
inst_3 : _root_.…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `Equiv.image_eq_preimage_symm`：image_eq_preimage_symm (e : α ≃ β) (s : Se
t α) : e '' s = e.symm ⁻¹' s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Continuous.closure_preimage_subset`：Continuous.closure_preimage_subset (
hf : Continuous f) (t : Set Y) : closure (f ⁻¹' t) subseteq f ⁻¹' closure t

--- 原说明 ---
If `f` is invertible and closable as well as its closure being invertible, then
the graph of the inverse of the closure is given by the closure of the graph of 
the inverse.
-/
theorem closure_inverse_graph (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.closure.inverse.graph = f.inverse.graph.topologicalClosure := by
  rw [inverse_graph hf, inverse_graph hcf, ← hf'.graph_closure_eq_closure_graph]
  apply SetLike.ext'
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.coe_coe,
    LinearEquiv.prodComm_apply]
  apply (image_closure_subset_closure_image continuous_swap).antisymm
  have h1 := (LinearEquiv.prodComm R E F).toEquiv.image_eq_preimage_symm f.graph
  have h2 := (LinearEquiv.prodComm R E F).toEquiv.image_eq_preimage_symm (_root_.closure f.graph)
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.prodComm_apply] at h1 h2
  rw [h1, h2]
  apply continuous_swap.closure_preimage_subset

/-- Assuming that `f` is invertible and closable, then the closure is invertible if and only
if the inverse of `f` is closable. -/
/-
**LinearPMap.inverse_isClosable_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_isClosable_iff (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosabl
e) : f.inverse.IsClosable ↔ LinearMap.ker f.closure.toFun = ⊥
参数：hf : LinearMap.ker f.toFun = ⊥；hf' : f.IsClosable。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearPMap.inverse_graph`：inverse_graph : (inverse f).graph = f.graph.ma
p (LinearEquiv.prodComm R E F : (E × F) ->ₗ[R] (F × E))
· 使用定理 `image_closure_subset_closure_image`：image_closure_subset_closure_image (
h : Continuous f) : f '' closure s subseteq closure (f '' s)
· 使用定理 `continuous_swap`：continuous_swap : Continuous (Prod.swap : X × Y -> Y × 
X)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `Submodule.topologicalClosure_coe`：Submodule.topologicalClosure_coe (s : 
Submodule R M) : (s.topologicalClosure : Set M) = closure (s : Set M)
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LinearPMap.IsClosable.graph_closure_eq_closure_graph`：∀ {R : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst
_2 : AddCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `LinearPMap.image_iff`：image_iff {f : E ->ₗ.[R] F} {x : E} {y : F} (hx : 
x in f.domain) : y = f ⟨x, hx⟩ ↔ (x, y) in f.graph
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `LinearPMap.toFun_eq_coe`：toFun_eq_coe (f : E ->ₛₗ.[σ] F) (x : f.domain) 
: f.toFun x = f x
· 使用定理 `LinearPMap.graph_fst_eq_zero_snd`：graph_fst_eq_zero_snd (f : E ->ₗ.[R] F
) {x : E} {x' : F} (h : (x, x') in f.graph) (hx : x = 0) : x' = 0
· 使用定理 `LinearPMap.closure_inverse_graph`：closure_inverse_graph (hf : LinearMap.
ker f.toFun = ⊥) (hf' : f.IsClosable) (hcf : LinearMap.ker f.closure.toFun = ⊥) 
: f.closure.inverse.gr…

--- 原说明 ---
Assuming that `f` is invertible and closable, then the closure is invertible if 
and only
if the inverse of `f` is closable.
-/
theorem inverse_isClosable_iff (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable) :
    f.inverse.IsClosable ↔ LinearMap.ker f.closure.toFun = ⊥ := by
  constructor
  · intro ⟨f', h⟩
    rw [LinearMap.ker_eq_bot']
    intro ⟨x, hx⟩ hx'
    simp only [Submodule.mk_eq_zero]
    rw [toFun_eq_coe, eq_comm, image_iff] at hx'
    have : (0, x) ∈ graph f' := by
      rw [← h, inverse_graph hf]
      rw [← hf'.graph_closure_eq_closure_graph, ← SetLike.mem_coe,
        Submodule.topologicalClosure_coe] at hx'
      apply image_closure_subset_closure_image continuous_swap
      simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      exact ⟨x, 0, hx', rfl, rfl⟩
    exact graph_fst_eq_zero_snd f' this rfl
  · intro h
    use f.closure.inverse
    exact (closure_inverse_graph hf hf' h).symm

/-- If `f` is invertible and closable, then taking the closure and the inverse commute. -/
/-
**LinearPMap.inverse_closure** 是 Mathlib 中的一个定理，位于命名空间 `LinearPMap`。
形式化陈述：inverse_closure (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable) (hcf
 : LinearMap.ker f.closure.toFun = ⊥) : f.inverse.closure = f.closure.inverse
参数：hf : LinearMap.ker f.toFun = ⊥；hf' : f.IsClosable；hcf : LinearMap.ker f.closu
re.toFun = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearPMap.eq_of_eq_graph`：eq_of_eq_graph {f g : E ->ₗ.[R] F} (h : f.gra
ph = g.graph) : f = g
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `Prod.continuousAdd`：∀ {M : Type u_3} {N : Type u_4} [inst : TopologicalS
pace M] [inst_1 : Add M] [ContinuousAdd M]   [inst_3 : TopologicalSpace N] [inst
_4 : Add…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearPMap.closure_inverse_graph`：closure_inverse_graph (hf : LinearMap.
ker f.toFun = ⊥) (hf' : f.IsClosable) (hcf : LinearMap.ker f.closure.toFun = ⊥) 
: f.closure.inverse.gr…
· 使用定理 `LinearPMap.IsClosable.graph_closure_eq_closure_graph`：∀ {R : Type u_1} {
E : Type u_2} {F : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup E] [inst
_2 : AddCommGroup F]   [inst_3 : _root_.Mo…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearPMap.inverse_isClosable_iff`：inverse_isClosable_iff (hf : LinearMa
p.ker f.toFun = ⊥) (hf' : f.IsClosable) : f.inverse.IsClosable ↔ LinearMap.ker f
.closure.toFun = ⊥

--- 原说明 ---
If `f` is invertible and closable, then taking the closure and the inverse commu
te.
-/
theorem inverse_closure (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.inverse.closure = f.closure.inverse := by
  apply eq_of_eq_graph
  rw [closure_inverse_graph hf hf' hcf,
    ((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]

end Inverse

end LinearPMap

