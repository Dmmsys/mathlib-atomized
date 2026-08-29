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

/--
Definition of `IsClosed` / `IsClosed` 的定义

English:
definition IsClosed
  signature: (f : E ->ₗ.[R] F)
  body: _root_.IsClosed (f.graph : Set (E × F))

中文:
定义 是闭集
  签名: (f : E ->ₗ.[R] F)
  定义体: _root_.IsClosed (f.graph : Set (E × F))

Depends on / 依赖: IsClosed, _root_, _root_.IsClosed, f.graph
-/
def IsClosed (f : E ->ₗ.[R] F) : Prop :=
  _root_.IsClosed (f.graph : Set (E × F))

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

/--
Definition of `IsClosable` / `IsClosable` 的定义

English:
definition IsClosable
  signature: (f : E ->ₗ.[R] F)
  body: exists f' : E ->ₗ.[R] F, f.graph.topologicalClosure = f'.graph

中文:
定义 IsClosable
  签名: (f : E ->ₗ.[R] F)
  定义体: exists f' : E ->ₗ.[R] F, f.graph.topologicalClosure = f'.graph

Depends on / 依赖: f.graph.topologicalClosure, topologicalClosure
-/
def IsClosable (f : E ->ₗ.[R] F) : Prop :=
  exists f' : E ->ₗ.[R] F, f.graph.topologicalClosure = f'.graph

/--
theorem `IsClosed.isClosable` / 定理 `IsClosed.isClosable`

English:
theorem IsClosed.isClosable
  given: {f : E ->ₗ.[R] F} (hf : f.IsClosed)
  statement: f.IsClosable
  proof: ⟨f, hf.submodule_topologicalClosure_eq⟩

中文:
定理 是闭集.isClosable
  条件: {f : E ->ₗ.[R] F} (hf : f.是闭集)
  结论: f.IsClosable
  证明: ⟨f, hf.submodule_topologicalClosure_eq⟩

Depends on / 依赖: hf.submodule_topologicalClosure_eq, submodule_topologicalClosure_eq
-/
theorem IsClosed.isClosable {f : E ->ₗ.[R] F} (hf : f.IsClosed) : f.IsClosable :=
  ⟨f, hf.submodule_topologicalClosure_eq⟩

/--
theorem `IsClosable.leIsClosable` / 定理 `IsClosable.leIsClosable`

English:
theorem IsClosable.leIsClosable
  given: {f g : E ->ₗ.[R] F} (hf : f.IsClosable) (hfg : g <= f)
  proof: by
  obtain ⟨f', hf⟩ := hf
  have : g.graph.topologicalClosure <= f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this 

中文:
定理 IsClosable.leIsClosable
  条件: {f g : E ->ₗ.[R] F} (hf : f.IsClosable) (hfg : g <= f)
  证明: by
  obtain ⟨f', hf⟩ := hf
  have : g.graph.topologicalClosure <= f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this 

Depends on / 依赖: Submodule, Submodule.toLinearPMap_graph_eq, Submodule.topologicalClosure_mono, g.graph.topologicalClosure, g.graph.topologicalClosure.toLinearPMap, graph_fst_eq_zero_snd, le_graph_of_le, toLinearPMap, toLinearPMap_graph_eq, topologicalClosure, topologicalClosure_mono
-/
theorem IsClosable.leIsClosable {f g : E ->ₗ.[R] F} (hf : f.IsClosable) (hfg : g <= f) :
    g.IsClosable := by
  obtain ⟨f', hf⟩ := hf
  have : g.graph.topologicalClosure <= f'.graph := by
    rw [← hf]
    exact Submodule.topologicalClosure_mono (le_graph_of_le hfg)
  use g.graph.topologicalClosure.toLinearPMap
  rw [Submodule.toLinearPMap_graph_eq]
  exact fun _ hx hx' => f'.graph_fst_eq_zero_snd (this hx) hx'

/--
theorem `IsClosable.existsUnique` / 定理 `IsClosable.existsUnique`

English:
theorem IsClosable.existsUnique
  given: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  proof: by
  refine existsUnique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph ?_
  rw [← hy₁]; rw [← hy₂]

中文:
定理 IsClosable.存在Unique
  条件: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  证明: by
  refine existsUnique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph ?_
  rw [← hy₁]; rw [← hy₂]

Depends on / 依赖: eq_of_eq_graph, existsUnique_of_exists_of_unique
-/
theorem IsClosable.existsUnique {f : E ->ₗ.[R] F} (hf : f.IsClosable) :
    exists! f' : E ->ₗ.[R] F, f.graph.topologicalClosure = f'.graph := by
  refine existsUnique_of_exists_of_unique hf fun _ _ hy₁ hy₂ => eq_of_eq_graph ?_
  rw [← hy₁]; rw [← hy₂]

open scoped Classical in
/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (f : E ->ₗ.[R] F)
  body: if hf : f.IsClosable then hf.choose else f

中文:
定义 closure
  签名: (f : E ->ₗ.[R] F)
  定义体: if hf : f.IsClosable then hf.choose else f

Depends on / 依赖: IsClosable, f.IsClosable, hf.choose
-/
noncomputable def closure (f : E ->ₗ.[R] F) : E ->ₗ.[R] F :=
  if hf : f.IsClosable then hf.choose else f

/--
theorem `closure_def` / 定理 `closure_def`

English:
theorem closure_def
  given: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  statement: f.closure = hf.choose
  proof: by
  simp [closure, hf]

中文:
定理 closure_def
  条件: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  结论: f.closure = hf.choose
  证明: by
  simp [closure, hf]

Depends on / 依赖: closure
-/
theorem closure_def {f : E ->ₗ.[R] F} (hf : f.IsClosable) : f.closure = hf.choose := by
  simp [closure, hf]

/--
theorem `closure_def'` / 定理 `closure_def'`

English:
theorem closure_def'
  given: {f : E ->ₗ.[R] F} (hf : ¬f.IsClosable)
  statement: f.closure = f
  proof: by simp [closure, hf]

中文:
定理 closure_def'
  条件: {f : E ->ₗ.[R] F} (hf : ¬f.IsClosable)
  结论: f.closure = f
  证明: by simp [closure, hf]

Depends on / 依赖: closure
-/
theorem closure_def' {f : E ->ₗ.[R] F} (hf : ¬f.IsClosable) : f.closure = f := by simp [closure, hf]

/--
theorem `IsClosable.graph_closure_eq_closure_graph` / 定理 `IsClosable.graph_closure_eq_closure_graph`

English:
theorem IsClosable.graph_closure_eq_closure_graph
  given: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  proof: by
  rw [closure_def hf]
  exact hf.choose_spec

中文:
定理 IsClosable.graph_closure_eq_closure_graph
  条件: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  证明: by
  rw [closure_def hf]
  exact hf.choose_spec

Depends on / 依赖: choose_spec, closure_def, hf.choose_spec
-/
theorem IsClosable.graph_closure_eq_closure_graph {f : E ->ₗ.[R] F} (hf : f.IsClosable) :
    f.graph.topologicalClosure = f.closure.graph := by
  rw [closure_def hf]
  exact hf.choose_spec

/--
theorem `le_closure` / 定理 `le_closure`

English:
theorem le_closure
  given: (f : E ->ₗ.[R] F)
  statement: f <= f.closure
  proof: by
  by_cases hf : f.IsClosable
  · refine le_of_le_graph ?_
    rw [← hf.graph_closure_eq_closure_graph]
    exact (graph f).le_topologicalClosure
  rw [closure_def' hf]

中文:
定理 le_closure
  条件: (f : E ->ₗ.[R] F)
  结论: f <= f.closure
  证明: by
  by_cases hf : f.IsClosable
  · refine le_of_le_graph ?_
    rw [← hf.graph_closure_eq_closure_graph]
    exact (graph f).le_topologicalClosure
  rw [closure_def' hf]

Depends on / 依赖: IsClosable, closure_def, f.IsClosable, graph_closure_eq_closure_graph, hf.graph_closure_eq_closure_graph, le_of_le_graph, le_topologicalClosure
-/
theorem le_closure (f : E ->ₗ.[R] F) : f <= f.closure := by
  by_cases hf : f.IsClosable
  · refine le_of_le_graph ?_
    rw [← hf.graph_closure_eq_closure_graph]
    exact (graph f).le_topologicalClosure
  rw [closure_def' hf]

/--
theorem `IsClosable.closure_mono` / 定理 `IsClosable.closure_mono`

English:
theorem IsClosable.closure_mono
  given: {f g : E ->ₗ.[R] F} (hg : g.IsClosable) (h : f <= g)
  proof: by
  refine le_of_le_graph ?_
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  rw [← hg.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)

中文:
定理 IsClosable.closure_mono
  条件: {f g : E ->ₗ.[R] F} (hg : g.IsClosable) (h : f <= g)
  证明: by
  refine le_of_le_graph ?_
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  rw [← hg.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)

Depends on / 依赖: Submodule, Submodule.topologicalClosure_mono, graph_closure_eq_closure_graph, hg.graph_closure_eq_closure_graph, hg.leIsClosable, leIsClosable, le_graph_of_le, le_of_le_graph, topologicalClosure_mono
-/
theorem IsClosable.closure_mono {f g : E ->ₗ.[R] F} (hg : g.IsClosable) (h : f <= g) :
    f.closure <= g.closure := by
  refine le_of_le_graph ?_
  rw [← (hg.leIsClosable h).graph_closure_eq_closure_graph]
  rw [← hg.graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_mono (le_graph_of_le h)

/--
theorem `IsClosable.closure_isClosed` / 定理 `IsClosable.closure_isClosed`

English:
theorem IsClosable.closure_isClosed
  given: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  statement: f.closure.IsClosed
  proof: by
  rw [IsClosed]; rw [← hf.graph_closure_eq_closure_graph]
  exact f.graph.isClosed_topologicalClosure

中文:
定理 IsClosable.closure_isClosed
  条件: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  结论: f.closure.是闭集
  证明: by
  rw [IsClosed]; rw [← hf.graph_closure_eq_closure_graph]
  exact f.graph.isClosed_topologicalClosure

Depends on / 依赖: IsClosed, f.graph.isClosed_topologicalClosure, graph_closure_eq_closure_graph, hf.graph_closure_eq_closure_graph, isClosed_topologicalClosure
-/
theorem IsClosable.closure_isClosed {f : E ->ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosed := by
  rw [IsClosed]; rw [← hf.graph_closure_eq_closure_graph]
  exact f.graph.isClosed_topologicalClosure

/--
theorem `IsClosable.closureIsClosable` / 定理 `IsClosable.closureIsClosable`

English:
theorem IsClosable.closureIsClosable
  given: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  statement: f.closure.IsClosable
  proof: hf.closure_isClosed.isClosable

中文:
定理 IsClosable.closureIsClosable
  条件: {f : E ->ₗ.[R] F} (hf : f.IsClosable)
  结论: f.closure.IsClosable
  证明: hf.closure_isClosed.isClosable

Depends on / 依赖: closure_isClosed, hf.closure_isClosed.isClosable, isClosable
-/
theorem IsClosable.closureIsClosable {f : E ->ₗ.[R] F} (hf : f.IsClosable) : f.closure.IsClosable :=
  hf.closure_isClosed.isClosable

/--
theorem `isClosable_iff_exists_closed_extension` / 定理 `isClosable_iff_exists_closed_extension`

English:
theorem isClosable_iff_exists_closed_extension
  given: {f : E ->ₗ.[R] F}
  proof: ⟨fun h => ⟨f.closure, h.closure_isClosed, f.le_closure⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩

中文:
定理 isClosable_iff_存在_closed_extension
  条件: {f : E ->ₗ.[R] F}
  证明: ⟨fun h => ⟨f.closure, h.closure_isClosed, f.le_closure⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩

Depends on / 依赖: closure, closure_isClosed, f.closure, f.le_closure, h.closure_isClosed, hg.isClosable.leIsClosable, isClosable, leIsClosable, le_closure
-/
theorem isClosable_iff_exists_closed_extension {f : E ->ₗ.[R] F} :
    f.IsClosable ↔ exists g : E ->ₗ.[R] F, g.IsClosed ∧ f <= g :=
  ⟨fun h => ⟨f.closure, h.closure_isClosed, f.le_closure⟩, fun ⟨_, hg, h⟩ =>
    hg.isClosable.leIsClosable h⟩

/-! ### The core of a linear operator -/


/--
Definition of `HasCore` / `HasCore` 的定义

English:
structure HasCore
  parameters: (f : E ->ₗ.[R] F) (S : Submodule R E)
  axioms and operations (2):
    - le_domain : S <= f.domain
    - closure_eq : (f.domRestrict S).closure = f

中文:
结构 有核
  参数: (f : E ->ₗ.[R] F) (S : 子模 R E)
  公理与运算 (2 个):
    - le_domain : S <= f.domain
    - closure_eq : (f.domRestrict S).closure = f
-/
structure HasCore (f : E ->ₗ.[R] F) (S : Submodule R E) : Prop where
  le_domain : S <= f.domain
  closure_eq : (f.domRestrict S).closure = f

/--
theorem `hasCore_def` / 定理 `hasCore_def`

English:
theorem hasCore_def
  given: {f : E ->ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S)
  proof: h.2

中文:
定理 hasCore_def
  条件: {f : E ->ₗ.[R] F} {S : 子模 R E} (h : f.有核 S)
  证明: h.2
-/
theorem hasCore_def {f : E ->ₗ.[R] F} {S : Submodule R E} (h : f.HasCore S) :
    (f.domRestrict S).closure = f :=
  h.2

/--
theorem `closureHasCore` / 定理 `closureHasCore`

English:
theorem closureHasCore
  given: (f : E ->ₗ.[R] F)
  statement: f.closure.HasCore f.domain
  proof: by
  refine ⟨f.le_closure.1, ?_⟩
  congr
  ext x h1 h2
  · simp only [domRestrict_domain, Submodule.mem_inf, and_iff_left_iff_imp]
    intro hx
    exact f.le_closure.1 hx
  let z : f.closure.domain := ⟨x, f.le_closure.1 h2⟩
  have hyz : x = z := rfl
  rw [f.le_closure.2 hyz]
  exact domRestrict_app

中文:
定理 closureHasCore
  条件: (f : E ->ₗ.[R] F)
  结论: f.closure.有核 f.domain
  证明: by
  refine ⟨f.le_closure.1, ?_⟩
  congr
  ext x h1 h2
  · simp only [domRestrict_domain, Submodule.mem_inf, and_iff_left_iff_imp]
    intro hx
    exact f.le_closure.1 hx
  let z : f.closure.domain := ⟨x, f.le_closure.1 h2⟩
  have hyz : x = z := rfl
  rw [f.le_closure.2 hyz]
  exact domRestrict_app

Depends on / 依赖: Submodule, Submodule.mem_inf, and_iff_left_iff_imp, closure, domRestrict_apply, domRestrict_domain, domain, f.closure.domain, f.le_closure, le_closure, mem_inf
-/
theorem closureHasCore (f : E ->ₗ.[R] F) : f.closure.HasCore f.domain := by
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

variable {f : E ->ₗ.[R] F}

/--
theorem `inverse_closed_iff` / 定理 `inverse_closed_iff`

English:
theorem inverse_closed_iff
  given: (hf : LinearMap.ker f.toFun = ⊥)
  statement: f.inverse.IsClosed ↔ f.IsClosed
  proof: by
  rw [IsClosed]; rw [inverse_graph hf]
  exact (ContinuousLinearEquiv.prodComm R E F).isClosed_image

中文:
定理 inverse_closed_iff
  条件: (hf : 线性映射.ker f.toFun = ⊥)
  结论: f.inverse.是闭集 ↔ f.是闭集
  证明: by
  rw [IsClosed]; rw [inverse_graph hf]
  exact (ContinuousLinearEquiv.prodComm R E F).isClosed_image

Depends on / 依赖: ContinuousLinearEquiv, ContinuousLinearEquiv.prodComm, IsClosed, inverse_graph, isClosed_image, prodComm
-/
theorem inverse_closed_iff (hf : LinearMap.ker f.toFun = ⊥) : f.inverse.IsClosed ↔ f.IsClosed := by
  rw [IsClosed]; rw [inverse_graph hf]
  exact (ContinuousLinearEquiv.prodComm R E F).isClosed_image

variable [ContinuousAdd E] [ContinuousAdd F]
variable [TopologicalSpace R] [ContinuousSMul R E] [ContinuousSMul R F]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `closure_inverse_graph` / 定理 `closure_inverse_graph`

English:
theorem closure_inverse_graph
  statement: (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
  proof: by
  rw [inverse_graph hf]; rw [inverse_graph hcf]; rw [← hf'.graph_closure_eq_closure_graph]
  apply SetLike.ext'
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.coe_coe,
    LinearEquiv.prodComm_apply]
  apply (image_closure_subset_closure_image continuous_swap).antis

中文:
定理 closure_inverse_graph
  结论: (hf : 线性映射.ker f.toFun = ⊥) (hf' : f.IsClosable)
  证明: by
  rw [inverse_graph hf]; rw [inverse_graph hcf]; rw [← hf'.graph_closure_eq_closure_graph]
  apply SetLike.ext'
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.coe_coe,
    LinearEquiv.prodComm_apply]
  apply (image_closure_subset_closure_image continuous_swap).antis

Depends on / 依赖: LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.coe_toEqui, LinearEquiv.prodComm, LinearEquiv.prodComm_apply, SetLike, SetLike.ext, Submodule, Submodule.map_coe, Submodule.topologicalClosure_coe, _root_, _root_.closure, antisymm, closure, coe_coe, coe_toEqui, continuous_swap, f.graph, graph_closure_eq_closure_graph, image_closure_subset_closure_image
-/
theorem closure_inverse_graph (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.closure.inverse.graph = f.inverse.graph.topologicalClosure := by
  rw [inverse_graph hf]; rw [inverse_graph hcf]; rw [← hf'.graph_closure_eq_closure_graph]
  apply SetLike.ext'
  simp only [Submodule.topologicalClosure_coe, Submodule.map_coe, LinearEquiv.coe_coe,
    LinearEquiv.prodComm_apply]
  apply (image_closure_subset_closure_image continuous_swap).antisymm
  have h1 := (LinearEquiv.prodComm R E F).toEquiv.image_eq_preimage_symm f.graph
  have h2 := (LinearEquiv.prodComm R E F).toEquiv.image_eq_preimage_symm (_root_.closure f.graph)
  simp only [LinearEquiv.coe_toEquiv, LinearEquiv.prodComm_apply] at h1 h2
  rw [h1]; rw [h2]
  apply continuous_swap.closure_preimage_subset

/--
theorem `inverse_isClosable_iff` / 定理 `inverse_isClosable_iff`

English:
theorem inverse_isClosable_iff
  given: (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
  proof: by
  constructor
  · intro ⟨f', h⟩
    rw [LinearMap.ker_eq_bot']
    intro ⟨x, hx⟩ hx'
    simp only [Submodule.mk_eq_zero]
    rw [toFun_eq_coe]; rw [eq_comm]; rw [image_iff] at hx'
    have : (0, x) in graph f' := by
      rw [← h]; rw [inverse_graph hf]
      rw [← hf'.graph_closure_eq_closure_g

中文:
定理 inverse_isClosable_iff
  条件: (hf : 线性映射.ker f.toFun = ⊥) (hf' : f.IsClosable)
  证明: by
  constructor
  · intro ⟨f', h⟩
    rw [LinearMap.ker_eq_bot']
    intro ⟨x, hx⟩ hx'
    simp only [Submodule.mk_eq_zero]
    rw [toFun_eq_coe]; rw [eq_comm]; rw [image_iff] at hx'
    have : (0, x) in graph f' := by
      rw [← h]; rw [inverse_graph hf]
      rw [← hf'.graph_closure_eq_closure_g

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, Prod.exists, Prod.mk.injEq, Prod.swap_prod_mk, Set.mem_image, SetLike, SetLike.mem_coe, Submodule, Submodule.mk_eq_zero, Submodule.topologicalClosure_coe, continuous_swap, eq_comm, graph_closure_eq_closure_graph, image_closure_subset_closure_image, image_iff, inverse_graph, ker_eq_bot, mem_coe, mem_image
-/
theorem inverse_isClosable_iff (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable) :
    f.inverse.IsClosable ↔ LinearMap.ker f.closure.toFun = ⊥ := by
  constructor
  · intro ⟨f', h⟩
    rw [LinearMap.ker_eq_bot']
    intro ⟨x, hx⟩ hx'
    simp only [Submodule.mk_eq_zero]
    rw [toFun_eq_coe]; rw [eq_comm]; rw [image_iff] at hx'
    have : (0, x) in graph f' := by
      rw [← h]; rw [inverse_graph hf]
      rw [← hf'.graph_closure_eq_closure_graph]; rw [← SetLike.mem_coe]; rw [Submodule.topologicalClosure_coe] at hx'
      apply image_closure_subset_closure_image continuous_swap
      simp only [Set.mem_image, Prod.exists, Prod.swap_prod_mk, Prod.mk.injEq]
      exact ⟨x, 0, hx', rfl, rfl⟩
    exact graph_fst_eq_zero_snd f' this rfl
  · intro h
    use f.closure.inverse
    exact (closure_inverse_graph hf hf' h).symm

/--
theorem `inverse_closure` / 定理 `inverse_closure`

English:
theorem inverse_closure
  statement: (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
  proof: by
  apply eq_of_eq_graph
  rw [closure_inverse_graph hf hf' hcf]; rw [((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]

中文:
定理 inverse_closure
  结论: (hf : 线性映射.ker f.toFun = ⊥) (hf' : f.IsClosable)
  证明: by
  apply eq_of_eq_graph
  rw [closure_inverse_graph hf hf' hcf]; rw [((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]

Depends on / 依赖: closure_inverse_graph, eq_of_eq_graph, graph_closure_eq_closure_graph, inverse_isClosable_iff
-/
theorem inverse_closure (hf : LinearMap.ker f.toFun = ⊥) (hf' : f.IsClosable)
    (hcf : LinearMap.ker f.closure.toFun = ⊥) :
    f.inverse.closure = f.closure.inverse := by
  apply eq_of_eq_graph
  rw [closure_inverse_graph hf hf' hcf]; rw [((inverse_isClosable_iff hf hf').mpr hcf).graph_closure_eq_closure_graph]

end Inverse

end LinearPMap
