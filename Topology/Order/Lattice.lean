/-
Copyright (c) 2021 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Topology.Constructions
public import Mathlib.Topology.Order.OrderClosed

/-!
# Topological lattices

In this file we define mixin classes `ContinuousInf` and `ContinuousSup`. We define the
class `TopologicalLattice` as a topological space and lattice `L` extending `ContinuousInf` and
`ContinuousSup`.

## References

* [Gierz et al, A Compendium of Continuous Lattices][GierzEtAl1980]

## Tags

topological, lattice
-/

public section

open Filter

open Topology

/--
Definition of `ContinuousInf` / `ContinuousInf` 的定义

English:
class ContinuousInf
  parameters: (L : Type*) [TopologicalSpace L] [Min L]
  axioms and operations (1):
    - continuous_inf : Continuous fun p : L × L => p.1 ⊓ p.2

中文:
类 余ntinuousInf
  参数: (L : 类型) [拓扑空间 L] [最小值 L]
  公理与运算 (1 个):
    - continuous_inf : 连续 fun p : L × L => p.1 ⊓ p.2
-/
class ContinuousInf (L : Type*) [TopologicalSpace L] [Min L] : Prop where
  /-- The infimum is continuous -/
  continuous_inf : Continuous fun p : L × L => p.1 ⊓ p.2

/--
Definition of `ContinuousSup` / `ContinuousSup` 的定义

English:
class ContinuousSup
  parameters: (L : Type*) [TopologicalSpace L] [Max L]
  axioms and operations (1):
    - continuous_sup : Continuous fun p : L × L => p.1 ⊔ p.2

中文:
类 余ntinuousSup
  参数: (L : 类型) [拓扑空间 L] [最大值 L]
  公理与运算 (1 个):
    - continuous_sup : 连续 fun p : L × L => p.1 ⊔ p.2
-/
class ContinuousSup (L : Type*) [TopologicalSpace L] [Max L] : Prop where
  /-- The supremum is continuous -/
  continuous_sup : Continuous fun p : L × L => p.1 ⊔ p.2

/--
Instance `OrderDual.continuousSup` / 实例 `OrderDual.continuousSup`

English:
instance OrderDual.continuousSup
  signature: (L : Type*) [TopologicalSpace L] [Min L]
  body: h.continuous_inf

中文:
实例 OrderDual.continuousSup
  签名: (L : 类型) [拓扑空间 L] [最小值 L]
  定义体: h.continuous_inf

Depends on / 依赖: continuous_inf, h.continuous_inf
-/
instance OrderDual.continuousSup (L : Type*) [TopologicalSpace L] [Min L]
    [h : ContinuousInf L] : ContinuousSup Lᵒᵈ where
  continuous_sup := h.continuous_inf

/--
Instance `OrderDual.continuousInf` / 实例 `OrderDual.continuousInf`

English:
instance OrderDual.continuousInf
  signature: (L : Type*) [TopologicalSpace L] [Max L]
  body: h.continuous_sup

中文:
实例 OrderDual.continuousInf
  签名: (L : 类型) [拓扑空间 L] [最大值 L]
  定义体: h.continuous_sup

Depends on / 依赖: continuous_sup, h.continuous_sup
-/
instance OrderDual.continuousInf (L : Type*) [TopologicalSpace L] [Max L]
    [h : ContinuousSup L] : ContinuousInf Lᵒᵈ where
  continuous_inf := h.continuous_sup

/--
Definition of `TopologicalLattice` / `TopologicalLattice` 的定义

English:
class TopologicalLattice
  parameters: (L : Type*) [TopologicalSpace L] [Lattice L]
  extends: ContinuousInf L, ContinuousSup L
  (no additional axioms)

中文:
类 拓扑格
  参数: (L : 类型) [拓扑空间 L] [格 L]
  继承: 余ntinuousInf L, 余ntinuousSup L
  (无附加公理)
-/
class TopologicalLattice (L : Type*) [TopologicalSpace L] [Lattice L] : Prop
  extends ContinuousInf L, ContinuousSup L

/--
Instance `OrderDual.topologicalLattice` / 实例 `OrderDual.topologicalLattice`

English:
instance OrderDual.topologicalLattice
  signature: (L : Type*) [TopologicalSpace L]

中文:
实例 OrderDual.topologicalLattice
  签名: (L : 类型) [拓扑空间 L]
-/
instance OrderDual.topologicalLattice (L : Type*) [TopologicalSpace L]
    [Lattice L] [TopologicalLattice L] : TopologicalLattice Lᵒᵈ where

-- see Note [lower instance priority]
instance (priority := 100) LinearOrder.topologicalLattice {L : Type*} [TopologicalSpace L]
    [LinearOrder L] [OrderClosedTopology L] : TopologicalLattice L where
  continuous_inf := continuous_min
  continuous_sup := continuous_max

variable {L X : Type*} [TopologicalSpace L] [TopologicalSpace X]

@[continuity]
/--
theorem `continuous_inf` / 定理 `continuous_inf`

English:
theorem continuous_inf
  given: [Min L] [ContinuousInf L]
  statement: Continuous fun p : L × L => p.1 ⊓ p.2
  proof: ContinuousInf.continuous_inf

@[continuity, fun_prop]

中文:
定理 continuous_inf
  条件: [最小值 L] [余ntinuousInf L]
  结论: 连续 fun p : L × L => p.1 ⊓ p.2
  证明: ContinuousInf.continuous_inf

@[continuity, fun_prop]

Depends on / 依赖: ContinuousInf, ContinuousInf.continuous_inf, continuous_inf
-/
theorem continuous_inf [Min L] [ContinuousInf L] : Continuous fun p : L × L => p.1 ⊓ p.2 :=
  ContinuousInf.continuous_inf

@[continuity, fun_prop]
/--
theorem `Continuous.inf` / 定理 `Continuous.inf`

English:
theorem Continuous.inf
  statement: [Min L] [ContinuousInf L] {f g : X -> L} (hf : Continuous f)
  proof: continuous_inf.comp (hf.prodMk hg :)

@[continuity]

中文:
定理 连续.下确界
  结论: [最小值 L] [余ntinuousInf L] {f g : X -> L} (hf : 连续 f)
  证明: continuous_inf.comp (hf.prodMk hg :)

@[continuity]

Depends on / 依赖: continuous_inf, continuous_inf.comp, hf.prodMk, prodMk
-/
theorem Continuous.inf [Min L] [ContinuousInf L] {f g : X -> L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊓ g x :=
  continuous_inf.comp (hf.prodMk hg :)

@[continuity]
/--
theorem `continuous_sup` / 定理 `continuous_sup`

English:
theorem continuous_sup
  given: [Max L] [ContinuousSup L]
  statement: Continuous fun p : L × L => p.1 ⊔ p.2
  proof: ContinuousSup.continuous_sup

@[continuity, fun_prop]

中文:
定理 continuous_sup
  条件: [最大值 L] [余ntinuousSup L]
  结论: 连续 fun p : L × L => p.1 ⊔ p.2
  证明: ContinuousSup.continuous_sup

@[continuity, fun_prop]

Depends on / 依赖: ContinuousSup, ContinuousSup.continuous_sup, continuous_sup
-/
theorem continuous_sup [Max L] [ContinuousSup L] : Continuous fun p : L × L => p.1 ⊔ p.2 :=
  ContinuousSup.continuous_sup

@[continuity, fun_prop]
/--
theorem `Continuous.sup` / 定理 `Continuous.sup`

English:
theorem Continuous.sup
  statement: [Max L] [ContinuousSup L] {f g : X -> L} (hf : Continuous f)
  proof: continuous_sup.comp (hf.prodMk hg :)

中文:
定理 连续.上确界
  结论: [最大值 L] [余ntinuousSup L] {f g : X -> L} (hf : 连续 f)
  证明: continuous_sup.comp (hf.prodMk hg :)

Depends on / 依赖: continuous_sup, continuous_sup.comp, hf.prodMk, prodMk
-/
theorem Continuous.sup [Max L] [ContinuousSup L] {f g : X -> L} (hf : Continuous f)
    (hg : Continuous g) : Continuous fun x => f x ⊔ g x :=
  continuous_sup.comp (hf.prodMk hg :)

namespace Filter.Tendsto

section SupInf

variable {α : Type*} {l : Filter α} {f g : α -> L} {x y : L}

/--
lemma `sup_nhds'` / 引理 `sup_nhds'`

English:
lemma sup_nhds'
  given: [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y))
  proof: (continuous_sup.tendsto _).comp (hf.prodMk_nhds hg)

中文:
引理 sup_nhds'
  条件: [最大值 L] [余ntinuousSup L] (hf : 收敛 f l (𝓝 x)) (hg : 收敛 g l (𝓝 y))
  证明: (continuous_sup.tendsto _).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_sup, continuous_sup.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
lemma sup_nhds' [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊔ g) l (𝓝 (x ⊔ y)) :=
  (continuous_sup.tendsto _).comp (hf.prodMk_nhds hg)

/--
lemma `sup_nhds` / 引理 `sup_nhds`

English:
lemma sup_nhds
  given: [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y))
  proof: hf.sup_nhds' hg

中文:
引理 sup_nhds
  条件: [最大值 L] [余ntinuousSup L] (hf : 收敛 f l (𝓝 x)) (hg : 收敛 g l (𝓝 y))
  证明: hf.sup_nhds' hg

Depends on / 依赖: hf.sup_nhds, sup_nhds
-/
lemma sup_nhds [Max L] [ContinuousSup L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊔ g i) l (𝓝 (x ⊔ y)) :=
  hf.sup_nhds' hg

/--
lemma `inf_nhds'` / 引理 `inf_nhds'`

English:
lemma inf_nhds'
  given: [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y))
  proof: (continuous_inf.tendsto _).comp (hf.prodMk_nhds hg)

中文:
引理 inf_nhds'
  条件: [最小值 L] [余ntinuousInf L] (hf : 收敛 f l (𝓝 x)) (hg : 收敛 g l (𝓝 y))
  证明: (continuous_inf.tendsto _).comp (hf.prodMk_nhds hg)

Depends on / 依赖: continuous_inf, continuous_inf.tendsto, hf.prodMk_nhds, prodMk_nhds, tendsto
-/
lemma inf_nhds' [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (f ⊓ g) l (𝓝 (x ⊓ y)) :=
  (continuous_inf.tendsto _).comp (hf.prodMk_nhds hg)

/--
lemma `inf_nhds` / 引理 `inf_nhds`

English:
lemma inf_nhds
  given: [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y))
  proof: hf.inf_nhds' hg

中文:
引理 inf_nhds
  条件: [最小值 L] [余ntinuousInf L] (hf : 收敛 f l (𝓝 x)) (hg : 收敛 g l (𝓝 y))
  证明: hf.inf_nhds' hg

Depends on / 依赖: hf.inf_nhds, inf_nhds
-/
lemma inf_nhds [Min L] [ContinuousInf L] (hf : Tendsto f l (𝓝 x)) (hg : Tendsto g l (𝓝 y)) :
    Tendsto (fun i => f i ⊓ g i) l (𝓝 (x ⊓ y)) :=
  hf.inf_nhds' hg

end SupInf

open Finset

variable {ι α : Type*} {s : Finset ι} {f : ι -> α -> L} {l : Filter α} {g : ι -> L}

/--
lemma `finset_sup'_nhds` / 引理 `finset_sup'_nhds`

English:
lemma finset_sup'_nhds
  statement: [SemilatticeSup L] [ContinuousSup L]
  proof: by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons a s ha hne ihs =>
    rw [forall_mem_cons] at hs
    simp only [sup'_cons, hne]
    exact hs.1.sup_nhds (ihs hs.2)

中文:
引理 finset_sup'_nhds
  结论: [SemilatticeSup L] [余ntinuousSup L]
  证明: by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons a s ha hne ihs =>
    rw [forall_mem_cons] at hs
    simp only [sup'_cons, hne]
    exact hs.1.sup_nhds (ihs hs.2)

Depends on / 依赖: Finset, Finset.Nonempty.cons_induction, Nonempty, _cons, cons_induction, forall_mem_cons, singleton, sup_nhds
-/
lemma finset_sup'_nhds [SemilatticeSup L] [ContinuousSup L]
    (hne : s.Nonempty) (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (s.sup' hne f) l (𝓝 (s.sup' hne g)) := by
  induction hne using Finset.Nonempty.cons_induction with
  | singleton => simpa using hs
  | cons a s ha hne ihs =>
    rw [forall_mem_cons] at hs
    simp only [sup'_cons, hne]
    exact hs.1.sup_nhds (ihs hs.2)

/--
lemma `finset_sup'_nhds_apply` / 引理 `finset_sup'_nhds_apply`

English:
lemma finset_sup'_nhds_apply
  statement: [SemilatticeSup L] [ContinuousSup L]
  proof: by
  simpa only [← Finset.sup'_apply] using finset_sup'_nhds hne hs

中文:
引理 finset_sup'_nhds_apply
  结论: [SemilatticeSup L] [余ntinuousSup L]
  证明: by
  simpa only [← Finset.sup'_apply] using finset_sup'_nhds hne hs
-/
lemma finset_sup'_nhds_apply [SemilatticeSup L] [ContinuousSup L]
    (hne : s.Nonempty) (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a => s.sup' hne (f · a)) l (𝓝 (s.sup' hne g)) := by
  simpa only [← Finset.sup'_apply] using finset_sup'_nhds hne hs

/--
lemma `finset_inf'_nhds` / 引理 `finset_inf'_nhds`

English:
lemma finset_inf'_nhds
  statement: [SemilatticeInf L] [ContinuousInf L]
  proof: finset_sup'_nhds (L := Lᵒᵈ) hne hs

中文:
引理 finset_inf'_nhds
  结论: [SemilatticeInf L] [余ntinuousInf L]
  证明: finset_sup'_nhds (L := Lᵒᵈ) hne hs

Depends on / 依赖: _nhds, finset_sup
-/
lemma finset_inf'_nhds [SemilatticeInf L] [ContinuousInf L]
    (hne : s.Nonempty) (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (s.inf' hne f) l (𝓝 (s.inf' hne g)) :=
  finset_sup'_nhds (L := Lᵒᵈ) hne hs

/--
lemma `finset_inf'_nhds_apply` / 引理 `finset_inf'_nhds_apply`

English:
lemma finset_inf'_nhds_apply
  statement: [SemilatticeInf L] [ContinuousInf L]
  proof: finset_sup'_nhds_apply (L := Lᵒᵈ) hne hs

中文:
引理 finset_inf'_nhds_apply
  结论: [SemilatticeInf L] [余ntinuousInf L]
  证明: finset_sup'_nhds_apply (L := Lᵒᵈ) hne hs
-/
lemma finset_inf'_nhds_apply [SemilatticeInf L] [ContinuousInf L]
    (hne : s.Nonempty) (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a => s.inf' hne (f · a)) l (𝓝 (s.inf' hne g)) :=
  finset_sup'_nhds_apply (L := Lᵒᵈ) hne hs

/--
lemma `finset_sup_nhds` / 引理 `finset_sup_nhds`

English:
lemma finset_sup_nhds
  statement: [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
  proof: by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using! tendsto_const_nhds
  · simp only [← sup'_eq_sup hne]
    exact finset_sup'_nhds hne hs

中文:
引理 finset_sup_nhds
  结论: [SemilatticeSup L] [有底序 L] [余ntinuousSup L]
  证明: by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using! tendsto_const_nhds
  · simp only [← sup'_eq_sup hne]
    exact finset_sup'_nhds hne hs

Depends on / 依赖: _eq_sup, _nhds, eq_empty_or_nonempty, finset_sup, s.eq_empty_or_nonempty, tendsto_const_nhds
-/
lemma finset_sup_nhds [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
    (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.sup f) l (𝓝 (s.sup g)) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simpa using! tendsto_const_nhds
  · simp only [← sup'_eq_sup hne]
    exact finset_sup'_nhds hne hs

/--
lemma `finset_sup_nhds_apply` / 引理 `finset_sup_nhds_apply`

English:
lemma finset_sup_nhds_apply
  statement: [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
  proof: by
  simpa only [← Finset.sup_apply] using finset_sup_nhds hs

中文:
引理 finset_sup_nhds_apply
  结论: [SemilatticeSup L] [有底序 L] [余ntinuousSup L]
  证明: by
  simpa only [← Finset.sup_apply] using finset_sup_nhds hs

Depends on / 依赖: Finset, Finset.sup_apply, finset_sup_nhds, sup_apply
-/
lemma finset_sup_nhds_apply [SemilatticeSup L] [OrderBot L] [ContinuousSup L]
    (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a => s.sup (f · a)) l (𝓝 (s.sup g)) := by
  simpa only [← Finset.sup_apply] using finset_sup_nhds hs

/--
lemma `finset_inf_nhds` / 引理 `finset_inf_nhds`

English:
lemma finset_inf_nhds
  statement: [SemilatticeInf L] [OrderTop L] [ContinuousInf L]
  proof: finset_sup_nhds (L := Lᵒᵈ) hs

中文:
引理 finset_inf_nhds
  结论: [SemilatticeInf L] [有顶序 L] [余ntinuousInf L]
  证明: finset_sup_nhds (L := Lᵒᵈ) hs

Depends on / 依赖: finset_sup_nhds
-/
lemma finset_inf_nhds [SemilatticeInf L] [OrderTop L] [ContinuousInf L]
    (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) : Tendsto (s.inf f) l (𝓝 (s.inf g)) :=
  finset_sup_nhds (L := Lᵒᵈ) hs

/--
lemma `finset_inf_nhds_apply` / 引理 `finset_inf_nhds_apply`

English:
lemma finset_inf_nhds_apply
  statement: [SemilatticeInf L] [OrderTop L] [ContinuousInf L]
  proof: finset_sup_nhds_apply (L := Lᵒᵈ) hs

中文:
引理 finset_inf_nhds_apply
  结论: [SemilatticeInf L] [有顶序 L] [余ntinuousInf L]
  证明: finset_sup_nhds_apply (L := Lᵒᵈ) hs

Depends on / 依赖: finset_sup_nhds_apply
-/
lemma finset_inf_nhds_apply [SemilatticeInf L] [OrderTop L] [ContinuousInf L]
    (hs : forall i in s, Tendsto (f i) l (𝓝 (g i))) :
    Tendsto (fun a => s.inf (f · a)) l (𝓝 (s.inf g)) :=
  finset_sup_nhds_apply (L := Lᵒᵈ) hs

end Filter.Tendsto

section Sup

variable [Max L] [ContinuousSup L] {f g : X -> L} {s : Set X} {x : X}

@[fun_prop]
/--
lemma `ContinuousAt.sup'` / 引理 `ContinuousAt.sup'`

English:
lemma ContinuousAt.sup'
  given: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  proof: hf.sup_nhds' hg

@[fun_prop]

中文:
引理 ContinuousAt.上确界'
  条件: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  证明: hf.sup_nhds' hg

@[fun_prop]

Depends on / 依赖: hf.sup_nhds, sup_nhds
-/
lemma ContinuousAt.sup' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f ⊔ g) x :=
  hf.sup_nhds' hg

@[fun_prop]
/--
lemma `ContinuousAt.sup` / 引理 `ContinuousAt.sup`

English:
lemma ContinuousAt.sup
  given: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  proof: hf.sup' hg

@[fun_prop]

中文:
引理 ContinuousAt.上确界
  条件: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  证明: hf.sup' hg

@[fun_prop]

Depends on / 依赖: hf.sup
-/
lemma ContinuousAt.sup (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => f a ⊔ g a) x :=
  hf.sup' hg

@[fun_prop]
/--
lemma `ContinuousWithinAt.sup'` / 引理 `ContinuousWithinAt.sup'`

English:
lemma ContinuousWithinAt.sup'
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: hf.sup_nhds' hg

@[fun_prop]

中文:
引理 ContinuousWithinAt.上确界'
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: hf.sup_nhds' hg

@[fun_prop]

Depends on / 依赖: hf.sup_nhds, sup_nhds
-/
lemma ContinuousWithinAt.sup' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f ⊔ g) s x :=
  hf.sup_nhds' hg

@[fun_prop]
/--
lemma `ContinuousWithinAt.sup` / 引理 `ContinuousWithinAt.sup`

English:
lemma ContinuousWithinAt.sup
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: hf.sup' hg

@[fun_prop]

中文:
引理 ContinuousWithinAt.上确界
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: hf.sup' hg

@[fun_prop]

Depends on / 依赖: hf.sup
-/
lemma ContinuousWithinAt.sup (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun a => f a ⊔ g a) s x :=
  hf.sup' hg

@[fun_prop]
/--
lemma `ContinuousOn.sup'` / 引理 `ContinuousOn.sup'`

English:
lemma ContinuousOn.sup'
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun x hx =>
  (hf x hx).sup' (hg x hx)

@[fun_prop]

中文:
引理 ContinuousOn.上确界'
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun x hx =>
  (hf x hx).sup' (hg x hx)

@[fun_prop]
-/
lemma ContinuousOn.sup' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f ⊔ g) s := fun x hx =>
  (hf x hx).sup' (hg x hx)

@[fun_prop]
/--
lemma `ContinuousOn.sup` / 引理 `ContinuousOn.sup`

English:
lemma ContinuousOn.sup
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: hf.sup' hg

@[fun_prop]

中文:
引理 ContinuousOn.上确界
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: hf.sup' hg

@[fun_prop]

Depends on / 依赖: hf.sup
-/
lemma ContinuousOn.sup (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => f a ⊔ g a) s :=
  hf.sup' hg

@[fun_prop]
/--
lemma `Continuous.sup'` / 引理 `Continuous.sup'`

English:
lemma Continuous.sup'
  given: (hf : Continuous f) (hg : Continuous g)
  statement: Continuous (f ⊔ g)
  proof: hf.sup hg

中文:
引理 连续.上确界'
  条件: (hf : 连续 f) (hg : 连续 g)
  结论: 连续 (f ⊔ g)
  证明: hf.sup hg

Depends on / 依赖: hf.sup
-/
lemma Continuous.sup' (hf : Continuous f) (hg : Continuous g) : Continuous (f ⊔ g) := hf.sup hg

end Sup

section Inf

variable [Min L] [ContinuousInf L] {f g : X -> L} {s : Set X} {x : X}

@[fun_prop]
/--
lemma `ContinuousAt.inf'` / 引理 `ContinuousAt.inf'`

English:
lemma ContinuousAt.inf'
  given: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  proof: hf.inf_nhds' hg

@[fun_prop]

中文:
引理 ContinuousAt.下确界'
  条件: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  证明: hf.inf_nhds' hg

@[fun_prop]

Depends on / 依赖: hf.inf_nhds, inf_nhds
-/
lemma ContinuousAt.inf' (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (f ⊓ g) x :=
  hf.inf_nhds' hg

@[fun_prop]
/--
lemma `ContinuousAt.inf` / 引理 `ContinuousAt.inf`

English:
lemma ContinuousAt.inf
  given: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  proof: hf.inf' hg

@[fun_prop]

中文:
引理 ContinuousAt.下确界
  条件: (hf : ContinuousAt f x) (hg : ContinuousAt g x)
  证明: hf.inf' hg

@[fun_prop]

Depends on / 依赖: hf.inf
-/
lemma ContinuousAt.inf (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    ContinuousAt (fun a => f a ⊓ g a) x :=
  hf.inf' hg

@[fun_prop]
/--
lemma `ContinuousWithinAt.inf'` / 引理 `ContinuousWithinAt.inf'`

English:
lemma ContinuousWithinAt.inf'
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: hf.inf_nhds' hg

@[fun_prop]

中文:
引理 ContinuousWithinAt.下确界'
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: hf.inf_nhds' hg

@[fun_prop]

Depends on / 依赖: hf.inf_nhds, inf_nhds
-/
lemma ContinuousWithinAt.inf' (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (f ⊓ g) s x :=
  hf.inf_nhds' hg

@[fun_prop]
/--
lemma `ContinuousWithinAt.inf` / 引理 `ContinuousWithinAt.inf`

English:
lemma ContinuousWithinAt.inf
  given: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  proof: hf.inf' hg

@[fun_prop]

中文:
引理 ContinuousWithinAt.下确界
  条件: (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x)
  证明: hf.inf' hg

@[fun_prop]

Depends on / 依赖: hf.inf
-/
lemma ContinuousWithinAt.inf (hf : ContinuousWithinAt f s x) (hg : ContinuousWithinAt g s x) :
    ContinuousWithinAt (fun a => f a ⊓ g a) s x :=
  hf.inf' hg

@[fun_prop]
/--
lemma `ContinuousOn.inf'` / 引理 `ContinuousOn.inf'`

English:
lemma ContinuousOn.inf'
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: fun x hx =>
  (hf x hx).inf' (hg x hx)

@[fun_prop]

中文:
引理 ContinuousOn.下确界'
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: fun x hx =>
  (hf x hx).inf' (hg x hx)

@[fun_prop]
-/
lemma ContinuousOn.inf' (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (f ⊓ g) s := fun x hx =>
  (hf x hx).inf' (hg x hx)

@[fun_prop]
/--
lemma `ContinuousOn.inf` / 引理 `ContinuousOn.inf`

English:
lemma ContinuousOn.inf
  given: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  proof: hf.inf' hg

@[fun_prop]

中文:
引理 ContinuousOn.下确界
  条件: (hf : ContinuousOn f s) (hg : ContinuousOn g s)
  证明: hf.inf' hg

@[fun_prop]

Depends on / 依赖: hf.inf
-/
lemma ContinuousOn.inf (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun a => f a ⊓ g a) s :=
  hf.inf' hg

@[fun_prop]
/--
lemma `Continuous.inf'` / 引理 `Continuous.inf'`

English:
lemma Continuous.inf'
  given: (hf : Continuous f) (hg : Continuous g)
  statement: Continuous (f ⊓ g)
  proof: hf.inf hg

中文:
引理 连续.下确界'
  条件: (hf : 连续 f) (hg : 连续 g)
  结论: 连续 (f ⊓ g)
  证明: hf.inf hg

Depends on / 依赖: hf.inf
-/
lemma Continuous.inf' (hf : Continuous f) (hg : Continuous g) : Continuous (f ⊓ g) := hf.inf hg

end Inf

section FinsetSup'

variable {ι : Type*} [SemilatticeSup L] [ContinuousSup L] {s : Finset ι}
  {f : ι -> X -> L} {t : Set X} {x : X}

@[fun_prop]
/--
lemma `ContinuousAt.finset_sup'_apply` / 引理 `ContinuousAt.finset_sup'_apply`

English:
lemma ContinuousAt.finset_sup'_apply
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x)
  proof: Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_sup'_apply
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_sup, _nhds_apply, finset_sup
-/
lemma ContinuousAt.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (fun a => s.sup' hne (f · a)) x :=
  Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]
/--
lemma `ContinuousAt.finset_sup'` / 引理 `ContinuousAt.finset_sup'`

English:
lemma ContinuousAt.finset_sup'
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x)
  proof: by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_sup'
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]
-/
lemma ContinuousAt.finset_sup' (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (s.sup' hne f) x := by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_sup'_apply` / 引理 `ContinuousWithinAt.finset_sup'_apply`

English:
lemma ContinuousWithinAt.finset_sup'_apply
  statement: (hne : s.Nonempty)
  proof: Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_sup'_apply
  结论: (hne : s.非空)
  证明: Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_sup, _nhds_apply, finset_sup
-/
lemma ContinuousWithinAt.finset_sup'_apply (hne : s.Nonempty)
    (hs : forall i in s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a => s.sup' hne (f · a)) t x :=
  Tendsto.finset_sup'_nhds_apply hne hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_sup'` / 引理 `ContinuousWithinAt.finset_sup'`

English:
lemma ContinuousWithinAt.finset_sup'
  statement: (hne : s.Nonempty)
  proof: by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_sup'
  结论: (hne : s.非空)
  证明: by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]
-/
lemma ContinuousWithinAt.finset_sup' (hne : s.Nonempty)
    (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.sup' hne f) t x := by
  simpa only [← Finset.sup'_apply] using finset_sup'_apply hne hs

@[fun_prop]
/--
lemma `ContinuousOn.finset_sup'_apply` / 引理 `ContinuousOn.finset_sup'_apply`

English:
lemma ContinuousOn.finset_sup'_apply
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_sup'_apply hne fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_sup'_apply
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_sup'_apply hne fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (fun a => s.sup' hne (f · a)) t := fun x hx =>
  ContinuousWithinAt.finset_sup'_apply hne fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `ContinuousOn.finset_sup'` / 引理 `ContinuousOn.finset_sup'`

English:
lemma ContinuousOn.finset_sup'
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_sup' hne fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_sup'
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_sup' hne fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_sup' (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (s.sup' hne f) t := fun x hx =>
  ContinuousWithinAt.finset_sup' hne fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `Continuous.finset_sup'_apply` / 引理 `Continuous.finset_sup'_apply`

English:
lemma Continuous.finset_sup'_apply
  given: (hne : s.Nonempty) (hs : forall i in s, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup'_apply _ fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

中文:
引理 连续.finset_sup'_apply
  条件: (hne : s.非空) (hs : 对任意 i in s, 连续 (f i))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup'_apply _ fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_sup, _apply, continuousAt, continuous_iff_continuousAt, finset_sup
-/
lemma Continuous.finset_sup'_apply (hne : s.Nonempty) (hs : forall i in s, Continuous (f i)) :
    Continuous (fun a => s.sup' hne (f · a)) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup'_apply _ fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]
/--
lemma `Continuous.finset_sup'` / 引理 `Continuous.finset_sup'`

English:
lemma Continuous.finset_sup'
  given: (hne : s.Nonempty) (hs : forall i in s, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup' _ fun i hi => (hs i hi).continuousAt

中文:
引理 连续.finset_sup'
  条件: (hne : s.非空) (hs : 对任意 i in s, 连续 (f i))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup' _ fun i hi => (hs i hi).continuousAt
-/
lemma Continuous.finset_sup' (hne : s.Nonempty) (hs : forall i in s, Continuous (f i)) :
    Continuous (s.sup' hne f) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup' _ fun i hi => (hs i hi).continuousAt

end FinsetSup'

section FinsetSup

variable {ι : Type*} [SemilatticeSup L] [OrderBot L] [ContinuousSup L] {s : Finset ι}
  {f : ι -> X -> L} {t : Set X} {x : X}

@[fun_prop]
/--
lemma `ContinuousAt.finset_sup_apply` / 引理 `ContinuousAt.finset_sup_apply`

English:
lemma ContinuousAt.finset_sup_apply
  given: (hs : forall i in s, ContinuousAt (f i) x)
  proof: Tendsto.finset_sup_nhds_apply hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_sup_apply
  条件: (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: Tendsto.finset_sup_nhds_apply hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_sup_nhds_apply, finset_sup_nhds_apply
-/
lemma ContinuousAt.finset_sup_apply (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (fun a => s.sup (f · a)) x :=
  Tendsto.finset_sup_nhds_apply hs

@[fun_prop]
/--
lemma `ContinuousAt.finset_sup` / 引理 `ContinuousAt.finset_sup`

English:
lemma ContinuousAt.finset_sup
  given: (hs : forall i in s, ContinuousAt (f i) x)
  proof: by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_sup
  条件: (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]

Depends on / 依赖: Finset, Finset.sup_apply, finset_sup_apply, sup_apply
-/
lemma ContinuousAt.finset_sup (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (s.sup f) x := by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_sup_apply` / 引理 `ContinuousWithinAt.finset_sup_apply`

English:
lemma ContinuousWithinAt.finset_sup_apply
  proof: Tendsto.finset_sup_nhds_apply hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_sup_apply
  证明: Tendsto.finset_sup_nhds_apply hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_sup_nhds_apply, finset_sup_nhds_apply
-/
lemma ContinuousWithinAt.finset_sup_apply
    (hs : forall i in s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a => s.sup (f · a)) t x :=
  Tendsto.finset_sup_nhds_apply hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_sup` / 引理 `ContinuousWithinAt.finset_sup`

English:
lemma ContinuousWithinAt.finset_sup
  proof: by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_sup
  证明: by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]

Depends on / 依赖: Finset, Finset.sup_apply, finset_sup_apply, sup_apply
-/
lemma ContinuousWithinAt.finset_sup
    (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.sup f) t x := by
  simpa only [← Finset.sup_apply] using finset_sup_apply hs

@[fun_prop]
/--
lemma `ContinuousOn.finset_sup_apply` / 引理 `ContinuousOn.finset_sup_apply`

English:
lemma ContinuousOn.finset_sup_apply
  given: (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_sup_apply fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_sup_apply
  条件: (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_sup_apply fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_sup_apply (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (fun a => s.sup (f · a)) t := fun x hx =>
  ContinuousWithinAt.finset_sup_apply fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `ContinuousOn.finset_sup` / 引理 `ContinuousOn.finset_sup`

English:
lemma ContinuousOn.finset_sup
  given: (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_sup fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_sup
  条件: (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_sup fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_sup (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (s.sup f) t := fun x hx =>
  ContinuousWithinAt.finset_sup fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `Continuous.finset_sup_apply` / 引理 `Continuous.finset_sup_apply`

English:
lemma Continuous.finset_sup_apply
  given: (hs : forall i in s, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup_apply fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

中文:
引理 连续.finset_sup_apply
  条件: (hs : 对任意 i in s, 连续 (f i))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup_apply fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_sup_apply, continuousAt, continuous_iff_continuousAt, finset_sup_apply
-/
lemma Continuous.finset_sup_apply (hs : forall i in s, Continuous (f i)) :
    Continuous (fun a => s.sup (f · a)) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup_apply fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]
/--
lemma `Continuous.finset_sup` / 引理 `Continuous.finset_sup`

English:
lemma Continuous.finset_sup
  given: (hs : forall i in s, Continuous (f i))
  statement: Continuous (s.sup f)
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup fun i hi => (hs i hi).continuousAt

中文:
引理 连续.finset_sup
  条件: (hs : 对任意 i in s, 连续 (f i))
  结论: 连续 (s.上确界 f)
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup fun i hi => (hs i hi).continuousAt

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_sup, continuousAt, continuous_iff_continuousAt, finset_sup
-/
lemma Continuous.finset_sup (hs : forall i in s, Continuous (f i)) : Continuous (s.sup f) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_sup fun i hi => (hs i hi).continuousAt

end FinsetSup

section FinsetInf'

variable {ι : Type*} [SemilatticeInf L] [ContinuousInf L] {s : Finset ι}
  {f : ι -> X -> L} {t : Set X} {x : X}

@[fun_prop]
/--
lemma `ContinuousAt.finset_inf'_apply` / 引理 `ContinuousAt.finset_inf'_apply`

English:
lemma ContinuousAt.finset_inf'_apply
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x)
  proof: Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_inf'_apply
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_inf, _nhds_apply, finset_inf
-/
lemma ContinuousAt.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (fun a => s.inf' hne (f · a)) x :=
  Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]
/--
lemma `ContinuousAt.finset_inf'` / 引理 `ContinuousAt.finset_inf'`

English:
lemma ContinuousAt.finset_inf'
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x)
  proof: by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_inf'
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]
-/
lemma ContinuousAt.finset_inf' (hne : s.Nonempty) (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (s.inf' hne f) x := by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_inf'_apply` / 引理 `ContinuousWithinAt.finset_inf'_apply`

English:
lemma ContinuousWithinAt.finset_inf'_apply
  statement: (hne : s.Nonempty)
  proof: Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_inf'_apply
  结论: (hne : s.非空)
  证明: Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_inf, _nhds_apply, finset_inf
-/
lemma ContinuousWithinAt.finset_inf'_apply (hne : s.Nonempty)
    (hs : forall i in s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a => s.inf' hne (f · a)) t x :=
  Tendsto.finset_inf'_nhds_apply hne hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_inf'` / 引理 `ContinuousWithinAt.finset_inf'`

English:
lemma ContinuousWithinAt.finset_inf'
  statement: (hne : s.Nonempty)
  proof: by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_inf'
  结论: (hne : s.非空)
  证明: by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]
-/
lemma ContinuousWithinAt.finset_inf' (hne : s.Nonempty)
    (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.inf' hne f) t x := by
  simpa only [← Finset.inf'_apply] using finset_inf'_apply hne hs

@[fun_prop]
/--
lemma `ContinuousOn.finset_inf'_apply` / 引理 `ContinuousOn.finset_inf'_apply`

English:
lemma ContinuousOn.finset_inf'_apply
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_inf'_apply hne fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_inf'_apply
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_inf'_apply hne fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (fun a => s.inf' hne (f · a)) t := fun x hx =>
  ContinuousWithinAt.finset_inf'_apply hne fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `ContinuousOn.finset_inf'` / 引理 `ContinuousOn.finset_inf'`

English:
lemma ContinuousOn.finset_inf'
  given: (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_inf' hne fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_inf'
  条件: (hne : s.非空) (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_inf' hne fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_inf' (hne : s.Nonempty) (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (s.inf' hne f) t := fun x hx =>
  ContinuousWithinAt.finset_inf' hne fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `Continuous.finset_inf'_apply` / 引理 `Continuous.finset_inf'_apply`

English:
lemma Continuous.finset_inf'_apply
  given: (hne : s.Nonempty) (hs : forall i in s, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf'_apply _ fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

中文:
引理 连续.finset_inf'_apply
  条件: (hne : s.非空) (hs : 对任意 i in s, 连续 (f i))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf'_apply _ fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_inf, _apply, continuousAt, continuous_iff_continuousAt, finset_inf
-/
lemma Continuous.finset_inf'_apply (hne : s.Nonempty) (hs : forall i in s, Continuous (f i)) :
    Continuous (fun a => s.inf' hne (f · a)) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf'_apply _ fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]
/--
lemma `Continuous.finset_inf'` / 引理 `Continuous.finset_inf'`

English:
lemma Continuous.finset_inf'
  given: (hne : s.Nonempty) (hs : forall i in s, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf' _ fun i hi => (hs i hi).continuousAt

中文:
引理 连续.finset_inf'
  条件: (hne : s.非空) (hs : 对任意 i in s, 连续 (f i))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf' _ fun i hi => (hs i hi).continuousAt
-/
lemma Continuous.finset_inf' (hne : s.Nonempty) (hs : forall i in s, Continuous (f i)) :
    Continuous (s.inf' hne f) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf' _ fun i hi => (hs i hi).continuousAt

end FinsetInf'

section FinsetInf

variable {ι : Type*} [SemilatticeInf L] [OrderTop L] [ContinuousInf L] {s : Finset ι}
  {f : ι -> X -> L} {t : Set X} {x : X}

@[fun_prop]
/--
lemma `ContinuousAt.finset_inf_apply` / 引理 `ContinuousAt.finset_inf_apply`

English:
lemma ContinuousAt.finset_inf_apply
  given: (hs : forall i in s, ContinuousAt (f i) x)
  proof: Tendsto.finset_inf_nhds_apply hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_inf_apply
  条件: (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: Tendsto.finset_inf_nhds_apply hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_inf_nhds_apply, finset_inf_nhds_apply
-/
lemma ContinuousAt.finset_inf_apply (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (fun a => s.inf (f · a)) x :=
  Tendsto.finset_inf_nhds_apply hs

@[fun_prop]
/--
lemma `ContinuousAt.finset_inf` / 引理 `ContinuousAt.finset_inf`

English:
lemma ContinuousAt.finset_inf
  given: (hs : forall i in s, ContinuousAt (f i) x)
  proof: by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]

中文:
引理 ContinuousAt.finset_inf
  条件: (hs : 对任意 i in s, ContinuousAt (f i) x)
  证明: by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]

Depends on / 依赖: Finset, Finset.inf_apply, finset_inf_apply, inf_apply
-/
lemma ContinuousAt.finset_inf (hs : forall i in s, ContinuousAt (f i) x) :
    ContinuousAt (s.inf f) x := by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_inf_apply` / 引理 `ContinuousWithinAt.finset_inf_apply`

English:
lemma ContinuousWithinAt.finset_inf_apply
  proof: Tendsto.finset_inf_nhds_apply hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_inf_apply
  证明: Tendsto.finset_inf_nhds_apply hs

@[fun_prop]

Depends on / 依赖: Tendsto, Tendsto.finset_inf_nhds_apply, finset_inf_nhds_apply
-/
lemma ContinuousWithinAt.finset_inf_apply
    (hs : forall i in s, ContinuousWithinAt (f i) t x) :
    ContinuousWithinAt (fun a => s.inf (f · a)) t x :=
  Tendsto.finset_inf_nhds_apply hs

@[fun_prop]
/--
lemma `ContinuousWithinAt.finset_inf` / 引理 `ContinuousWithinAt.finset_inf`

English:
lemma ContinuousWithinAt.finset_inf
  proof: by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]

中文:
引理 ContinuousWithinAt.finset_inf
  证明: by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]

Depends on / 依赖: Finset, Finset.inf_apply, finset_inf_apply, inf_apply
-/
lemma ContinuousWithinAt.finset_inf
    (hs : forall i in s, ContinuousWithinAt (f i) t x) : ContinuousWithinAt (s.inf f) t x := by
  simpa only [← Finset.inf_apply] using finset_inf_apply hs

@[fun_prop]
/--
lemma `ContinuousOn.finset_inf_apply` / 引理 `ContinuousOn.finset_inf_apply`

English:
lemma ContinuousOn.finset_inf_apply
  given: (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_inf_apply fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_inf_apply
  条件: (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_inf_apply fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_inf_apply (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (fun a => s.inf (f · a)) t := fun x hx =>
  ContinuousWithinAt.finset_inf_apply fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `ContinuousOn.finset_inf` / 引理 `ContinuousOn.finset_inf`

English:
lemma ContinuousOn.finset_inf
  given: (hs : forall i in s, ContinuousOn (f i) t)
  proof: fun x hx =>
  ContinuousWithinAt.finset_inf fun i hi => hs i hi x hx

@[fun_prop]

中文:
引理 ContinuousOn.finset_inf
  条件: (hs : 对任意 i in s, ContinuousOn (f i) t)
  证明: fun x hx =>
  ContinuousWithinAt.finset_inf fun i hi => hs i hi x hx

@[fun_prop]
-/
lemma ContinuousOn.finset_inf (hs : forall i in s, ContinuousOn (f i) t) :
    ContinuousOn (s.inf f) t := fun x hx =>
  ContinuousWithinAt.finset_inf fun i hi => hs i hi x hx

@[fun_prop]
/--
lemma `Continuous.finset_inf_apply` / 引理 `Continuous.finset_inf_apply`

English:
lemma Continuous.finset_inf_apply
  given: (hs : forall i in s, Continuous (f i))
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf_apply fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

中文:
引理 连续.finset_inf_apply
  条件: (hs : 对任意 i in s, 连续 (f i))
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf_apply fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_inf_apply, continuousAt, continuous_iff_continuousAt, finset_inf_apply
-/
lemma Continuous.finset_inf_apply (hs : forall i in s, Continuous (f i)) :
    Continuous (fun a => s.inf (f · a)) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf_apply fun i hi =>
    (hs i hi).continuousAt

@[fun_prop]
/--
lemma `Continuous.finset_inf` / 引理 `Continuous.finset_inf`

English:
lemma Continuous.finset_inf
  given: (hs : forall i in s, Continuous (f i))
  statement: Continuous (s.inf f)
  proof: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf fun i hi => (hs i hi).continuousAt

中文:
引理 连续.finset_inf
  条件: (hs : 对任意 i in s, 连续 (f i))
  结论: 连续 (s.下确界 f)
  证明: continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf fun i hi => (hs i hi).continuousAt

Depends on / 依赖: ContinuousAt, ContinuousAt.finset_inf, continuousAt, continuous_iff_continuousAt, finset_inf
-/
lemma Continuous.finset_inf (hs : forall i in s, Continuous (f i)) : Continuous (s.inf f) :=
  continuous_iff_continuousAt.2 fun _ => ContinuousAt.finset_inf fun i hi => (hs i hi).continuousAt

end FinsetInf
