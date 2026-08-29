/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Topology.Sets.Closeds
public import Mathlib.Topology.Sets.OpenCover

/-!
# Sober spaces

A quasi-sober space is a topological space where every irreducible closed subset has a generic
point.
A sober space is a quasi-sober space where every irreducible closed subset
has a *unique* generic point. This is if and only if the space is T0, and thus sober spaces can be
stated via `[QuasiSober α] [T0Space α]`.

## Main definition

* `IsGenericPoint` : `x` is the generic point of `S` if `S` is the closure of `x`.
* `QuasiSober` : A space is quasi-sober if every irreducible closed subset has a generic point.
* `genericPoints` : The set of generic points of irreducible components.

-/

@[expose] public section


open Set

variable {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]

section genericPoint

/-- `x` is a generic point of `S` if `S` is the closure of `x`. -/
@[stacks 004X "(1)"]
/--
Definition of `IsGenericPoint` / `IsGenericPoint` 的定义

English:
definition IsGenericPoint
  signature: (x : α) (S : Set α)
  body: closure ({x} : Set α) = S

中文:
定义 IsGenericPoint
  签名: (x : α) (S : 集合 α)
  定义体: closure ({x} : Set α) = S

Depends on / 依赖: closure
-/
def IsGenericPoint (x : α) (S : Set α) : Prop :=
  closure ({x} : Set α) = S

/--
theorem `isGenericPoint_def` / 定理 `isGenericPoint_def`

English:
theorem isGenericPoint_def
  given: {x : α} {S : Set α}
  statement: IsGenericPoint x S ↔ closure ({x} : Set α) = S
  proof: Iff.rfl

中文:
定理 isGenericPoint_def
  条件: {x : α} {S : 集合 α}
  结论: IsGenericPoint x S ↔ closure ({x} : 集合 α) = S
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem isGenericPoint_def {x : α} {S : Set α} : IsGenericPoint x S ↔ closure ({x} : Set α) = S :=
  Iff.rfl

/--
theorem `IsGenericPoint.def` / 定理 `IsGenericPoint.def`

English:
theorem IsGenericPoint.def
  given: {x : α} {S : Set α} (h : IsGenericPoint x S)
  proof: h

中文:
定理 IsGenericPoint.def
  条件: {x : α} {S : 集合 α} (h : IsGenericPoint x S)
  证明: h
-/
theorem IsGenericPoint.def {x : α} {S : Set α} (h : IsGenericPoint x S) :
    closure ({x} : Set α) = S :=
  h

/--
theorem `isGenericPoint_closure` / 定理 `isGenericPoint_closure`

English:
theorem isGenericPoint_closure
  given: {x : α}
  statement: IsGenericPoint x (closure ({x} : Set α))
  proof: refl _

中文:
定理 isGenericPoint_closure
  条件: {x : α}
  结论: IsGenericPoint x (closure ({x} : 集合 α))
  证明: refl _
-/
theorem isGenericPoint_closure {x : α} : IsGenericPoint x (closure ({x} : Set α)) :=
  refl _

variable {x y : α} {S U Z : Set α}

/--
theorem `isGenericPoint_iff_specializes` / 定理 `isGenericPoint_iff_specializes`

English:
theorem isGenericPoint_iff_specializes
  statement: IsGenericPoint x S ↔ forall y, x ⤳ y ↔ y in S
  proof: by
  simp only [specializes_iff_mem_closure, IsGenericPoint, Set.ext_iff]

中文:
定理 isGenericPoint_iff_specializes
  结论: IsGenericPoint x S ↔ 对任意 y, x ⤳ y ↔ y in S
  证明: by
  simp only [specializes_iff_mem_closure, IsGenericPoint, Set.ext_iff]

Depends on / 依赖: IsGenericPoint, Set.ext_iff, ext_iff, specializes_iff_mem_closure
-/
theorem isGenericPoint_iff_specializes : IsGenericPoint x S ↔ forall y, x ⤳ y ↔ y in S := by
  simp only [specializes_iff_mem_closure, IsGenericPoint, Set.ext_iff]

namespace IsGenericPoint

/--
theorem `specializes_iff_mem` / 定理 `specializes_iff_mem`

English:
theorem specializes_iff_mem
  given: (h : IsGenericPoint x S)
  statement: x ⤳ y ↔ y in S
  proof: isGenericPoint_iff_specializes.1 h y

中文:
定理 specializes_iff_mem
  条件: (h : IsGenericPoint x S)
  结论: x ⤳ y ↔ y in S
  证明: isGenericPoint_iff_specializes.1 h y

Depends on / 依赖: isGenericPoint_iff_specializes
-/
theorem specializes_iff_mem (h : IsGenericPoint x S) : x ⤳ y ↔ y in S :=
  isGenericPoint_iff_specializes.1 h y

/--
theorem `specializes` / 定理 `specializes`

English:
theorem specializes
  given: (h : IsGenericPoint x S) (h' : y in S)
  statement: x ⤳ y
  proof: h.specializes_iff_mem.2 h'

中文:
定理 specializes
  条件: (h : IsGenericPoint x S) (h' : y in S)
  结论: x ⤳ y
  证明: h.specializes_iff_mem.2 h'
-/
protected theorem specializes (h : IsGenericPoint x S) (h' : y in S) : x ⤳ y :=
  h.specializes_iff_mem.2 h'

/--
theorem `mem` / 定理 `mem`

English:
theorem mem
  given: (h : IsGenericPoint x S)
  statement: x in S
  proof: h.specializes_iff_mem.1 specializes_rfl

中文:
定理 mem
  条件: (h : IsGenericPoint x S)
  结论: x in S
  证明: h.specializes_iff_mem.1 specializes_rfl
-/
protected theorem mem (h : IsGenericPoint x S) : x in S :=
  h.specializes_iff_mem.1 specializes_rfl

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: (h : IsGenericPoint x S)
  statement: IsClosed S
  proof: h.def ▸ isClosed_closure

中文:
定理 isClosed
  条件: (h : IsGenericPoint x S)
  结论: 是闭集 S
  证明: h.def ▸ isClosed_closure
-/
protected theorem isClosed (h : IsGenericPoint x S) : IsClosed S :=
  h.def ▸ isClosed_closure

/--
theorem `isIrreducible` / 定理 `isIrreducible`

English:
theorem isIrreducible
  given: (h : IsGenericPoint x S)
  statement: IsIrreducible S
  proof: h.def ▸ isIrreducible_singleton.closure

中文:
定理 isIrreducible
  条件: (h : IsGenericPoint x S)
  结论: 是不可约 S
  证明: h.def ▸ isIrreducible_singleton.closure
-/
protected theorem isIrreducible (h : IsGenericPoint x S) : IsIrreducible S :=
  h.def ▸ isIrreducible_singleton.closure

/--
theorem `inseparable` / 定理 `inseparable`

English:
theorem inseparable
  given: (h : IsGenericPoint x S) (h' : IsGenericPoint y S)
  proof: (h.specializes h'.mem).antisymm (h'.specializes h.mem)

中文:
定理 inseparable
  条件: (h : IsGenericPoint x S) (h' : IsGenericPoint y S)
  证明: (h.specializes h'.mem).antisymm (h'.specializes h.mem)
-/
protected theorem inseparable (h : IsGenericPoint x S) (h' : IsGenericPoint y S) :
    Inseparable x y :=
  (h.specializes h'.mem).antisymm (h'.specializes h.mem)

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: [T0Space α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S)
  statement: x = y
  proof: (h.inseparable h').eq

中文:
定理 eq
  条件: [T0空间 α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S)
  结论: x = y
  证明: (h.inseparable h').eq
-/
protected theorem eq [T0Space α] (h : IsGenericPoint x S) (h' : IsGenericPoint y S) : x = y :=
  (h.inseparable h').eq

/--
theorem `mem_open_set_iff` / 定理 `mem_open_set_iff`

English:
theorem mem_open_set_iff
  given: (h : IsGenericPoint x S) (hU : IsOpen U)
  statement: x in U ↔ (S inter U).Nonempty
  proof: ⟨fun h' => ⟨x, h.mem, h'⟩, fun ⟨_y, hyS, hyU⟩ => (h.specializes hyS).mem_open hU hyU⟩

中文:
定理 mem_open_set_iff
  条件: (h : IsGenericPoint x S) (hU : 是开集 U)
  结论: x in U ↔ (S inter U).非空
  证明: ⟨fun h' => ⟨x, h.mem, h'⟩, fun ⟨_y, hyS, hyU⟩ => (h.specializes hyS).mem_open hU hyU⟩

Depends on / 依赖: h.mem, h.specializes, mem_open, specializes
-/
theorem mem_open_set_iff (h : IsGenericPoint x S) (hU : IsOpen U) : x in U ↔ (S inter U).Nonempty :=
  ⟨fun h' => ⟨x, h.mem, h'⟩, fun ⟨_y, hyS, hyU⟩ => (h.specializes hyS).mem_open hU hyU⟩

/--
theorem `disjoint_iff` / 定理 `disjoint_iff`

English:
theorem disjoint_iff
  given: (h : IsGenericPoint x S) (hU : IsOpen U)
  statement: Disjoint S U ↔ x ∉ U
  proof: by
  rw [h.mem_open_set_iff hU]; rw [← not_disjoint_iff_nonempty_inter]; rw [Classical.not_not]

中文:
定理 disjoint_iff
  条件: (h : IsGenericPoint x S) (hU : 是开集 U)
  结论: Disjoint S U ↔ x ∉ U
  证明: by
  rw [h.mem_open_set_iff hU]; rw [← not_disjoint_iff_nonempty_inter]; rw [Classical.not_not]

Depends on / 依赖: Classical, Classical.not_not, h.mem_open_set_iff, mem_open_set_iff, not_disjoint_iff_nonempty_inter, not_not
-/
theorem disjoint_iff (h : IsGenericPoint x S) (hU : IsOpen U) : Disjoint S U ↔ x ∉ U := by
  rw [h.mem_open_set_iff hU]; rw [← not_disjoint_iff_nonempty_inter]; rw [Classical.not_not]

/--
theorem `mem_closed_set_iff` / 定理 `mem_closed_set_iff`

English:
theorem mem_closed_set_iff
  given: (h : IsGenericPoint x S) (hZ : IsClosed Z)
  statement: x in Z ↔ S subseteq Z
  proof: by
  rw [← h.def]; rw [hZ.closure_subset_iff]; rw [singleton_subset_iff]

中文:
定理 mem_closed_set_iff
  条件: (h : IsGenericPoint x S) (hZ : 是闭集 Z)
  结论: x in Z ↔ S subseteq Z
  证明: by
  rw [← h.def]; rw [hZ.closure_subset_iff]; rw [singleton_subset_iff]

Depends on / 依赖: closure_subset_iff, h.def, hZ.closure_subset_iff, singleton_subset_iff
-/
theorem mem_closed_set_iff (h : IsGenericPoint x S) (hZ : IsClosed Z) : x in Z ↔ S subseteq Z := by
  rw [← h.def]; rw [hZ.closure_subset_iff]; rw [singleton_subset_iff]

/--
theorem `image` / 定理 `image`

English:
theorem image
  given: (h : IsGenericPoint x S) {f : α -> β} (hf : Continuous f)
  proof: by
  rw [isGenericPoint_def]; rw [← h.def]; rw [← image_singleton]; rw [closure_image_closure hf]

中文:
定理 像
  条件: (h : IsGenericPoint x S) {f : α -> β} (hf : 连续 f)
  证明: by
  rw [isGenericPoint_def]; rw [← h.def]; rw [← image_singleton]; rw [closure_image_closure hf]
-/
protected theorem image (h : IsGenericPoint x S) {f : α -> β} (hf : Continuous f) :
    IsGenericPoint (f x) (closure (f '' S)) := by
  rw [isGenericPoint_def]; rw [← h.def]; rw [← image_singleton]; rw [closure_image_closure hf]

end IsGenericPoint

/--
theorem `isGenericPoint_iff_forall_closed` / 定理 `isGenericPoint_iff_forall_closed`

English:
theorem isGenericPoint_iff_forall_closed
  given: (hS : IsClosed S) (hxS : x in S)
  proof: by
  have : closure {x} subseteq S := closure_minimal (singleton_subset_iff.2 hxS) hS
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_and, closure, subset_sInter_iff,
    mem_ofPred_eq, and_imp, singleton_subset_iff]

中文:
定理 isGenericPoint_iff_对任意_closed
  条件: (hS : 是闭集 S) (hxS : x in S)
  证明: by
  have : closure {x} subseteq S := closure_minimal (singleton_subset_iff.2 hxS) hS
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_and, closure, subset_sInter_iff,
    mem_ofPred_eq, and_imp, singleton_subset_iff]

Depends on / 依赖: IsGenericPoint, and_imp, closure, closure_minimal, mem_ofPred_eq, simp_rw, singleton_subset_iff, subset_antisymm_iff, subset_sInter_iff, subseteq, true_and
-/
theorem isGenericPoint_iff_forall_closed (hS : IsClosed S) (hxS : x in S) :
    IsGenericPoint x S ↔ forall Z : Set α, IsClosed Z -> x in Z -> S subseteq Z := by
  have : closure {x} subseteq S := closure_minimal (singleton_subset_iff.2 hxS) hS
  simp_rw [IsGenericPoint, subset_antisymm_iff, this, true_and, closure, subset_sInter_iff,
    mem_ofPred_eq, and_imp, singleton_subset_iff]

end genericPoint

section Sober

/-- A space is sober if every irreducible closed subset has a generic point. -/
@[mk_iff, stacks 004X "(3)"]
/--
Definition of `QuasiSober` / `QuasiSober` 的定义

English:
class QuasiSober
  parameters: (α : Type*) [TopologicalSpace α]
  axioms and operations (1):
    - sober : forall {S : Set α}, IsIrreducible S -> IsClosed S -> exists x, IsGenericPoint x S

中文:
类 拟醇
  参数: (α : 类型) [拓扑空间 α]
  公理与运算 (1 个):
    - sober : 对任意 {S : 集合 α}, 是不可约 S -> 是闭集 S -> 存在 x, IsGenericPoint x S
-/
class QuasiSober (α : Type*) [TopologicalSpace α] : Prop where
  sober : forall {S : Set α}, IsIrreducible S -> IsClosed S -> exists x, IsGenericPoint x S

/--
Definition of `IsIrreducible.genericPoint` / `IsIrreducible.genericPoint` 的定义

English:
definition IsIrreducible.genericPoint
  signature: [QuasiSober α] {S : Set α} (hS : IsIrreducible S)
  body: (QuasiSober.sober hS.closure isClosed_closure).choose

中文:
定义 是不可约.genericPoint
  签名: [拟醇 α] {S : 集合 α} (hS : 是不可约 S)
  定义体: (QuasiSober.sober hS.closure isClosed_closure).choose

Depends on / 依赖: QuasiSober, QuasiSober.sober, closure, hS.closure, isClosed_closure
-/
noncomputable def IsIrreducible.genericPoint [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    α :=
  (QuasiSober.sober hS.closure isClosed_closure).choose

/--
theorem `IsIrreducible.isGenericPoint_genericPoint_closure` / 定理 `IsIrreducible.isGenericPoint_genericPoint_closure`

English:
theorem IsIrreducible.isGenericPoint_genericPoint_closure
  proof: (QuasiSober.sober hS.closure isClosed_closure).choose_spec

中文:
定理 是不可约.isGenericPoint_genericPoint_closure
  证明: (QuasiSober.sober hS.closure isClosed_closure).choose_spec

Depends on / 依赖: QuasiSober, QuasiSober.sober, choose_spec, closure, hS.closure, isClosed_closure
-/
theorem IsIrreducible.isGenericPoint_genericPoint_closure
    [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    IsGenericPoint hS.genericPoint (closure S) :=
  (QuasiSober.sober hS.closure isClosed_closure).choose_spec

/--
theorem `IsIrreducible.isGenericPoint_genericPoint` / 定理 `IsIrreducible.isGenericPoint_genericPoint`

English:
theorem IsIrreducible.isGenericPoint_genericPoint
  statement: [QuasiSober α] {S : Set α}
  proof: by
  convert! hS.isGenericPoint_genericPoint_closure; exact hS'.closure_eq.symm

@[simp]

中文:
定理 是不可约.isGenericPoint_genericPoint
  结论: [拟醇 α] {S : 集合 α}
  证明: by
  convert! hS.isGenericPoint_genericPoint_closure; exact hS'.closure_eq.symm

@[simp]

Depends on / 依赖: closure_eq, closure_eq.symm, convert, hS.isGenericPoint_genericPoint_closure, isGenericPoint_genericPoint_closure
-/
theorem IsIrreducible.isGenericPoint_genericPoint [QuasiSober α] {S : Set α}
    (hS : IsIrreducible S) (hS' : IsClosed S) :
    IsGenericPoint hS.genericPoint S := by
  convert! hS.isGenericPoint_genericPoint_closure; exact hS'.closure_eq.symm

@[simp]
/--
theorem `IsIrreducible.genericPoint_closure_eq` / 定理 `IsIrreducible.genericPoint_closure_eq`

English:
theorem IsIrreducible.genericPoint_closure_eq
  given: [QuasiSober α] {S : Set α} (hS : IsIrreducible S)
  proof: hS.isGenericPoint_genericPoint_closure

中文:
定理 是不可约.genericPoint_closure_eq
  条件: [拟醇 α] {S : 集合 α} (hS : 是不可约 S)
  证明: hS.isGenericPoint_genericPoint_closure

Depends on / 依赖: hS.isGenericPoint_genericPoint_closure, isGenericPoint_genericPoint_closure
-/
theorem IsIrreducible.genericPoint_closure_eq [QuasiSober α] {S : Set α} (hS : IsIrreducible S) :
    closure ({hS.genericPoint} : Set α) = closure S :=
  hS.isGenericPoint_genericPoint_closure

/--
theorem `IsIrreducible.closure_genericPoint` / 定理 `IsIrreducible.closure_genericPoint`

English:
theorem IsIrreducible.closure_genericPoint
  statement: [QuasiSober α] {S : Set α}
  proof: hS.isGenericPoint_genericPoint_closure.trans hS'.closure_eq

中文:
定理 是不可约.closure_genericPoint
  结论: [拟醇 α] {S : 集合 α}
  证明: hS.isGenericPoint_genericPoint_closure.trans hS'.closure_eq

Depends on / 依赖: closure_eq, hS.isGenericPoint_genericPoint_closure.trans, isGenericPoint_genericPoint_closure
-/
theorem IsIrreducible.closure_genericPoint [QuasiSober α] {S : Set α}
    (hS : IsIrreducible S) (hS' : IsClosed S) :
    closure ({hS.genericPoint} : Set α) = S :=
  hS.isGenericPoint_genericPoint_closure.trans hS'.closure_eq

variable (α)

/--
Definition of `genericPoint` / `genericPoint` 的定义

English:
definition genericPoint
  signature: [QuasiSober α] [IrreducibleSpace α]
  body: (IrreducibleSpace.isIrreducible_univ α).genericPoint

中文:
定义 genericPoint
  签名: [拟醇 α] [不可约空间 α]
  定义体: (IrreducibleSpace.isIrreducible_univ α).genericPoint

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, genericPoint, isIrreducible_univ
-/
noncomputable def genericPoint [QuasiSober α] [IrreducibleSpace α] : α :=
  (IrreducibleSpace.isIrreducible_univ α).genericPoint

/--
theorem `genericPoint_spec` / 定理 `genericPoint_spec`

English:
theorem genericPoint_spec
  given: [QuasiSober α] [IrreducibleSpace α]
  proof: by
  simpa using! (IrreducibleSpace.isIrreducible_univ α).isGenericPoint_genericPoint_closure

@[simp]

中文:
定理 genericPoint_spec
  条件: [拟醇 α] [不可约空间 α]
  证明: by
  simpa using! (IrreducibleSpace.isIrreducible_univ α).isGenericPoint_genericPoint_closure

@[simp]

Depends on / 依赖: IrreducibleSpace, IrreducibleSpace.isIrreducible_univ, isGenericPoint_genericPoint_closure, isIrreducible_univ
-/
theorem genericPoint_spec [QuasiSober α] [IrreducibleSpace α] :
    IsGenericPoint (genericPoint α) univ := by
  simpa using! (IrreducibleSpace.isIrreducible_univ α).isGenericPoint_genericPoint_closure

@[simp]
/--
theorem `genericPoint_closure` / 定理 `genericPoint_closure`

English:
theorem genericPoint_closure
  given: [QuasiSober α] [IrreducibleSpace α]
  proof: genericPoint_spec α

中文:
定理 genericPoint_closure
  条件: [拟醇 α] [不可约空间 α]
  证明: genericPoint_spec α

Depends on / 依赖: genericPoint_spec
-/
theorem genericPoint_closure [QuasiSober α] [IrreducibleSpace α] :
    closure ({genericPoint α} : Set α) = univ :=
  genericPoint_spec α

variable {α}

/--
theorem `genericPoint_specializes` / 定理 `genericPoint_specializes`

English:
theorem genericPoint_specializes
  given: [QuasiSober α] [IrreducibleSpace α] (x : α)
  statement: genericPoint α ⤳ x
  proof: (IsIrreducible.isGenericPoint_genericPoint_closure _).specializes (by simp)

中文:
定理 genericPoint_specializes
  条件: [拟醇 α] [不可约空间 α] (x : α)
  结论: genericPoint α ⤳ x
  证明: (IsIrreducible.isGenericPoint_genericPoint_closure _).specializes (by simp)

Depends on / 依赖: IsIrreducible, IsIrreducible.isGenericPoint_genericPoint_closure, isGenericPoint_genericPoint_closure, specializes
-/
theorem genericPoint_specializes [QuasiSober α] [IrreducibleSpace α] (x : α) : genericPoint α ⤳ x :=
  (IsIrreducible.isGenericPoint_genericPoint_closure _).specializes (by simp)

attribute [local instance] specializationOrder

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `irreducibleSetEquivPoints` / `irreducibleSetEquivPoints` 的定义

English:
definition irreducibleSetEquivPoints
  signature: [QuasiSober α] [T0Space α]
  body: s.2.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := by
    refine TopologicalSpace.IrreducibleCloseds.ext ?_
    simp only [IsIrreducible.genericPoint_closure_eq, TopologicalSpace.IrreducibleCloseds.coe_mk,
      closure_eq_iff_is

中文:
定义 irreducibleSetEquivPoints
  签名: [拟醇 α] [T0空间 α]
  定义体: s.2.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := by
    refine TopologicalSpace.IrreducibleCloseds.ext ?_
    simp only [IsIrreducible.genericPoint_closure_eq, TopologicalSpace.IrreducibleCloseds.coe_mk,
      closure_eq_iff_is

Depends on / 依赖: genericPoint
-/
noncomputable def irreducibleSetEquivPoints [QuasiSober α] [T0Space α] :
    TopologicalSpace.IrreducibleCloseds α ≃o α where
  toFun s := s.2.genericPoint
  invFun x := ⟨closure ({x} : Set α), isIrreducible_singleton.closure, isClosed_closure⟩
  left_inv s := by
    refine TopologicalSpace.IrreducibleCloseds.ext ?_
    simp only [IsIrreducible.genericPoint_closure_eq, TopologicalSpace.IrreducibleCloseds.coe_mk,
      closure_eq_iff_isClosed.mpr s.3]
    rfl
  right_inv x := isIrreducible_singleton.closure.isGenericPoint_genericPoint_closure.eq
      (by rw [closure_closure]; exact isGenericPoint_closure)
  map_rel_iff' := by
    rintro ⟨s, hs, hs'⟩ ⟨t, ht, ht'⟩
    refine specializes_iff_closure_subset.trans ?_
    simp
    rfl

@[simp]
/--
lemma `coe_irreducibleEquivPoints_symm_apply` / 引理 `coe_irreducibleEquivPoints_symm_apply`

English:
lemma coe_irreducibleEquivPoints_symm_apply
  given: [QuasiSober α] [T0Space α] (x : α)
  proof: rfl

中文:
引理 coe_irreducibleEquivPoints_symm_apply
  条件: [拟醇 α] [T0空间 α] (x : α)
  证明: rfl
-/
lemma coe_irreducibleEquivPoints_symm_apply [QuasiSober α] [T0Space α] (x : α) :
    (irreducibleSetEquivPoints.symm x : Set α) = closure {x} := rfl

/--
lemma `Topology.IsClosedEmbedding.quasiSober` / 引理 `Topology.IsClosedEmbedding.quasiSober`

English:
lemma Topology.IsClosedEmbedding.quasiSober
  given: {f : α -> β} (hf : IsClosedEmbedding f) [QuasiSober β]
  proof: by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    obtain ⟨y, -, rfl⟩ := hx.mem
    use y
    apply image_injective.mpr hf.injective
    rw [← hx.def]; rw [← hf.closure_image_eq]; rw [image_singleton]

中文:
引理 拓扑.是闭嵌入.quasiSober
  条件: {f : α -> β} (hf : 是闭嵌入 f) [拟醇 β]
  证明: by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    obtain ⟨y, -, rfl⟩ := hx.mem
    use y
    apply image_injective.mpr hf.injective
    rw [← hx.def]; rw [← hf.closure_image_eq]; rw [image_singleton]

Depends on / 依赖: QuasiSober, QuasiSober.sober, closure_image_eq, continuous, continuousOn, hS.image, hf.closure_image_eq, hf.continuous.continuousOn, hf.injective, hf.isClosedMap, hx.def, hx.mem, image_injective, image_injective.mpr, image_singleton, injective, isClosedMap
-/
lemma Topology.IsClosedEmbedding.quasiSober {f : α -> β} (hf : IsClosedEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS'' (hf.isClosedMap _ hS')
    obtain ⟨y, -, rfl⟩ := hx.mem
    use y
    apply image_injective.mpr hf.injective
    rw [← hx.def]; rw [← hf.closure_image_eq]; rw [image_singleton]

/--
theorem `Topology.IsOpenEmbedding.quasiSober` / 定理 `Topology.IsOpenEmbedding.quasiSober`

English:
theorem Topology.IsOpenEmbedding.quasiSober
  given: {f : α -> β} (hf : IsOpenEmbedding f) [QuasiSober β]
  proof: by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    obtain ⟨T, hT, rfl⟩ := hf.isInducing.isClosed_iff.mp hS'
    rw [image_preimage_eq_inter_range] at hx hS''
    have hxT : x in T := by
      rw [← hT.closure_eq]
      e

中文:
定理 拓扑.是开嵌入.quasiSober
  条件: {f : α -> β} (hf : 是开嵌入 f) [拟醇 β]
  证明: by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    obtain ⟨T, hT, rfl⟩ := hf.isInducing.isClosed_iff.mp hS'
    rw [image_preimage_eq_inter_range] at hx hS''
    have hxT : x in T := by
      rw [← hT.closure_eq]
      e

Depends on / 依赖: Nonempty, Nonempty.mono, QuasiSober, QuasiSober.sober, closure, closure_eq, closure_eq_prei, closure_mono, continuous, continuousOn, hS.image, hT.closure_eq, hf.continuous.continuousOn, hf.isEmbedding.closure_eq_prei, hf.isInducing.isClosed_iff.mp, hf.isOpen_range, hx.mem, hx.mem_open_set_iff, image_preimage_eq_inter_range, inter_subset_left
-/
theorem Topology.IsOpenEmbedding.quasiSober {f : α -> β} (hf : IsOpenEmbedding f) [QuasiSober β] :
    QuasiSober α where
  sober hS hS' := by
    have hS'' := hS.image f hf.continuous.continuousOn
    obtain ⟨x, hx⟩ := QuasiSober.sober hS''.closure isClosed_closure
    obtain ⟨T, hT, rfl⟩ := hf.isInducing.isClosed_iff.mp hS'
    rw [image_preimage_eq_inter_range] at hx hS''
    have hxT : x in T := by
      rw [← hT.closure_eq]
      exact closure_mono inter_subset_left hx.mem
    obtain ⟨y, rfl⟩ : x in range f := by
      rw [hx.mem_open_set_iff hf.isOpen_range]
      refine Nonempty.mono ?_ hS''.1
      simpa using subset_closure
    use y
    change _ = _
    rw [hf.isEmbedding.closure_eq_preimage_closure_image]; rw [image_singleton]; rw [show _ = _ from hx]
    apply image_injective.mpr hf.injective
    ext z
    simp only [image_preimage_eq_inter_range, mem_inter_iff, and_congr_left_iff]
    exact fun hy => ⟨fun h => hT.closure_eq ▸ closure_mono inter_subset_left h,
      fun h => subset_closure ⟨h, hy⟩⟩

/--
lemma `TopologicalSpace.IsOpenCover.quasiSober_iff_forall` / 引理 `TopologicalSpace.IsOpenCover.quasiSober_iff_forall`

English:
lemma TopologicalSpace.IsOpenCover.quasiSober_iff_forall
  statement: {ι : Type*} {U : ι -> Opens α}
  proof: by
  refine ⟨fun h i => (U i).isOpenEmbedding'.quasiSober, fun hU' => (quasiSober_iff _).mpr ?_⟩
  · rintro t ⟨⟨x, hx⟩, h⟩ h'
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have H : IsIrreducible ((↑) ⁻¹' t : Set (U i)) :=
      ⟨⟨⟨x, hi⟩, hx⟩, h.preimage (U i).isOpenEmbedding'⟩
    use H.genericPoint
  

中文:
引理 拓扑空间.IsOpenCover.quasiSober_iff_对任意
  结论: {ι : 类型} {U : ι -> Opens α}
  证明: by
  refine ⟨fun h i => (U i).isOpenEmbedding'.quasiSober, fun hU' => (quasiSober_iff _).mpr ?_⟩
  · rintro t ⟨⟨x, hx⟩, h⟩ h'
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have H : IsIrreducible ((↑) ⁻¹' t : Set (U i)) :=
      ⟨⟨⟨x, hi⟩, hx⟩, h.preimage (U i).isOpenEmbedding'⟩
    use H.genericPoint
  

Depends on / 依赖: H.genericPoint, H.isGenericPoint_genericPoint_closure.mem, IsIrreducible, closure_eq, closure_image_closure, closure_preimage_subset, closure_subset_iff, continuou, continuous_subtype_val, continuous_subtype_val.closure_preimage_subset, exists_mem, genericPoint, h.preimage, hU.exists_mem, image_singleton, isGenericPoint_genericPoint_closure, isOpenEmbedding, le_antisymm, preimage, quasiSober
-/
lemma TopologicalSpace.IsOpenCover.quasiSober_iff_forall {ι : Type*} {U : ι -> Opens α}
    (hU : TopologicalSpace.IsOpenCover U) : QuasiSober α ↔ forall i, QuasiSober (U i) := by
  refine ⟨fun h i => (U i).isOpenEmbedding'.quasiSober, fun hU' => (quasiSober_iff _).mpr ?_⟩
  · rintro t ⟨⟨x, hx⟩, h⟩ h'
    obtain ⟨i, hi⟩ := hU.exists_mem x
    have H : IsIrreducible ((↑) ⁻¹' t : Set (U i)) :=
      ⟨⟨⟨x, hi⟩, hx⟩, h.preimage (U i).isOpenEmbedding'⟩
    use H.genericPoint
    apply le_antisymm
    · simpa [h'.closure_subset_iff, h'.closure_eq] using!
        continuous_subtype_val.closure_preimage_subset _ H.isGenericPoint_genericPoint_closure.mem
    rw [← image_singleton]; rw [← closure_image_closure continuous_subtype_val]; rw [H.isGenericPoint_genericPoint_closure.def]
    refine (subset_closure_inter_of_isPreirreducible_of_isOpen h (U i).isOpen ⟨x, ⟨hx, hi⟩⟩).trans
      (closure_mono ?_)
    simpa only [inter_comm t, ← Subtype.image_preimage_coe] using! Set.image_mono subset_closure

/--
lemma `TopologicalSpace.IsOpenCover.quasiSober` / 引理 `TopologicalSpace.IsOpenCover.quasiSober`

English:
lemma TopologicalSpace.IsOpenCover.quasiSober
  statement: {ι : Type*} {U : ι -> Opens α}
  proof: hU.quasiSober_iff_forall.mpr ‹_›

中文:
引理 拓扑空间.IsOpenCover.quasiSober
  结论: {ι : 类型} {U : ι -> Opens α}
  证明: hU.quasiSober_iff_forall.mpr ‹_›

Depends on / 依赖: hU.quasiSober_iff_forall.mpr, quasiSober_iff_forall
-/
lemma TopologicalSpace.IsOpenCover.quasiSober {ι : Type*} {U : ι -> Opens α}
    (hU : TopologicalSpace.IsOpenCover U) [forall i, QuasiSober (U i)] : QuasiSober α :=
  hU.quasiSober_iff_forall.mpr ‹_›

/--
theorem `quasiSober_of_open_cover` / 定理 `quasiSober_of_open_cover`

English:
theorem quasiSober_of_open_cover
  statement: (S : Set (Set α)) (hS : forall s : S, IsOpen (s : Set α))
  proof: TopologicalSpace.IsOpenCover.quasiSober (U := fun s : S => ⟨s, hS s⟩) by
    simpa [TopologicalSpace.IsOpenCover, ← SetLike.coe_set_eq, sUnion_eq_iUnion] using hS'

中文:
定理 quasiSober_of_open_cover
  结论: (S : 集合 (集合 α)) (hS : 对任意 s : S, 是开集 (s : 集合 α))
  证明: TopologicalSpace.IsOpenCover.quasiSober (U := fun s : S => ⟨s, hS s⟩) by
    simpa [TopologicalSpace.IsOpenCover, ← SetLike.coe_set_eq, sUnion_eq_iUnion] using hS'

Depends on / 依赖: IsOpenCover, SetLike, SetLike.coe_set_eq, TopologicalSpace, TopologicalSpace.IsOpenCover, TopologicalSpace.IsOpenCover.quasiSober, coe_set_eq, quasiSober, sUnion_eq_iUnion
-/
theorem quasiSober_of_open_cover (S : Set (Set α)) (hS : forall s : S, IsOpen (s : Set α))
    [forall s : S, QuasiSober s] (hS' : ⋃₀ S = ⊤) : QuasiSober α :=
TopologicalSpace.IsOpenCover.quasiSober (U := fun s : S => ⟨s, hS s⟩) by
    simpa [TopologicalSpace.IsOpenCover, ← SetLike.coe_set_eq, sUnion_eq_iUnion] using hS'

/--
Any R1 space is a quasi-sober space because any irreducible set is
contained in the closure of a singleton.
-/
-- see note [lower instance priority]
instance (priority := 100) R1Space.quasiSober [R1Space α] : QuasiSober α where
  sober h hs := by
    obtain ⟨x, hx⟩ := h.nonempty
    use x
    apply subset_antisymm
    · rw [← hs.closure_eq]
      exact closure_mono (singleton_subset_iff.mpr hx)
    · exact isPreirreducible_iff_forall_mem_subset_closure_singleton.mp h.isPreirreducible x hx

open scoped Set.Notation in
/--
lemma `QuasiSober.of_subset` / 引理 `QuasiSober.of_subset`

English:
lemma QuasiSober.of_subset
  given: {V W : Set α} [QuasiSober W] (hV : IsClosed (W ↓inter V)) (h : V subseteq W)
  proof: Topology.IsClosedEmbedding.quasiSober .inclusion h hV

中文:
引理 拟醇.of_subset
  条件: {V W : 集合 α} [拟醇 W] (hV : 是闭集 (W ↓inter V)) (h : V subseteq W)
  证明: Topology.IsClosedEmbedding.quasiSober .inclusion h hV

Depends on / 依赖: IsClosedEmbedding, Topology, Topology.IsClosedEmbedding.quasiSober, inclusion, quasiSober
-/
lemma QuasiSober.of_subset {V W : Set α} [QuasiSober W] (hV : IsClosed (W ↓inter V)) (h : V subseteq W) :
QuasiSober V := Topology.IsClosedEmbedding.quasiSober .inclusion h hV

/--
lemma `QuasiSober.inter_of_isClosed_of_quasiSober_left` / 引理 `QuasiSober.inter_of_isClosed_of_quasiSober_left`

English:
lemma QuasiSober.inter_of_isClosed_of_quasiSober_left
  statement: {V : Set α} (W : Set α) [QuasiSober W]
  proof: by
  refine QuasiSober.of_subset ?_ (Set.inter_subset_left : W inter V subseteq W)
  rw [Subtype.preimage_coe_self_inter W V]
  exact IsClosed.preimage_val hV

中文:
引理 拟醇.inter_of_isClosed_of_quasiSober_left
  结论: {V : 集合 α} (W : 集合 α) [拟醇 W]
  证明: by
  refine QuasiSober.of_subset ?_ (Set.inter_subset_left : W inter V subseteq W)
  rw [Subtype.preimage_coe_self_inter W V]
  exact IsClosed.preimage_val hV

Depends on / 依赖: IsClosed, IsClosed.preimage_val, QuasiSober, QuasiSober.of_subset, Set.inter_subset_left, Subtype, Subtype.preimage_coe_self_inter, inter_subset_left, of_subset, preimage_coe_self_inter, preimage_val, subseteq
-/
lemma QuasiSober.inter_of_isClosed_of_quasiSober_left {V : Set α} (W : Set α) [QuasiSober W]
    (hV : IsClosed V) : QuasiSober (W inter V : Set α) := by
  refine QuasiSober.of_subset ?_ (Set.inter_subset_left : W inter V subseteq W)
  rw [Subtype.preimage_coe_self_inter W V]
  exact IsClosed.preimage_val hV

/--
lemma `QuasiSober.inter_of_isClosed_of_quasiSober_right` / 引理 `QuasiSober.inter_of_isClosed_of_quasiSober_right`

English:
lemma QuasiSober.inter_of_isClosed_of_quasiSober_right
  statement: {V : Set α} (W : Set α) [QuasiSober V]
  proof: by
  rw [inter_comm]
  exact .inter_of_isClosed_of_quasiSober_left V hW

中文:
引理 拟醇.inter_of_isClosed_of_quasiSober_right
  结论: {V : 集合 α} (W : 集合 α) [拟醇 V]
  证明: by
  rw [inter_comm]
  exact .inter_of_isClosed_of_quasiSober_left V hW

Depends on / 依赖: inter_comm, inter_of_isClosed_of_quasiSober_left
-/
lemma QuasiSober.inter_of_isClosed_of_quasiSober_right {V : Set α} (W : Set α) [QuasiSober V]
    (hW : IsClosed W) : QuasiSober (W inter V : Set α) := by
  rw [inter_comm]
  exact .inter_of_isClosed_of_quasiSober_left V hW

end Sober

section genericPoints

variable (α) in
/--
Definition of `genericPoints` / `genericPoints` 的定义

English:
definition genericPoints
  signature: : Set α
  body: { x | closure {x} in irreducibleComponents α }

中文:
定义 genericPoints
  签名: : 集合 α
  定义体: { x | closure {x} in irreducibleComponents α }

Depends on / 依赖: closure, irreducibleComponents
-/
def genericPoints : Set α := { x | closure {x} in irreducibleComponents α }

namespace genericPoints

/--
Definition of `component` / `component` 的定义

English:
definition component
  signature: (x : genericPoints α)
  body: ⟨closure {x.1}, x.2⟩

中文:
定义 component
  签名: (x : genericPoints α)
  定义体: ⟨closure {x.1}, x.2⟩

Depends on / 依赖: closure
-/
def component (x : genericPoints α) : irreducibleComponents α :=
  ⟨closure {x.1}, x.2⟩

/--
lemma `isGenericPoint` / 引理 `isGenericPoint`

English:
lemma isGenericPoint
  given: (x : genericPoints α)
  statement: IsGenericPoint x.1 (component x).1
  proof: rfl

中文:
引理 isGenericPoint
  条件: (x : genericPoints α)
  结论: IsGenericPoint x.1 (component x).1
  证明: rfl
-/
lemma isGenericPoint (x : genericPoints α) : IsGenericPoint x.1 (component x).1 := rfl

/--
lemma `component_injective` / 引理 `component_injective`

English:
lemma component_injective
  given: [T0Space α]
  statement: Function.Injective (component (α := α))
  proof: fun x y e => Subtype.ext ((isGenericPoint x).eq (e ▸ isGenericPoint y))

中文:
引理 component_injective
  条件: [T0空间 α]
  结论: 函数.单射 (component (α := α))
  证明: fun x y e => Subtype.ext ((isGenericPoint x).eq (e ▸ isGenericPoint y))
-/
lemma component_injective [T0Space α] : Function.Injective (component (α := α)) :=
  fun x y e => Subtype.ext ((isGenericPoint x).eq (e ▸ isGenericPoint y))

/-- The generic point of an irreducible component. -/
noncomputable
/--
Definition of `ofComponent` / `ofComponent` 的定义

English:
definition ofComponent
  signature: [QuasiSober α] (x : irreducibleComponents α)
  body: ⟨x.2.1.genericPoint, show _ in irreducibleComponents α from
    (x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)).symm ▸ x.2⟩

中文:
定义 ofComponent
  签名: [拟醇 α] (x : irreducibleComponents α)
  定义体: ⟨x.2.1.genericPoint, show _ in irreducibleComponents α from
    (x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)).symm ▸ x.2⟩

Depends on / 依赖: genericPoint, irreducibleComponents, isClosed_of_mem_irreducibleComponents, isGenericPoint_genericPoint
-/
def ofComponent [QuasiSober α] (x : irreducibleComponents α) : genericPoints α :=
  ⟨x.2.1.genericPoint, show _ in irreducibleComponents α from
    (x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)).symm ▸ x.2⟩

/--
lemma `isGenericPoint_ofComponent` / 引理 `isGenericPoint_ofComponent`

English:
lemma isGenericPoint_ofComponent
  given: [QuasiSober α] (x : irreducibleComponents α)
  proof: x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)

@[simp]

中文:
引理 isGenericPoint_ofComponent
  条件: [拟醇 α] (x : irreducibleComponents α)
  证明: x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)

@[simp]

Depends on / 依赖: isClosed_of_mem_irreducibleComponents, isGenericPoint_genericPoint
-/
lemma isGenericPoint_ofComponent [QuasiSober α] (x : irreducibleComponents α) :
    IsGenericPoint (ofComponent x).1 x :=
    x.2.1.isGenericPoint_genericPoint (isClosed_of_mem_irreducibleComponents x.1 x.2)

@[simp]
/--
lemma `component_ofComponent` / 引理 `component_ofComponent`

English:
lemma component_ofComponent
  given: [QuasiSober α] (x : irreducibleComponents α)
  proof: Subtype.ext (isGenericPoint_ofComponent x)

@[simp]

中文:
引理 component_ofComponent
  条件: [拟醇 α] (x : irreducibleComponents α)
  证明: Subtype.ext (isGenericPoint_ofComponent x)

@[simp]

Depends on / 依赖: Subtype, Subtype.ext, isGenericPoint_ofComponent
-/
lemma component_ofComponent [QuasiSober α] (x : irreducibleComponents α) :
    component (ofComponent x) = x :=
  Subtype.ext (isGenericPoint_ofComponent x)

@[simp]
/--
lemma `ofComponent_component` / 引理 `ofComponent_component`

English:
lemma ofComponent_component
  given: [T0Space α] [QuasiSober α] (x : genericPoints α)
  proof: component_injective (component_ofComponent _)

中文:
引理 ofComponent_component
  条件: [T0空间 α] [拟醇 α] (x : genericPoints α)
  证明: component_injective (component_ofComponent _)

Depends on / 依赖: component_injective, component_ofComponent
-/
lemma ofComponent_component [T0Space α] [QuasiSober α] (x : genericPoints α) :
    ofComponent (component x) = x :=
  component_injective (component_ofComponent _)

/--
lemma `component_surjective` / 引理 `component_surjective`

English:
lemma component_surjective
  given: [QuasiSober α]
  statement: Function.Surjective (component (α := α))
  proof: Function.HasRightInverse.surjective ⟨ofComponent, component_ofComponent⟩

中文:
引理 component_surjective
  条件: [拟醇 α]
  结论: 函数.满射 (component (α := α))
  证明: Function.HasRightInverse.surjective ⟨ofComponent, component_ofComponent⟩
-/
lemma component_surjective [QuasiSober α] : Function.Surjective (component (α := α)) :=
  Function.HasRightInverse.surjective ⟨ofComponent, component_ofComponent⟩

/--
lemma `finite` / 引理 `finite`

English:
lemma finite
  given: [T0Space α] (h : (irreducibleComponents α).Finite)
  statement: (genericPoints α).Finite
  proof: @Finite.of_injective _ _ h _ component_injective

中文:
引理 finite
  条件: [T0空间 α] (h : (irreducibleComponents α).有限)
  结论: (genericPoints α).有限
  证明: @Finite.of_injective _ _ h _ component_injective

Depends on / 依赖: Finite, Finite.of_injective, component_injective, of_injective
-/
lemma finite [T0Space α] (h : (irreducibleComponents α).Finite) : (genericPoints α).Finite :=
  @Finite.of_injective _ _ h _ component_injective

/-- In a sober space, the generic points corresponds bijectively to irreducible components -/
@[simps]
noncomputable
/--
Definition of `equiv` / `equiv` 的定义

English:
definition equiv
  signature: [T0Space α] [QuasiSober α]
  body: ⟨component, ofComponent, ofComponent_component, component_ofComponent⟩

中文:
定义 equiv
  签名: [T0空间 α] [拟醇 α]
  定义体: ⟨component, ofComponent, ofComponent_component, component_ofComponent⟩

Depends on / 依赖: component, component_ofComponent, ofComponent, ofComponent_component
-/
def equiv [T0Space α] [QuasiSober α] : genericPoints α ≃ irreducibleComponents α :=
  ⟨component, ofComponent, ofComponent_component, component_ofComponent⟩

/--
lemma `closure` / 引理 `closure`

English:
lemma closure
  given: [QuasiSober α]
  statement: closure (genericPoints α) = Set.univ
  proof: by
  refine Set.eq_univ_iff_forall.mpr fun x => Set.subset_def.mp ?_ x mem_irreducibleComponent
  refine (isGenericPoint_ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).symm.trans_subset (closure_mono ?_)
  exact Set.singleton_subset_iff.mpr (ofComponent _).2

中文:
引理 closure
  条件: [拟醇 α]
  结论: closure (genericPoints α) = 集合.univ
  证明: by
  refine Set.eq_univ_iff_forall.mpr fun x => Set.subset_def.mp ?_ x mem_irreducibleComponent
  refine (isGenericPoint_ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).symm.trans_subset (closure_mono ?_)
  exact Set.singleton_subset_iff.mpr (ofComponent _).2

Depends on / 依赖: Set.eq_univ_iff_forall.mpr, Set.singleton_subset_iff.mpr, Set.subset_def.mp, closure_mono, eq_univ_iff_forall, irreducibleComponent_mem_irreducibleComponents, isGenericPoint_ofComponent, mem_irreducibleComponent, ofComponent, singleton_subset_iff, subset_def, symm.trans_subset, trans_subset
-/
lemma closure [QuasiSober α] : closure (genericPoints α) = Set.univ := by
  refine Set.eq_univ_iff_forall.mpr fun x => Set.subset_def.mp ?_ x mem_irreducibleComponent
  refine (isGenericPoint_ofComponent
    ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩).symm.trans_subset (closure_mono ?_)
  exact Set.singleton_subset_iff.mpr (ofComponent _).2

end genericPoints

/--
lemma `genericPoints_eq_singleton` / 引理 `genericPoints_eq_singleton`

English:
lemma genericPoints_eq_singleton
  given: [QuasiSober α] [IrreducibleSpace α] [T0Space α]
  proof: by
  ext x
  rw [genericPoints]; rw [irreducibleComponents_eq_singleton]
  exact ⟨((genericPoint_spec α).eq · |>.symm), (· ▸ genericPoint_spec α)⟩

中文:
引理 genericPoints_eq_singleton
  条件: [拟醇 α] [不可约空间 α] [T0空间 α]
  证明: by
  ext x
  rw [genericPoints]; rw [irreducibleComponents_eq_singleton]
  exact ⟨((genericPoint_spec α).eq · |>.symm), (· ▸ genericPoint_spec α)⟩

Depends on / 依赖: genericPoint_spec, genericPoints, irreducibleComponents_eq_singleton
-/
lemma genericPoints_eq_singleton [QuasiSober α] [IrreducibleSpace α] [T0Space α] :
    genericPoints α = {genericPoint α} := by
  ext x
  rw [genericPoints]; rw [irreducibleComponents_eq_singleton]
  exact ⟨((genericPoint_spec α).eq · |>.symm), (· ▸ genericPoint_spec α)⟩

end genericPoints
