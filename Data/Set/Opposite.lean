/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Data.Opposite
public import Mathlib.Data.Set.Operations

/-!
# The opposite of a set

The opposite of a set `s` is simply the set obtained by taking the opposite of each member of `s`.
-/

@[expose] public section

variable {α : Type*}

open Opposite

namespace Set

/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (s : Set α)
  body: unop ⁻¹' s

中文:
定义 op
  签名: (s : 集合 α)
  定义体: unop ⁻¹' s
-/
protected def op (s : Set α) : Set αᵒᵖ :=
  unop ⁻¹' s

/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: (s : Set αᵒᵖ)
  body: op ⁻¹' s

@[simp]

中文:
定义 unop
  签名: (s : 集合 αᵒᵖ)
  定义体: op ⁻¹' s

@[simp]
-/
protected def unop (s : Set αᵒᵖ) : Set α :=
  op ⁻¹' s

@[simp]
/--
theorem `mem_op` / 定理 `mem_op`

English:
theorem mem_op
  given: {s : Set α} {a : αᵒᵖ}
  statement: a in s.op ↔ unop a in s
  proof: Iff.rfl

@[simp 1100]

中文:
定理 mem_op
  条件: {s : 集合 α} {a : αᵒᵖ}
  结论: a in s.op ↔ unop a in s
  证明: Iff.rfl

@[simp 1100]

Depends on / 依赖: Iff.rfl, X.carrier.str, carrier
-/
theorem mem_op {s : Set α} {a : αᵒᵖ} : a in s.op ↔ unop a in s :=
  Iff.rfl

@[simp 1100]
/--
theorem `op_mem_op` / 定理 `op_mem_op`

English:
theorem op_mem_op
  given: {s : Set α} {a : α}
  statement: op a in s.op ↔ a in s
  proof: by rfl

@[simp]

中文:
定理 op_mem_op
  条件: {s : 集合 α} {a : α}
  结论: op a in s.op ↔ a in s
  证明: by rfl

@[simp]
-/
theorem op_mem_op {s : Set α} {a : α} : op a in s.op ↔ a in s := by rfl

@[simp]
/--
theorem `mem_unop` / 定理 `mem_unop`

English:
theorem mem_unop
  given: {s : Set αᵒᵖ} {a : α}
  statement: a in s.unop ↔ op a in s
  proof: Iff.rfl

@[simp 1100]

中文:
定理 mem_unop
  条件: {s : 集合 αᵒᵖ} {a : α}
  结论: a in s.unop ↔ op a in s
  证明: Iff.rfl

@[simp 1100]

Depends on / 依赖: Iff.rfl
-/
theorem mem_unop {s : Set αᵒᵖ} {a : α} : a in s.unop ↔ op a in s :=
  Iff.rfl

@[simp 1100]
/--
theorem `unop_mem_unop` / 定理 `unop_mem_unop`

English:
theorem unop_mem_unop
  given: {s : Set αᵒᵖ} {a : αᵒᵖ}
  statement: unop a in s.unop ↔ a in s
  proof: by rfl

@[simp]

中文:
定理 unop_mem_unop
  条件: {s : 集合 αᵒᵖ} {a : αᵒᵖ}
  结论: unop a in s.unop ↔ a in s
  证明: by rfl

@[simp]

Depends on / 依赖: comp_id, whiskerRight_id
-/
theorem unop_mem_unop {s : Set αᵒᵖ} {a : αᵒᵖ} : unop a in s.unop ↔ a in s := by rfl

@[simp]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (s : Set α)
  statement: s.op.unop = s
  proof: rfl

@[simp]

中文:
定理 op_unop
  条件: (s : 集合 α)
  结论: s.op.unop = s
  证明: rfl

@[simp]
-/
theorem op_unop (s : Set α) : s.op.unop = s := rfl

@[simp]
/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (s : Set αᵒᵖ)
  statement: s.unop.op = s
  proof: rfl

中文:
定理 unop_op
  条件: (s : 集合 αᵒᵖ)
  结论: s.unop.op = s
  证明: rfl
-/
theorem unop_op (s : Set αᵒᵖ) : s.unop.op = s := rfl

/-- The members of the opposite of a set are in bijection with the members of the set itself. -/
@[simps]
/--
Definition of `opEquiv_self` / `opEquiv_self` 的定义

English:
definition opEquiv_self
  signature: (s : Set α)
  body: ⟨fun x => ⟨unop x, x.2⟩, fun x => ⟨op x, x.2⟩, fun _ => rfl, fun _ => rfl⟩

中文:
定义 opEquiv_self
  签名: (s : 集合 α)
  定义体: ⟨fun x => ⟨unop x, x.2⟩, fun x => ⟨op x, x.2⟩, fun _ => rfl, fun _ => rfl⟩
-/
def opEquiv_self (s : Set α) : s.op ≃ s :=
  ⟨fun x => ⟨unop x, x.2⟩, fun x => ⟨op x, x.2⟩, fun _ => rfl, fun _ => rfl⟩

/-- Taking opposites as an equivalence of powersets. -/
@[simps]
/--
Definition of `opEquiv` / `opEquiv` 的定义

English:
definition opEquiv
  signature: : Set α ≃ Set αᵒᵖ
  body: ⟨Set.op, Set.unop, op_unop, unop_op⟩

@[simp]

中文:
定义 opEquiv
  签名: : 集合 α ≃ 集合 αᵒᵖ
  定义体: ⟨Set.op, Set.unop, op_unop, unop_op⟩

@[simp]

Depends on / 依赖: Set.op, Set.unop, op_unop, unop_op
-/
def opEquiv : Set α ≃ Set αᵒᵖ :=
  ⟨Set.op, Set.unop, op_unop, unop_op⟩

@[simp]
/--
theorem `singleton_op` / 定理 `singleton_op`

English:
theorem singleton_op
  given: (x : α)
  statement: ({x} : Set α).op = {op x}
  proof: by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

@[simp]

中文:
定理 singleton_op
  条件: (x : α)
  结论: ({x} : 集合 α).op = {op x}
  证明: by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

@[simp]

Depends on / 依赖: op_injective, unop_injective
-/
theorem singleton_op (x : α) : ({x} : Set α).op = {op x} := by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

@[simp]
/--
theorem `singleton_unop` / 定理 `singleton_unop`

English:
theorem singleton_unop
  given: (x : αᵒᵖ)
  statement: ({x} : Set αᵒᵖ).unop = {unop x}
  proof: by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]

中文:
定理 singleton_unop
  条件: (x : αᵒᵖ)
  结论: ({x} : 集合 αᵒᵖ).unop = {unop x}
  证明: by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]

Depends on / 依赖: op_injective, unop_injective
-/
theorem singleton_unop (x : αᵒᵖ) : ({x} : Set αᵒᵖ).unop = {unop x} := by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]
/--
theorem `singleton_op_unop` / 定理 `singleton_op_unop`

English:
theorem singleton_op_unop
  given: (x : α)
  statement: ({op x} : Set αᵒᵖ).unop = {x}
  proof: by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]

中文:
定理 singleton_op_unop
  条件: (x : α)
  结论: ({op x} : 集合 αᵒᵖ).unop = {x}
  证明: by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]

Depends on / 依赖: op_injective, unop_injective
-/
theorem singleton_op_unop (x : α) : ({op x} : Set αᵒᵖ).unop = {x} := by
  ext
  constructor
  · apply op_injective
  · apply unop_injective

@[simp 1100]
/--
theorem `singleton_unop_op` / 定理 `singleton_unop_op`

English:
theorem singleton_unop_op
  given: (x : αᵒᵖ)
  statement: ({unop x} : Set α).op = {x}
  proof: by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

中文:
定理 singleton_unop_op
  条件: (x : αᵒᵖ)
  结论: ({unop x} : 集合 α).op = {x}
  证明: by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

Depends on / 依赖: op_injective, unop_injective
-/
theorem singleton_unop_op (x : αᵒᵖ) : ({unop x} : Set α).op = {x} := by
  ext
  constructor
  · apply unop_injective
  · apply op_injective

end Set
