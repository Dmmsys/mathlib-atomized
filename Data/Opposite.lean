/-
Copyright (c) 2018 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Reid Barton, Simon Hudon, Kenny Lau
-/
module

public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Small.Defs

/-!
# Opposites

In this file we define a structure `Opposite α` containing a single field of type `α` and
two bijections `op : α → αᵒᵖ` and `unop : αᵒᵖ → α`. If `α` is a category, then `αᵒᵖ` is the
opposite category, with all arrows reversed.

-/

@[expose] public section


universe v u

-- morphism levels before object levels. See note [category theory universes].
variable (α : Sort u)

/--
Definition of `Opposite` / `Opposite` 的定义

English:
structure Opposite
  parameters: where
  axioms and operations (2):
    - op : :
    - unop : α

中文:
结构 Opposite
  参数: where
  公理与运算 (2 个):
    - op : :
    - unop : α
-/
structure Opposite where
  /-- The canonical map `α → αᵒᵖ`. -/
  op ::
  /-- The canonical map `αᵒᵖ → α`. -/
  unop : α

attribute [pp_nodot] Opposite.unop

/-- Make sure that `Opposite.op a` is pretty-printed as `op a` instead of `{ unop := a }` or
`⟨a⟩`. -/
@[app_unexpander Opposite.op]
protected meta def Opposite.unexpander_op : Lean.PrettyPrinter.Unexpander
  | s => pure s

@[inherit_doc]
notation:max -- Use a high right binding power (like that of postfix ⁻¹) so that, for example,
-- `Presheaf Cᵒᵖ` parses as `Presheaf (Cᵒᵖ)` and not `(Presheaf C)ᵒᵖ`.
α "ᵒᵖ" => Opposite α

namespace Opposite

variable {α}

/--
theorem `op_injective` / 定理 `op_injective`

English:
theorem op_injective
  statement: Function.Injective (op : α -> αᵒᵖ)
  proof: fun _ _ => congr_arg Opposite.unop

中文:
定理 op_injective
  结论: Function.Injective (op : α -> αᵒᵖ)
  证明: fun _ _ => congr_arg Opposite.unop

Depends on / 依赖: Opposite, Opposite.unop, congr_arg
-/
theorem op_injective : Function.Injective (op : α -> αᵒᵖ) := fun _ _ => congr_arg Opposite.unop

/--
theorem `unop_injective` / 定理 `unop_injective`

English:
theorem unop_injective
  statement: Function.Injective (unop : αᵒᵖ -> α)
  proof: fun _ _ h => congrArg op h

@[simp]

中文:
定理 unop_injective
  结论: Function.Injective (unop : αᵒᵖ -> α)
  证明: fun _ _ h => congrArg op h

@[simp]
-/
theorem unop_injective : Function.Injective (unop : αᵒᵖ -> α) := fun _ _ h => congrArg op h

@[simp]
/--
theorem `op_unop` / 定理 `op_unop`

English:
theorem op_unop
  given: (x : αᵒᵖ)
  statement: op (unop x) = x
  proof: rfl

中文:
定理 op_unop
  条件: (x : αᵒᵖ)
  结论: op (unop x) = x
  证明: rfl
-/
theorem op_unop (x : αᵒᵖ) : op (unop x) = x :=
  rfl

/--
theorem `unop_op` / 定理 `unop_op`

English:
theorem unop_op
  given: (x : α)
  statement: unop (op x) = x
  proof: rfl

中文:
定理 unop_op
  条件: (x : α)
  结论: unop (op x) = x
  证明: rfl
-/
theorem unop_op (x : α) : unop (op x) = x :=
  rfl

-- We could prove these by `Iff.rfl`, but that would make these eligible for `dsimp`. That would be
-- a bad idea because `Opposite` is irreducible.
/--
theorem `op_inj_iff` / 定理 `op_inj_iff`

English:
theorem op_inj_iff
  given: (x y : α)
  statement: op x = op y ↔ x = y
  proof: op_injective.eq_iff

@[simp]

中文:
定理 op_inj_iff
  条件: (x y : α)
  结论: op x = op y ↔ x = y
  证明: op_injective.eq_iff

@[simp]

Depends on / 依赖: eq_iff, op_injective, op_injective.eq_iff
-/
theorem op_inj_iff (x y : α) : op x = op y ↔ x = y :=
  op_injective.eq_iff

@[simp]
/--
theorem `unop_inj_iff` / 定理 `unop_inj_iff`

English:
theorem unop_inj_iff
  given: (x y : αᵒᵖ)
  statement: unop x = unop y ↔ x = y
  proof: unop_injective.eq_iff

中文:
定理 unop_inj_iff
  条件: (x y : αᵒᵖ)
  结论: unop x = unop y ↔ x = y
  证明: unop_injective.eq_iff

Depends on / 依赖: eq_iff, unop_injective, unop_injective.eq_iff
-/
theorem unop_inj_iff (x y : αᵒᵖ) : unop x = unop y ↔ x = y :=
  unop_injective.eq_iff

/--
Definition of `equivToOpposite` / `equivToOpposite` 的定义

English:
definition equivToOpposite
  signature: : α ≃ αᵒᵖ where
  body: op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop

中文:
定义 equivToOpposite
  签名: : α ≃ αᵒᵖ where
  定义体: op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop
-/
def equivToOpposite : α ≃ αᵒᵖ where
  toFun := op
  invFun := unop
  left_inv := unop_op
  right_inv := op_unop

/--
theorem `op_surjective` / 定理 `op_surjective`

English:
theorem op_surjective
  statement: Function.Surjective (op : α -> αᵒᵖ)
  proof: equivToOpposite.surjective

中文:
定理 op_surjective
  结论: Function.Surjective (op : α -> αᵒᵖ)
  证明: equivToOpposite.surjective

Depends on / 依赖: equivToOpposite, equivToOpposite.surjective, surjective
-/
theorem op_surjective : Function.Surjective (op : α -> αᵒᵖ) := equivToOpposite.surjective

/--
theorem `unop_surjective` / 定理 `unop_surjective`

English:
theorem unop_surjective
  statement: Function.Surjective (unop : αᵒᵖ -> α)
  proof: equivToOpposite.symm.surjective

@[simp]

中文:
定理 unop_surjective
  结论: Function.Surjective (unop : αᵒᵖ -> α)
  证明: equivToOpposite.symm.surjective

@[simp]

Depends on / 依赖: equivToOpposite, equivToOpposite.symm.surjective, surjective
-/
theorem unop_surjective : Function.Surjective (unop : αᵒᵖ -> α) := equivToOpposite.symm.surjective

@[simp]
/--
theorem `equivToOpposite_coe` / 定理 `equivToOpposite_coe`

English:
theorem equivToOpposite_coe
  statement: (equivToOpposite : α -> αᵒᵖ) = op
  proof: rfl

@[simp]

中文:
定理 equivToOpposite_coe
  结论: (equivToOpposite : α -> αᵒᵖ) = op
  证明: rfl

@[simp]
-/
theorem equivToOpposite_coe : (equivToOpposite : α -> αᵒᵖ) = op :=
  rfl

@[simp]
/--
theorem `equivToOpposite_symm_coe` / 定理 `equivToOpposite_symm_coe`

English:
theorem equivToOpposite_symm_coe
  statement: (equivToOpposite.symm : αᵒᵖ -> α) = unop
  proof: rfl

中文:
定理 equivToOpposite_symm_coe
  结论: (equivToOpposite.symm : αᵒᵖ -> α) = unop
  证明: rfl
-/
theorem equivToOpposite_symm_coe : (equivToOpposite.symm : αᵒᵖ -> α) = unop :=
  rfl

/--
theorem `op_eq_iff_eq_unop` / 定理 `op_eq_iff_eq_unop`

English:
theorem op_eq_iff_eq_unop
  given: {x : α} {y}
  statement: op x = y ↔ x = unop y
  proof: equivToOpposite.eq_symm_apply.symm

中文:
定理 op_eq_iff_eq_unop
  条件: {x : α} {y}
  结论: op x = y ↔ x = unop y
  证明: equivToOpposite.eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, equivToOpposite, equivToOpposite.eq_symm_apply.symm
-/
theorem op_eq_iff_eq_unop {x : α} {y} : op x = y ↔ x = unop y :=
  equivToOpposite.eq_symm_apply.symm

/--
theorem `unop_eq_iff_eq_op` / 定理 `unop_eq_iff_eq_op`

English:
theorem unop_eq_iff_eq_op
  given: {x} {y : α}
  statement: unop x = y ↔ x = op y
  proof: equivToOpposite.symm.eq_symm_apply.symm

中文:
定理 unop_eq_iff_eq_op
  条件: {x} {y : α}
  结论: unop x = y ↔ x = op y
  证明: equivToOpposite.symm.eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, equivToOpposite, equivToOpposite.symm.eq_symm_apply.symm
-/
theorem unop_eq_iff_eq_op {x} {y : α} : unop x = y ↔ x = op y :=
  equivToOpposite.symm.eq_symm_apply.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited αᵒᵖ
  body: ⟨op default⟩

中文:
实例 [Inhabited
  签名: α] : Inhabited αᵒᵖ
  定义体: ⟨op default⟩
-/
instance [Inhabited α] : Inhabited αᵒᵖ :=
  ⟨op default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: α] : Nonempty αᵒᵖ
  body: Nonempty.map op ‹_›

中文:
实例 [Nonempty
  签名: α] : Nonempty αᵒᵖ
  定义体: Nonempty.map op ‹_›

Depends on / 依赖: Nonempty, Nonempty.map
-/
instance [Nonempty α] : Nonempty αᵒᵖ := Nonempty.map op ‹_›

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : Subsingleton αᵒᵖ
  body: unop_injective.subsingleton

中文:
实例 [Subsingleton
  签名: α] : Subsingleton αᵒᵖ
  定义体: unop_injective.subsingleton

Depends on / 依赖: subsingleton, unop_injective, unop_injective.subsingleton
-/
instance [Subsingleton α] : Subsingleton αᵒᵖ := unop_injective.subsingleton

/--
Instance `small` / 实例 `small`

English:
instance small
  signature: {X : Type v} [Small.{u} X]
  body: by
  obtain ⟨S, ⟨e⟩⟩ := Small.equiv_small (α := X)
  exact ⟨S, ⟨equivToOpposite.symm.trans e⟩⟩

中文:
实例 small
  签名: {X : 类型v} [Small.{u} X]
  定义体: by
  obtain ⟨S, ⟨e⟩⟩ := Small.equiv_small (α := X)
  exact ⟨S, ⟨equivToOpposite.symm.trans e⟩⟩

Depends on / 依赖: Small.equiv_small, equivToOpposite, equivToOpposite.symm.trans, equiv_small
-/
instance small {X : Type v} [Small.{u} X] : Small.{u} Xᵒᵖ := by
  obtain ⟨S, ⟨e⟩⟩ := Small.equiv_small (α := X)
  exact ⟨S, ⟨equivToOpposite.symm.trans e⟩⟩

end Opposite
