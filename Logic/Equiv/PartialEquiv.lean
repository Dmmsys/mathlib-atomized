/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Set.Piecewise
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Tactic.Core
public import Mathlib.Tactic.Attr.Core

/-!
# Partial equivalences

This file defines equivalences between subsets of given types.
An element `e` of `PartialEquiv α β` is made of two maps `e.toFun` and `e.invFun` respectively
from α to β and from β to α (just like equivs), which are inverse to each other on the subsets
`e.source` and `e.target` of respectively α and β.

They are designed in particular to define charts on manifolds.

The main functionality is `e.trans f`, which composes the two partial equivalences by restricting
the source and target to the maximal set where the composition makes sense.

As for equivs, we register a coercion to functions and use it in our simp normal form: we write
`e x` and `e.symm y` instead of `e.toFun x` and `e.invFun y`.

## Main definitions

* `Equiv.toPartialEquiv`: associating a partial equiv to an equiv, with source = target = univ
* `PartialEquiv.symm`: the inverse of a partial equivalence
* `PartialEquiv.trans`: the composition of two partial equivalences
* `PartialEquiv.refl`: the identity partial equivalence
* `PartialEquiv.ofSet`: the identity on a set `s`
* `EqOnSource`: equivalence relation describing the "right" notion of equality for partial
  equivalences (see below in implementation notes)

## Implementation notes

There are at least three possible implementations of partial equivalences:
* equivs on subtypes
* pairs of functions taking values in `Option α` and `Option β`, equal to none where the partial
  equivalence is not defined
* pairs of functions defined everywhere, keeping the source and target as additional data

Each of these implementations has pros and cons.
* When dealing with subtypes, one still need to define additional API for composition and
  restriction of domains. Checking that one always belongs to the right subtype makes things very
  tedious, and leads quickly to DTT hell (as the subtype `u ∩ v` is not the "same" as `v ∩ u`, for
  instance).
* With option-valued functions, the composition is very neat (it is just the usual composition, and
  the domain is restricted automatically). These are implemented in `PEquiv.lean`. For manifolds,
  where one wants to discuss thoroughly the smoothness of the maps, this creates however a lot of
  overhead as one would need to extend all classes of smoothness to option-valued maps.
* The `PartialEquiv` version as explained above is easier to use for manifolds. The drawback is that
  there is extra useless data (the values of `toFun` and `invFun` outside of `source` and `target`).
  In particular, the equality notion between partial equivs is not "the right one", i.e., coinciding
  source and target and equality there. Moreover, there are no partial equivs in this sense between
  an empty type and a nonempty type. Since empty types are not that useful, and since one almost
  never needs to talk about equal partial equivs, this is not an issue in practice.
  Still, we introduce an equivalence relation `EqOnSource` that captures this right notion of
  equality, and show that many properties are invariant under this equivalence relation.

### Local coding conventions

If a lemma deals with the intersection of a set with either source or target of a `PartialEquiv`,
then it should use `e.source ∩ s` or `e.target ∩ t`, not `s ∩ e.source` or `t ∩ e.target`.

-/

@[expose] public section
open Lean Meta Elab Tactic

/-! Implementation of the `mfld_set_tac` tactic for working with the domains of partially-defined
functions (`PartialEquiv`, `OpenPartialHomeomorph`, etc).

This is in a separate file from `Mathlib/Tactic/Attr/Register.lean` because attributes need a
new file to become functional.
-/

namespace Mathlib.Tactic.MfldSetTac

/-- A very basic tactic to show that sets showing up in manifolds coincide or are included
in one another. -/
elab (name := mfldSetTac) "mfld_set_tac" : tactic => withMainContext do
  let g ← getMainGoal
  let goalTy := (← instantiateMVars (← g.getDecl).type).getAppFnArgs
  match goalTy with
  | (``Eq, #[_ty, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      apply Set.ext; intro my_y
      constructor <;>
        · intro h_my_y
          try simp only [*, mfld_simps] at h_my_y
          try simp only [*, mfld_simps])))
  | (``LE.le, #[_ty, _inst, _e₁, _e₂]) =>
    evalTactic (← `(tactic| (
      intro my_y h_my_y
      try simp only [*, mfld_simps] at h_my_y
      try simp only [*, mfld_simps])))
  | _ => throwError "goal should be an equality or an inclusion"

attribute [mfld_simps] and_true eq_self_iff_true Function.comp_apply

end Mathlib.Tactic.MfldSetTac

open Function Set

variable {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-- Local equivalence between subsets `source` and `target` of `α` and `β` respectively. The
(global) maps `toFun : α → β` and `invFun : β → α` map `source` to `target` and conversely, and are
inverse to each other there. The values of `toFun` outside of `source` and of `invFun` outside of
`target` are irrelevant. -/
/-
**PartialEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_5 → Type u_6 → Type (max u_5 u_6)
参数：max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local equivalence between subsets `source` and `target` of `α` and `β` respectiv
ely. The
(global) maps `toFun : α → β` and `invFun : β → α` map `source` to `target` and 
conversely, and are
inverse to each other there. The values of `toFun` outside of `source` and of `i
nvFun` outside of
`target` are irrelevant.
-/
structure PartialEquiv (α : Type*) (β : Type*) where
  /-- The global function which has a partial inverse. Its value outside of the `source` subset is
  irrelevant. -/
  toFun : α → β
  /-- The partial inverse to `toFun`. Its value outside of the `target` subset is irrelevant. -/
  invFun : β → α
  /-- The domain of the partial equivalence. -/
  source : Set α
  /-- The codomain of the partial equivalence. -/
  target : Set β
  /-- The proposition that elements of `source` are mapped to elements of `target`. -/
  map_source' : ∀ ⦃x⦄, x ∈ source → toFun x ∈ target
  /-- The proposition that elements of `target` are mapped to elements of `source`. -/
  map_target' : ∀ ⦃x⦄, x ∈ target → invFun x ∈ source
  /-- The proposition that `invFun` is a left-inverse of `toFun` on `source`. -/
  left_inv' : ∀ ⦃x⦄, x ∈ source → invFun (toFun x) = x
  /-- The proposition that `invFun` is a right-inverse of `toFun` on `target`. -/
  right_inv' : ∀ ⦃x⦄, x ∈ target → toFun (invFun x) = x

attribute [coe] PartialEquiv.toFun

namespace PartialEquiv

variable (e : PartialEquiv α β) (e' : PartialEquiv β γ)

/-
**PartialEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `PartialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] [Inhabited β] : Inhabited (PartialEquiv α β) :=
  ⟨⟨const α default, const β default, ∅, ∅, mapsTo_empty _ _, mapsTo_empty _ _, eqOn_empty _ _,
      eqOn_empty _ _⟩⟩

/-- The inverse of a partial equivalence -/
@[symm]
/-
**PartialEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → PartialEquiv α β → PartialEquiv β α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : β⦄, x ∈ self.target → self.invFun x ∈ self.source
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
· 使用定理 `PartialEquiv.right_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : Partial
Equiv α β) ⦃x : β⦄, x ∈ self.target → ↑self (self.invFun x) = x
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x

--- 原说明 ---
The inverse of a partial equivalence
-/
protected def symm : PartialEquiv β α where
  toFun := e.invFun
  invFun := e.toFun
  source := e.target
  target := e.source
  map_source' := e.map_target'
  map_target' := e.map_source'
  left_inv' := e.right_inv'
  right_inv' := e.left_inv'
/-
**PartialEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `PartialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (PartialEquiv α β) fun _ => α → β :=
  ⟨PartialEquiv.toFun⟩

/-- See Note [custom simps projection] -/
/-
**PartialEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv.Simps`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → PartialEquiv α β → β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : PartialEquiv α β) : β → α :=
  e.symm

initialize_simps_projections PartialEquiv (toFun → apply, invFun → symm_apply)
/-
**PartialEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：coe_mk (f : α -> β) (g s t ml mr il ir) : (PartialEquiv.mk f g s t ml mr i
l ir : α -> β) = f
参数：f : α -> β；g s t ml mr il ir。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : α → β) (g s t ml mr il ir) :
    (PartialEquiv.mk f g s t ml mr il ir : α → β) = f := rfl

@[simp, mfld_simps]
/-
**PartialEquiv.coe_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：coe_symm_mk (f : α -> β) (g s t ml mr il ir) : ((PartialEquiv.mk f g s t m
l mr il ir).symm : β -> α) = g
参数：f : α -> β；g s t ml mr il ir。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_mk (f : α → β) (g s t ml mr il ir) :
    ((PartialEquiv.mk f g s t ml mr il ir).symm : β → α) = g :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.invFun_as_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：invFun_as_coe : e.invFun = e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_as_coe : e.invFun = e.symm :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.map_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：map_source {x : α} (h : x in e.source) : e x in e.target
参数：h : x in e.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target
-/
theorem map_source {x : α} (h : x ∈ e.source) : e x ∈ e.target :=
  e.map_source' h

/-- Variant of `e.map_source` and `map_source'`, stated for images of subsets of `source`. -/
/-
**PartialEquiv.image_source_subset** 是 Mathlib 中的一个引理，位于命名空间 `PartialEquiv`。
形式化陈述：image_source_subset : e '' e.source subseteq e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_of_eq_of_mem`：mem_of_eq_of_mem {x y : α} {s : Set α} (hx : x = y
) (h : y in s) : x in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.map_source'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : α⦄, x ∈ self.source → ↑self x ∈ self.target

--- 原说明 ---
Variant of `e.map_source` and `map_source'`, stated for images of subsets of `so
urce`.
-/
lemma image_source_subset : e '' e.source ⊆ e.target :=
  fun _ ⟨_, hx, hex⟩ ↦ mem_of_eq_of_mem (id hex.symm) (e.map_source' hx)

@[deprecated (since := "2026-06-17")] alias map_source'' := image_source_subset

@[simp, mfld_simps]
/-
**PartialEquiv.map_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：map_target {x : β} (h : x in e.target) : e.symm x in e.source
参数：h : x in e.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_target'`：∀ {α : Type u_5} {β : Type u_6} (self : Partia
lEquiv α β) ⦃x : β⦄, x ∈ self.target → self.invFun x ∈ self.source
-/
theorem map_target {x : β} (h : x ∈ e.target) : e.symm x ∈ e.source :=
  e.map_target' h

@[simp, mfld_simps]
/-
**PartialEquiv.left_inv** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：left_inv {x : α} (h : x in e.source) : e.symm (e x) = x
参数：h : x in e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : PartialE
quiv α β) ⦃x : α⦄, x ∈ self.source → self.invFun (↑self x) = x
-/
theorem left_inv {x : α} (h : x ∈ e.source) : e.symm (e x) = x :=
  e.left_inv' h

@[simp, mfld_simps]
/-
**PartialEquiv.right_inv** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：right_inv {x : β} (h : x in e.target) : e (e.symm x) = x
参数：h : x in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.right_inv'`：∀ {α : Type u_5} {β : Type u_6} (self : Partial
Equiv α β) ⦃x : β⦄, x ∈ self.target → ↑self (self.invFun x) = x
-/
theorem right_inv {x : β} (h : x ∈ e.target) : e (e.symm x) = x :=
  e.right_inv' h
/-
**PartialEquiv.target_subset_range** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：target_subset_range : e.target subseteq range e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
-/
theorem target_subset_range : e.target ⊆ range e :=
  fun x hx ↦ ⟨e.symm x, right_inv e hx⟩
/-
**PartialEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_apply_eq {x : α} {y : β} (hx : x in e.source) (hy : y in e.target) : 
e.symm y = x ↔ y = e x
参数：hx : x in e.source；hy : y in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
-/
theorem symm_apply_eq {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    e.symm y = x ↔ y = e x :=
  ⟨fun h => by rw [← e.right_inv hy, h], fun h => by rw [← e.left_inv hx, h]⟩
/-
**PartialEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：eq_symm_apply {x : α} {y : β} (hx : x in e.source) (hy : y in e.target) : 
x = e.symm y ↔ e x = y
参数：hx : x in e.source；hy : y in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.symm_apply_eq`：symm_apply_eq {x : α} {y : β} (hx : x in e.s
ource) (hy : y in e.target) : e.symm y = x ↔ y = e x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem eq_symm_apply {x : α} {y : β} (hx : x ∈ e.source) (hy : y ∈ e.target) :
    x = e.symm y ↔ e x = y := by
  simp [eq_comm, ← symm_apply_eq e hx hy]
/-
**PartialEquiv.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.MapsTo (↑e) e.
source e.target
参数：e : PartialEquiv α β；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
-/
protected theorem mapsTo : MapsTo e e.source e.target := fun _ => e.map_source
/-
**PartialEquiv.mapsTo_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：mapsTo_symm : MapsTo e.symm e.target e.source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
-/
theorem mapsTo_symm : MapsTo e.symm e.target e.source :=
  e.symm.mapsTo

@[deprecated (since := "2026-05-18")] alias symm_mapsTo := mapsTo_symm
/-
**PartialEquiv.leftInvOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.LeftInvOn (↑e.
symm) (↑e) e.source
参数：e : PartialEquiv α β；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
-/
protected theorem leftInvOn : LeftInvOn e.symm e e.source := fun _ => e.left_inv
/-
**PartialEquiv.rightInvOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.RightInvOn (↑e
.symm) (↑e) e.target
参数：e : PartialEquiv α β；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.right_inv`：right_inv {x : β} (h : x in e.target) : e (e.sym
m x) = x
-/
protected theorem rightInvOn : RightInvOn e.symm e e.target := fun _ => e.right_inv
/-
**PartialEquiv.invOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.InvOn (↑e.symm
) (↑e) e.source e.target
参数：e : PartialEquiv α β；↑e.symm；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
· 使用定理 `PartialEquiv.rightInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqu
iv α β), Set.RightInvOn (↑e.symm) (↑e) e.target
-/
protected theorem invOn : InvOn e.symm e e.source e.target :=
  ⟨e.leftInvOn, e.rightInvOn⟩
/-
**PartialEquiv.injOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.InjOn (↑e) e.s
ource
参数：e : PartialEquiv α β；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
-/
protected theorem injOn : InjOn e e.source :=
  e.leftInvOn.injOn
/-
**PartialEquiv.bijOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.BijOn (↑e) e.s
ource e.target
参数：e : PartialEquiv α β；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InvOn.bijOn`：bijOn (h : InvOn f' f s t) (hf : MapsTo f s t) (hf' : M
apsTo f' t s) : BijOn f s t
· 使用定理 `PartialEquiv.invOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InvOn (↑e.symm) (↑e) e.source e.target
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
· 使用定理 `PartialEquiv.mapsTo_symm`：mapsTo_symm : MapsTo e.symm e.target e.source
-/
protected theorem bijOn : BijOn e e.source e.target :=
  e.invOn.bijOn e.mapsTo e.mapsTo_symm
/-
**PartialEquiv.surjOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α β), Set.SurjOn (↑e) e.
source e.target
参数：e : PartialEquiv α β；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.surjOn`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.SurjOn f s t
· 使用定理 `PartialEquiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.BijOn (↑e) e.source e.target
-/
protected theorem surjOn : SurjOn e e.source e.target :=
  e.bijOn.surjOn

/-- Interpret an `Equiv` as a `PartialEquiv` by restricting it to `s` in the domain
and to `t` in the codomain. -/
@[simps -fullyApplied]
/-
**PartialEquiv._root_.Equiv.toPartialEquivOfImageEq** 是 Mathlib 中的一个定义，位于命名空间 `P
artialEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Interpret an `Equiv` as a `PartialEquiv` by restricting it to `s` in the domain
and to `t` in the codomain.
-/
def _root_.Equiv.toPartialEquivOfImageEq (e : α ≃ β) (s : Set α) (t : Set β) (h : e '' s = t) :
    PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := s
  target := t
  map_source' _ hx := h ▸ mem_image_of_mem _ hx
  map_target' x hx := by
    subst t
    rcases hx with ⟨x, hx, rfl⟩
    rwa [e.symm_apply_apply]
  left_inv' x _ := e.symm_apply_apply x
  right_inv' x _ := e.apply_symm_apply x

/-- Associate a `PartialEquiv` to an `Equiv`. -/
@[simps! (attr := mfld_simps) -fullyApplied]
/-
**PartialEquiv._root_.Equiv.toPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartialEqu
iv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associate a `PartialEquiv` to an `Equiv`.
-/
def _root_.Equiv.toPartialEquiv (e : α ≃ β) : PartialEquiv α β :=
  e.toPartialEquivOfImageEq univ univ <| by rw [image_univ, e.surjective.range_eq]
/-
**PartialEquiv.inhabitedOfEmpty** 是 Mathlib 中的一个实例，位于命名空间 `PartialEquiv`。
形式化陈述：inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (PartialEquiv α β)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance inhabitedOfEmpty [IsEmpty α] [IsEmpty β] : Inhabited (PartialEquiv α β) :=
  ⟨((Equiv.equivEmpty α).trans (Equiv.equivEmpty β).symm).toPartialEquiv⟩

/-- Create a copy of a `PartialEquiv` providing better definitional equalities. -/
@[simps -fullyApplied]
/-
**PartialEquiv.copy** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：copy (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg : 
⇑e.symm = g) (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) : P
artialEquiv α β where toFun
参数：e : PartialEquiv α β；f : α -> β；hf : ⇑e = f；g : β -> α；hg : ⇑e.symm = g；s : S
et α；hs : e.source = s；t : Set β；ht : e.target = t。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Create a copy of a `PartialEquiv` providing better definitional equalities.
-/
def copy (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g) (s : Set α)
    (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    PartialEquiv α β where
  toFun := f
  invFun := g
  source := s
  target := t
  map_source' _ := ht ▸ hs ▸ hf ▸ e.map_source
  map_target' _ := hs ▸ ht ▸ hg ▸ e.map_target
  left_inv' _ := hs ▸ hf ▸ hg ▸ e.left_inv
  right_inv' _ := ht ▸ hf ▸ hg ▸ e.right_inv
/-
**PartialEquiv.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：copy_eq (e : PartialEquiv α β) (f : α -> β) (hf : ⇑e = f) (g : β -> α) (hg
 : ⇑e.symm = g) (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) 
: e.copy f hf g hg s hs t ht = e
参数：e : PartialEquiv α β；f : α -> β；hf : ⇑e = f；g : β -> α；hg : ⇑e.symm = g；s : S
et α；hs : e.source = s；t : Set β；ht : e.target = t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem copy_eq (e : PartialEquiv α β) (f : α → β) (hf : ⇑e = f) (g : β → α) (hg : ⇑e.symm = g)
    (s : Set α) (hs : e.source = s) (t : Set β) (ht : e.target = t) :
    e.copy f hf g hg s hs t ht = e := by
  subst f g s t
  cases e
  rfl

/-- Associate to a `PartialEquiv` an `Equiv` between the source and the target. -/
/-
**PartialEquiv.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (e : PartialEquiv α β) → ↑e.source ≃ ↑e.
target
参数：e : PartialEquiv α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Associate to a `PartialEquiv` an `Equiv` between the source and the target.
-/
protected def toEquiv : e.source ≃ e.target where
  toFun x := ⟨e x, e.map_source x.mem⟩
  invFun y := ⟨e.symm y, e.map_target y.mem⟩
  left_inv := fun ⟨_, hx⟩ => Subtype.ext <| e.left_inv hx
  right_inv := fun ⟨_, hy⟩ => Subtype.ext <| e.right_inv hy
/-
**PartialEquiv.toEquiv_eq_codRestrict_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Partia
lEquiv`。
形式化陈述：toEquiv_eq_codRestrict_restrict : e.toEquiv = codRestrict (e.source.domRes
trict e) e.target (by simp)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_eq_codRestrict_restrict :
    e.toEquiv = codRestrict (e.source.domRestrict e) e.target (by simp) :=
  rfl
/-
**PartialEquiv.toEquiv_symm_eq_codRestrict_restrict** 是 Mathlib 中的一个引理，位于命名空间 `P
artialEquiv`。
形式化陈述：toEquiv_symm_eq_codRestrict_restrict : e.toEquiv.symm = codRestrict (e.tar
get.domRestrict e.invFun) e.source (by simp)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma toEquiv_symm_eq_codRestrict_restrict :
    e.toEquiv.symm = codRestrict (e.target.domRestrict e.invFun) e.source (by simp) := by
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.symm_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_source : e.symm.source = e.target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_source : e.symm.source = e.target :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.symm_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_target : e.symm.target = e.source
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_target : e.symm.target = e.source :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_symm : e.symm.symm = e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm : e.symm.symm = e := rfl
/-
**PartialEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_bijective : Function.Bijective (PartialEquiv.symm : PartialEquiv α β 
-> PartialEquiv β α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `PartialEquiv.symm_symm`：symm_symm : e.symm.symm = e
-/
theorem symm_bijective :
    Function.Bijective (PartialEquiv.symm : PartialEquiv α β → PartialEquiv β α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**PartialEquiv.image_source_eq_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：image_source_eq_target : e '' e.source = e.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `PartialEquiv.bijOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.BijOn (↑e) e.source e.target
-/
theorem image_source_eq_target : e '' e.source = e.target :=
  e.bijOn.image_eq
/-
**PartialEquiv.forall_mem_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：forall_mem_target {p : β -> Prop} : (forall y in e.target, p y) ↔ forall x
 in e.source, p (e x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `Set.forall_mem_image`：forall_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (forall y in f '' s, p y) ↔ forall ⦃x⦄, x in s -> p (f x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem forall_mem_target {p : β → Prop} : (∀ y ∈ e.target, p y) ↔ ∀ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, forall_mem_image]
/-
**PartialEquiv.exists_mem_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：exists_mem_target {p : β -> Prop} : (exists y in e.target, p y) ↔ exists x
 in e.source, p (e x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `Set.exists_mem_image`：exists_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (exists y in f '' s, p y) ↔ exists x in s, p (f x)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem exists_mem_target {p : β → Prop} : (∃ y ∈ e.target, p y) ↔ ∃ x ∈ e.source, p (e x) := by
  rw [← image_source_eq_target, exists_mem_image]

/-- We say that `t : Set β` is an image of `s : Set α` under a partial equivalence if
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
/-
**PartialEquiv.IsImage** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：IsImage (s : Set α) (t : Set β) : Prop
参数：s : Set α；t : Set β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `t : Set β` is an image of `s : Set α` under a partial equivalence i
f
any of the following equivalent conditions hold:

* `e '' (e.source ∩ s) = e.target ∩ t`;
* `e.source ∩ e ⁻¹ t = e.source ∩ s`;
* `∀ x ∈ e.source, e x ∈ t ↔ x ∈ s` (this one is used in the definition).
-/
def IsImage (s : Set α) (t : Set β) : Prop :=
  ∀ ⦃x⦄, x ∈ e.source → (e x ∈ t ↔ x ∈ s)

namespace IsImage

variable {e} {s : Set α} {t : Set β} {x : α}

/-
**PartialEquiv.IsImage.apply_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsI
mage`。
形式化陈述：apply_mem_iff (h : e.IsImage s t) (hx : x in e.source) : e x in t ↔ x in s
参数：h : e.IsImage s t；hx : x in e.source。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem apply_mem_iff (h : e.IsImage s t) (hx : x ∈ e.source) : e x ∈ t ↔ x ∈ s :=
  h hx
/-
**PartialEquiv.IsImage.symm_apply_mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqui
v.IsImage`。
形式化陈述：symm_apply_mem_iff (h : e.IsImage s t) : forall ⦃y⦄, y in e.target -> (e.s
ymm y in s ↔ y in t)
参数：h : e.IsImage s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PartialEquiv.forall_mem_target`：forall_mem_target {p : β -> Prop} : (for
all y in e.target, p y) ↔ forall x in e.source, p (e x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symm_apply_mem_iff (h : e.IsImage s t) : ∀ ⦃y⦄, y ∈ e.target → (e.symm y ∈ s ↔ y ∈ t) :=
  e.forall_mem_target.mpr fun x hx => by rw [e.left_inv hx, h hx]
/-
**PartialEquiv.IsImage.symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : PartialEquiv α β} {s : Set α} {t : Se
t β}, e.IsImage s t → e.symm.IsImage t s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.symm_apply_mem_iff`：symm_apply_mem_iff (h : e.IsIma
ge s t) : forall ⦃y⦄, y in e.target -> (e.symm y in s ↔ y in t)
-/
protected theorem symm (h : e.IsImage s t) : e.symm.IsImage t s :=
  h.symm_apply_mem_iff

@[simp]
/-
**PartialEquiv.IsImage.symm_iff** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`
。
形式化陈述：symm_iff : e.symm.IsImage t s ↔ e.IsImage s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.symm`：∀ {α : Type u_1} {β : Type u_2} {e : PartialE
quiv α β} {s : Set α} {t : Set β}, e.IsImage s t → e.symm.IsImage t s
-/
theorem symm_iff : e.symm.IsImage t s ↔ e.IsImage s t :=
  ⟨fun h => h.symm, fun h => h.symm⟩
/-
**PartialEquiv.IsImage.mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : PartialEquiv α β} {s : Set α} {t : Se
t β},   e.IsImage s t → Set.MapsTo (↑e) (e.source ∩ s) (e.target ∩ t)
参数：↑e；e.source ∩ s；e.target ∩ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected theorem mapsTo (h : e.IsImage s t) : MapsTo e (e.source ∩ s) (e.target ∩ t) :=
  fun _ hx => ⟨e.mapsTo hx.1, (h hx.1).2 hx.2⟩
/-
**PartialEquiv.IsImage.symm_mapsTo** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsIma
ge`。
形式化陈述：symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target inter t) (e.sour
ce inter s)
参数：h : e.IsImage s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {e : Partia
lEquiv α β} {s : Set α} {t : Set β},   e.IsImage s t → Set.MapsTo (↑e) (e.source
 ∩ s) (e.target ∩…
· 使用定理 `PartialEquiv.IsImage.symm`：∀ {α : Type u_1} {β : Type u_2} {e : PartialE
quiv α β} {s : Set α} {t : Set β}, e.IsImage s t → e.symm.IsImage t s
-/
theorem symm_mapsTo (h : e.IsImage s t) : MapsTo e.symm (e.target ∩ t) (e.source ∩ s) :=
  h.symm.mapsTo

/-- Restrict a `PartialEquiv` to a pair of corresponding sets. -/
@[simps -fullyApplied]
/-
**PartialEquiv.IsImage.restr** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：restr (h : e.IsImage s t) : PartialEquiv α β where toFun
参数：h : e.IsImage s t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {e : Partia
lEquiv α β} {s : Set α} {t : Set β},   e.IsImage s t → Set.MapsTo (↑e) (e.source
 ∩ s) (e.target ∩…
· 使用定理 `PartialEquiv.IsImage.symm_mapsTo`：symm_mapsTo (h : e.IsImage s t) : Maps
To e.symm (e.target inter t) (e.source inter s)

--- 原说明 ---
Restrict a `PartialEquiv` to a pair of corresponding sets.
-/
def restr (h : e.IsImage s t) : PartialEquiv α β where
  toFun := e
  invFun := e.symm
  source := e.source ∩ s
  target := e.target ∩ t
  map_source' := h.mapsTo
  map_target' := h.symm_mapsTo
  left_inv' := e.leftInvOn.mono inter_subset_left
  right_inv' := e.rightInvOn.mono inter_subset_left
/-
**PartialEquiv.IsImage.image_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`
。
形式化陈述：image_eq (h : e.IsImage s t) : e '' (e.source inter s) = e.target inter t
参数：h : e.IsImage s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem image_eq (h : e.IsImage s t) : e '' (e.source ∩ s) = e.target ∩ t :=
  h.restr.image_source_eq_target
/-
**PartialEquiv.IsImage.symm_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsI
mage`。
形式化陈述：symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target inter t) = e.sourc
e inter s
参数：h : e.IsImage s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e '' (e.so
urce inter s) = e.target inter t
· 使用定理 `PartialEquiv.IsImage.symm`：∀ {α : Type u_1} {β : Type u_2} {e : PartialE
quiv α β} {s : Set α} {t : Set β}, e.IsImage s t → e.symm.IsImage t s
-/
theorem symm_image_eq (h : e.IsImage s t) : e.symm '' (e.target ∩ t) = e.source ∩ s :=
  h.symm.image_eq
/-
**PartialEquiv.IsImage.iff_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.I
sImage`。
形式化陈述：iff_preimage_eq : e.IsImage s t ↔ e.source inter e ⁻¹' t = e.source inter 
s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem iff_preimage_eq : e.IsImage s t ↔ e.source ∩ e ⁻¹' t = e.source ∩ s := by
  simp only [IsImage, Set.ext_iff, mem_inter_iff, mem_preimage, and_congr_right_iff]

alias ⟨preimage_eq, of_preimage_eq⟩ := iff_preimage_eq
/-
**PartialEquiv.IsImage.iff_symm_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEq
uiv.IsImage`。
形式化陈述：iff_symm_preimage_eq : e.IsImage s t ↔ e.target inter e.symm ⁻¹' s = e.tar
get inter t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `PartialEquiv.IsImage.symm_iff`：symm_iff : e.symm.IsImage t s ↔ e.IsImage
 s t
· 使用定理 `PartialEquiv.IsImage.iff_preimage_eq`：iff_preimage_eq : e.IsImage s t ↔ 
e.source inter e ⁻¹' t = e.source inter s
-/
theorem iff_symm_preimage_eq : e.IsImage s t ↔ e.target ∩ e.symm ⁻¹' s = e.target ∩ t :=
  symm_iff.symm.trans iff_preimage_eq

alias ⟨symm_preimage_eq, of_symm_preimage_eq⟩ := iff_symm_preimage_eq
/-
**PartialEquiv.IsImage.of_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsIma
ge`。
形式化陈述：of_image_eq (h : e '' (e.source inter s) = e.target inter t) : e.IsImage s
 t
参数：h : e '' (e.source inter s) = e.target inter t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.of_symm_preimage_eq`：∀ {α : Type u_1} {β : Type u_2
} {e : PartialEquiv α β} {s : Set α} {t : Set β},   e.target ∩ ↑e.symm ⁻¹' s = e
.target ∩ t → e.IsImage s t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e '' (e.so
urce inter s) = e.target inter t
-/
theorem of_image_eq (h : e '' (e.source ∩ s) = e.target ∩ t) : e.IsImage s t :=
  of_symm_preimage_eq <| Eq.trans (of_symm_preimage_eq rfl).image_eq.symm h
/-
**PartialEquiv.IsImage.of_symm_image_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.
IsImage`。
形式化陈述：of_symm_image_eq (h : e.symm '' (e.target inter t) = e.source inter s) : e
.IsImage s t
参数：h : e.symm '' (e.target inter t) = e.source inter s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.of_preimage_eq`：∀ {α : Type u_1} {β : Type u_2} {e 
: PartialEquiv α β} {s : Set α} {t : Set β},   e.source ∩ ↑e ⁻¹' t = e.source ∩ 
s → e.IsImage s t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.IsImage.symm_image_eq`：symm_image_eq (h : e.IsImage s t) : 
e.symm '' (e.target inter t) = e.source inter s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PartialEquiv.IsImage.iff_preimage_eq`：iff_preimage_eq : e.IsImage s t ↔ 
e.source inter e ⁻¹' t = e.source inter s
-/
theorem of_symm_image_eq (h : e.symm '' (e.target ∩ t) = e.source ∩ s) : e.IsImage s t :=
  of_preimage_eq <| Eq.trans (iff_preimage_eq.2 rfl).symm_image_eq.symm h
/-
**PartialEquiv.IsImage.compl** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : PartialEquiv α β} {s : Set α} {t : Se
t β}, e.IsImage s t → e.IsImage sᶜ tᶜ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_congr`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
protected theorem compl (h : e.IsImage s t) : e.IsImage sᶜ tᶜ := fun _ hx => not_congr (h hx)
/-
**PartialEquiv.IsImage.inter** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : PartialEquiv α β} {s : Set α} {t : Se
t β} {s' : Set α} {t' : Set β},   e.IsImage s t → e.IsImage s' t' → e.IsImage (s
 ∩ s') (t ∩ t')
参数：s ∩ s'；t ∩ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `and_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
-/
protected theorem inter {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∩ s') (t ∩ t') := fun _ hx => and_congr (h hx) (h' hx)
/-
**PartialEquiv.IsImage.union** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : PartialEquiv α β} {s : Set α} {t : Se
t β} {s' : Set α} {t' : Set β},   e.IsImage s t → e.IsImage s' t' → e.IsImage (s
 ∪ s') (t ∪ t')
参数：s ∪ s'；t ∪ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
-/
protected theorem union {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s ∪ s') (t ∪ t') := fun _ hx => or_congr (h hx) (h' hx)
/-
**PartialEquiv.IsImage.diff** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.IsImage`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e : PartialEquiv α β} {s : Set α} {t : Se
t β} {s' : Set α} {t' : Set β},   e.IsImage s t → e.IsImage s' t' → e.IsImage (s
 \ s') (t \ t')
参数：s \ s'；t \ t'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.inter`：∀ {α : Type u_1} {β : Type u_2} {e : Partial
Equiv α β} {s : Set α} {t : Set β} {s' : Set α} {t' : Set β},   e.IsImage s t → 
e.IsImage s' t' …
· 使用定理 `PartialEquiv.IsImage.compl`：∀ {α : Type u_1} {β : Type u_2} {e : Partial
Equiv α β} {s : Set α} {t : Set β}, e.IsImage s t → e.IsImage sᶜ tᶜ
-/
protected theorem diff {s' t'} (h : e.IsImage s t) (h' : e.IsImage s' t') :
    e.IsImage (s \ s') (t \ t') :=
  h.inter h'.compl
/-
**PartialEquiv.IsImage.leftInvOn_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqu
iv.IsImage`。
形式化陈述：leftInvOn_piecewise {e' : PartialEquiv α β} [forall i, Decidable (i in s)]
 [forall i, Decidable (i in t)] (h : e.IsImage s t) (h' : e'.IsImage s t) : Left
InvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source)
参数：i in s；i in t；h : e.IsImage s t；h' : e'.IsImage s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piecewise_eq_of_mem`：piecewise_eq_of_mem {i : α} (hi : i in s) : s.p
iecewise f g i = f i
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `Set.piecewise_eq_of_notMem`：piecewise_eq_of_notMem {i : α} (hi : i ∉ s) 
: s.piecewise f g i = g i
· 使用定理 `PartialEquiv.IsImage.compl`：∀ {α : Type u_1} {β : Type u_2} {e : Partial
Equiv α β} {s : Set α} {t : Set β}, e.IsImage s t → e.IsImage sᶜ tᶜ
-/
theorem leftInvOn_piecewise {e' : PartialEquiv α β} [∀ i, Decidable (i ∈ s)]
    [∀ i, Decidable (i ∈ t)] (h : e.IsImage s t) (h' : e'.IsImage s t) :
    LeftInvOn (t.piecewise e.symm e'.symm) (s.piecewise e e') (s.ite e.source e'.source) := by
  rintro x (⟨he, hs⟩ | ⟨he, hs : x ∉ s⟩)
  · rw [piecewise_eq_of_mem _ _ _ hs, piecewise_eq_of_mem _ _ _ ((h he).2 hs), e.left_inv he]
  · rw [piecewise_eq_of_notMem _ _ _ hs, piecewise_eq_of_notMem _ _ _ ((h'.compl he).2 hs),
      e'.left_inv he]
/-
**PartialEquiv.IsImage.inter_eq_of_inter_eq_of_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `P
artialEquiv.IsImage`。
形式化陈述：inter_eq_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t) (
h' : e'.IsImage s t) (hs : e.source inter s = e'.source inter s) (heq : EqOn e e
' (e.source inter s)) : e.target inter t = e'.target inter t
参数：h : e.IsImage s t；h' : e'.IsImage s t；hs : e.source inter s = e'.source inter
 s；heq : EqOn e e' (e.source inter s)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e '' (e.so
urce inter s) = e.target inter t
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
-/
theorem inter_eq_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (h' : e'.IsImage s t) (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    e.target ∩ t = e'.target ∩ t := by rw [← h.image_eq, ← h'.image_eq, ← hs, heq.image_eq]
/-
**PartialEquiv.IsImage.symm_eq_on_of_inter_eq_of_eqOn** 是 Mathlib 中的一个定理，位于命名空间 
`PartialEquiv.IsImage`。
形式化陈述：symm_eq_on_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
 (hs : e.source inter s = e'.source inter s) (heq : EqOn e e' (e.source inter s)
) : EqOn e.symm e'.symm (e.target inter t)
参数：h : e.IsImage s t；hs : e.source inter s = e'.source inter s；heq : EqOn e e' (
e.source inter s)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.IsImage.image_eq`：image_eq (h : e.IsImage s t) : e '' (e.so
urce inter s) = e.target inter t
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem symm_eq_on_of_inter_eq_of_eqOn {e' : PartialEquiv α β} (h : e.IsImage s t)
    (hs : e.source ∩ s = e'.source ∩ s) (heq : EqOn e e' (e.source ∩ s)) :
    EqOn e.symm e'.symm (e.target ∩ t) := by
  rw [← h.image_eq]
  rintro y ⟨x, hx, rfl⟩
  have hx' := hx; rw [hs] at hx'
  rw [e.left_inv hx.1, heq hx, e'.left_inv hx'.1]

end IsImage

/-
**PartialEquiv.isImage_source_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：isImage_source_target : e.IsImage e.source e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isImage_source_target : e.IsImage e.source e.target := fun x hx => by simp [hx]
/-
**PartialEquiv.isImage_source_target_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Part
ialEquiv`。
形式化陈述：isImage_source_target_of_disjoint (e' : PartialEquiv α β) (hs : Disjoint e
.source e'.source) (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.t
arget
参数：e' : PartialEquiv α β；hs : Disjoint e.source e'.source；ht : Disjoint e.target
 e'.target。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.of_image_eq`：of_image_eq (h : e '' (e.source inter 
s) = e.target inter t) : e.IsImage s t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
-/
theorem isImage_source_target_of_disjoint (e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) : e.IsImage e'.source e'.target :=
  IsImage.of_image_eq <| by rw [hs.inter_eq, ht.inter_eq, image_empty]
/-
**PartialEquiv.image_source_inter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：image_source_inter_eq' (s : Set α) : e '' (e.source inter s) = e.target in
ter e.symm ⁻¹' s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.LeftInvOn.image_inter'`：image_inter' (hf : LeftInvOn f' f s) : f '' 
(s₁ inter s) = f' ⁻¹' s₁ inter f '' s
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem image_source_inter_eq' (s : Set α) : e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' s := by
  rw [inter_comm, e.leftInvOn.image_inter', image_source_eq_target, inter_comm]
/-
**PartialEquiv.image_source_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：image_source_inter_eq (s : Set α) : e '' (e.source inter s) = e.target int
er e.symm ⁻¹' (e.source inter s)
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.LeftInvOn.image_inter`：image_inter (hf : LeftInvOn f' f s) : f '' (s
₁ inter s) = f' ⁻¹' (s₁ inter s) inter f '' s
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem image_source_inter_eq (s : Set α) :
    e '' (e.source ∩ s) = e.target ∩ e.symm ⁻¹' (e.source ∩ s) := by
  rw [inter_comm, e.leftInvOn.image_inter, image_source_eq_target, inter_comm]
/-
**PartialEquiv.image_eq_target_inter_inv_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Par
tialEquiv`。
形式化陈述：image_eq_target_inter_inv_preimage {s : Set α} (h : s subseteq e.source) :
 e '' s = e.target inter e.symm ⁻¹' s
参数：h : s subseteq e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
· 使用定理 `Set.inter_eq_self_of_subset_right`：inter_eq_self_of_subset_right {s t : 
Set α} : t subseteq s -> s inter t = t
-/
theorem image_eq_target_inter_inv_preimage {s : Set α} (h : s ⊆ e.source) :
    e '' s = e.target ∩ e.symm ⁻¹' s := by
  rw [← e.image_source_inter_eq', inter_eq_self_of_subset_right h]
/-
**PartialEquiv.symm_image_eq_source_inter_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Pa
rtialEquiv`。
形式化陈述：symm_image_eq_source_inter_preimage {s : Set β} (h : s subseteq e.target) 
: e.symm '' s = e.source inter e ⁻¹' s
参数：h : s subseteq e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_eq_target_inter_inv_preimage`：image_eq_target_inter_i
nv_preimage {s : Set α} (h : s subseteq e.source) : e '' s = e.target inter e.sy
mm ⁻¹' s
-/
theorem symm_image_eq_source_inter_preimage {s : Set β} (h : s ⊆ e.target) :
    e.symm '' s = e.source ∩ e ⁻¹' s :=
  e.symm.image_eq_target_inter_inv_preimage h
/-
**PartialEquiv.symm_image_target_inter_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqui
v`。
形式化陈述：symm_image_target_inter_eq (s : Set β) : e.symm '' (e.target inter s) = e.
source inter e ⁻¹' (e.target inter s)
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_inter_eq`：image_source_inter_eq (s : Set α) : 
e '' (e.source inter s) = e.target inter e.symm ⁻¹' (e.source inter s)
-/
theorem symm_image_target_inter_eq (s : Set β) :
    e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' (e.target ∩ s) :=
  e.symm.image_source_inter_eq _
/-
**PartialEquiv.symm_image_target_inter_eq'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqu
iv`。
形式化陈述：symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target inter s) = e
.source inter e ⁻¹' s
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_inter_eq'`：image_source_inter_eq' (s : Set α) 
: e '' (e.source inter s) = e.target inter e.symm ⁻¹' s
-/
theorem symm_image_target_inter_eq' (s : Set β) : e.symm '' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  e.symm.image_source_inter_eq' _
/-
**PartialEquiv.source_inter_preimage_inv_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Par
tialEquiv`。
形式化陈述：source_inter_preimage_inv_preimage (s : Set α) : e.source inter e ⁻¹' e.sy
mm ⁻¹' s = e.source inter s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_congr_right_iff`：∀ {a b c : Prop}, (a ∧ b ↔ a ∧ c) ↔ a → (b ↔ c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem source_inter_preimage_inv_preimage (s : Set α) :
    e.source ∩ e ⁻¹' e.symm ⁻¹' s = e.source ∩ s :=
  Set.ext fun x => and_congr_right_iff.2 fun hx =>
    by simp only [mem_preimage, e.left_inv hx]
/-
**PartialEquiv.source_inter_preimage_target_inter** 是 Mathlib 中的一个定理，位于命名空间 `Par
tialEquiv`。
形式化陈述：source_inter_preimage_target_inter (s : Set β) : e.source inter e ⁻¹' (e.t
arget inter s) = e.source inter e ⁻¹' s
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PartialEquiv.map_source`：map_source {x : α} (h : x in e.source) : e x in
 e.target
-/
theorem source_inter_preimage_target_inter (s : Set β) :
    e.source ∩ e ⁻¹' (e.target ∩ s) = e.source ∩ e ⁻¹' s :=
  ext fun _ => ⟨fun hx => ⟨hx.1, hx.2.2⟩, fun hx => ⟨hx.1, e.map_source hx.1, hx.2⟩⟩
/-
**PartialEquiv.target_inter_inv_preimage_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Par
tialEquiv`。
形式化陈述：target_inter_inv_preimage_preimage (s : Set β) : e.target inter e.symm ⁻¹'
 e ⁻¹' s = e.target inter s
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.source_inter_preimage_inv_preimage`：source_inter_preimage_i
nv_preimage (s : Set α) : e.source inter e ⁻¹' e.symm ⁻¹' s = e.source inter s
-/
theorem target_inter_inv_preimage_preimage (s : Set β) :
    e.target ∩ e.symm ⁻¹' e ⁻¹' s = e.target ∩ s :=
  e.symm.source_inter_preimage_inv_preimage _
/-
**PartialEquiv.symm_image_image_of_subset_source** 是 Mathlib 中的一个定理，位于命名空间 `Part
ialEquiv`。
形式化陈述：symm_image_image_of_subset_source {s : Set α} (h : s subseteq e.source) : 
e.symm '' e '' s = s
参数：h : s subseteq e.source。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.LeftInvOn.image_image`：image_image (hf : LeftInvOn f' f s) : f' '' f
 '' s = s
· 使用定理 `Set.LeftInvOn.mono`：mono (hf : LeftInvOn f' f s) (ht : s₁ subseteq s) : 
LeftInvOn f' f s₁
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
-/
theorem symm_image_image_of_subset_source {s : Set α} (h : s ⊆ e.source) : e.symm '' e '' s = s :=
  (e.leftInvOn.mono h).image_image
/-
**PartialEquiv.image_symm_image_of_subset_target** 是 Mathlib 中的一个定理，位于命名空间 `Part
ialEquiv`。
形式化陈述：image_symm_image_of_subset_target {s : Set β} (h : s subseteq e.target) : 
e '' e.symm '' s = s
参数：h : s subseteq e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.symm_image_image_of_subset_source`：symm_image_image_of_subs
et_source {s : Set α} (h : s subseteq e.source) : e.symm '' e '' s = s
-/
theorem image_symm_image_of_subset_target {s : Set β} (h : s ⊆ e.target) : e '' e.symm '' s = s :=
  e.symm.symm_image_image_of_subset_source h
/-
**PartialEquiv.source_subset_preimage_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialE
quiv`。
形式化陈述：source_subset_preimage_target : e.source subseteq e ⁻¹' e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
-/
theorem source_subset_preimage_target : e.source ⊆ e ⁻¹' e.target :=
  e.mapsTo
/-
**PartialEquiv.symm_image_target_eq_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqu
iv`。
形式化陈述：symm_image_target_eq_source : e.symm '' e.target = e.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem symm_image_target_eq_source : e.symm '' e.target = e.source :=
  e.symm.image_source_eq_target
/-
**PartialEquiv.target_subset_preimage_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialE
quiv`。
形式化陈述：target_subset_preimage_source : e.target subseteq e.symm ⁻¹' e.source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.mapsTo_symm`：mapsTo_symm : MapsTo e.symm e.target e.source
-/
theorem target_subset_preimage_source : e.target ⊆ e.symm ⁻¹' e.source :=
  e.mapsTo_symm

/-- Two partial equivs that have the same `source`, same `toFun` and same `invFun`, coincide. -/
@[ext]
/-
**PartialEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β},   (∀ (x : α), ↑
e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.source = e'.source → e = 
e'
参数：∀ (x : α), ↑e x = ↑e' x；∀ (x : β), ↑e.symm x = ↑e'.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.mk.congr_simp`：∀ {α : Type u_5} {β : Type u_6} (toFun toFun
_1 : α → β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : 
invFun = invFun_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Two partial equivs that have the same `source`, same `toFun` and same `invFun`, 
coincide.
-/
protected theorem ext {e e' : PartialEquiv α β} (h : ∀ x, e x = e' x)
    (hsymm : ∀ x, e.symm x = e'.symm x) (hs : e.source = e'.source) : e = e' := by
  have A : (e : α → β) = e' := by
    ext x
    exact h x
  have B : (e.symm : β → α) = e'.symm := by
    ext x
    exact hsymm x
  have I : e '' e.source = e.target := e.image_source_eq_target
  have I' : e' '' e'.source = e'.target := e'.image_source_eq_target
  rw [A, hs, I'] at I
  cases e; cases e'
  simp_all

/-- Restricting a partial equivalence to `e.source ∩ s` -/
/-
**PartialEquiv.restr** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → PartialEquiv α β → Set α → PartialEquiv 
α β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restricting a partial equivalence to `e.source ∩ s`
-/
protected def restr (s : Set α) : PartialEquiv α β :=
  (@IsImage.of_symm_preimage_eq α β e s (e.symm ⁻¹' s) rfl).restr

@[simp, mfld_simps]
/-
**PartialEquiv.restr_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：restr_coe (s : Set α) : (e.restr s : α -> β) = e
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_coe (s : Set α) : (e.restr s : α → β) = e :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.restr_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：restr_coe_symm (s : Set α) : ((e.restr s).symm : β -> α) = e.symm
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_coe_symm (s : Set α) : ((e.restr s).symm : β → α) = e.symm :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.restr_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：restr_source (s : Set α) : (e.restr s).source = e.source inter s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_source (s : Set α) : (e.restr s).source = e.source ∩ s :=
  rfl
/-
**PartialEquiv.source_restr_subset_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqui
v`。
形式化陈述：source_restr_subset_source (s : Set α) : (e.restr s).source subseteq e.sou
rce
参数：s : Set α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
-/
theorem source_restr_subset_source (s : Set α) : (e.restr s).source ⊆ e.source := inter_subset_left

@[simp, mfld_simps]
/-
**PartialEquiv.restr_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：restr_target (s : Set α) : (e.restr s).target = e.target inter e.symm ⁻¹' 
s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem restr_target (s : Set α) : (e.restr s).target = e.target ∩ e.symm ⁻¹' s :=
  rfl
/-
**PartialEquiv.restr_eq_of_source_subset** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv
`。
形式化陈述：restr_eq_of_source_subset {e : PartialEquiv α β} {s : Set α} (h : e.source
 subseteq s) : e.restr s = e
参数：h : e.source subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_eq_self_of_subset_left`：inter_eq_self_of_subset_left {s t : Se
t α} : s subseteq t -> s inter t = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restr_eq_of_source_subset {e : PartialEquiv α β} {s : Set α} (h : e.source ⊆ s) :
    e.restr s = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [inter_eq_self_of_subset_left h])

@[simp, mfld_simps]
/-
**PartialEquiv.restr_univ** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：restr_univ {e : PartialEquiv α β} : e.restr univ = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.restr_eq_of_source_subset`：restr_eq_of_source_subset {e : P
artialEquiv α β} {s : Set α} (h : e.source subseteq s) : e.restr s = e
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
-/
theorem restr_univ {e : PartialEquiv α β} : e.restr univ = e :=
  restr_eq_of_source_subset (subset_univ _)

/-- The identity partial equiv -/
/-
**PartialEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：(α : Type u_5) → PartialEquiv α α
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity partial equiv
-/
protected def refl (α : Type*) : PartialEquiv α α :=
  (Equiv.refl α).toPartialEquiv

@[simp, mfld_simps]
/-
**PartialEquiv.refl_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_source : (PartialEquiv.refl α).source = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_source : (PartialEquiv.refl α).source = univ :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.refl_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_target : (PartialEquiv.refl α).target = univ
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_target : (PartialEquiv.refl α).target = univ :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.refl_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_coe : (PartialEquiv.refl α : α -> α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_coe : (PartialEquiv.refl α : α → α) = id :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_symm : (PartialEquiv.refl α).symm = PartialEquiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (PartialEquiv.refl α).symm = PartialEquiv.refl α :=
  rfl

@[mfld_simps]
/-
**PartialEquiv.refl_restr_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_restr_source (s : Set α) : ((PartialEquiv.refl α).restr s).source = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem refl_restr_source (s : Set α) : ((PartialEquiv.refl α).restr s).source = s := by simp

@[mfld_simps]
/-
**PartialEquiv.refl_restr_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_restr_target (s : Set α) : ((PartialEquiv.refl α).restr s).target = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem refl_restr_target (s : Set α) : ((PartialEquiv.refl α).restr s).target = s := by simp

/-- The identity partial equivalence on a set `s` -/
/-
**PartialEquiv.ofSet** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：ofSet (s : Set α) : PartialEquiv α α where toFun
参数：s : Set α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity partial equivalence on a set `s`
-/
def ofSet (s : Set α) : PartialEquiv α α where
  toFun := id
  invFun := id
  source := s
  target := s
  map_source' _ hx := hx
  map_target' _ hx := hx
  left_inv' _ _ := rfl
  right_inv' _ _ := rfl

@[simp, mfld_simps]
/-
**PartialEquiv.ofSet_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：ofSet_source (s : Set α) : (PartialEquiv.ofSet s).source = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_source (s : Set α) : (PartialEquiv.ofSet s).source = s :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.ofSet_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：ofSet_target (s : Set α) : (PartialEquiv.ofSet s).target = s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_target (s : Set α) : (PartialEquiv.ofSet s).target = s :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.ofSet_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：ofSet_coe (s : Set α) : (PartialEquiv.ofSet s : α -> α) = id
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_coe (s : Set α) : (PartialEquiv.ofSet s : α → α) = id :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.ofSet_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：ofSet_symm (s : Set α) : (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet 
s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofSet_symm (s : Set α) : (PartialEquiv.ofSet s).symm = PartialEquiv.ofSet s :=
  rfl

/-- `Function.const` as a `PartialEquiv`.
It consists of two constant maps in opposite directions. -/
@[simps]
/-
**PartialEquiv.single** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：single (a : α) (b : β) : PartialEquiv α β where toFun
参数：a : α；b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Function.const` as a `PartialEquiv`.
It consists of two constant maps in opposite directions.
-/
def single (a : α) (b : β) : PartialEquiv α β where
  toFun := Function.const α b
  invFun := Function.const β a
  source := {a}
  target := {b}
  map_source' _ _ := rfl
  map_target' _ _ := rfl
  left_inv' a' ha' := by rw [eq_of_mem_singleton ha', const_apply]
  right_inv' b' hb' := by rw [eq_of_mem_singleton hb', const_apply]

/-- Composing two partial equivs if the target of the first coincides with the source of the
second. -/
@[simps]
/-
**PartialEquiv.trans'** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} → (e : PartialEquiv
 α β) → (e' : PartialEquiv β γ) → e.target = e'.source → PartialEquiv α γ
参数：e : PartialEquiv α β；e' : PartialEquiv β γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing two partial equivs if the target of the first coincides with the sourc
e of the
second.
-/
protected def trans' (e' : PartialEquiv β γ) (h : e.target = e'.source) : PartialEquiv α γ where
  toFun := e' ∘ e
  invFun := e.symm ∘ e'.symm
  source := e.source
  target := e'.target
  map_source' x hx := by simp [← h, hx]
  map_target' y hy := by simp [h, hy]
  left_inv' x hx := by simp [hx, ← h]
  right_inv' y hy := by simp [hy, h]

/-- Composing two partial equivs, by restricting to the maximal domain where their composition
is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ f` for this.
-/
@[trans]
/-
**PartialEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → PartialEquiv α β → Part
ialEquiv β γ → PartialEquiv α γ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing two partial equivs, by restricting to the maximal domain where their c
omposition
is well defined.
Within the `Manifold` namespace, there is the notation `e ≫ f` for this.
-/
protected def trans : PartialEquiv α γ :=
  PartialEquiv.trans' (e.symm.restr e'.source).symm (e'.restr e.target) (inter_comm _ _)

@[simp, mfld_simps]
/-
**PartialEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：coe_trans : (e.trans e' : α -> γ) = e' ∘ e
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans : (e.trans e' : α → γ) = e' ∘ e :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.coe_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：coe_trans_symm : ((e.trans e').symm : γ -> α) = e.symm ∘ e'.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans_symm : ((e.trans e').symm : γ → α) = e.symm ∘ e'.symm :=
  rfl
/-
**PartialEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_apply {x : α} : (e.trans e') x = e' (e x)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply {x : α} : (e.trans e') x = e' (e x) :=
  rfl
/-
**PartialEquiv.trans_symm_eq_symm_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialE
quiv`。
形式化陈述：trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_symm_eq_symm_trans_symm : (e.trans e').symm = e'.symm.trans e.symm := rfl

@[simp, mfld_simps]
/-
**PartialEquiv.trans_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_source : (e.trans e').source = e.source inter e ⁻¹' e'.source
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_source : (e.trans e').source = e.source ∩ e ⁻¹' e'.source :=
  rfl
/-
**PartialEquiv.trans_source'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_source' : (e.trans e').source = e.source inter e ⁻¹' (e.target inter
 e'.source)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem trans_source' : (e.trans e').source = e.source ∩ e ⁻¹' (e.target ∩ e'.source) := by
  mfld_set_tac
/-
**PartialEquiv.trans_source''** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_source'' : (e.trans e').source = e.symm '' (e.target inter e'.source
)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_source'`：trans_source' : (e.trans e').source = e.sour
ce inter e ⁻¹' (e.target inter e'.source)
· 使用定理 `PartialEquiv.symm_image_target_inter_eq`：symm_image_target_inter_eq (s :
 Set β) : e.symm '' (e.target inter s) = e.source inter e ⁻¹' (e.target inter s)
-/
theorem trans_source'' : (e.trans e').source = e.symm '' (e.target ∩ e'.source) := by
  rw [e.trans_source', e.symm_image_target_inter_eq]
/-
**PartialEquiv.image_trans_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：image_trans_source : e '' (e.trans e').source = e.target inter e'.source
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_source_eq_target`：image_source_eq_target : e '' e.sou
rce = e.target
-/
theorem image_trans_source : e '' (e.trans e').source = e.target ∩ e'.source :=
  (e.symm.restr e'.source).symm.image_source_eq_target

@[simp, mfld_simps]
/-
**PartialEquiv.trans_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_target : (e.trans e').target = e'.target inter e'.symm ⁻¹' e.target
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_target : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' e.target :=
  rfl
/-
**PartialEquiv.trans_target'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_target' : (e.trans e').target = e'.target inter e'.symm ⁻¹' (e'.sour
ce inter e.target)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.trans_source'`：trans_source' : (e.trans e').source = e.sour
ce inter e ⁻¹' (e.target inter e'.source)
-/
theorem trans_target' : (e.trans e').target = e'.target ∩ e'.symm ⁻¹' (e'.source ∩ e.target) :=
  trans_source' e'.symm e.symm
/-
**PartialEquiv.trans_target''** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_target'' : (e.trans e').target = e' '' (e'.source inter e.target)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.trans_source''`：trans_source'' : (e.trans e').source = e.sy
mm '' (e.target inter e'.source)
-/
theorem trans_target'' : (e.trans e').target = e' '' (e'.source ∩ e.target) :=
  trans_source'' e'.symm e.symm
/-
**PartialEquiv.inv_image_trans_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source inter 
e.target
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.image_trans_source`：image_trans_source : e '' (e.trans e').
source = e.target inter e'.source
-/
theorem inv_image_trans_target : e'.symm '' (e.trans e').target = e'.source ∩ e.target :=
  image_trans_source e'.symm e.symm
/-
**PartialEquiv.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_assoc (e'' : PartialEquiv γ δ) : (e.trans e').trans e'' = e.trans (e
'.trans e'')
参数：e'' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_assoc (e'' : PartialEquiv γ δ) : (e.trans e').trans e'' = e.trans (e'.trans e'') :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [trans_source, @preimage_comp α β γ, inter_assoc])

@[simp, mfld_simps]
/-
**PartialEquiv.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_refl : e.trans (PartialEquiv.refl β) = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_refl : e.trans (PartialEquiv.refl β) = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])

@[simp, mfld_simps]
/-
**PartialEquiv.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_trans : (PartialEquiv.refl α).trans e = e
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem refl_trans : (PartialEquiv.refl α).trans e = e :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source, preimage_id])
/-
**PartialEquiv.trans_ofSet** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_ofSet (s : Set β) : e.trans (ofSet s) = e.restr (e ⁻¹' s)
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
-/
theorem trans_ofSet (s : Set β) : e.trans (ofSet s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) rfl
/-
**PartialEquiv.trans_refl_restr** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_refl_restr (s : Set β) : e.trans ((PartialEquiv.refl β).restr s) = e
.restr (e ⁻¹' s)
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_refl_restr (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) (by simp [trans_source])
/-
**PartialEquiv.trans_refl_restr'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_refl_restr' (s : Set β) : e.trans ((PartialEquiv.refl β).restr s) = 
e.restr (e.source inter e ⁻¹' s)
参数：s : Set β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
-/
theorem trans_refl_restr' (s : Set β) :
    e.trans ((PartialEquiv.refl β).restr s) = e.restr (e.source ∩ e ⁻¹' s) :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) <| by
    simp only [trans_source, restr_source, refl_source, univ_inter]
    rw [← inter_assoc, inter_self]
/-
**PartialEquiv.restr_trans** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s
参数：s : Set α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.inter_comm`：inter_comm (a b : Set α) : a inter b = b inter a
· 使用定理 `Set.inter_assoc`：inter_assoc (a b c : Set α) : a inter b inter c = a int
er (b inter c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restr_trans (s : Set α) : (e.restr s).trans e' = (e.trans e').restr s :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl) <| by
    simp [trans_source, inter_comm, inter_assoc]

/-- A lemma commonly useful when `e` and `e'` are charts of a manifold. -/
/-
**PartialEquiv.mem_symm_trans_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：mem_symm_trans_source {e' : PartialEquiv α γ} {x : α} (he : x in e.source)
 (he' : x in e'.source) : e x in (e.symm.trans e').source
参数：he : x in e.source；he' : x in e'.source。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.mapsTo`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.MapsTo (↑e) e.source e.target
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `PartialEquiv.symm_symm`：symm_symm : e.symm.symm = e
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x

--- 原说明 ---
A lemma commonly useful when `e` and `e'` are charts of a manifold.
-/
theorem mem_symm_trans_source {e' : PartialEquiv α γ} {x : α} (he : x ∈ e.source)
    (he' : x ∈ e'.source) : e x ∈ (e.symm.trans e').source :=
  ⟨e.mapsTo he, by rwa [mem_preimage, PartialEquiv.symm_symm, e.left_inv he]⟩

/-- `EqOnSource e e'` means that `e` and `e'` have the same source, and coincide there. Then `e`
and `e'` should really be considered the same partial equiv. -/
/-
**PartialEquiv.EqOnSource** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：EqOnSource (e e' : PartialEquiv α β) : Prop
参数：e e' : PartialEquiv α β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EqOnSource e e'` means that `e` and `e'` have the same source, and coincide the
re. Then `e`
and `e'` should really be considered the same partial equiv.
-/
def EqOnSource (e e' : PartialEquiv α β) : Prop :=
  e.source = e'.source ∧ e.source.EqOn e e'

/-- `EqOnSource` is an equivalence relation. This instance provides the `≈` notation between two
`PartialEquiv`s. -/
/-
**PartialEquiv.eqOnSourceSetoid** 是 Mathlib 中的一个实例，位于命名空间 `PartialEquiv`。
形式化陈述：eqOnSourceSetoid : Setoid (PartialEquiv α β) where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EqOnSource` is an equivalence relation. This instance provides the `≈` notation
 between two
`PartialEquiv`s.
-/
instance eqOnSourceSetoid : Setoid (PartialEquiv α β) where
  r := EqOnSource
  iseqv := by constructor <;> grind [EqOnSource, EqOn]
/-
**PartialEquiv.eqOnSource_refl** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：eqOnSource_refl : e ≈ e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
-/
theorem eqOnSource_refl : e ≈ e :=
  Setoid.refl _

/-- Two equivalent partial equivs have the same source. -/
/-
**PartialEquiv.EqOnSource.source_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOn
Source`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β}, e ≈ e' → e.sour
ce = e'.source
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Two equivalent partial equivs have the same source.
-/
theorem EqOnSource.source_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.source = e'.source :=
  h.1

/-- Two equivalent partial equivs coincide on the source. -/
/-
**PartialEquiv.EqOnSource.eqOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOnSourc
e`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β}, e ≈ e' → Set.Eq
On (↑e) (↑e') e.source
参数：↑e；↑e'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Two equivalent partial equivs coincide on the source.
-/
theorem EqOnSource.eqOn {e e' : PartialEquiv α β} (h : e ≈ e') : e.source.EqOn e e' :=
  h.2

/-- Two equivalent partial equivs have the same target. -/
/-
**PartialEquiv.EqOnSource.target_eq** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOn
Source`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β}, e ≈ e' → e.targ
et = e'.target
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.EqOnSource.source_eq`：∀ {α : Type u_1} {β : Type u_2} {e e'
 : PartialEquiv α β}, e ≈ e' → e.source = e'.source
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Two equivalent partial equivs have the same target.
-/
theorem EqOnSource.target_eq {e e' : PartialEquiv α β} (h : e ≈ e') : e.target = e'.target := by
  simp only [← image_source_eq_target, ← source_eq h, h.2.image_eq]

/-- If two partial equivs are equivalent, so are their inverses. -/
/-
**PartialEquiv.EqOnSource.symm'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOnSour
ce`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β}, e ≈ e' → e.symm
 ≈ e'.symm
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.EqOnSource.target_eq`：∀ {α : Type u_1} {β : Type u_2} {e e'
 : PartialEquiv α β}, e ≈ e' → e.target = e'.target
· 使用定理 `Set.eqOn_of_leftInvOn_of_rightInvOn`：eqOn_of_leftInvOn_of_rightInvOn (h₁
 : LeftInvOn f₁' f s) (h₂ : RightInvOn f₂' f t) (h : MapsTo f₂' t s) : EqOn f₁' 
f₂' t
· 使用定理 `PartialEquiv.leftInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqui
v α β), Set.LeftInvOn (↑e.symm) (↑e) e.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.RightInvOn.congr_right`：congr_right (h₁ : RightInvOn f' f₁ t) (hg : 
MapsTo f' t s) (heq : EqOn f₁ f₂ s) : RightInvOn f' f₂ t
· 使用定理 `PartialEquiv.rightInvOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEqu
iv α β), Set.RightInvOn (↑e.symm) (↑e) e.target
· 使用定理 `PartialEquiv.mapsTo_symm`：mapsTo_symm : MapsTo e.symm e.target e.source
· 使用定理 `Set.EqOn.symm`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α → 
β}, Set.EqOn f₁ f₂ s → Set.EqOn f₂ f₁ s
· 使用定理 `PartialEquiv.EqOnSource.eqOn`：∀ {α : Type u_1} {β : Type u_2} {e e' : Pa
rtialEquiv α β}, e ≈ e' → Set.EqOn (↑e) (↑e') e.source
· 使用定理 `PartialEquiv.EqOnSource.source_eq`：∀ {α : Type u_1} {β : Type u_2} {e e'
 : PartialEquiv α β}, e ≈ e' → e.source = e'.source
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
If two partial equivs are equivalent, so are their inverses.
-/
theorem EqOnSource.symm' {e e' : PartialEquiv α β} (h : e ≈ e') : e.symm ≈ e'.symm := by
  refine ⟨target_eq h, eqOn_of_leftInvOn_of_rightInvOn e.leftInvOn ?_ ?_⟩ <;>
    simp only [symm_source, target_eq h, source_eq h, e'.mapsTo_symm]
  exact e'.rightInvOn.congr_right e'.mapsTo_symm (source_eq h ▸ h.eqOn.symm)

/-- Two equivalent partial equivs have coinciding inverses on the target. -/
/-
**PartialEquiv.EqOnSource.symm_eqOn** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOn
Source`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β}, e ≈ e' → Set.Eq
On (↑e.symm) (↑e'.symm) e.target
参数：↑e.symm；↑e'.symm。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.EqOnSource.eqOn`：∀ {α : Type u_1} {β : Type u_2} {e e' : Pa
rtialEquiv α β}, e ≈ e' → Set.EqOn (↑e) (↑e') e.source
· 使用定理 `PartialEquiv.EqOnSource.symm'`：∀ {α : Type u_1} {β : Type u_2} {e e' : P
artialEquiv α β}, e ≈ e' → e.symm ≈ e'.symm

--- 原说明 ---
Two equivalent partial equivs have coinciding inverses on the target.
-/
theorem EqOnSource.symm_eqOn {e e' : PartialEquiv α β} (h : e ≈ e') :
    EqOn e.symm e'.symm e.target :=
  eqOn h.symm'

/-- Composition of partial equivs respects equivalence. -/
/-
**PartialEquiv.EqOnSource.trans'** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOnSou
rce`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {e e' : PartialEquiv α β} {
f f' : PartialEquiv β γ},   e ≈ e' → f ≈ f' → e.trans f ≈ e'.trans f'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.trans_source''`：trans_source'' : (e.trans e').source = e.sy
mm '' (e.target inter e'.source)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PartialEquiv.EqOnSource.target_eq`：∀ {α : Type u_1} {β : Type u_2} {e e'
 : PartialEquiv α β}, e ≈ e' → e.target = e'.target
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.EqOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : 
α → β}, Set.EqOn f₁ f₂ s → f₁ '' s = f₂ '' s
· 使用定理 `Set.EqOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {f₁ f₂ : 
α → β}, s₁ ⊆ s₂ → Set.EqOn f₁ f₂ s₂ → Set.EqOn f₁ f₂ s₁
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `PartialEquiv.EqOnSource.eqOn`：∀ {α : Type u_1} {β : Type u_2} {e e' : Pa
rtialEquiv α β}, e ≈ e' → Set.EqOn (↑e) (↑e') e.source
· 使用定理 `PartialEquiv.EqOnSource.symm'`：∀ {α : Type u_1} {β : Type u_2} {e e' : P
artialEquiv α β}, e ≈ e' → e.symm ≈ e'.symm
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `PartialEquiv.trans_source`：trans_source : (e.trans e').source = e.source
 inter e ⁻¹' e'.source
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Composition of partial equivs respects equivalence.
-/
theorem EqOnSource.trans' {e e' : PartialEquiv α β} {f f' : PartialEquiv β γ} (he : e ≈ e')
    (hf : f ≈ f') : e.trans f ≈ e'.trans f' := by
  constructor
  · rw [trans_source'', trans_source'', ← target_eq he, ← hf.1]
    exact (he.symm'.eqOn.mono inter_subset_left).image_eq
  · intro x hx
    rw [trans_source] at hx
    simp [Function.comp_apply, PartialEquiv.coe_trans, (he.2 hx.1).symm, hf.2 hx.2]

/-- Restriction of partial equivs respects equivalence. -/
/-
**PartialEquiv.EqOnSource.restr** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv.EqOnSour
ce`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β}, e ≈ e' → ∀ (s :
 Set α), e.restr s ≈ e'.restr s
参数：s : Set α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Restriction of partial equivs respects equivalence.
-/
theorem EqOnSource.restr {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set α) :
    e.restr s ≈ e'.restr s := by
  constructor
  · simp [he.1]
  · intro x hx
    simp only [mem_inter_iff, restr_source] at hx
    exact he.2 hx.1

/-- Preimages are respected by equivalence. -/
/-
**PartialEquiv.EqOnSource.source_inter_preimage_eq** 是 Mathlib 中的一个定理，位于命名空间 `Pa
rtialEquiv.EqOnSource`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α β},   e ≈ e' → ∀ (s
 : Set β), e.source ∩ ↑e ⁻¹' s = e'.source ∩ ↑e' ⁻¹' s
参数：s : Set β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.EqOn.inter_preimage_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} 
{f₁ f₂ : α → β},   Set.EqOn f₁ f₂ s → ∀ (t : Set β), s ∩ f₁ ⁻¹' t = s ∩ f₂ ⁻¹' t
· 使用定理 `PartialEquiv.EqOnSource.eqOn`：∀ {α : Type u_1} {β : Type u_2} {e e' : Pa
rtialEquiv α β}, e ≈ e' → Set.EqOn (↑e) (↑e') e.source
· 使用定理 `PartialEquiv.EqOnSource.source_eq`：∀ {α : Type u_1} {β : Type u_2} {e e'
 : PartialEquiv α β}, e ≈ e' → e.source = e'.source

--- 原说明 ---
Preimages are respected by equivalence.
-/
theorem EqOnSource.source_inter_preimage_eq {e e' : PartialEquiv α β} (he : e ≈ e') (s : Set β) :
    e.source ∩ e ⁻¹' s = e'.source ∩ e' ⁻¹' s := by rw [he.eqOn.inter_preimage_eq, source_eq he]

/-- Composition of a partial equivalence and its inverse is equivalent to
the restriction of the identity to the source. -/
/-
**PartialEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：self_trans_symm : e.trans e.symm ≈ ofSet e.source
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `PartialEquiv.ofSet_source`：ofSet_source (s : Set α) : (PartialEquiv.ofSe
t s).source = s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.left_inv`：left_inv {x : α} (h : x in e.source) : e.symm (e 
x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Composition of a partial equivalence and its inverse is equivalent to
the restriction of the identity to the source.
-/
theorem self_trans_symm : e.trans e.symm ≈ ofSet e.source := by
  have A : (e.trans e.symm).source = e.source := by mfld_set_tac
  refine ⟨by rw [A, ofSet_source], fun x hx => ?_⟩
  rw [A] at hx
  simp only [hx, mfld_simps]

/-- Composition of the inverse of a partial equivalence and this partial equivalence is equivalent
to the restriction of the identity to the target. -/
/-
**PartialEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_trans_self : e.symm.trans e ≈ ofSet e.target
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.self_trans_symm`：self_trans_symm : e.trans e.symm ≈ ofSet e
.source

--- 原说明 ---
Composition of the inverse of a partial equivalence and this partial equivalence
 is equivalent
to the restriction of the identity to the target.
-/
theorem symm_trans_self : e.symm.trans e ≈ ofSet e.target :=
  self_trans_symm e.symm

/-- Two equivalent partial equivs are equal when the source and target are `univ`. -/
/-
**PartialEquiv.eq_of_eqOnSource_univ** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：eq_of_eqOnSource_univ (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source
 = univ) (t : e.target = univ) : e = e'
参数：e e' : PartialEquiv α β；h : e ≈ e'；s : e.source = univ；t : e.target = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `PartialEquiv.EqOnSource.symm'`：∀ {α : Type u_1} {β : Type u_2} {e e' : P
artialEquiv α β}, e ≈ e' → e.symm ≈ e'.symm
· 使用定理 `PartialEquiv.symm_source`：symm_source : e.symm.source = e.target
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Two equivalent partial equivs are equal when the source and target are `univ`.
-/
theorem eq_of_eqOnSource_univ (e e' : PartialEquiv α β) (h : e ≈ e') (s : e.source = univ)
    (t : e.target = univ) : e = e' := by
  refine PartialEquiv.ext (fun x => ?_) (fun x => ?_) h.1
  · apply h.2
    rw [s]
    exact mem_univ _
  · apply h.symm'.2
    rw [symm_source, t]
    exact mem_univ _

section Prod

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- The product of two partial equivalences, as a partial equivalence on the product. -/
/-
**PartialEquiv.prod** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：prod (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : PartialEquiv (α × γ)
 (β × δ) where source
参数：e : PartialEquiv α β；e' : PartialEquiv γ δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two partial equivalences, as a partial equivalence on the product
.
-/
def prod (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : PartialEquiv (α × γ) (β × δ) where
  source := e.source ×ˢ e'.source
  target := e.target ×ˢ e'.target
  toFun p := (e p.1, e' p.2)
  invFun p := (e.symm p.1, e'.symm p.2)
  map_source' p hp := by simp_all
  map_target' p hp := by simp_all
  left_inv' p hp   := by simp_all
  right_inv' p hp  := by simp_all

@[simp, mfld_simps]
/-
**PartialEquiv.prod_source** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：prod_source (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : (e.prod e').s
ource = e.source ×ˢ e'.source
参数：e : PartialEquiv α β；e' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_source (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').source = e.source ×ˢ e'.source :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.prod_target** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：prod_target (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : (e.prod e').t
arget = e.target ×ˢ e'.target
参数：e : PartialEquiv α β；e' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_target (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').target = e.target ×ˢ e'.target :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.prod_coe** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：prod_coe (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : (e.prod e' : α ×
 γ -> β × δ) = fun p => (e p.1, e' p.2)
参数：e : PartialEquiv α β；e' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e' : α × γ → β × δ) = fun p => (e p.1, e' p.2) :=
  rfl
/-
**PartialEquiv.prod_coe_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：prod_coe_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : ((e.prod e'
).symm : β × δ -> α × γ) = fun p => (e.symm p.1, e'.symm p.2)
参数：e : PartialEquiv α β；e' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prod_coe_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    ((e.prod e').symm : β × δ → α × γ) = fun p => (e.symm p.1, e'.symm p.2) :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.prod_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：prod_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) : (e.prod e').sym
m = e.symm.prod e'.symm
参数：e : PartialEquiv α β；e' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_symm (e : PartialEquiv α β) (e' : PartialEquiv γ δ) :
    (e.prod e').symm = e.symm.prod e'.symm := by
  ext x <;> simp [prod_coe_symm]

@[simp, mfld_simps]
/-
**PartialEquiv.refl_prod_refl** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：refl_prod_refl : (PartialEquiv.refl α).prod (PartialEquiv.refl β) = Partia
lEquiv.refl (α × β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.prod_symm`：prod_symm (e : PartialEquiv α β) (e' : PartialEq
uiv γ δ) : (e.prod e').symm = e.symm.prod e'.symm
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.univ_prod_univ`：univ_prod_univ : @univ α ×ˢ @univ β = univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem refl_prod_refl :
    (PartialEquiv.refl α).prod (PartialEquiv.refl β) = PartialEquiv.refl (α × β) := by
  ext ⟨x, y⟩ <;> simp

@[simp, mfld_simps]
/-
**PartialEquiv.prod_trans** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：prod_trans {η : Type*} {ε : Type*} (e : PartialEquiv α β) (f : PartialEqui
v β γ) (e' : PartialEquiv δ η) (f' : PartialEquiv η ε) : (e.prod e').trans (f.pr
od f') = (e.trans f).prod (e'.trans f')
参数：e : PartialEquiv α β；f : PartialEquiv β γ；e' : PartialEquiv δ η；f' : PartialE
quiv η ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `Prod.ext`：∀ {α : Type u} {β : Type v} {x y : α × β}, x.1 = y.1 → x.2 = y
.2 → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.prod_symm`：prod_symm (e : PartialEquiv α β) (e' : PartialEq
uiv γ δ) : (e.prod e').symm = e.symm.prod e'.symm
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
-/
theorem prod_trans {η : Type*} {ε : Type*} (e : PartialEquiv α β) (f : PartialEquiv β γ)
    (e' : PartialEquiv δ η) (f' : PartialEquiv η ε) :
    (e.prod e').trans (f.prod f') = (e.trans f).prod (e'.trans f') := by
  ext ⟨x, y⟩ <;> simp; tauto

end Prod

/-- Combine two `PartialEquiv`s using `Set.piecewise`. The source of the new `PartialEquiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for target.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.target \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.isImage s t` and
`e'.isImage s t`. -/
@[simps -fullyApplied]
/-
**PartialEquiv.piecewise** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：piecewise (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [forall x, Dec
idable (x in s)] [forall y, Decidable (y in t)] (H : e.IsImage s t) (H' : e'.IsI
mage s t) : PartialEquiv α β where toFun
参数：e e' : PartialEquiv α β；s : Set α；t : Set β；x in s；y in t；H : e.IsImage s t；H
' : e'.IsImage s t。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.IsImage.leftInvOn_piecewise`：leftInvOn_piecewise {e' : Part
ialEquiv α β} [forall i, Decidable (i in s)] [forall i, Decidable (i in t)] (h :
 e.IsImage s t) (h' : e'.IsIma…

--- 原说明 ---
Combine two `PartialEquiv`s using `Set.piecewise`. The source of the new `Partia
lEquiv` is
`s.ite e.source e'.source = e.source ∩ s ∪ e'.source \ s`, and similarly for tar
get.  The function
sends `e.source ∩ s` to `e.target ∩ t` using `e` and `e'.source \ s` to `e'.targ
et \ t` using `e'`,
and similarly for the inverse function. The definition assumes `e.isImage s t` a
nd
`e'.isImage s t`.
-/
def piecewise (e e' : PartialEquiv α β) (s : Set α) (t : Set β) [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    PartialEquiv α β where
  toFun := s.piecewise e e'
  invFun := t.piecewise e.symm e'.symm
  source := s.ite e.source e'.source
  target := t.ite e.target e'.target
  map_source' := H.mapsTo.piecewise_ite H'.compl.mapsTo
  map_target' := H.symm.mapsTo.piecewise_ite H'.symm.compl.mapsTo
  left_inv' := H.leftInvOn_piecewise H'
  right_inv' := H.symm.leftInvOn_piecewise H'.symm
/-
**PartialEquiv.symm_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：symm_piecewise (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [forall x
, Decidable (x in s)] [forall y, Decidable (y in t)] (H : e.IsImage s t) (H' : e
'.IsImage s t) : (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H
.symm H'.symm
参数：e e' : PartialEquiv α β；x in s；y in t；H : e.IsImage s t；H' : e'.IsImage s t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_piecewise (e e' : PartialEquiv α β) {s : Set α} {t : Set β} [∀ x, Decidable (x ∈ s)]
    [∀ y, Decidable (y ∈ t)] (H : e.IsImage s t) (H' : e'.IsImage s t) :
    (e.piecewise e' s t H H').symm = e.symm.piecewise e'.symm t s H.symm H'.symm :=
  rfl

/-- Combine two `PartialEquiv`s with disjoint sources and disjoint targets. We reuse
`PartialEquiv.piecewise`, then override `source` and `target` to ensure better definitional
equalities. -/
@[simps! -fullyApplied]
/-
**PartialEquiv.disjointUnion** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：disjointUnion (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
 (ht : Disjoint e.target e'.target) [forall x, Decidable (x in e.source)] [foral
l y, Decidable (y in e.target)] : PartialEquiv α β
参数：e e' : PartialEquiv α β；hs : Disjoint e.source e'.source；ht : Disjoint e.targ
et e'.target；x in e.source；y in e.target。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.isImage_source_target`：isImage_source_target : e.IsImage e.
source e.target

--- 原说明 ---
Combine two `PartialEquiv`s with disjoint sources and disjoint targets. We reuse
`PartialEquiv.piecewise`, then override `source` and `target` to ensure better d
efinitional
equalities.
-/
def disjointUnion (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] : PartialEquiv α β :=
  (e.piecewise e' e.source e.target e.isImage_source_target <|
        e'.isImage_source_target_of_disjoint _ hs.symm ht.symm).copy
    _ rfl _ rfl (e.source ∪ e'.source) (ite_left _ _) (e.target ∪ e'.target) (ite_left _ _)
/-
**PartialEquiv.disjointUnion_eq_piecewise** 是 Mathlib 中的一个定理，位于命名空间 `PartialEqui
v`。
形式化陈述：disjointUnion_eq_piecewise (e e' : PartialEquiv α β) (hs : Disjoint e.sour
ce e'.source) (ht : Disjoint e.target e'.target) [forall x, Decidable (x in e.so
urce)] [forall y, Decidable (y in e.target)] : e.disjointUnion e' hs ht = e.piec
ewise e' e.source e.target e.isImage_source_target (e'.isImage_source_target_of_
disjoint _ hs.symm ht.symm)
参数：e e' : PartialEquiv α β；hs : Disjoint e.source e'.source；ht : Disjoint e.targ
et e'.target；x in e.source；y in e.target。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.copy_eq`：copy_eq (e : PartialEquiv α β) (f : α -> β) (hf : 
⇑e = f) (g : β -> α) (hg : ⇑e.symm = g) (s : Set α) (hs : e.source = s) (t : Set
 β) (ht : …
· 使用定理 `PartialEquiv.isImage_source_target`：isImage_source_target : e.IsImage e.
source e.target
-/
theorem disjointUnion_eq_piecewise (e e' : PartialEquiv α β) (hs : Disjoint e.source e'.source)
    (ht : Disjoint e.target e'.target) [∀ x, Decidable (x ∈ e.source)]
    [∀ y, Decidable (y ∈ e.target)] :
    e.disjointUnion e' hs ht =
      e.piecewise e' e.source e.target e.isImage_source_target
        (e'.isImage_source_target_of_disjoint _ hs.symm ht.symm) :=
  copy_eq ..

section Pi

variable {ι : Type*} {αi βi γi : ι → Type*}

/-- The product of a family of partial equivalences, as a partial equivalence on the pi type. -/
@[simps (attr := mfld_simps) -fullyApplied apply source target]
/-
**PartialEquiv.pi** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：{ι : Type u_5} →   {αi : ι → Type u_6} →     {βi : ι → Type u_7} → ((i : ι
) → PartialEquiv (αi i) (βi i)) → PartialEquiv ((i : ι) → αi i) ((i : ι) → βi i)
参数：(i : ι) → PartialEquiv (αi i) (βi i)；(i : ι) → αi i；(i : ι) → βi i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of a family of partial equivalences, as a partial equivalence on the
 pi type.
-/
protected def pi (ei : ∀ i, PartialEquiv (αi i) (βi i)) : PartialEquiv (∀ i, αi i) (∀ i, βi i) where
  toFun := Pi.map fun i ↦ ei i
  invFun := Pi.map fun i ↦ (ei i).symm
  source := pi univ fun i => (ei i).source
  target := pi univ fun i => (ei i).target
  map_source' _ hf i hi := (ei i).map_source (hf i hi)
  map_target' _ hf i hi := (ei i).map_target (hf i hi)
  left_inv' _ hf := funext fun i => (ei i).left_inv (hf i trivial)
  right_inv' _ hf := funext fun i => (ei i).right_inv (hf i trivial)

@[simp, mfld_simps]
/-
**PartialEquiv.pi_symm** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：pi_symm (ei : forall i, PartialEquiv (αi i) (βi i)) : (PartialEquiv.pi ei)
.symm = .pi fun i => (ei i).symm
参数：ei : forall i, PartialEquiv (αi i) (βi i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_symm (ei : ∀ i, PartialEquiv (αi i) (βi i)) :
    (PartialEquiv.pi ei).symm = .pi fun i ↦ (ei i).symm :=
  rfl
/-
**PartialEquiv.pi_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：pi_symm_apply (ei : forall i, PartialEquiv (αi i) (βi i)) : ⇑(PartialEquiv
.pi ei).symm = fun f i => (ei i).symm (f i)
参数：ei : forall i, PartialEquiv (αi i) (βi i)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pi_symm_apply (ei : ∀ i, PartialEquiv (αi i) (βi i)) :
    ⇑(PartialEquiv.pi ei).symm = fun f i ↦ (ei i).symm (f i) :=
  rfl

@[simp, mfld_simps]
/-
**PartialEquiv.pi_refl** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：pi_refl : (PartialEquiv.pi fun i => PartialEquiv.refl (αi i)) = .refl (for
all i, αi i)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.pi_apply`：∀ {ι : Type u_5} {αi : ι → Type u_6} {βi : ι → Ty
pe u_7} (ei : (i : ι) → PartialEquiv (αi i) (βi i)),   ↑(PartialEquiv.pi ei) = P
i.map fun i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `PartialEquiv.pi_source`：∀ {ι : Type u_5} {αi : ι → Type u_6} {βi : ι → T
ype u_7} (ei : (i : ι) → PartialEquiv (αi i) (βi i)),   (PartialEquiv.pi ei).sou
rce = Set.un…
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_refl : (PartialEquiv.pi fun i ↦ PartialEquiv.refl (αi i)) = .refl (∀ i, αi i) := by
  ext <;> simp

@[simp, mfld_simps]
/-
**PartialEquiv.pi_trans** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：pi_trans (ei : forall i, PartialEquiv (αi i) (βi i)) (ei' : forall i, Part
ialEquiv (βi i) (γi i)) : (PartialEquiv.pi ei).trans (PartialEquiv.pi ei') = .pi
 fun i => (ei i).trans (ei' i)
参数：ei : forall i, PartialEquiv (αi i) (βi i)；ei' : forall i, PartialEquiv (βi i)
 (γi i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.pi_apply`：∀ {ι : Type u_5} {αi : ι → Type u_6} {βi : ι → Ty
pe u_7} (ei : (i : ι) → PartialEquiv (αi i) (βi i)),   ↑(PartialEquiv.pi ei) = P
i.map fun i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `PartialEquiv.pi_source`：∀ {ι : Type u_5} {αi : ι → Type u_6} {βi : ι → T
ype u_7} (ei : (i : ι) → PartialEquiv (αi i) (βi i)),   (PartialEquiv.pi ei).sou
rce = Set.un…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem pi_trans (ei : ∀ i, PartialEquiv (αi i) (βi i)) (ei' : ∀ i, PartialEquiv (βi i) (γi i)) :
    (PartialEquiv.pi ei).trans (PartialEquiv.pi ei') = .pi fun i ↦ (ei i).trans (ei' i) := by
  ext <;> simp [forall_and]

end Pi

/-
**PartialEquiv.surjective_of_target_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `PartialEq
uiv`。
形式化陈述：surjective_of_target_eq_univ (h : e.target = univ) : Surjective e
参数：h : e.target = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.surjOn_univ`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, Set.SurjOn
 f Set.univ Set.univ ↔ Function.Surjective f
· 使用定理 `Set.SurjOn.mono`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} {t₁ t₂ 
: Set β} {f : α → β},   s₁ ⊆ s₂ → t₁ ⊆ t₂ → Set.SurjOn f s₁ t₂ → Set.SurjOn f s₂
 t₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.surjOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α
 β), Set.SurjOn (↑e) e.source e.target
-/
lemma surjective_of_target_eq_univ (h : e.target = univ) :
    Surjective e :=
  surjOn_univ.mp <| e.surjOn.mono (by simp) (by simp [h])
/-
**PartialEquiv.injective_of_source_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `PartialEqu
iv`。
形式化陈述：injective_of_source_eq_univ (h : e.source = univ) : Injective e
参数：h : e.source = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.injOn`：∀ {α : Type u_1} {β : Type u_2} (e : PartialEquiv α 
β), Set.InjOn (↑e) e.source
-/
lemma injective_of_source_eq_univ (h : e.source = univ) : Injective e := by simpa [h] using e.injOn
/-
**PartialEquiv.injective_symm_of_target_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Parti
alEquiv`。
形式化陈述：injective_symm_of_target_eq_univ (h : e.target = univ) : Injective e.symm
参数：h : e.target = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialEquiv.injective_of_source_eq_univ`：injective_of_source_eq_univ (h
 : e.source = univ) : Injective e
-/
lemma injective_symm_of_target_eq_univ (h : e.target = univ) :
    Injective e.symm :=
  e.symm.injective_of_source_eq_univ h
/-
**PartialEquiv.surjective_symm_of_source_eq_univ** 是 Mathlib 中的一个引理，位于命名空间 `Part
ialEquiv`。
形式化陈述：surjective_symm_of_source_eq_univ (h : e.source = univ) : Surjective e.sym
m
参数：h : e.source = univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `PartialEquiv.surjective_of_target_eq_univ`：surjective_of_target_eq_univ 
(h : e.target = univ) : Surjective e
-/
lemma surjective_symm_of_source_eq_univ (h : e.source = univ) :
    Surjective e.symm :=
  e.symm.surjective_of_target_eq_univ h

end PartialEquiv

namespace Set

-- All arguments are explicit to avoid missing information in the pretty printer output
/-- A bijection between two sets `s : Set α` and `t : Set β` provides a partial equivalence
between `α` and `β`. -/
@[simps -fullyApplied]
/-
**Set.BijOn.toPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set.BijOn`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} → [Nonempty α] → (f : α → β) → (s : Set 
α) → (t : Set β) → Set.BijOn f s t → PartialEquiv α β
参数：f : α → β；s : Set α；t : Set β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.BijOn.mapsTo`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set β
} {f : α → β}, Set.BijOn f s t → Set.MapsTo f s t

--- 原说明 ---
A bijection between two sets `s : Set α` and `t : Set β` provides a partial equi
valence
between `α` and `β`.
-/
noncomputable def BijOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (t : Set β)
    (hf : BijOn f s t) : PartialEquiv α β where
  toFun := f
  invFun := invFunOn f s
  source := s
  target := t
  map_source' := hf.mapsTo
  map_target' := hf.surjOn.mapsTo_invFunOn
  left_inv' := hf.invOn_invFunOn.1
  right_inv' := hf.invOn_invFunOn.2

/-- A map injective on a subset of its domain provides a partial equivalence. -/
@[simp, mfld_simps]
/-
**Set.InjOn.toPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Set.InjOn`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → [Nonempty α] → (f : α → β) → (s : Set α)
 → Set.InjOn f s → PartialEquiv α β
参数：f : α → β；s : Set α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Set.InjOn.bijOn_image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f : 
α → β}, Set.InjOn f s → Set.BijOn f s (f '' s)

--- 原说明 ---
A map injective on a subset of its domain provides a partial equivalence.
-/
noncomputable def InjOn.toPartialEquiv [Nonempty α] (f : α → β) (s : Set α) (hf : InjOn f s) :
    PartialEquiv α β :=
  hf.bijOn_image.toPartialEquiv f s (f '' s)

end Set

namespace Equiv

/- `Equiv`s give rise to `PartialEquiv`s. We set up simp lemmas to reduce most properties of the
`PartialEquiv` to that of the `Equiv`. -/
variable (e : α ≃ β) (e' : β ≃ γ)

@[simp, mfld_simps]
/-
**Equiv.refl_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：refl_toPartialEquiv : (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem refl_toPartialEquiv : (Equiv.refl α).toPartialEquiv = PartialEquiv.refl α :=
  rfl

@[simp, mfld_simps]
/-
**Equiv.symm_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_toPartialEquiv : e.symm.toPartialEquiv = e.toPartialEquiv.symm :=
  rfl

@[simp, mfld_simps]
/-
**Equiv.trans_toPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_toPartialEquiv : (e.trans e').toPartialEquiv = e.toPartialEquiv.tran
s e'.toPartialEquiv
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.ext`：∀ {α : Type u_1} {β : Type u_2} {e e' : PartialEquiv α
 β},   (∀ (x : α), ↑e x = ↑e' x) → (∀ (x : β), ↑e.symm x = ↑e'.symm x) → e.sourc
e = e'…
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.toPartialEquivOfImageEq_source`：∀ {α : Type u_1} {β : Type u_2} (e
 : α ≃ β) (s : Set α) (t : Set β) (h : ⇑e '' s = t),   (e.toPartialEquivOfImageE
q s t h).source = s
· 使用定理 `Equiv.toPartialEquivOfImageEq_apply`：∀ {α : Type u_1} {β : Type u_2} (e 
: α ≃ β) (s : Set α) (t : Set β) (h : ⇑e '' s = t),   ↑(e.toPartialEquivOfImageE
q s t h) = ⇑e
· 使用定理 `Set.inter_self`：inter_self (a : Set α) : a inter a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_toPartialEquiv :
    (e.trans e').toPartialEquiv = e.toPartialEquiv.trans e'.toPartialEquiv :=
  PartialEquiv.ext (fun _ => rfl) (fun _ => rfl)
    (by simp [PartialEquiv.trans_source, Equiv.toPartialEquiv])

/-- Precompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
/-
**Equiv.transPartialEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：transPartialEquiv (e : α ≃ β) (f' : PartialEquiv β γ) : PartialEquiv α γ
参数：e : α ≃ β；f' : PartialEquiv β γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Precompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior.
-/
def transPartialEquiv (e : α ≃ β) (f' : PartialEquiv β γ) : PartialEquiv α γ :=
  (e.toPartialEquiv.trans f').copy _ rfl _ rfl (e ⁻¹' f'.source) (univ_inter _) f'.target
    (inter_univ _)
/-
**Equiv.transPartialEquiv_eq_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：transPartialEquiv_eq_trans (e : α ≃ β) (f' : PartialEquiv β γ) : e.transPa
rtialEquiv f' = e.toPartialEquiv.trans f'
参数：e : α ≃ β；f' : PartialEquiv β γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.copy_eq`：copy_eq (e : PartialEquiv α β) (f : α -> β) (hf : 
⇑e = f) (g : β -> α) (hg : ⇑e.symm = g) (s : Set α) (hs : e.source = s) (t : Set
 β) (ht : …
-/
theorem transPartialEquiv_eq_trans (e : α ≃ β) (f' : PartialEquiv β γ) :
    e.transPartialEquiv f' = e.toPartialEquiv.trans f' :=
  PartialEquiv.copy_eq ..

@[simp, mfld_simps]
/-
**Equiv.transPartialEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：transPartialEquiv_trans (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : Partial
Equiv γ δ) : (e.transPartialEquiv f').trans f'' = e.transPartialEquiv (f'.trans 
f'')
参数：e : α ≃ β；f' : PartialEquiv β γ；f'' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.transPartialEquiv_eq_trans`：transPartialEquiv_eq_trans (e : α ≃ β)
 (f' : PartialEquiv β γ) : e.transPartialEquiv f' = e.toPartialEquiv.trans f'
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transPartialEquiv_trans (e : α ≃ β) (f' : PartialEquiv β γ) (f'' : PartialEquiv γ δ) :
    (e.transPartialEquiv f').trans f'' = e.transPartialEquiv (f'.trans f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc]

@[simp, mfld_simps]
/-
**Equiv.trans_transPartialEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：trans_transPartialEquiv (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ) 
: (e.trans e').transPartialEquiv f'' = e.transPartialEquiv (e'.transPartialEquiv
 f'')
参数：e : α ≃ β；e' : β ≃ γ；f'' : PartialEquiv γ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.transPartialEquiv_eq_trans`：transPartialEquiv_eq_trans (e : α ≃ β)
 (f' : PartialEquiv β γ) : e.transPartialEquiv f' = e.toPartialEquiv.trans f'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.trans_toPartialEquiv`：trans_toPartialEquiv : (e.trans e').toPartia
lEquiv = e.toPartialEquiv.trans e'.toPartialEquiv
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_transPartialEquiv (e : α ≃ β) (e' : β ≃ γ) (f'' : PartialEquiv γ δ) :
    (e.trans e').transPartialEquiv f'' = e.transPartialEquiv (e'.transPartialEquiv f'') := by
  simp only [transPartialEquiv_eq_trans, PartialEquiv.trans_assoc, trans_toPartialEquiv]

@[simp]
/-
**Equiv.coe_transPartialEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：coe_transPartialEquiv {f : α ≃ β} {g : PartialEquiv β γ} : f.transPartialE
quiv g = g ∘ f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_transPartialEquiv {f : α ≃ β} {g : PartialEquiv β γ} : f.transPartialEquiv g = g ∘ f :=
  rfl

@[simp]
/-
**Equiv.coe_transPartialEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `Equiv`。
形式化陈述：coe_transPartialEquiv_symm {f : α ≃ β} {g : PartialEquiv β γ} : (f.transPa
rtialEquiv g).symm = f.symm ∘ g.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_transPartialEquiv_symm {f : α ≃ β} {g : PartialEquiv β γ} :
    (f.transPartialEquiv g).symm = f.symm ∘ g.symm :=
  rfl

end Equiv

namespace PartialEquiv

/-- Postcompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior. -/
@[simps!]
/-
**PartialEquiv.transEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PartialEquiv`。
形式化陈述：transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) : PartialEquiv α γ
参数：e : PartialEquiv α β；f' : β ≃ γ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Postcompose a partial equivalence with an equivalence.
We modify the source and target to have better definitional behavior.
-/
def transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) : PartialEquiv α γ :=
  (e.trans f'.toPartialEquiv).copy _ rfl _ rfl e.source (inter_univ _) (f'.symm ⁻¹' e.target)
    (univ_inter _)
/-
**PartialEquiv.transEquiv_eq_trans** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：transEquiv_eq_trans (e : PartialEquiv α β) (e' : β ≃ γ) : e.transEquiv e' 
= e.trans e'.toPartialEquiv
参数：e : PartialEquiv α β；e' : β ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PartialEquiv.copy_eq`：copy_eq (e : PartialEquiv α β) (f : α -> β) (hf : 
⇑e = f) (g : β -> α) (hg : ⇑e.symm = g) (s : Set α) (hs : e.source = s) (t : Set
 β) (ht : …
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem transEquiv_eq_trans (e : PartialEquiv α β) (e' : β ≃ γ) :
    e.transEquiv e' = e.trans e'.toPartialEquiv :=
  copy_eq ..

@[simp, mfld_simps]
/-
**PartialEquiv.transEquiv_transEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：transEquiv_transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ) : 
(e.transEquiv f').transEquiv f'' = e.transEquiv (f'.trans f'')
参数：e : PartialEquiv α β；f' : β ≃ γ；f'' : γ ≃ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PartialEquiv.transEquiv_eq_trans`：transEquiv_eq_trans (e : PartialEquiv 
α β) (e' : β ≃ γ) : e.transEquiv e' = e.trans e'.toPartialEquiv
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `Equiv.trans_toPartialEquiv`：trans_toPartialEquiv : (e.trans e').toPartia
lEquiv = e.toPartialEquiv.trans e'.toPartialEquiv
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem transEquiv_transEquiv (e : PartialEquiv α β) (f' : β ≃ γ) (f'' : γ ≃ δ) :
    (e.transEquiv f').transEquiv f'' = e.transEquiv (f'.trans f'') := by
  simp only [transEquiv_eq_trans, trans_assoc, Equiv.trans_toPartialEquiv]

@[simp, mfld_simps]
/-
**PartialEquiv.trans_transEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：trans_transEquiv (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃
 δ) : (e.trans e').transEquiv f'' = e.trans (e'.transEquiv f'')
参数：e : PartialEquiv α β；e' : PartialEquiv β γ；f'' : γ ≃ δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PartialEquiv.transEquiv_eq_trans`：transEquiv_eq_trans (e : PartialEquiv 
α β) (e' : β ≃ γ) : e.transEquiv e' = e.trans e'.toPartialEquiv
· 使用定理 `PartialEquiv.trans_assoc`：trans_assoc (e'' : PartialEquiv γ δ) : (e.tran
s e').trans e'' = e.trans (e'.trans e'')
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem trans_transEquiv (e : PartialEquiv α β) (e' : PartialEquiv β γ) (f'' : γ ≃ δ) :
    (e.trans e').transEquiv f'' = e.trans (e'.transEquiv f'') := by
  simp only [transEquiv_eq_trans, trans_assoc]
/-
**PartialEquiv.coe_transEquiv** 是 Mathlib 中的一个定理，位于命名空间 `PartialEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f : PartialEquiv α β} {g :
 β ≃ γ}, ↑(f.transEquiv g) = ⇑g ∘ ↑f
参数：f.transEquiv g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_transEquiv {f : PartialEquiv α β} {g : β ≃ γ} : f.transEquiv g = g ∘ f := rfl

@[simp]
/-
**PartialEquiv.coe_transEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `PartialEquiv`。
形式化陈述：coe_transEquiv_symm {f : PartialEquiv α β} {g : β ≃ γ} : (f.transEquiv g).
symm = f.symm ∘ g.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_transEquiv_symm {f : PartialEquiv α β} {g : β ≃ γ} :
    (f.transEquiv g).symm = f.symm ∘ g.symm :=
  rfl

end PartialEquiv

