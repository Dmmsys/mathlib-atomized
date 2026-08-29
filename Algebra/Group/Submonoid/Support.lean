/-
Copyright (c) 2026 Artie Khovanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Artie Khovanov
-/
module

public import Mathlib.Algebra.Group.Subgroup.Pointwise
public import Mathlib.Algebra.Group.Subgroup.Lattice

import Mathlib.Tactic.ApplyFun

/-!
# Supports of submonoids

Let `G` be an (additive) group, and let `M` be a submonoid of `G`.
The *support* of `M` is `M ∩ -M`, the largest subgroup of `G` contained in `M`.
A submonoid `C` is *pointed*, or a *positive cone*, if it has zero support.
A submonoid `C` is *spanning* if the subgroup it generates is `G` itself.

The names for these concepts are taken from the theory of convex cones.

## Main definitions

* `AddSubmonoid.support`: the support of a submonoid.
* `AddSubmonoid.IsPointed`: typeclass for submonoids with zero support.
* `AddSubmonoid.IsSpanning`: typeclass for submonoids generating the whole group.

-/

@[expose] public section

namespace Submonoid

open scoped Pointwise

variable {G : Type*} [Group G] (M : Submonoid G)

/--
The support of a submonoid `M` of a group `G` is `M ∩ M⁻¹`,
the largest subgroup of `G` contained in `M`.
-/
@[to_additive (attr := simps!)
/-- The support of a submonoid `M` of a group `G` is `M ∩ -M`,
the largest subgroup of `G` contained in `M`. -/]
/--
Definition of `mulSupport` / `mulSupport` 的定义

English:
definition mulSupport
  signature: : Subgroup G where
  body: M ⊓ M⁻¹
  inv_mem' := by aesop

中文:
定义 mulSupport
  签名: : 子群 G where
  定义体: M ⊓ M⁻¹
  inv_mem' := by aesop
-/
def mulSupport : Subgroup G where
  toSubmonoid := M ⊓ M⁻¹
  inv_mem' := by aesop

variable {M} in
@[to_additive (attr := simp)]
/--
theorem `mem_mulSupport` / 定理 `mem_mulSupport`

English:
theorem mem_mulSupport
  given: {x}
  statement: x in M.mulSupport ↔ x in M ∧ x⁻¹ in M
  proof: .rfl

@[to_additive (attr := simp)]

中文:
定理 mem_mulSupport
  条件: {x}
  结论: x in M.mulSupport ↔ x in M ∧ x⁻¹ in M
  证明: .rfl

@[to_additive (attr := simp)]
-/
theorem mem_mulSupport {x} : x in M.mulSupport ↔ x in M ∧ x⁻¹ in M := .rfl

@[to_additive (attr := simp)]
/--
theorem `mulSupport_toSubmonoid` / 定理 `mulSupport_toSubmonoid`

English:
theorem mulSupport_toSubmonoid
  statement: M.mulSupport.toSubmonoid = M ⊓ M⁻¹
  proof: rfl

中文:
定理 mulSupport_toSubmonoid
  结论: M.mulSupport.toSubmonoid = M ⊓ M⁻¹
  证明: rfl
-/
theorem mulSupport_toSubmonoid : M.mulSupport.toSubmonoid = M ⊓ M⁻¹ := rfl

/-- The support of a submonoid is the largest subgroup it contains. -/
@[to_additive /-- The support of a submonoid is the largest subgroup it contains. -/]
/--
theorem `_root_.Subgroup.gc_toSubmonoid_mulSupport` / 定理 `_root_.Subgroup.gc_toSubmonoid_mulSupport`

English:
theorem _root_.Subgroup.gc_toSubmonoid_mulSupport
  proof: fun _ _ => ⟨fun _ _ => by aesop, fun h _ hx => (h hx).1⟩

中文:
定理 _root_.子群.gc_toSubmonoid_mulSupport
  证明: fun _ _ => ⟨fun _ _ => by aesop, fun h _ hx => (h hx).1⟩

Depends on / 依赖: Subgroup, Subgroup.toSubmonoid, mulSupport, toSubmonoid
-/
theorem _root_.Subgroup.gc_toSubmonoid_mulSupport :
    GaloisConnection (α := Subgroup G) Subgroup.toSubmonoid mulSupport :=
  fun _ _ => ⟨fun _ _ => by aesop, fun h _ hx => (h hx).1⟩

variable {M}

variable (M) in
/-- A submonoid is pointed if it has zero support. -/
@[to_additive /-- A submonoid is pointed if it has zero support. -/]
/--
Definition of `IsMulPointed` / `IsMulPointed` 的定义

English:
definition IsMulPointed
  body: forall x in M, x⁻¹ in M -> x = 1

中文:
定义 IsMulPointed
  定义体: forall x in M, x⁻¹ in M -> x = 1
-/
def IsMulPointed := forall x in M, x⁻¹ in M -> x = 1

namespace IsMulPointed

@[to_additive (attr := aesop 90%)]
/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: (h : forall x in M, x⁻¹ in M -> x = 1)
  statement: M.IsMulPointed
  proof: h -- for Aesop

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₁]))]

中文:
定理 mk
  条件: (h : 对任意 x in M, x⁻¹ in M -> x = 1)
  结论: M.IsMulPointed
  证明: h -- for Aesop

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₁]))]
-/
theorem mk (h : forall x in M, x⁻¹ in M -> x = 1) : M.IsMulPointed := h -- for Aesop

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₁]))]
/--
theorem `eq_one_of_mem_of_inv_mem` / 定理 `eq_one_of_mem_of_inv_mem`

English:
theorem eq_one_of_mem_of_inv_mem
  statement: (hM : M.IsMulPointed)
  proof: hM _ hx₁ hx₂

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive]

中文:
定理 eq_one_of_mem_of_inv_mem
  结论: (hM : M.IsMulPointed)
  证明: hM _ hx₁ hx₂

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive]
-/
theorem eq_one_of_mem_of_inv_mem (hM : M.IsMulPointed)
    {x : G} (hx₁ : x in M) (hx₂ : x⁻¹ in M) : x = 1 := hM _ hx₁ hx₂

@[to_additive (attr := aesop safe forward (immediate := [hM, hx₂]))]
alias eq_one_of_mem_of_inv_mem₂ := eq_one_of_mem_of_inv_mem -- for Aesop

@[to_additive]
/--
theorem `_root_.isMulPointed_iff_mulSupport_eq_bot` / 定理 `_root_.isMulPointed_iff_mulSupport_eq_bot`

English:
theorem _root_.isMulPointed_iff_mulSupport_eq_bot
  statement: M.IsMulPointed ↔ M.mulSupport = ⊥ where
  proof: by aesop
  mpr h := fun x => by
    apply_fun (x in ·) at h
    aesop

@[to_additive (attr := simp)]
alias ⟨mulSupport_eq_bot, _⟩ := isMulPointed_iff_mulSupport_eq_bot

@[to_additive]
alias ⟨_, of_mulSupport_eq_bot⟩ := isMulPointed_iff_mulSupport_eq_bot

中文:
定理 _root_.isMulPointed_iff_mulSupport_eq_bot
  结论: M.IsMulPointed ↔ M.mulSupport = ⊥ where
  证明: by aesop
  mpr h := fun x => by
    apply_fun (x in ·) at h
    aesop

@[to_additive (attr := simp)]
alias ⟨mulSupport_eq_bot, _⟩ := isMulPointed_iff_mulSupport_eq_bot

@[to_additive]
alias ⟨_, of_mulSupport_eq_bot⟩ := isMulPointed_iff_mulSupport_eq_bot

Depends on / 依赖: apply_fun
-/
theorem _root_.isMulPointed_iff_mulSupport_eq_bot : M.IsMulPointed ↔ M.mulSupport = ⊥ where
  mp := by aesop
  mpr h := fun x => by
    apply_fun (x in ·) at h
    aesop

@[to_additive (attr := simp)]
alias ⟨mulSupport_eq_bot, _⟩ := isMulPointed_iff_mulSupport_eq_bot

@[to_additive]
alias ⟨_, of_mulSupport_eq_bot⟩ := isMulPointed_iff_mulSupport_eq_bot

end IsMulPointed

variable (M) in
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/
@[to_additive
/-- A submonoid `M` of a group `G` is spanning if `M` generates `G` as a subgroup. -/]
/--
Definition of `IsMulSpanning` / `IsMulSpanning` 的定义

English:
definition IsMulSpanning
  body: forall a : G, a in M ∨ a⁻¹ in M

中文:
定义 IsMulSpanning
  定义体: forall a : G, a in M ∨ a⁻¹ in M
-/
def IsMulSpanning := forall a : G, a in M ∨ a⁻¹ in M

namespace IsMulSpanning

@[to_additive (attr := aesop 90%)]
/--
theorem `mk` / 定理 `mk`

English:
theorem mk
  given: (h : forall a : G, a in M ∨ a⁻¹ in M)
  statement: M.IsMulSpanning
  proof: h -- for Aesop

@[to_additive (attr := aesop safe forward)]

中文:
定理 mk
  条件: (h : 对任意 a : G, a in M ∨ a⁻¹ in M)
  结论: M.IsMulSpanning
  证明: h -- for Aesop

@[to_additive (attr := aesop safe forward)]
-/
theorem mk (h : forall a : G, a in M ∨ a⁻¹ in M) : M.IsMulSpanning := h -- for Aesop

@[to_additive (attr := aesop safe forward)]
/--
theorem `mem_or_inv_mem` / 定理 `mem_or_inv_mem`

English:
theorem mem_or_inv_mem
  given: (hM : M.IsMulSpanning) (a : G)
  statement: a in M ∨ a⁻¹ in M
  proof: by aesop

@[to_additive]

中文:
定理 mem_or_inv_mem
  条件: (hM : M.IsMulSpanning) (a : G)
  结论: a in M ∨ a⁻¹ in M
  证明: by aesop

@[to_additive]
-/
theorem mem_or_inv_mem (hM : M.IsMulSpanning) (a : G) : a in M ∨ a⁻¹ in M := by aesop

@[to_additive]
/--
theorem `of_le` / 定理 `of_le`

English:
theorem of_le
  given: {N : Submonoid G} (hM : M.IsMulSpanning) (h : M <= N)
  proof: by aesop

@[to_additive]

中文:
定理 of_le
  条件: {N : 子幺半群 G} (hM : M.IsMulSpanning) (h : M <= N)
  证明: by aesop

@[to_additive]
-/
theorem of_le {N : Submonoid G} (hM : M.IsMulSpanning) (h : M <= N) :
    N.IsMulSpanning := by aesop

@[to_additive]
/--
theorem `maximal_isMulPointed` / 定理 `maximal_isMulPointed`

English:
theorem maximal_isMulPointed
  given: (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning)
  proof: ⟨hMp, fun N hN h => by rw [SetLike.le_def] at h ⊢; aesop⟩

中文:
定理 maximal_isMulPointed
  条件: (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning)
  证明: ⟨hMp, fun N hN h => by rw [SetLike.le_def] at h ⊢; aesop⟩

Depends on / 依赖: SetLike, SetLike.le_def, le_def
-/
theorem maximal_isMulPointed (hMp : M.IsMulPointed) (hMs : M.IsMulSpanning) :
    Maximal IsMulPointed M :=
  ⟨hMp, fun N hN h => by rw [SetLike.le_def] at h ⊢; aesop⟩

end Submonoid.IsMulSpanning
