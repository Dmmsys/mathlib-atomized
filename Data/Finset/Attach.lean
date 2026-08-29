/-
Copyright (c) 2015 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Minchao Wu, Mario Carneiro
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Multiset.MapFold

/-!
# Attaching a proof of membership to a finite set

## Main declarations

* `Finset.attach`: Given `s : Finset α`, `attach s` forms a finset of elements of the subtype
  `{a // a ∈ s}`; in other words, it attaches elements to a proof of membership in the set.

## Tags

finite sets, finset

-/

@[expose] public section

-- Assert that we define `Finset` without the material on `List.sublists`.
-- Note that we cannot use `List.sublists` itself as that is defined very early.
assert_not_exists List.sublistsLen Multiset.powerset CompleteLattice IsOrderedMonoid

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*} {γ : Type*}

namespace Finset

-- TODO: these should be global attributes, but this will require fixing other files
attribute [local trans] Subset.trans Superset.trans

/-! ### attach -/

/--
Definition of `attach` / `attach` 的定义

English:
definition attach
  signature: (s : Finset α)
  body: ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩

@[simp]

中文:
定义 attach
  签名: (s : 有限集 α)
  定义体: ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩

@[simp]

Depends on / 依赖: Multiset, Multiset.attach, attach, nodup_attach
-/
def attach (s : Finset α) : Finset { x // x in s } :=
  ⟨Multiset.attach s.1, nodup_attach.2 s.2⟩

@[simp]
/--
theorem `attach_val` / 定理 `attach_val`

English:
theorem attach_val
  given: (s : Finset α)
  statement: s.attach.1 = s.1.attach
  proof: rfl

@[simp, grind ←]

中文:
定理 attach_val
  条件: (s : 有限集 α)
  结论: s.attach.1 = s.1.attach
  证明: rfl

@[simp, grind ←]
-/
theorem attach_val (s : Finset α) : s.attach.1 = s.1.attach :=
  rfl

@[simp, grind ←]
/--
theorem `mem_attach` / 定理 `mem_attach`

English:
theorem mem_attach
  given: (s : Finset α)
  statement: forall x, x in s.attach
  proof: Multiset.mem_attach _

@[simp, norm_cast]

中文:
定理 mem_attach
  条件: (s : 有限集 α)
  结论: 对任意 x, x in s.attach
  证明: Multiset.mem_attach _

@[simp, norm_cast]

Depends on / 依赖: Multiset, Multiset.mem_attach, mem_attach
-/
theorem mem_attach (s : Finset α) : forall x, x in s.attach :=
  Multiset.mem_attach _

@[simp, norm_cast]
/--
theorem `coe_attach` / 定理 `coe_attach`

English:
theorem coe_attach
  given: (s : Finset α)
  statement: (s.attach : Set s) = Set.univ
  proof: by ext; simp

中文:
定理 coe_attach
  条件: (s : 有限集 α)
  结论: (s.attach : 集合 s) = 集合.univ
  证明: by ext; simp
-/
theorem coe_attach (s : Finset α) : (s.attach : Set s) = Set.univ := by ext; simp

end Finset
