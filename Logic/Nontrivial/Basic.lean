/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Prod.Basic
public import Mathlib.Logic.Function.Basic
public import Mathlib.Logic.Nontrivial.Defs
public import Mathlib.Logic.Unique
public import Mathlib.Order.Defs.LinearOrder

import Mathlib.Tactic.Attr.Register

/-!
# Nontrivial types

Results about `Nontrivial`.
-/

@[expose] public section

variable {α : Type*} {β : Type*}

-- `x` and `y` are explicit here, as they are often needed to guide typechecking of `h`.
/--
theorem `nontrivial_of_lt` / 定理 `nontrivial_of_lt`

English:
theorem nontrivial_of_lt
  given: [Preorder α] (x y : α) (h : x < y)
  statement: Nontrivial α
  proof: ⟨⟨x, y, ne_of_lt h⟩⟩

中文:
定理 nontrivial_of_lt
  条件: [Preorder α] (x y : α) (h : x < y)
  结论: Nontrivial α
  证明: ⟨⟨x, y, ne_of_lt h⟩⟩

Depends on / 依赖: ne_of_lt
-/
theorem nontrivial_of_lt [Preorder α] (x y : α) (h : x < y) : Nontrivial α :=
  ⟨⟨x, y, ne_of_lt h⟩⟩

/--
theorem `exists_pair_lt` / 定理 `exists_pair_lt`

English:
theorem exists_pair_lt
  given: (α : Type*) [Nontrivial α] [LinearOrder α]
  statement: exists x y : α, x < y
  proof: by
  rcases exists_pair_ne α with ⟨x, y, hxy⟩
  cases lt_or_gt_of_ne hxy <;> exact ⟨_, _, ‹_›⟩

中文:
定理 exists_pair_lt
  条件: (α : 类型) [Nontrivial α] [LinearOrder α]
  结论: 存在 x y : α, x < y
  证明: by
  rcases exists_pair_ne α with ⟨x, y, hxy⟩
  cases lt_or_gt_of_ne hxy <;> exact ⟨_, _, ‹_›⟩

Depends on / 依赖: exists_pair_ne, lt_or_gt_of_ne
-/
theorem exists_pair_lt (α : Type*) [Nontrivial α] [LinearOrder α] : exists x y : α, x < y := by
  rcases exists_pair_ne α with ⟨x, y, hxy⟩
  cases lt_or_gt_of_ne hxy <;> exact ⟨_, _, ‹_›⟩

/--
theorem `nontrivial_iff_lt` / 定理 `nontrivial_iff_lt`

English:
theorem nontrivial_iff_lt
  given: [LinearOrder α]
  statement: Nontrivial α ↔ exists x y : α, x < y
  proof: ⟨fun h => @exists_pair_lt α h _, fun ⟨x, y, h⟩ => nontrivial_of_lt x y h⟩

中文:
定理 nontrivial_iff_lt
  条件: [LinearOrder α]
  结论: Nontrivial α ↔ 存在 x y : α, x < y
  证明: ⟨fun h => @exists_pair_lt α h _, fun ⟨x, y, h⟩ => nontrivial_of_lt x y h⟩

Depends on / 依赖: exists_pair_lt, nontrivial_of_lt
-/
theorem nontrivial_iff_lt [LinearOrder α] : Nontrivial α ↔ exists x y : α, x < y :=
  ⟨fun h => @exists_pair_lt α h _, fun ⟨x, y, h⟩ => nontrivial_of_lt x y h⟩

/--
theorem `Subtype.nontrivial_iff_exists_ne` / 定理 `Subtype.nontrivial_iff_exists_ne`

English:
theorem Subtype.nontrivial_iff_exists_ne
  given: (p : α -> Prop) (x : Subtype p)
  proof: by
  simp only [_root_.nontrivial_iff_exists_ne x, Subtype.exists, Ne, Subtype.ext_iff]

中文:
定理 Subtype.nontrivial_iff_exists_ne
  条件: (p : α -> 命题) (x : Subtype p)
  证明: by
  simp only [_root_.nontrivial_iff_exists_ne x, Subtype.exists, Ne, Subtype.ext_iff]

Depends on / 依赖: Subtype, Subtype.exists, Subtype.ext_iff, _root_, _root_.nontrivial_iff_exists_ne, ext_iff, nontrivial_iff_exists_ne
-/
theorem Subtype.nontrivial_iff_exists_ne (p : α -> Prop) (x : Subtype p) :
    Nontrivial (Subtype p) ↔ exists (y : α) (_ : p y), y != x := by
  simp only [_root_.nontrivial_iff_exists_ne x, Subtype.exists, Ne, Subtype.ext_iff]

open scoped Classical in
/--
Definition of `nontrivialPSumUnique` / `nontrivialPSumUnique` 的定义

English:
definition nontrivialPSumUnique
  signature: (α : Type*) [Inhabited α]
  body: if h : Nontrivial α then PSum.inl h
  else
    PSum.inr
      { default := default,
        uniq := fun x : α => by
          by_contra H
          exact h ⟨_, _, H⟩ }

中文:
定义 nontrivialPSumUnique
  签名: (α : 类型) [Inhabited α]
  定义体: if h : Nontrivial α then PSum.inl h
  else
    PSum.inr
      { default := default,
        uniq := fun x : α => by
          by_contra H
          exact h ⟨_, _, H⟩ }

Depends on / 依赖: Nontrivial, PSum.inl, PSum.inr
-/
noncomputable def nontrivialPSumUnique (α : Type*) [Inhabited α] :
    Nontrivial α oplus' Unique α :=
  if h : Nontrivial α then PSum.inl h
  else
    PSum.inr
      { default := default,
        uniq := fun x : α => by
          by_contra H
          exact h ⟨_, _, H⟩ }

/--
Instance `Option.nontrivial` / 实例 `Option.nontrivial`

English:
instance Option.nontrivial
  signature: [Nonempty α]
  body: by
  inhabit α
  exact ⟨none, some default, nofun⟩

中文:
实例 Option.nontrivial
  签名: [Nonempty α]
  定义体: by
  inhabit α
  exact ⟨none, some default, nofun⟩

Depends on / 依赖: inhabit
-/
instance Option.nontrivial [Nonempty α] : Nontrivial (Option α) := by
  inhabit α
  exact ⟨none, some default, nofun⟩

/--
Instance `nontrivial_prod_right` / 实例 `nontrivial_prod_right`

English:
instance nontrivial_prod_right
  signature: [Nonempty α] [Nontrivial β]
  body: Prod.snd_surjective.nontrivial

中文:
实例 nontrivial_prod_right
  签名: [Nonempty α] [Nontrivial β]
  定义体: Prod.snd_surjective.nontrivial

Depends on / 依赖: Prod.snd_surjective.nontrivial, nontrivial, snd_surjective
-/
instance nontrivial_prod_right [Nonempty α] [Nontrivial β] : Nontrivial (α × β) :=
  Prod.snd_surjective.nontrivial

/--
Instance `nontrivial_prod_left` / 实例 `nontrivial_prod_left`

English:
instance nontrivial_prod_left
  signature: [Nontrivial α] [Nonempty β]
  body: Prod.fst_surjective.nontrivial

中文:
实例 nontrivial_prod_left
  签名: [Nontrivial α] [Nonempty β]
  定义体: Prod.fst_surjective.nontrivial

Depends on / 依赖: Prod.fst_surjective.nontrivial, fst_surjective, nontrivial
-/
instance nontrivial_prod_left [Nontrivial α] [Nonempty β] : Nontrivial (α × β) :=
  Prod.fst_surjective.nontrivial

namespace Pi

variable {I : Type*} {f : I -> Type*}

/--
theorem `nontrivial_at` / 定理 `nontrivial_at`

English:
theorem nontrivial_at
  given: (i' : I) [inst : forall i, Nonempty (f i)] [Nontrivial (f i')]
  proof: by
  classical
  let := Classical.decEq (forall i : I, f i)
  exact (Function.update_injective (fun i => Classical.choice (inst i)) i').nontrivial

中文:
定理 nontrivial_at
  条件: (i' : I) [inst : 对任意 i, Nonempty (f i)] [Nontrivial (f i')]
  证明: by
  classical
  let := Classical.decEq (forall i : I, f i)
  exact (Function.update_injective (fun i => Classical.choice (inst i)) i').nontrivial

Depends on / 依赖: Classical, Classical.choice, Classical.decEq, Function, Function.update_injective, choice, classical, nontrivial, update_injective
-/
theorem nontrivial_at (i' : I) [inst : forall i, Nonempty (f i)] [Nontrivial (f i')] :
    Nontrivial (forall i : I, f i) := by
  classical
  let := Classical.decEq (forall i : I, f i)
  exact (Function.update_injective (fun i => Classical.choice (inst i)) i').nontrivial

/--
Instance `nontrivial` / 实例 `nontrivial`

English:
instance nontrivial
  signature: [Inhabited I] [forall i, Nonempty (f i)] [Nontrivial (f default)]
  body: nontrivial_at default

中文:
实例 nontrivial
  签名: [Inhabited I] [对任意 i, Nonempty (f i)] [Nontrivial (f default)]
  定义体: nontrivial_at default

Depends on / 依赖: nontrivial_at
-/
instance nontrivial [Inhabited I] [forall i, Nonempty (f i)] [Nontrivial (f default)] :
    Nontrivial (forall i : I, f i) :=
  nontrivial_at default

end Pi

/--
Instance `Function.nontrivial` / 实例 `Function.nontrivial`

English:
instance Function.nontrivial
  signature: [h : Nonempty α] [Nontrivial β]
  body: h.elim fun a => Pi.nontrivial_at a

@[nontriviality]

中文:
实例 Function.nontrivial
  签名: [h : Nonempty α] [Nontrivial β]
  定义体: h.elim fun a => Pi.nontrivial_at a

@[nontriviality]

Depends on / 依赖: Pi.nontrivial_at, h.elim, nontrivial_at
-/
instance Function.nontrivial [h : Nonempty α] [Nontrivial β] : Nontrivial (α -> β) :=
  h.elim fun a => Pi.nontrivial_at a

@[nontriviality]
/--
theorem `Subsingleton.le` / 定理 `Subsingleton.le`

English:
theorem Subsingleton.le
  given: [Preorder α] [Subsingleton α] (x y : α)
  statement: x <= y
  proof: le_of_eq (Subsingleton.elim x y)

中文:
定理 Subsingleton.le
  条件: [Preorder α] [Subsingleton α] (x y : α)
  结论: x <= y
  证明: le_of_eq (Subsingleton.elim x y)
-/
protected theorem Subsingleton.le [Preorder α] [Subsingleton α] (x y : α) : x <= y :=
  le_of_eq (Subsingleton.elim x y)
