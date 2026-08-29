/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Data.Set.Operations
public import Mathlib.Util.Notation3

/-!
# Notation classes for set supremum and infimum

In this file we introduce notation for indexed suprema, infima, unions, and intersections.

## Main definitions

- `SupSet α`: typeclass introducing the operation `SupSet.sSup` (exported to the root namespace);
  `sSup s` is the supremum of the set `s`;
- `InfSet`: similar typeclass for infimum of a set;
- `iSup f`, `iInf f`: supremum and infimum of an indexed family of elements,
  defined as `sSup (Set.range f)` and `sInf (Set.range f)`, respectively;
- `Set.sUnion s`, `Set.sInter s`: same as `sSup s` and `sInf s`,
  but works only for sets of sets;
- `Set.iUnion s`, `Set.iInter s`: same as `iSup s` and `iInf s`,
  but works only for indexed families of sets.

## Notation

- `⨆ i, f i`, `⨅ i, f i`: supremum and infimum of an indexed family, respectively;
- `⋃₀ s`, `⋂₀ s`: union and intersection of a set of sets;
- `⋃ i, s i`, `⋂ i, s i`: union and intersection of an indexed family of sets.

-/

@[expose] public section

open Set

universe u v
variable {α : Type u} {ι : Sort v}

/--
Definition of `SupSet` / `SupSet` 的定义

English:
class SupSet
  parameters: (α : Type*)
  axioms and operations (1):
    - sSup : Set α -> α

中文:
类 上确界集
  参数: (α : 类型)
  公理与运算 (1 个):
    - sSup : 集合 α -> α
-/
class SupSet (α : Type*) where
  /-- Supremum of a set -/
  sSup : Set α -> α

/-- Class for the `sInf` operator -/
@[to_dual existing]
/--
Definition of `InfSet` / `InfSet` 的定义

English:
class InfSet
  parameters: (α : Type*)
  axioms and operations (1):
    - sInf : Set α -> α

中文:
类 下确界集
  参数: (α : 类型)
  公理与运算 (1 个):
    - sInf : 集合 α -> α
-/
class InfSet (α : Type*) where
  /-- Infimum of a set -/
  sInf : Set α -> α

export SupSet (sSup)

export InfSet (sInf)

/-- Indexed supremum -/
@[to_dual /-- Indexed infimum -/]
/--
Definition of `iSup` / `iSup` 的定义

English:
definition iSup
  signature: [SupSet α] (s : ι -> α)
  body: sSup (range s)

@[to_dual]

中文:
定义 iSup
  签名: [上确界集 α] (s : ι -> α)
  定义体: sSup (range s)

@[to_dual]
-/
def iSup [SupSet α] (s : ι -> α) : α :=
  sSup (range s)

@[to_dual]
instance (priority := 50) infSet_to_nonempty (α) [InfSet α] : Nonempty α :=
  ⟨sInf ∅⟩

/-- Indexed supremum. -/
notation3 "⨆ " (...)", " r:60:(scoped f => iSup f) => r

/-- Indexed infimum. -/
notation3 "⨅ " (...)", " r:60:(scoped f => iInf f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed supremum. -/
@[app_delab iSup]
meta def iSup_delab : Delab := whenPPOption Lean.getPPNotation withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨆ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨆ ($x:ident : $dom), $body)
      else
        `(⨆ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨆ $x:ident, ⨆ (_ : $y:ident in $s), $body)
    | `(⨆ ($x:ident : $_), ⨆ (_ : $y:ident in $s), $body) =>
      if x == y then `(⨆ $x:ident in $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- Delaborator for indexed infimum. -/
@[app_delab iInf]
meta def iInf_delab : Delab := whenPPOption Lean.getPPNotation withOverApp 4 do
  let #[_, ι, _, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⨅ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⨅ ($x:ident : $dom), $body)
      else
        `(⨅ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⨅ $x:ident, ⨅ (_ : $y:ident in $s), $body)
    | `(⨅ ($x:ident : $_), ⨅ (_ : $y:ident in $s), $body) =>
      if x == y then `(⨅ $x:ident in $s, $body) else pure stx
    | _ => pure stx
  return stx
end delaborators

namespace Set

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Set α)
  body: ⟨fun s => { a | forall t in s, a in t }⟩

中文:
实例 :
  签名: 下确界集 (集合 α)
  定义体: ⟨fun s => { a | forall t in s, a in t }⟩
-/
instance : InfSet (Set α) :=
  ⟨fun s => { a | forall t in s, a in t }⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (Set α)
  body: ⟨fun s => { a | exists t in s, a in t }⟩

中文:
实例 :
  签名: 上确界集 (集合 α)
  定义体: ⟨fun s => { a | exists t in s, a in t }⟩
-/
instance : SupSet (Set α) :=
  ⟨fun s => { a | exists t in s, a in t }⟩

/--
Definition of `sInter` / `sInter` 的定义

English:
definition sInter
  signature: (S : Set (Set α))
  body: sInf S

中文:
定义 集合交集
  签名: (S : 集合 (集合 α))
  定义体: sInf S
-/
def sInter (S : Set (Set α)) : Set α :=
  sInf S

/-- Notation for `Set.sInter` Intersection of a set of sets. -/
prefix:110 "⋂₀ " => sInter

/--
Definition of `sUnion` / `sUnion` 的定义

English:
definition sUnion
  signature: (S : Set (Set α))
  body: sSup S

中文:
定义 集合并集
  签名: (S : 集合 (集合 α))
  定义体: sSup S
-/
def sUnion (S : Set (Set α)) : Set α :=
  sSup S

/-- Notation for `Set.sUnion`. Union of a set of sets. -/
prefix:110 "⋃₀ " => sUnion

@[simp, grind =, push]
/--
theorem `mem_sInter` / 定理 `mem_sInter`

English:
theorem mem_sInter
  given: {x : α} {S : Set (Set α)}
  statement: x in ⋂₀ S ↔ forall t in S, x in t
  proof: Iff.rfl

@[simp, grind =, push]

中文:
定理 mem_s整数er
  条件: {x : α} {S : 集合 (集合 α)}
  结论: x in ⋂₀ S ↔ 对任意 t in S, x in t
  证明: Iff.rfl

@[simp, grind =, push]

Depends on / 依赖: Iff.rfl
-/
theorem mem_sInter {x : α} {S : Set (Set α)} : x in ⋂₀ S ↔ forall t in S, x in t :=
  Iff.rfl

@[simp, grind =, push]
/--
theorem `mem_sUnion` / 定理 `mem_sUnion`

English:
theorem mem_sUnion
  given: {x : α} {S : Set (Set α)}
  statement: x in ⋃₀ S ↔ exists t in S, x in t
  proof: Iff.rfl

中文:
定理 mem_sUnion
  条件: {x : α} {S : 集合 (集合 α)}
  结论: x in ⋃₀ S ↔ 存在 t in S, x in t
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mem_sUnion {x : α} {S : Set (Set α)} : x in ⋃₀ S ↔ exists t in S, x in t :=
  Iff.rfl

/--
Definition of `iUnion` / `iUnion` 的定义

English:
definition iUnion
  signature: (s : ι -> Set α)
  body: iSup s

中文:
定义 iUnion
  签名: (s : ι -> 集合 α)
  定义体: iSup s
-/
def iUnion (s : ι -> Set α) : Set α :=
  iSup s

/--
Definition of `iInter` / `iInter` 的定义

English:
definition iInter
  signature: (s : ι -> Set α)
  body: iInf s

中文:
定义 i整数er
  签名: (s : ι -> 集合 α)
  定义体: iInf s
-/
def iInter (s : ι -> Set α) : Set α :=
  iInf s

/-- Notation for `Set.iUnion`. Indexed union of a family of sets -/
notation3 "⋃ " (...)", " r:60:(scoped f => iUnion f) => r

/-- Notation for `Set.iInter`. Indexed intersection of a family of sets -/
notation3 "⋂ " (...)", " r:60:(scoped f => iInter f) => r

section delaborators

open Lean Lean.PrettyPrinter.Delaborator

/-- Delaborator for indexed unions. -/
@[app_delab Set.iUnion]
meta def iUnion_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋃ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋃ ($x:ident : $dom), $body)
      else
        `(⋃ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋃ $x:ident, ⋃ (_ : $y:ident in $s), $body)
    | `(⋃ ($x:ident : $_), ⋃ (_ : $y:ident in $s), $body) =>
      if x == y then `(⋃ $x:ident in $s, $body) else pure stx
    | _ => pure stx
  return stx

/-- Delaborator for indexed intersections. -/
@[app_delab Set.iInter]
meta def sInter_delab : Delab := whenPPOption Lean.getPPNotation do
  let #[_, ι, f] := (← SubExpr.getExpr).getAppArgs | failure
  unless f.isLambda do failure
  let prop ← Meta.isProp ι
  let dep := f.bindingBody!.hasLooseBVar 0
  let ppTypes ← getPPOption getPPFunBinderTypes
  let stx ← SubExpr.withAppArg do
    let dom ← SubExpr.withBindingDomain delab
    withBindingBodyUnusedName fun x => do
      let x : TSyntax `ident := .mk x
      let body ← delab
      if prop && !dep then
        `(⋂ (_ : $dom), $body)
      else if prop || ppTypes then
        `(⋂ ($x:ident : $dom), $body)
      else
        `(⋂ $x:ident, $body)
  -- Cute binders
  let stx : Term ←
    match stx with
    | `(⋂ $x:ident, ⋂ (_ : $y:ident in $s), $body)
    | `(⋂ ($x:ident : $_), ⋂ (_ : $y:ident in $s), $body) =>
      if x == y then `(⋂ $x:ident in $s, $body) else pure stx
    | _ => pure stx
  return stx

end delaborators

@[simp, push]
/--
theorem `mem_iUnion` / 定理 `mem_iUnion`

English:
theorem mem_iUnion
  given: {x : α} {s : ι -> Set α}
  statement: (x in ⋃ i, s i) ↔ exists i, x in s i
  proof: ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x in _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp, push]

中文:
定理 mem_iUnion
  条件: {x : α} {s : ι -> 集合 α}
  结论: (x in ⋃ i, s i) ↔ 存在 i, x in s i
  证明: ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x in _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp, push]

Depends on / 依赖: t_eq, t_eq.symm
-/
theorem mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ exists i, x in s i :=
  ⟨fun ⟨_, ⟨⟨a, (t_eq : s a = _)⟩, (h : x in _)⟩⟩ => ⟨a, t_eq.symm ▸ h⟩, fun ⟨a, h⟩ =>
    ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩

@[simp, push]
/--
theorem `mem_iInter` / 定理 `mem_iInter`

English:
theorem mem_iInter
  given: {x : α} {s : ι -> Set α}
  statement: (x in ⋂ i, s i) ↔ forall i, x in s i
  proof: ⟨fun (h : forall a in { a : Set α | exists i, s i = a }, x in a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩

@[simp]

中文:
定理 mem_i整数er
  条件: {x : α} {s : ι -> 集合 α}
  结论: (x in ⋂ i, s i) ↔ 对任意 i, x in s i
  证明: ⟨fun (h : forall a in { a : Set α | exists i, s i = a }, x in a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩

@[simp]
-/
theorem mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ forall i, x in s i :=
  ⟨fun (h : forall a in { a : Set α | exists i, s i = a }, x in a) a => h (s a) ⟨a, rfl⟩,
    fun h _ ⟨a, (eq : s a = _)⟩ => eq ▸ h a⟩

@[simp]
/--
theorem `sSup_eq_sUnion` / 定理 `sSup_eq_sUnion`

English:
theorem sSup_eq_sUnion
  given: (S : Set (Set α))
  statement: sSup S = ⋃₀ S
  proof: rfl

@[simp]

中文:
定理 sSup_eq_sUnion
  条件: (S : 集合 (集合 α))
  结论: sSup S = ⋃₀ S
  证明: rfl

@[simp]
-/
theorem sSup_eq_sUnion (S : Set (Set α)) : sSup S = ⋃₀ S :=
  rfl

@[simp]
/--
theorem `sInf_eq_sInter` / 定理 `sInf_eq_sInter`

English:
theorem sInf_eq_sInter
  given: (S : Set (Set α))
  statement: sInf S = ⋂₀ S
  proof: rfl

@[simp]

中文:
定理 sInf_eq_s整数er
  条件: (S : 集合 (集合 α))
  结论: sInf S = ⋂₀ S
  证明: rfl

@[simp]
-/
theorem sInf_eq_sInter (S : Set (Set α)) : sInf S = ⋂₀ S :=
  rfl

@[simp]
/--
theorem `iSup_eq_iUnion` / 定理 `iSup_eq_iUnion`

English:
theorem iSup_eq_iUnion
  given: (s : ι -> Set α)
  statement: iSup s = iUnion s
  proof: rfl

@[simp]

中文:
定理 iSup_eq_iUnion
  条件: (s : ι -> 集合 α)
  结论: iSup s = iUnion s
  证明: rfl

@[simp]
-/
theorem iSup_eq_iUnion (s : ι -> Set α) : iSup s = iUnion s :=
  rfl

@[simp]
/--
theorem `iInf_eq_iInter` / 定理 `iInf_eq_iInter`

English:
theorem iInf_eq_iInter
  given: (s : ι -> Set α)
  statement: iInf s = iInter s
  proof: rfl

中文:
定理 iInf_eq_i整数er
  条件: (s : ι -> 集合 α)
  结论: iInf s = i整数er s
  证明: rfl
-/
theorem iInf_eq_iInter (s : ι -> Set α) : iInf s = iInter s :=
  rfl

end Set
