/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn, Violeta Hernández Palacios
-/
module

public import Mathlib.SetTheory.Ordinal.Arithmetic

/-!
# Arithmetic on families of ordinals

This file proves basic results about the suprema of families of ordinals.

Various other basic arithmetic results are given in `Principal.lean` instead.
-/

@[expose] public noncomputable section

assert_not_exists Field Module

open Function Cardinal Set Order

universe u v w

namespace Ordinal

variable {α β : Type*}

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a specified
well-ordering. -/
@[deprecated enum (since := "2026-04-06")]
/--
Definition of `bfamilyOfFamily'` / `bfamilyOfFamily'` 的定义

English:
definition bfamilyOfFamily'
  signature: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α)
  body: fun a ha => f (enum r ⟨a, ha⟩)

中文:
定义 bfamilyOfFamily'
  签名: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] (f : ι -> α)
  定义体: fun a ha => f (enum r ⟨a, ha⟩)
-/
def bfamilyOfFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α) :
    forall a < type r, α := fun a ha => f (enum r ⟨a, ha⟩)

/-- Converts a family indexed by a `Type u` to one indexed by an `Ordinal.{u}` using a well-ordering
given by the axiom of choice. -/
@[deprecated enum (since := "2026-04-06")]
/--
Definition of `bfamilyOfFamily` / `bfamilyOfFamily` 的定义

English:
definition bfamilyOfFamily
  signature: {ι : Type u}
  body: bfamilyOfFamily' WellOrderingRel

中文:
定义 bfamilyOfFamily
  签名: {ι : 类型u}
  定义体: bfamilyOfFamily' WellOrderingRel

Depends on / 依赖: WellOrderingRel, bfamilyOfFamily
-/
def bfamilyOfFamily {ι : Type u} : (ι -> α) -> forall a < type (@WellOrderingRel ι), α :=
  bfamilyOfFamily' WellOrderingRel

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a specified
well-ordering. -/
@[deprecated typein (since := "2026-04-06")]
/--
Definition of `familyOfBFamily'` / `familyOfBFamily'` 的定义

English:
definition familyOfBFamily'
  signature: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho : type r = o)
  body: fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

中文:
定义 familyOfBFamily'
  签名: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] {o} (ho : type r = o)
  定义体: fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)
-/
def familyOfBFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : forall a < o, α) : ι -> α := fun i =>
  f (typein r i)
    (by
      rw [← ho]
      exact typein_lt_type r i)

/-- Converts a family indexed by an `Ordinal.{u}` to one indexed by a `Type u` using a well-ordering
given by the axiom of choice. -/
@[deprecated typein (since := "2026-04-06")]
/--
Definition of `familyOfBFamily` / `familyOfBFamily` 的定义

English:
definition familyOfBFamily
  signature: (o : Ordinal) (f : forall a < o, α)
  body: familyOfBFamily' (· < ·) (type_toType o) f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

中文:
定义 familyOfBFamily
  签名: (o : 序数) (f : 对任意 a < o, α)
  定义体: familyOfBFamily' (· < ·) (type_toType o) f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

Depends on / 依赖: familyOfBFamily, type_toType
-/
def familyOfBFamily (o : Ordinal) (f : forall a < o, α) : o.ToType -> α :=
  familyOfBFamily' (· < ·) (type_toType o) f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/--
theorem `bfamilyOfFamily'_typein` / 定理 `bfamilyOfFamily'_typein`

English:
theorem bfamilyOfFamily'_typein
  given: {ι} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α) (i)
  proof: by
  simp only [bfamilyOfFamily', enum_typein]

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

中文:
定理 bfamilyOfFamily'_typein
  条件: {ι} (r : ι -> ι -> 命题) [是良序 ι r] (f : ι -> α) (i)
  证明: by
  simp only [bfamilyOfFamily', enum_typein]

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
-/
theorem bfamilyOfFamily'_typein {ι} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α) (i) :
    bfamilyOfFamily' r f (typein r i) (typein_lt_type r i) = f i := by
  simp only [bfamilyOfFamily', enum_typein]

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/--
theorem `bfamilyOfFamily_typein` / 定理 `bfamilyOfFamily_typein`

English:
theorem bfamilyOfFamily_typein
  given: {ι} (f : ι -> α) (i)
  proof: bfamilyOfFamily'_typein _ f i

中文:
定理 bfamilyOfFamily_typein
  条件: {ι} (f : ι -> α) (i)
  证明: bfamilyOfFamily'_typein _ f i

Depends on / 依赖: _typein, bfamilyOfFamily
-/
theorem bfamilyOfFamily_typein {ι} (f : ι -> α) (i) :
    bfamilyOfFamily f (typein _ i) (typein_lt_type _ i) = f i :=
  bfamilyOfFamily'_typein _ f i

set_option backward.isDefEq.respectTransparency false in
@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `familyOfBFamily'_enum` / 定理 `familyOfBFamily'_enum`

English:
theorem familyOfBFamily'_enum
  statement: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o}
  proof: by
  simp only [familyOfBFamily', typein_enum]

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]

中文:
定理 familyOfBFamily'_enum
  结论: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] {o}
  证明: by
  simp only [familyOfBFamily', typein_enum]

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
-/
theorem familyOfBFamily'_enum {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : forall a < o, α) (i hi) :
    familyOfBFamily' r ho f (enum r ⟨i, by rwa [ho]⟩) = f i hi := by
  simp only [familyOfBFamily', typein_enum]

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `familyOfBFamily_enum` / 定理 `familyOfBFamily_enum`

English:
theorem familyOfBFamily_enum
  given: (o : Ordinal) (f : forall a < o, α) (i hi)
  proof: familyOfBFamily'_enum _ (type_toType o) f _ _

中文:
定理 familyOfBFamily_enum
  条件: (o : 序数) (f : 对任意 a < o, α) (i hi)
  证明: familyOfBFamily'_enum _ (type_toType o) f _ _

Depends on / 依赖: ToType, hi.trans_eq, o.ToType, trans_eq, type_toType
-/
theorem familyOfBFamily_enum (o : Ordinal) (f : forall a < o, α) (i hi) :
    familyOfBFamily o f (enum (α := o.ToType) (· < ·) ⟨i, hi.trans_eq (type_toType _).symm⟩)
    = f i hi :=
  familyOfBFamily'_enum _ (type_toType o) f _ _

/-- The range of a family indexed by ordinals. -/
@[deprecated range (since := "2026-04-06")]
/--
Definition of `brange` / `brange` 的定义

English:
definition brange
  signature: (o : Ordinal) (f : forall a < o, α)
  body: { a | exists i hi, f i hi = a }

@[deprecated mem_range (since := "2026-04-06")]

中文:
定义 brange
  签名: (o : 序数) (f : 对任意 a < o, α)
  定义体: { a | exists i hi, f i hi = a }

@[deprecated mem_range (since := "2026-04-06")]
-/
def brange (o : Ordinal) (f : forall a < o, α) : Set α :=
  { a | exists i hi, f i hi = a }

@[deprecated mem_range (since := "2026-04-06")]
/--
theorem `mem_brange` / 定理 `mem_brange`

English:
theorem mem_brange
  given: {o : Ordinal} {f : forall a < o, α} {a}
  statement: a in brange o f ↔ exists i hi, f i hi = a
  proof: Iff.rfl

@[deprecated mem_range_self (since := "2026-04-06")]

中文:
定理 mem_brange
  条件: {o : 序数} {f : 对任意 a < o, α} {a}
  结论: a in brange o f ↔ 存在 i hi, f i hi = a
  证明: Iff.rfl

@[deprecated mem_range_self (since := "2026-04-06")]

Depends on / 依赖: Iff.rfl
-/
theorem mem_brange {o : Ordinal} {f : forall a < o, α} {a} : a in brange o f ↔ exists i hi, f i hi = a :=
  Iff.rfl

@[deprecated mem_range_self (since := "2026-04-06")]
/--
theorem `mem_brange_self` / 定理 `mem_brange_self`

English:
theorem mem_brange_self
  given: {o} (f : forall a < o, α) (i hi)
  statement: f i hi in brange o f
  proof: ⟨i, hi, rfl⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]

中文:
定理 mem_brange_self
  条件: {o} (f : 对任意 a < o, α) (i hi)
  结论: f i hi in brange o f
  证明: ⟨i, hi, rfl⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
-/
theorem mem_brange_self {o} (f : forall a < o, α) (i hi) : f i hi in brange o f :=
  ⟨i, hi, rfl⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `range_familyOfBFamily'` / 定理 `range_familyOfBFamily'`

English:
theorem range_familyOfBFamily'
  statement: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o}
  proof: by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]

中文:
定理 range_familyOfBFamily'
  结论: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] {o}
  证明: by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]

Depends on / 依赖: Set.ext, _enum, familyOfBFamily, mem_brange_self
-/
theorem range_familyOfBFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : forall a < o, α) : range (familyOfBFamily' r ho f) = brange o f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨b, rfl⟩
    apply mem_brange_self
  · rintro ⟨i, hi, rfl⟩
    exact ⟨_, familyOfBFamily'_enum _ _ _ _ _⟩

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `range_familyOfBFamily` / 定理 `range_familyOfBFamily`

English:
theorem range_familyOfBFamily
  given: {o} (f : forall a < o, α)
  statement: range (familyOfBFamily o f) = brange o f
  proof: range_familyOfBFamily' _ _ f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

中文:
定理 range_familyOfBFamily
  条件: {o} (f : 对任意 a < o, α)
  结论: range (familyOfBFamily o f) = brange o f
  证明: range_familyOfBFamily' _ _ f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

Depends on / 依赖: range_familyOfBFamily
-/
theorem range_familyOfBFamily {o} (f : forall a < o, α) : range (familyOfBFamily o f) = brange o f :=
  range_familyOfBFamily' _ _ f

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/--
theorem `brange_bfamilyOfFamily'` / 定理 `brange_bfamilyOfFamily'`

English:
theorem brange_bfamilyOfFamily'
  given: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α)
  proof: by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

中文:
定理 brange_bfamilyOfFamily'
  条件: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] (f : ι -> α)
  证明: by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

Depends on / 依赖: Set.ext, _typein, bfamilyOfFamily, mem_range_self
-/
theorem brange_bfamilyOfFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α) :
    brange _ (bfamilyOfFamily' r f) = range f := by
  refine Set.ext fun a => ⟨?_, ?_⟩
  · rintro ⟨i, hi, rfl⟩
    apply mem_range_self
  · rintro ⟨b, rfl⟩
    exact ⟨_, _, bfamilyOfFamily'_typein _ _ _⟩

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/--
theorem `brange_bfamilyOfFamily` / 定理 `brange_bfamilyOfFamily`

English:
theorem brange_bfamilyOfFamily
  given: {ι : Type u} (f : ι -> α)
  statement: brange _ (bfamilyOfFamily f) = range f
  proof: brange_bfamilyOfFamily' _ _

@[deprecated "brange is deprecated" (since := "2026-04-06")]

中文:
定理 brange_bfamilyOfFamily
  条件: {ι : 类型u} (f : ι -> α)
  结论: brange _ (bfamilyOfFamily f) = range f
  证明: brange_bfamilyOfFamily' _ _

@[deprecated "brange is deprecated" (since := "2026-04-06")]

Depends on / 依赖: brange_bfamilyOfFamily
-/
theorem brange_bfamilyOfFamily {ι : Type u} (f : ι -> α) : brange _ (bfamilyOfFamily f) = range f :=
  brange_bfamilyOfFamily' _ _

@[deprecated "brange is deprecated" (since := "2026-04-06")]
/--
theorem `brange_const` / 定理 `brange_const`

English:
theorem brange_const
  given: {o : Ordinal} (ho : o != 0) {c : α}
  statement: (brange o fun _ _ => c) = {c}
  proof: by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.ToType (nonempty_toType_iff.2 ho) c

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

中文:
定理 brange_const
  条件: {o : 序数} (ho : o != 0) {c : α}
  结论: (brange o fun _ _ => c) = {c}
  证明: by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.ToType (nonempty_toType_iff.2 ho) c

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

Depends on / 依赖: Set.range_const, ToType, nonempty_toType_iff, o.ToType, range_const, range_familyOfBFamily
-/
theorem brange_const {o : Ordinal} (ho : o != 0) {c : α} : (brange o fun _ _ => c) = {c} := by
  rw [← range_familyOfBFamily]
  exact @Set.range_const _ o.ToType (nonempty_toType_iff.2 ho) c

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/--
theorem `comp_bfamilyOfFamily'` / 定理 `comp_bfamilyOfFamily'`

English:
theorem comp_bfamilyOfFamily'
  statement: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α)
  proof: rfl

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]

中文:
定理 comp_bfamilyOfFamily'
  结论: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] (f : ι -> α)
  证明: rfl

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
-/
theorem comp_bfamilyOfFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> α)
    (g : α -> β) : (fun i hi => g (bfamilyOfFamily' r f i hi)) = bfamilyOfFamily' r (g ∘ f) :=
  rfl

@[deprecated "bfamilyOfFamily is deprecated" (since := "2026-04-06")]
/--
theorem `comp_bfamilyOfFamily` / 定理 `comp_bfamilyOfFamily`

English:
theorem comp_bfamilyOfFamily
  given: {ι : Type u} (f : ι -> α) (g : α -> β)
  proof: rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]

中文:
定理 comp_bfamilyOfFamily
  条件: {ι : 类型u} (f : ι -> α) (g : α -> β)
  证明: rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
-/
theorem comp_bfamilyOfFamily {ι : Type u} (f : ι -> α) (g : α -> β) :
    (fun i hi => g (bfamilyOfFamily f i hi)) = bfamilyOfFamily (g ∘ f) :=
  rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `comp_familyOfBFamily'` / 定理 `comp_familyOfBFamily'`

English:
theorem comp_familyOfBFamily'
  statement: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o}
  proof: rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]

中文:
定理 comp_familyOfBFamily'
  结论: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] {o}
  证明: rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
-/
theorem comp_familyOfBFamily' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o}
    (ho : type r = o) (f : forall a < o, α) (g : α -> β) :
    g ∘ familyOfBFamily' r ho f = familyOfBFamily' r ho fun i hi => g (f i hi) :=
  rfl

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `comp_familyOfBFamily` / 定理 `comp_familyOfBFamily`

English:
theorem comp_familyOfBFamily
  given: {o} (f : forall a < o, α) (g : α -> β)
  proof: rfl

中文:
定理 comp_familyOfBFamily
  条件: {o} (f : 对任意 a < o, α) (g : α -> β)
  证明: rfl
-/
theorem comp_familyOfBFamily {o} (f : forall a < o, α) (g : α -> β) :
    g ∘ familyOfBFamily o f = familyOfBFamily o fun i hi => g (f i hi) :=
  rfl


/--
theorem `bddAbove_of_small` / 定理 `bddAbove_of_small`

English:
theorem bddAbove_of_small
  given: {s : Set Ordinal.{u}} [Small.{u} s]
  statement: BddAbove s
  proof: by
  obtain ⟨a, ha⟩ := Cardinal.bddAbove_of_small (s := (succ ∘ card) '' s)
  refine ⟨a.ord, fun b hb => le_of_lt ?_⟩
  simpa [lt_ord] using ha (mem_image_of_mem _ hb)

@[deprecated bddAbove_of_small (since := "2026-04-04")]

中文:
定理 bddAbove_of_small
  条件: {s : 集合 序数.{u}} [Small.{u} s]
  结论: BddAbove s
  证明: by
  obtain ⟨a, ha⟩ := Cardinal.bddAbove_of_small (s := (succ ∘ card) '' s)
  refine ⟨a.ord, fun b hb => le_of_lt ?_⟩
  simpa [lt_ord] using ha (mem_image_of_mem _ hb)

@[deprecated bddAbove_of_small (since := "2026-04-04")]

Depends on / 依赖: Cardinal, Cardinal.bddAbove_of_small, a.ord, bddAbove_of_small, le_of_lt, lt_ord, mem_image_of_mem
-/
theorem bddAbove_of_small {s : Set Ordinal.{u}} [Small.{u} s] : BddAbove s := by
  obtain ⟨a, ha⟩ := Cardinal.bddAbove_of_small (s := (succ ∘ card) '' s)
  refine ⟨a.ord, fun b hb => le_of_lt ?_⟩
  simpa [lt_ord] using ha (mem_image_of_mem _ hb)

@[deprecated bddAbove_of_small (since := "2026-04-04")]
/--
theorem `bddAbove_range` / 定理 `bddAbove_range`

English:
theorem bddAbove_range
  given: {ι : Type u} (f : ι -> Ordinal.{max u v})
  statement: BddAbove (Set.range f)
  proof: bddAbove_of_small

中文:
定理 bddAbove_range
  条件: {ι : 类型u} (f : ι -> 序数.{最大值 u v})
  结论: BddAbove (集合.range f)
  证明: bddAbove_of_small

Depends on / 依赖: bddAbove_of_small
-/
theorem bddAbove_range {ι : Type u} (f : ι -> Ordinal.{max u v}) : BddAbove (Set.range f) :=
  bddAbove_of_small

/--
theorem `bddAbove_iff_small` / 定理 `bddAbove_iff_small`

English:
theorem bddAbove_iff_small
  given: {s : Set Ordinal.{u}}
  statement: BddAbove s ↔ Small.{u} s
  proof: ⟨fun ⟨a, h⟩ => small_subset (s := Iic a) fun _ hx => h hx, fun _ => bddAbove_of_small⟩

中文:
定理 bddAbove_iff_small
  条件: {s : 集合 序数.{u}}
  结论: BddAbove s ↔ Small.{u} s
  证明: ⟨fun ⟨a, h⟩ => small_subset (s := Iic a) fun _ hx => h hx, fun _ => bddAbove_of_small⟩

Depends on / 依赖: bddAbove_of_small, small_subset
-/
theorem bddAbove_iff_small {s : Set Ordinal.{u}} : BddAbove s ↔ Small.{u} s :=
  ⟨fun ⟨a, h⟩ => small_subset (s := Iic a) fun _ hx => h hx, fun _ => bddAbove_of_small⟩

/--
theorem `bddAbove_image` / 定理 `bddAbove_image`

English:
theorem bddAbove_image
  statement: {s : Set Ordinal.{u}} (hf : BddAbove s)
  proof: by
  rw [bddAbove_iff_small] at hf ⊢
  exact small_lift _

中文:
定理 bddAbove_image
  结论: {s : 集合 序数.{u}} (hf : BddAbove s)
  证明: by
  rw [bddAbove_iff_small] at hf ⊢
  exact small_lift _

Depends on / 依赖: bddAbove_iff_small, small_lift
-/
theorem bddAbove_image {s : Set Ordinal.{u}} (hf : BddAbove s)
    (f : Ordinal.{u} -> Ordinal.{max u v}) : BddAbove (f '' s) := by
  rw [bddAbove_iff_small] at hf ⊢
  exact small_lift _

/--
theorem `bddAbove_range_comp` / 定理 `bddAbove_range_comp`

English:
theorem bddAbove_range_comp
  statement: {ι : Type u} {f : ι -> Ordinal.{v}} (hf : BddAbove (range f))
  proof: by
  rw [range_comp]
  exact bddAbove_image hf g

中文:
定理 bddAbove_range_comp
  结论: {ι : 类型u} {f : ι -> 序数.{v}} (hf : BddAbove (range f))
  证明: by
  rw [range_comp]
  exact bddAbove_image hf g

Depends on / 依赖: bddAbove_image, range_comp
-/
theorem bddAbove_range_comp {ι : Type u} {f : ι -> Ordinal.{v}} (hf : BddAbove (range f))
    (g : Ordinal.{v} -> Ordinal.{max v w}) : BddAbove (range (g ∘ f)) := by
  rw [range_comp]
  exact bddAbove_image hf g

/--
theorem `le_iSup` / 定理 `le_iSup`

English:
theorem le_iSup
  given: {ι} (f : ι -> Ordinal.{u}) [Small.{u} ι]
  statement: forall i, f i <= ⨆ i, f i
  proof: le_ciSup bddAbove_of_small

中文:
定理 le_iSup
  条件: {ι} (f : ι -> 序数.{u}) [Small.{u} ι]
  结论: 对任意 i, f i <= ⨆ i, f i
  证明: le_ciSup bddAbove_of_small
-/
protected theorem le_iSup {ι} (f : ι -> Ordinal.{u}) [Small.{u} ι] : forall i, f i <= ⨆ i, f i :=
  le_ciSup bddAbove_of_small

/-- `ciSup_le_iff'` whenever the input type is small in the output universe. -/
@[simp]
/--
theorem `iSup_le_iff` / 定理 `iSup_le_iff`

English:
theorem iSup_le_iff
  given: {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι]
  proof: ciSup_le_iff' bddAbove_of_small

中文:
定理 iSup_le_iff
  条件: {ι} {f : ι -> 序数.{u}} {a : 序数.{u}} [Small.{u} ι]
  证明: ciSup_le_iff' bddAbove_of_small
-/
protected theorem iSup_le_iff {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    ⨆ i, f i <= a ↔ forall i, f i <= a :=
  ciSup_le_iff' bddAbove_of_small

/--
theorem `iSup_le` / 定理 `iSup_le`

English:
theorem iSup_le
  given: {ι} {f : ι -> Ordinal} {a}
  statement: (forall i, f i <= a) -> ⨆ i, f i <= a
  proof: ciSup_le'

中文:
定理 iSup_le
  条件: {ι} {f : ι -> 序数} {a}
  结论: (对任意 i, f i <= a) -> ⨆ i, f i <= a
  证明: ciSup_le'
-/
protected theorem iSup_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i <= a) -> ⨆ i, f i <= a :=
  ciSup_le'

/-- `lt_ciSup_iff'` whenever the input type is small in the output universe. -/
@[simp]
/--
theorem `lt_iSup_iff` / 定理 `lt_iSup_iff`

English:
theorem lt_iSup_iff
  given: {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι]
  proof: lt_ciSup_iff' bddAbove_of_small

中文:
定理 lt_iSup_iff
  条件: {ι} {f : ι -> 序数.{u}} {a : 序数.{u}} [Small.{u} ι]
  证明: lt_ciSup_iff' bddAbove_of_small
-/
protected theorem lt_iSup_iff {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    a < ⨆ i, f i ↔ exists i, a < f i :=
  lt_ciSup_iff' bddAbove_of_small

/--
theorem `lt_iSup_add_one` / 定理 `lt_iSup_add_one`

English:
theorem lt_iSup_add_one
  given: {ι} (f : ι -> Ordinal.{u}) [Small.{u} ι] (i)
  statement: f i < ⨆ i, f i + 1
  proof: by
  rw [← add_one_le_iff]
  apply Ordinal.le_iSup

中文:
定理 lt_iSup_add_one
  条件: {ι} (f : ι -> 序数.{u}) [Small.{u} ι] (i)
  结论: f i < ⨆ i, f i + 1
  证明: by
  rw [← add_one_le_iff]
  apply Ordinal.le_iSup

Depends on / 依赖: Ordinal, Ordinal.le_iSup, add_one_le_iff, le_iSup
-/
theorem lt_iSup_add_one {ι} (f : ι -> Ordinal.{u}) [Small.{u} ι] (i) : f i < ⨆ i, f i + 1 := by
  rw [← add_one_le_iff]
  apply Ordinal.le_iSup

/--
theorem `iSup_add_one_le_iff` / 定理 `iSup_add_one_le_iff`

English:
theorem iSup_add_one_le_iff
  given: {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι]
  proof: by
  simp

中文:
定理 iSup_add_one_le_iff
  条件: {ι} {f : ι -> 序数.{u}} {a : 序数.{u}} [Small.{u} ι]
  证明: by
  simp
-/
theorem iSup_add_one_le_iff {ι} {f : ι -> Ordinal.{u}} {a : Ordinal.{u}} [Small.{u} ι] :
    ⨆ i, f i + 1 <= a ↔ forall i, f i < a := by
  simp

/--
theorem `iSup_add_one_le` / 定理 `iSup_add_one_le`

English:
theorem iSup_add_one_le
  given: {ι} {f : ι -> Ordinal.{u}} {a} (h : forall i, f i < a)
  statement: ⨆ i, f i + 1 <= a
  proof: ciSup_le' (by simpa)

中文:
定理 iSup_add_one_le
  条件: {ι} {f : ι -> 序数.{u}} {a} (h : 对任意 i, f i < a)
  结论: ⨆ i, f i + 1 <= a
  证明: ciSup_le' (by simpa)

Depends on / 依赖: ciSup_le
-/
theorem iSup_add_one_le {ι} {f : ι -> Ordinal.{u}} {a} (h : forall i, f i < a) : ⨆ i, f i + 1 <= a :=
  ciSup_le' (by simpa)

/--
theorem `lt_iSup_add_one_iff` / 定理 `lt_iSup_add_one_iff`

English:
theorem lt_iSup_add_one_iff
  given: {ι} {f : ι -> Ordinal.{u}} {a} [Small.{u} ι]
  proof: by
  simp

中文:
定理 lt_iSup_add_one_iff
  条件: {ι} {f : ι -> 序数.{u}} {a} [Small.{u} ι]
  证明: by
  simp
-/
theorem lt_iSup_add_one_iff {ι} {f : ι -> Ordinal.{u}} {a} [Small.{u} ι] :
    a < ⨆ i, f i + 1 ↔ exists i, a <= f i := by
  simp

-- TODO: state in terms of `IsSuccLimit`.
/--
theorem `succ_lt_iSup_of_ne_iSup` / 定理 `succ_lt_iSup_of_ne_iSup`

English:
theorem succ_lt_iSup_of_ne_iSup
  statement: {ι} {f : ι -> Ordinal.{u}} [Small.{u} ι]
  proof: by
  by_contra! hoa
  exact hao.not_ge (Ordinal.iSup_le fun i => le_of_lt_succ <|
    ((Ordinal.le_iSup _ _).lt_of_ne (hf i)).trans_le hoa)

中文:
定理 succ_lt_iSup_of_ne_iSup
  结论: {ι} {f : ι -> 序数.{u}} [Small.{u} ι]
  证明: by
  by_contra! hoa
  exact hao.not_ge (Ordinal.iSup_le fun i => le_of_lt_succ <|
    ((Ordinal.le_iSup _ _).lt_of_ne (hf i)).trans_le hoa)

Depends on / 依赖: Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, hao.not_ge, iSup_le, le_iSup, le_of_lt_succ, lt_of_ne, not_ge, trans_le
-/
theorem succ_lt_iSup_of_ne_iSup {ι} {f : ι -> Ordinal.{u}} [Small.{u} ι]
    (hf : forall i, f i != iSup f) {a} (hao : a < iSup f) : succ a < iSup f := by
  by_contra! hoa
  exact hao.not_ge (Ordinal.iSup_le fun i => le_of_lt_succ <|
    ((Ordinal.le_iSup _ _).lt_of_ne (hf i)).trans_le hoa)

-- TODO: generalize to conditionally complete lattices.
/--
theorem `iSup_eq_zero_iff` / 定理 `iSup_eq_zero_iff`

English:
theorem iSup_eq_zero_iff
  given: {ι} {f : ι -> Ordinal.{u}} [Small.{u} ι]
  proof: by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (Ordinal.iSup_le fun i => nonpos_iff_eq_zero.2 (h i)) zero_le⟩
  rw [← nonpos_iff_eq_zero]; rw [← h]
  exact Ordinal.le_iSup f i

@[deprecated congrArg (since := "2026-03-27")]

中文:
定理 iSup_eq_zero_iff
  条件: {ι} {f : ι -> 序数.{u}} [Small.{u} ι]
  证明: by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (Ordinal.iSup_le fun i => nonpos_iff_eq_zero.2 (h i)) zero_le⟩
  rw [← nonpos_iff_eq_zero]; rw [← h]
  exact Ordinal.le_iSup f i

@[deprecated congrArg (since := "2026-03-27")]

Depends on / 依赖: Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, iSup_le, le_antisymm, le_iSup, nonpos_iff_eq_zero, zero_le
-/
theorem iSup_eq_zero_iff {ι} {f : ι -> Ordinal.{u}} [Small.{u} ι] :
    iSup f = 0 ↔ forall i, f i = 0 := by
  refine
    ⟨fun h i => ?_, fun h =>
      le_antisymm (Ordinal.iSup_le fun i => nonpos_iff_eq_zero.2 (h i)) zero_le⟩
  rw [← nonpos_iff_eq_zero]; rw [← h]
  exact Ordinal.le_iSup f i

@[deprecated congrArg (since := "2026-03-27")]
/--
theorem `iSup_eq_of_range_eq` / 定理 `iSup_eq_of_range_eq`

English:
theorem iSup_eq_of_range_eq
  statement: {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal}
  proof: congr_arg _ h

中文:
定理 iSup_eq_of_range_eq
  结论: {ι ι'} {f : ι -> 序数} {g : ι' -> 序数}
  证明: congr_arg _ h

Depends on / 依赖: congr_arg
-/
theorem iSup_eq_of_range_eq {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal}
    (h : Set.range f = Set.range g) : iSup f = iSup g :=
  congr_arg _ h

-- TODO: generalize to conditionally complete lattices
/--
theorem `iSup_sum` / 定理 `iSup_sum`

English:
theorem iSup_sum
  given: {α β} (f : α oplus β -> Ordinal.{u}) [Small.{u} α] [Small.{u} β]
  proof: by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x => f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x => f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' bddAbove_of_small
    rintro i ⟨a, rfl⟩

中文:
定理 iSup_sum
  条件: {α β} (f : α oplus β -> 序数.{u}) [Small.{u} α] [Small.{u} β]
  证明: by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x => f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x => f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' bddAbove_of_small
    rintro i ⟨a, rfl⟩

Depends on / 依赖: Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, Sum.inl, Sum.inr, all_goals, antisymm, bddAbove_of_small, csSup_le_csSup, iSup_le, le_iSup, le_max_of_le_left, le_max_of_le_right, max_le, mem_range_self
-/
theorem iSup_sum {α β} (f : α oplus β -> Ordinal.{u}) [Small.{u} α] [Small.{u} β] :
    iSup f = max (⨆ a, f (Sum.inl a)) (⨆ b, f (Sum.inr b)) := by
  apply (Ordinal.iSup_le _).antisymm (max_le _ _)
  · rintro (i | i)
    · exact le_max_of_le_left (Ordinal.le_iSup (fun x => f (Sum.inl x)) i)
    · exact le_max_of_le_right (Ordinal.le_iSup (fun x => f (Sum.inr x)) i)
  all_goals
    apply csSup_le_csSup' bddAbove_of_small
    rintro i ⟨a, rfl⟩
    apply mem_range_self

/--
theorem `unbounded_range_of_le_iSup` / 定理 `unbounded_range_of_le_iSup`

English:
theorem unbounded_range_of_le_iSup
  statement: {α β : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β -> α)
  proof: (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
h.not_gt lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)

中文:
定理 unbounded_range_of_le_iSup
  结论: {α β : 类型u} (r : α -> α -> 命题) [是良序 α r] (f : β -> α)
  证明: (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
h.not_gt lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)

Depends on / 依赖: Ordinal, Ordinal.iSup_le, h.not_gt, iSup_le, lt_of_le_of_lt, mem_range_self, not_bounded_iff, not_gt, typein_lt_type, typein_lt_typein
-/
theorem unbounded_range_of_le_iSup {α β : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β -> α)
    (h : type r <= ⨆ i, typein r (f i)) : Unbounded r (range f) :=
  (not_bounded_iff _).1 fun ⟨x, hx⟩ =>
h.not_gt lt_of_le_of_lt
      (Ordinal.iSup_le fun y => ((typein_lt_typein r).2 <| hx _ <| mem_range_self y).le)
      (typein_lt_type r x)

/--
theorem `sSup_ord` / 定理 `sSup_ord`

English:
theorem sSup_ord
  given: (s : Set Cardinal)
  statement: (sSup s).ord = sSup (ord '' s)
  proof: by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · simp
  · by_cases hs : BddAbove s
    · exact isNormal_ord.map_sSup hn hs
    · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (bddAbove_ord_image_iff.not.2 hs)]
      simp

中文:
定理 sSup_ord
  条件: (s : 集合 基数)
  结论: (sSup s).ord = sSup (ord '' s)
  证明: by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · simp
  · by_cases hs : BddAbove s
    · exact isNormal_ord.map_sSup hn hs
    · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (bddAbove_ord_image_iff.not.2 hs)]
      simp

Depends on / 依赖: BddAbove, bddAbove_ord_image_iff, bddAbove_ord_image_iff.not, csSup_of_not_bddAbove, eq_empty_or_nonempty, isNormal_ord, isNormal_ord.map_sSup, map_sSup, s.eq_empty_or_nonempty
-/
theorem sSup_ord (s : Set Cardinal) : (sSup s).ord = sSup (ord '' s) := by
  obtain rfl | hn := s.eq_empty_or_nonempty
  · simp
  · by_cases hs : BddAbove s
    · exact isNormal_ord.map_sSup hn hs
    · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (bddAbove_ord_image_iff.not.2 hs)]
      simp

/--
theorem `iSup_ord` / 定理 `iSup_ord`

English:
theorem iSup_ord
  given: {ι} (f : ι -> Cardinal)
  statement: (⨆ i, f i).ord = ⨆ i, (f i).ord
  proof: by
  rw [iSup]; rw [iSup]; rw [sSup_ord]; rw [range_comp']

中文:
定理 iSup_ord
  条件: {ι} (f : ι -> 基数)
  结论: (⨆ i, f i).ord = ⨆ i, (f i).ord
  证明: by
  rw [iSup]; rw [iSup]; rw [sSup_ord]; rw [range_comp']

Depends on / 依赖: range_comp, sSup_ord
-/
theorem iSup_ord {ι} (f : ι -> Cardinal) : (⨆ i, f i).ord = ⨆ i, (f i).ord := by
  rw [iSup]; rw [iSup]; rw [sSup_ord]; rw [range_comp']

/--
theorem `lift_card_sInf_compl_le` / 定理 `lift_card_sInf_compl_le`

English:
theorem lift_card_sInf_compl_le
  given: (s : Set Ordinal.{u})
  proof: by
  rw [← Cardinal.mk_Iio_ordinal]
  refine mk_le_mk_of_subset fun x (hx : x < _) => ?_
  rw [← not_notMem]
  exact notMem_of_lt_csInf' hx

中文:
定理 lift_card_sInf_compl_le
  条件: (s : 集合 序数.{u})
  证明: by
  rw [← Cardinal.mk_Iio_ordinal]
  refine mk_le_mk_of_subset fun x (hx : x < _) => ?_
  rw [← not_notMem]
  exact notMem_of_lt_csInf' hx

Depends on / 依赖: Cardinal, Cardinal.mk_Iio_ordinal, mk_Iio_ordinal, mk_le_mk_of_subset, notMem_of_lt_csInf, not_notMem
-/
theorem lift_card_sInf_compl_le (s : Set Ordinal.{u}) :
    Cardinal.lift.{u + 1} (sInf sᶜ).card <= #s := by
  rw [← Cardinal.mk_Iio_ordinal]
  refine mk_le_mk_of_subset fun x (hx : x < _) => ?_
  rw [← not_notMem]
  exact notMem_of_lt_csInf' hx

/--
theorem `card_sInf_range_compl_le_lift` / 定理 `card_sInf_range_compl_le_lift`

English:
theorem card_sInf_range_compl_le_lift
  given: {ι : Type u} (f : ι -> Ordinal.{max u v})
  proof: by
  rw [← Cardinal.lift_le.{max u v + 1}]; rw [Cardinal.lift_lift]
  apply (lift_card_sInf_compl_le _).trans
  rw [← Cardinal.lift_id'.{u]; rw [max u v + 1} #(range _)]
  exact mk_range_le_lift

中文:
定理 card_sInf_range_compl_le_lift
  条件: {ι : 类型u} (f : ι -> 序数.{最大值 u v})
  证明: by
  rw [← Cardinal.lift_le.{max u v + 1}]; rw [Cardinal.lift_lift]
  apply (lift_card_sInf_compl_le _).trans
  rw [← Cardinal.lift_id'.{u]; rw [max u v + 1} #(range _)]
  exact mk_range_le_lift

Depends on / 依赖: Cardinal, Cardinal.lift_id, Cardinal.lift_le, Cardinal.lift_lift, lift_card_sInf_compl_le, lift_id, lift_le, lift_lift, mk_range_le_lift
-/
theorem card_sInf_range_compl_le_lift {ι : Type u} (f : ι -> Ordinal.{max u v}) :
    (sInf (range f)ᶜ).card <= Cardinal.lift.{v} #ι := by
  rw [← Cardinal.lift_le.{max u v + 1}]; rw [Cardinal.lift_lift]
  apply (lift_card_sInf_compl_le _).trans
  rw [← Cardinal.lift_id'.{u]; rw [max u v + 1} #(range _)]
  exact mk_range_le_lift

/--
theorem `card_sInf_range_compl_le` / 定理 `card_sInf_range_compl_le`

English:
theorem card_sInf_range_compl_le
  given: {ι : Type u} (f : ι -> Ordinal.{u})
  proof: Cardinal.lift_id #ι ▸ card_sInf_range_compl_le_lift f

中文:
定理 card_sInf_range_compl_le
  条件: {ι : 类型u} (f : ι -> 序数.{u})
  证明: Cardinal.lift_id #ι ▸ card_sInf_range_compl_le_lift f

Depends on / 依赖: Cardinal, Cardinal.lift_id, card_sInf_range_compl_le_lift, lift_id
-/
theorem card_sInf_range_compl_le {ι : Type u} (f : ι -> Ordinal.{u}) :
    (sInf (range f)ᶜ).card <= #ι :=
  Cardinal.lift_id #ι ▸ card_sInf_range_compl_le_lift f

/--
theorem `sInf_compl_lt_lift_ord_succ` / 定理 `sInf_compl_lt_lift_ord_succ`

English:
theorem sInf_compl_lt_lift_ord_succ
  given: {ι : Type u} (f : ι -> Ordinal.{max u v})
  proof: by
  rw [lift_ord]; rw [Cardinal.lift_succ]; rw [← card_le_iff]
  exact card_sInf_range_compl_le_lift f

中文:
定理 sInf_compl_lt_lift_ord_succ
  条件: {ι : 类型u} (f : ι -> 序数.{最大值 u v})
  证明: by
  rw [lift_ord]; rw [Cardinal.lift_succ]; rw [← card_le_iff]
  exact card_sInf_range_compl_le_lift f

Depends on / 依赖: Cardinal, Cardinal.lift_succ, card_le_iff, card_sInf_range_compl_le_lift, lift_ord, lift_succ
-/
theorem sInf_compl_lt_lift_ord_succ {ι : Type u} (f : ι -> Ordinal.{max u v}) :
    sInf (range f)ᶜ < lift.{v} (succ #ι).ord := by
  rw [lift_ord]; rw [Cardinal.lift_succ]; rw [← card_le_iff]
  exact card_sInf_range_compl_le_lift f

/--
theorem `sInf_compl_lt_ord_succ` / 定理 `sInf_compl_lt_ord_succ`

English:
theorem sInf_compl_lt_ord_succ
  given: {ι : Type u} (f : ι -> Ordinal.{u})
  proof: lift_id (succ #ι).ord ▸ sInf_compl_lt_lift_ord_succ f

中文:
定理 sInf_compl_lt_ord_succ
  条件: {ι : 类型u} (f : ι -> 序数.{u})
  证明: lift_id (succ #ι).ord ▸ sInf_compl_lt_lift_ord_succ f

Depends on / 依赖: lift_id, sInf_compl_lt_lift_ord_succ
-/
theorem sInf_compl_lt_ord_succ {ι : Type u} (f : ι -> Ordinal.{u}) :
    sInf (range f)ᶜ < (succ #ι).ord :=
  lift_id (succ #ι).ord ▸ sInf_compl_lt_lift_ord_succ f

/--
theorem `bddAbove_add_one_image_iff` / 定理 `bddAbove_add_one_image_iff`

English:
theorem bddAbove_add_one_image_iff
  given: {s : Set Ordinal}
  proof: by
  constructor <;> rintro ⟨a, ha⟩
  · exact ⟨a, fun b hb => (lt_add_one _).le.trans (ha (mem_image_of_mem _ hb))⟩
  · use a + 1
    simpa [upperBounds]

中文:
定理 bddAbove_add_one_image_iff
  条件: {s : 集合 序数}
  证明: by
  constructor <;> rintro ⟨a, ha⟩
  · exact ⟨a, fun b hb => (lt_add_one _).le.trans (ha (mem_image_of_mem _ hb))⟩
  · use a + 1
    simpa [upperBounds]

Depends on / 依赖: le.trans, lt_add_one, mem_image_of_mem, upperBounds
-/
theorem bddAbove_add_one_image_iff {s : Set Ordinal} :
    BddAbove ((· + 1) '' s) ↔ BddAbove s := by
  constructor <;> rintro ⟨a, ha⟩
  · exact ⟨a, fun b hb => (lt_add_one _).le.trans (ha (mem_image_of_mem _ hb))⟩
  · use a + 1
    simpa [upperBounds]

/--
theorem `bddAbove_range_add_one_iff` / 定理 `bddAbove_range_add_one_iff`

English:
theorem bddAbove_range_add_one_iff
  given: {f : β -> Ordinal.{u}}
  proof: by
  rw [range_comp' (· + 1)]; rw [bddAbove_add_one_image_iff]

中文:
定理 bddAbove_range_add_one_iff
  条件: {f : β -> 序数.{u}}
  证明: by
  rw [range_comp' (· + 1)]; rw [bddAbove_add_one_image_iff]

Depends on / 依赖: bddAbove_add_one_image_iff, range_comp
-/
theorem bddAbove_range_add_one_iff {f : β -> Ordinal.{u}} :
    BddAbove (range fun i => f i + 1) ↔ BddAbove (range f) := by
  rw [range_comp' (· + 1)]; rw [bddAbove_add_one_image_iff]

/--
theorem `sSup_le_sSup_add_one` / 定理 `sSup_le_sSup_add_one`

English:
theorem sSup_le_sSup_add_one
  given: (s : Set Ordinal)
  statement: sSup s <= sSup ((· + 1) '' s)
  proof: by
  by_cases hs : BddAbove s
  · have hs' := bddAbove_add_one_image_iff.2 hs
    rw [csSup_le_iff' hs]
    exact fun x hx => (lt_add_one _).le.trans (le_csSup hs' (mem_image_of_mem _ hx))
  · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := _ '' _)]
    rwa [bddAbove_add_one_image_iff]

中文:
定理 sSup_le_sSup_add_one
  条件: (s : 集合 序数)
  结论: sSup s <= sSup ((· + 1) '' s)
  证明: by
  by_cases hs : BddAbove s
  · have hs' := bddAbove_add_one_image_iff.2 hs
    rw [csSup_le_iff' hs]
    exact fun x hx => (lt_add_one _).le.trans (le_csSup hs' (mem_image_of_mem _ hx))
  · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := _ '' _)]
    rwa [bddAbove_add_one_image_iff]

Depends on / 依赖: BddAbove, bddAbove_add_one_image_iff, csSup_le_iff, csSup_of_not_bddAbove, le.trans, le_csSup, lt_add_one, mem_image_of_mem
-/
theorem sSup_le_sSup_add_one (s : Set Ordinal) : sSup s <= sSup ((· + 1) '' s) := by
  by_cases hs : BddAbove s
  · have hs' := bddAbove_add_one_image_iff.2 hs
    rw [csSup_le_iff' hs]
    exact fun x hx => (lt_add_one _).le.trans (le_csSup hs' (mem_image_of_mem _ hx))
  · rw [csSup_of_not_bddAbove hs, csSup_of_not_bddAbove (s := _ '' _)]
    rwa [bddAbove_add_one_image_iff]

/--
theorem `iSup_le_iSup_add_one` / 定理 `iSup_le_iSup_add_one`

English:
theorem iSup_le_iSup_add_one
  given: (f : β -> Ordinal)
  statement: ⨆ i, f i <= ⨆ i, f i + 1
  proof: by
  rw [iSup]; rw [iSup]; rw [range_comp' (· + 1)]
  exact sSup_le_sSup_add_one _

中文:
定理 iSup_le_iSup_add_one
  条件: (f : β -> 序数)
  结论: ⨆ i, f i <= ⨆ i, f i + 1
  证明: by
  rw [iSup]; rw [iSup]; rw [range_comp' (· + 1)]
  exact sSup_le_sSup_add_one _

Depends on / 依赖: range_comp, sSup_le_sSup_add_one
-/
theorem iSup_le_iSup_add_one (f : β -> Ordinal) : ⨆ i, f i <= ⨆ i, f i + 1 := by
  rw [iSup]; rw [iSup]; rw [range_comp' (· + 1)]
  exact sSup_le_sSup_add_one _

/--
theorem `iSup_add_one` / 定理 `iSup_add_one`

English:
theorem iSup_add_one
  statement: {β : Type*} [LinearOrder β] [NoMaxOrder β]
  proof: by
  apply (iSup_le_iSup_add_one f).antisymm'
  by_cases hf' : BddAbove (range f)
  · rw [ciSup_le_iff' (bddAbove_range_add_one_iff.2 hf')]
    intro i
    obtain ⟨j, hj⟩ := exists_gt i
    apply (le_ciSup hf' j).trans'
    rw [add_one_le_iff]
    exact hf hj
  · rw [ciSup_of_not_bddAbove hf', ciSup

中文:
定理 iSup_add_one
  结论: {β : 类型} [线性序 β] [NoMax序 β]
  证明: by
  apply (iSup_le_iSup_add_one f).antisymm'
  by_cases hf' : BddAbove (range f)
  · rw [ciSup_le_iff' (bddAbove_range_add_one_iff.2 hf')]
    intro i
    obtain ⟨j, hj⟩ := exists_gt i
    apply (le_ciSup hf' j).trans'
    rw [add_one_le_iff]
    exact hf hj
  · rw [ciSup_of_not_bddAbove hf', ciSup

Depends on / 依赖: BddAbove, add_one_le_iff, antisymm, bddAbove_range_add_one_iff, ciSup_le_iff, ciSup_of_not_bddAbove, exists_gt, iSup_le_iSup_add_one, le_ciSup
-/
theorem iSup_add_one {β : Type*} [LinearOrder β] [NoMaxOrder β]
    {f : β -> Ordinal.{u}} (hf : StrictMono f) : ⨆ i, f i + 1 = ⨆ i, f i := by
  apply (iSup_le_iSup_add_one f).antisymm'
  by_cases hf' : BddAbove (range f)
  · rw [ciSup_le_iff' (bddAbove_range_add_one_iff.2 hf')]
    intro i
    obtain ⟨j, hj⟩ := exists_gt i
    apply (le_ciSup hf' j).trans'
    rw [add_one_le_iff]
    exact hf hj
  · rw [ciSup_of_not_bddAbove hf', ciSup_of_not_bddAbove]
    rwa [← bddAbove_range_add_one_iff] at hf'

/--
theorem `iSup_Iio_add_one` / 定理 `iSup_Iio_add_one`

English:
theorem iSup_Iio_add_one
  statement: {a : Ordinal.{u}} {f : Iio a -> Ordinal.{u}}
  proof: by
  have := ha.noMaxOrder_Iio
  exact iSup_add_one hf

中文:
定理 iSup_Iio_add_one
  结论: {a : 序数.{u}} {f : 左无界右开区间 a -> 序数.{u}}
  证明: by
  have := ha.noMaxOrder_Iio
  exact iSup_add_one hf

Depends on / 依赖: ha.noMaxOrder_Iio, iSup_add_one, noMaxOrder_Iio
-/
theorem iSup_Iio_add_one {a : Ordinal.{u}} {f : Iio a -> Ordinal.{u}}
    (hf : StrictMono f) (ha : IsSuccPrelimit a) : ⨆ i : Iio a, f i + 1 = ⨆ i : Iio a, f i := by
  have := ha.noMaxOrder_Iio
  exact iSup_add_one hf

section bsup

@[deprecated "familyOfBFamily is deprecated" (since := "2026-04-06")]
/--
theorem `iSup_eq_iSup` / 定理 `iSup_eq_iSup`

English:
theorem iSup_eq_iSup
  statement: {ι ι' : Type u} (r : ι -> ι -> Prop) (r' : ι' -> ι' -> Prop) [IsWellOrder ι r]
  proof: congrArg sSup (by simp_rw [range_familyOfBFamily'])

中文:
定理 iSup_eq_iSup
  结论: {ι ι' : 类型u} (r : ι -> ι -> 命题) (r' : ι' -> ι' -> 命题) [是良序 ι r]
  证明: congrArg sSup (by simp_rw [range_familyOfBFamily'])

Depends on / 依赖: range_familyOfBFamily, simp_rw
-/
theorem iSup_eq_iSup {ι ι' : Type u} (r : ι -> ι -> Prop) (r' : ι' -> ι' -> Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o : Ordinal} (ho : type r = o) (ho' : type r' = o) (f : forall a < o, Ordinal) :
    iSup (familyOfBFamily' r ho f) = iSup (familyOfBFamily' r' ho' f) :=
  congrArg sSup (by simp_rw [range_familyOfBFamily'])

/-- The supremum of a family of ordinals indexed by the set of ordinals less than some
`o : Ordinal.{u}`. This is a special case of `iSup` over the family provided by
`familyOfBFamily`. -/
@[deprecated "write `⨆ i : Iio a, f i` instead." (since := "2026-04-05")]
/--
Definition of `bsup` / `bsup` 的定义

English:
definition bsup
  signature: (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v})
  body: iSup (familyOfBFamily o f)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定义 bsup
  签名: (o : 序数.{u}) (f : 对任意 a < o, 序数.{最大值 u v})
  定义体: iSup (familyOfBFamily o f)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: familyOfBFamily
-/
def bsup (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  iSup (familyOfBFamily o f)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `iSup_eq_bsup` / 定理 `iSup_eq_bsup`

English:
theorem iSup_eq_bsup
  given: {o : Ordinal} (f : forall a < o, Ordinal)
  proof: rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 iSup_eq_bsup
  条件: {o : 序数} (f : 对任意 a < o, 序数)
  证明: rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
-/
theorem iSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordinal) :
    iSup (familyOfBFamily o f) = bsup o f :=
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `iSup'_eq_bsup` / 定理 `iSup'_eq_bsup`

English:
theorem iSup'_eq_bsup
  statement: {o : Ordinal} {ι} (r : ι -> ι -> Prop) [IsWellOrder ι r] (ho : type r = o)
  proof: iSup_eq_iSup r _ ho _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 iSup'_eq_bsup
  结论: {o : 序数} {ι} (r : ι -> ι -> 命题) [是良序 ι r] (ho : type r = o)
  证明: iSup_eq_iSup r _ ho _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: iSup_eq_iSup
-/
theorem iSup'_eq_bsup {o : Ordinal} {ι} (r : ι -> ι -> Prop) [IsWellOrder ι r] (ho : type r = o)
    (f : forall a < o, Ordinal) : iSup (familyOfBFamily' r ho f) = bsup o f :=
  iSup_eq_iSup r _ ho _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `sSup_eq_bsup` / 定理 `sSup_eq_bsup`

English:
theorem sSup_eq_bsup
  given: {o : Ordinal} (f : forall a < o, Ordinal)
  statement: sSup (brange o f) = bsup o f
  proof: by
  congr
  rw [range_familyOfBFamily]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 sSup_eq_bsup
  条件: {o : 序数} (f : 对任意 a < o, 序数)
  结论: sSup (brange o f) = bsup o f
  证明: by
  congr
  rw [range_familyOfBFamily]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: range_familyOfBFamily
-/
theorem sSup_eq_bsup {o : Ordinal} (f : forall a < o, Ordinal) : sSup (brange o f) = bsup o f := by
  congr
  rw [range_familyOfBFamily]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup'_eq_iSup` / 定理 `bsup'_eq_iSup`

English:
theorem bsup'_eq_iSup
  given: {ι} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> Ordinal)
  proof: by
  simp +unfoldPartialApp only [← iSup'_eq_bsup r, enum_typein, familyOfBFamily', bfamilyOfFamily']

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup'_eq_iSup
  条件: {ι} (r : ι -> ι -> 命题) [是良序 ι r] (f : ι -> 序数)
  证明: by
  simp +unfoldPartialApp only [← iSup'_eq_bsup r, enum_typein, familyOfBFamily', bfamilyOfFamily']

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: _eq_bsup, bfamilyOfFamily, enum_typein, familyOfBFamily, unfoldPartialApp
-/
theorem bsup'_eq_iSup {ι} (r : ι -> ι -> Prop) [IsWellOrder ι r] (f : ι -> Ordinal) :
    bsup _ (bfamilyOfFamily' r f) = iSup f := by
  simp +unfoldPartialApp only [← iSup'_eq_bsup r, enum_typein, familyOfBFamily', bfamilyOfFamily']

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_eq_iSup` / 定理 `bsup_eq_iSup`

English:
theorem bsup_eq_iSup
  given: {ι} (f : ι -> Ordinal)
  statement: bsup _ (bfamilyOfFamily f) = iSup f
  proof: bsup'_eq_iSup _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_eq_iSup
  条件: {ι} (f : ι -> 序数)
  结论: bsup _ (bfamilyOfFamily f) = iSup f
  证明: bsup'_eq_iSup _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: _eq_iSup
-/
theorem bsup_eq_iSup {ι} (f : ι -> Ordinal) : bsup _ (bfamilyOfFamily f) = iSup f :=
  bsup'_eq_iSup _ f

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_eq_bsup` / 定理 `bsup_eq_bsup`

English:
theorem bsup_eq_bsup
  statement: {ι : Type u} (r r' : ι -> ι -> Prop) [IsWellOrder ι r] [IsWellOrder ι r']
  proof: by
  rw [bsup'_eq_iSup]; rw [bsup'_eq_iSup]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_eq_bsup
  结论: {ι : 类型u} (r r' : ι -> ι -> 命题) [是良序 ι r] [是良序 ι r']
  证明: by
  rw [bsup'_eq_iSup]; rw [bsup'_eq_iSup]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: _eq_iSup
-/
theorem bsup_eq_bsup {ι : Type u} (r r' : ι -> ι -> Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι -> Ordinal.{max u v}) :
    bsup.{_, v} _ (bfamilyOfFamily' r f) = bsup.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [bsup'_eq_iSup]; rw [bsup'_eq_iSup]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_congr` / 定理 `bsup_congr`

English:
theorem bsup_congr
  given: {o₁ o₂ : Ordinal.{u}} (f : forall a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂)
  proof: by
  subst ho
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_congr
  条件: {o₁ o₂ : 序数.{u}} (f : 对任意 a < o₁, 序数.{最大值 u v}) (ho : o₁ = o₂)
  证明: by
  subst ho
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
-/
theorem bsup_congr {o₁ o₂ : Ordinal.{u}} (f : forall a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    bsup.{_, v} o₁ f = bsup.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_le_iff` / 定理 `bsup_le_iff`

English:
theorem bsup_le_iff
  given: {o f a}
  statement: bsup.{u, v} o f <= a ↔ forall i h, f i h <= a
  proof: Ordinal.iSup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_le_iff
  条件: {o f a}
  结论: bsup.{u, v} o f <= a ↔ 对任意 i h, f i h <= a
  证明: Ordinal.iSup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: Ordinal, Ordinal.iSup_le_iff.trans, familyOfBFamily_enum, iSup_le_iff
-/
theorem bsup_le_iff {o f a} : bsup.{u, v} o f <= a ↔ forall i h, f i h <= a :=
  Ordinal.iSup_le_iff.trans
    ⟨fun h i hi => by
      rw [← familyOfBFamily_enum o f]
      exact h _, fun h _ => h _ _⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_le` / 定理 `bsup_le`

English:
theorem bsup_le
  given: {o : Ordinal} {f : forall b < o, Ordinal} {a}
  proof: bsup_le_iff.2

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_le
  条件: {o : 序数} {f : 对任意 b < o, 序数} {a}
  证明: bsup_le_iff.2

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_le_iff
-/
theorem bsup_le {o : Ordinal} {f : forall b < o, Ordinal} {a} :
    (forall i h, f i h <= a) -> bsup.{u, v} o f <= a :=
  bsup_le_iff.2

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `le_bsup` / 定理 `le_bsup`

English:
theorem le_bsup
  given: {o} (f : forall a < o, Ordinal) (i h)
  statement: f i h <= bsup o f
  proof: bsup_le_iff.1 le_rfl _ _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 le_bsup
  条件: {o} (f : 对任意 a < o, 序数) (i h)
  结论: f i h <= bsup o f
  证明: bsup_le_iff.1 le_rfl _ _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_le_iff, le_rfl
-/
theorem le_bsup {o} (f : forall a < o, Ordinal) (i h) : f i h <= bsup o f :=
  bsup_le_iff.1 le_rfl _ _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `lt_bsup` / 定理 `lt_bsup`

English:
theorem lt_bsup
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) {a}
  proof: by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

@[deprecated IsNormal.map_iSup (since := "2026-04-05")]

中文:
定理 lt_bsup
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v}) {a}
  证明: by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

@[deprecated IsNormal.map_iSup (since := "2026-04-05")]

Depends on / 依赖: bsup_le_iff, not_congr, not_forall, not_le
-/
theorem lt_bsup {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) {a} :
    a < bsup.{_, v} o f ↔ exists i hi, a < f i hi := by
  simpa only [not_forall, not_le] using not_congr (@bsup_le_iff.{_, v} _ f a)

@[deprecated IsNormal.map_iSup (since := "2026-04-05")]
/--
theorem `IsNormal.bsup` / 定理 `IsNormal.bsup`

English:
theorem IsNormal.bsup
  given: {f : Ordinal -> Ordinal} (H : IsNormal f) {o : Ordinal}
  proof: inductionOn o fun α r _ g h => by
    have := type_ne_zero_iff_nonempty.1 h
    rw [← iSup'_eq_bsup r]; rw [Order.IsNormal.map_iSup H bddAbove_of_small]; rw [← iSup'_eq_bsup r] <;>
      rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 是正规.bsup
  条件: {f : 序数 -> 序数} (H : 是正规 f) {o : 序数}
  证明: inductionOn o fun α r _ g h => by
    have := type_ne_zero_iff_nonempty.1 h
    rw [← iSup'_eq_bsup r]; rw [Order.IsNormal.map_iSup H bddAbove_of_small]; rw [← iSup'_eq_bsup r] <;>
      rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: IsNormal, Order.IsNormal.map_iSup, _eq_bsup, bddAbove_of_small, inductionOn, map_iSup, type_ne_zero_iff_nonempty
-/
theorem IsNormal.bsup {f : Ordinal -> Ordinal} (H : IsNormal f) {o : Ordinal} :
    forall (g : forall a < o, Ordinal), o != 0 -> f (bsup o g) = bsup o fun a h => f (g a h) :=
  inductionOn o fun α r _ g h => by
    have := type_ne_zero_iff_nonempty.1 h
    rw [← iSup'_eq_bsup r]; rw [Order.IsNormal.map_iSup H bddAbove_of_small]; rw [← iSup'_eq_bsup r] <;>
      rfl

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `lt_bsup_of_ne_bsup` / 定理 `lt_bsup_of_ne_bsup`

English:
theorem lt_bsup_of_ne_bsup
  given: {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}}
  proof: ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 lt_bsup_of_ne_bsup
  条件: {o : 序数.{u}} {f : 对任意 a < o, 序数.{最大值 u v}}
  证明: ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: le_bsup, lt_of_le_of_ne, ne_of_lt
-/
theorem lt_bsup_of_ne_bsup {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}} :
    (forall i h, f i h != bsup.{_, v} o f) ↔ forall i h, f i h < bsup.{_, v} o f :=
  ⟨fun hf _ _ => lt_of_le_of_ne (le_bsup _ _ _) (hf _ _), fun hf _ _ => ne_of_lt (hf _ _)⟩

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_not_succ_of_ne_bsup` / 定理 `bsup_not_succ_of_ne_bsup`

English:
theorem bsup_not_succ_of_ne_bsup
  statement: {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}}
  proof: by
  rw [← iSup_eq_bsup] at *
  exact succ_lt_iSup_of_ne_iSup fun i => hf _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_not_succ_of_ne_bsup
  结论: {o : 序数.{u}} {f : 对任意 a < o, 序数.{最大值 u v}}
  证明: by
  rw [← iSup_eq_bsup] at *
  exact succ_lt_iSup_of_ne_iSup fun i => hf _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: iSup_eq_bsup, succ_lt_iSup_of_ne_iSup
-/
theorem bsup_not_succ_of_ne_bsup {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}}
    (hf : forall {i : Ordinal} (h : i < o), f i h != bsup.{_, v} o f) (a) :
    a < bsup.{_, v} o f -> succ a < bsup.{_, v} o f := by
  rw [← iSup_eq_bsup] at *
  exact succ_lt_iSup_of_ne_iSup fun i => hf _

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_eq_zero_iff` / 定理 `bsup_eq_zero_iff`

English:
theorem bsup_eq_zero_iff
  given: {o} {f : forall a < o, Ordinal}
  statement: bsup o f = 0 ↔ forall i hi, f i hi = 0
  proof: by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => nonpos_iff_eq_zero.2 (h i hi)) zero_le⟩
  rw [← nonpos_iff_eq_zero]; rw [← h]
  exact le_bsup f i hi

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_eq_zero_iff
  条件: {o} {f : 对任意 a < o, 序数}
  结论: bsup o f = 0 ↔ 对任意 i hi, f i hi = 0
  证明: by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => nonpos_iff_eq_zero.2 (h i hi)) zero_le⟩
  rw [← nonpos_iff_eq_zero]; rw [← h]
  exact le_bsup f i hi

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_le, le_antisymm, le_bsup, nonpos_iff_eq_zero, zero_le
-/
theorem bsup_eq_zero_iff {o} {f : forall a < o, Ordinal} : bsup o f = 0 ↔ forall i hi, f i hi = 0 := by
  refine
    ⟨fun h i hi => ?_, fun h =>
      le_antisymm (bsup_le fun i hi => nonpos_iff_eq_zero.2 (h i hi)) zero_le⟩
  rw [← nonpos_iff_eq_zero]; rw [← h]
  exact le_bsup f i hi

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `lt_bsup_of_limit` / 定理 `lt_bsup_of_limit`

English:
theorem lt_bsup_of_limit
  statement: {o : Ordinal} {f : forall a < o, Ordinal}
  proof: (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 lt_bsup_of_limit
  结论: {o : 序数} {f : 对任意 a < o, 序数}
  证明: (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: le_bsup, lt_succ, trans_le
-/
theorem lt_bsup_of_limit {o : Ordinal} {f : forall a < o, Ordinal}
    (hf : forall {a a'} (ha : a < o) (ha' : a' < o), a < a' -> f a ha < f a' ha')
    (ho : forall a < o, succ a < o) (i h) : f i h < bsup o f :=
  (hf _ _ <| lt_succ i).trans_le (le_bsup f (succ i) <| ho _ h)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_succ_of_mono` / 定理 `bsup_succ_of_mono`

English:
theorem bsup_succ_of_mono
  statement: {o : Ordinal} {f : forall a < succ o, Ordinal}
  proof: le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_succ_of_mono
  结论: {o : 序数} {f : 对任意 a < succ o, 序数}
  证明: le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_le, le_antisymm, le_bsup, le_of_lt_succ
-/
theorem bsup_succ_of_mono {o : Ordinal} {f : forall a < succ o, Ordinal}
    (hf : forall {i j} (hi hj), i <= j -> f i hi <= f j hj) : bsup _ f = f o (lt_succ o) :=
  le_antisymm (bsup_le fun _i hi => hf _ _ <| le_of_lt_succ hi) (le_bsup _ _ _)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_zero` / 定理 `bsup_zero`

English:
theorem bsup_zero
  given: (f : forall a < (0 : Ordinal), Ordinal)
  statement: bsup 0 f = 0
  proof: bsup_eq_zero_iff.2 fun _i hi => (not_lt_zero hi).elim

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_zero
  条件: (f : 对任意 a < (0 : 序数), 序数)
  结论: bsup 0 f = 0
  证明: bsup_eq_zero_iff.2 fun _i hi => (not_lt_zero hi).elim

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_eq_zero_iff, not_lt_zero
-/
theorem bsup_zero (f : forall a < (0 : Ordinal), Ordinal) : bsup 0 f = 0 :=
  bsup_eq_zero_iff.2 fun _i hi => (not_lt_zero hi).elim

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_const` / 定理 `bsup_const`

English:
theorem bsup_const
  given: {o : Ordinal.{u}} (ho : o != 0) (a : Ordinal.{max u v})
  proof: le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (pos_iff_ne_zero.2 ho))

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_const
  条件: {o : 序数.{u}} (ho : o != 0) (a : 序数.{最大值 u v})
  证明: le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (pos_iff_ne_zero.2 ho))

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_le, le_antisymm, le_bsup, le_rfl, pos_iff_ne_zero
-/
theorem bsup_const {o : Ordinal.{u}} (ho : o != 0) (a : Ordinal.{max u v}) :
    (bsup.{_, v} o fun _ _ => a) = a :=
  le_antisymm (bsup_le fun _ _ => le_rfl) (le_bsup _ 0 (pos_iff_ne_zero.2 ho))

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_one` / 定理 `bsup_one`

English:
theorem bsup_one
  given: (f : forall a < (1 : Ordinal), Ordinal)
  statement: bsup 1 f = f 0 zero_lt_one
  proof: by
  simp_rw [← iSup_eq_bsup, ciSup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_one
  条件: (f : 对任意 a < (1 : 序数), 序数)
  结论: bsup 1 f = f 0 zero_lt_one
  证明: by
  simp_rw [← iSup_eq_bsup, ciSup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: ciSup_unique, familyOfBFamily, iSup_eq_bsup, simp_rw, typein_one_toType
-/
theorem bsup_one (f : forall a < (1 : Ordinal), Ordinal) : bsup 1 f = f 0 zero_lt_one := by
  simp_rw [← iSup_eq_bsup, ciSup_unique, familyOfBFamily, familyOfBFamily', typein_one_toType]

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_le_of_brange_subset` / 定理 `bsup_le_of_brange_subset`

English:
theorem bsup_le_of_brange_subset
  statement: {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
  proof: bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_le_of_brange_subset
  结论: {o o'} {f : 对任意 a < o, 序数} {g : 对任意 a < o', 序数}
  证明: bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: bsup_le, le_bsup
-/
theorem bsup_le_of_brange_subset {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
    (h : brange o f subseteq brange o' g) : bsup.{u, max v w} o f <= bsup.{v, max u w} o' g :=
  bsup_le fun i hi => by
    obtain ⟨j, hj, hj'⟩ := h ⟨i, hi, rfl⟩
    rw [← hj']
    apply le_bsup

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `bsup_eq_of_brange_eq` / 定理 `bsup_eq_of_brange_eq`

English:
theorem bsup_eq_of_brange_eq
  statement: {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
  proof: (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

中文:
定理 bsup_eq_of_brange_eq
  结论: {o o'} {f : 对任意 a < o, 序数} {g : 对任意 a < o', 序数}
  证明: (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]

Depends on / 依赖: antisymm, bsup_le_of_brange_subset, h.ge, h.le
-/
theorem bsup_eq_of_brange_eq {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
    (h : brange o f = brange o' g) : bsup.{u, max v w} o f = bsup.{v, max u w} o' g :=
  (bsup_le_of_brange_subset.{u, v, w} h.le).antisymm (bsup_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "bsup is deprecated" (since := "2026-04-05")]
/--
theorem `iSup_Iio_eq_bsup` / 定理 `iSup_Iio_eq_bsup`

English:
theorem iSup_Iio_eq_bsup
  given: {o} {f : forall a < o, Ordinal}
  statement: ⨆ a : Iio o, f a.1 a.2 = bsup o f
  proof: by
  simp_rw [Iio, bsup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_ofPred]

中文:
定理 iSup_Iio_eq_bsup
  条件: {o} {f : 对任意 a < o, 序数}
  结论: ⨆ a : 左无界右开区间 o, f a.1 a.2 = bsup o f
  证明: by
  simp_rw [Iio, bsup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_ofPred]

Depends on / 依赖: Subtype, Subtype.exists, brange, mem_ofPred, range_familyOfBFamily, simp_rw
-/
theorem iSup_Iio_eq_bsup {o} {f : forall a < o, Ordinal} : ⨆ a : Iio o, f a.1 a.2 = bsup o f := by
  simp_rw [Iio, bsup, iSup, range_familyOfBFamily, brange, range, Subtype.exists, mem_ofPred]

end bsup

section lsub

/-- The least strict upper bound of a family of ordinals. -/
@[deprecated "write `⨆ i, f i + 1` instead." (since := "2026-03-27")]
/--
Definition of `lsub` / `lsub` 的定义

English:
definition lsub
  signature: {ι : Type u} (f : ι -> Ordinal.{max u v})
  body: iSup (succ ∘ f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定义 lsub
  签名: {ι : 类型u} (f : ι -> 序数.{最大值 u v})
  定义体: iSup (succ ∘ f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
-/
def lsub {ι : Type u} (f : ι -> Ordinal.{max u v}) : Ordinal :=
  iSup (succ ∘ f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `iSup_eq_lsub` / 定理 `iSup_eq_lsub`

English:
theorem iSup_eq_lsub
  given: {ι} (f : ι -> Ordinal)
  statement: iSup (succ ∘ f) = lsub f
  proof: rfl

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 iSup_eq_lsub
  条件: {ι} (f : ι -> 序数)
  结论: iSup (succ ∘ f) = lsub f
  证明: rfl

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
-/
theorem iSup_eq_lsub {ι} (f : ι -> Ordinal) : iSup (succ ∘ f) = lsub f :=
  rfl

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_le_iff` / 定理 `lsub_le_iff`

English:
theorem lsub_le_iff
  given: {ι} {f : ι -> Ordinal} {a}
  statement: lsub f <= a ↔ forall i, f i < a
  proof: Ordinal.iSup_add_one_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_le_iff
  条件: {ι} {f : ι -> 序数} {a}
  结论: lsub f <= a ↔ 对任意 i, f i < a
  证明: Ordinal.iSup_add_one_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: Ordinal, Ordinal.iSup_add_one_le_iff, iSup_add_one_le_iff
-/
theorem lsub_le_iff {ι} {f : ι -> Ordinal} {a} : lsub f <= a ↔ forall i, f i < a :=
  Ordinal.iSup_add_one_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_le` / 定理 `lsub_le`

English:
theorem lsub_le
  given: {ι} {f : ι -> Ordinal} {a}
  statement: (forall i, f i < a) -> lsub f <= a
  proof: lsub_le_iff.2

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_le
  条件: {ι} {f : ι -> 序数} {a}
  结论: (对任意 i, f i < a) -> lsub f <= a
  证明: lsub_le_iff.2

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: lsub_le_iff
-/
theorem lsub_le {ι} {f : ι -> Ordinal} {a} : (forall i, f i < a) -> lsub f <= a :=
  lsub_le_iff.2

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lt_lsub` / 定理 `lt_lsub`

English:
theorem lt_lsub
  given: {ι} (f : ι -> Ordinal) (i)
  statement: f i < lsub f
  proof: Ordinal.lt_iSup_add_one f i

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lt_lsub
  条件: {ι} (f : ι -> 序数) (i)
  结论: f i < lsub f
  证明: Ordinal.lt_iSup_add_one f i

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: Ordinal, Ordinal.lt_iSup_add_one, lt_iSup_add_one
-/
theorem lt_lsub {ι} (f : ι -> Ordinal) (i) : f i < lsub f :=
  Ordinal.lt_iSup_add_one f i

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lt_lsub_iff` / 定理 `lt_lsub_iff`

English:
theorem lt_lsub_iff
  given: {ι} {f : ι -> Ordinal} {a}
  statement: a < lsub f ↔ exists i, a <= f i
  proof: by
  simpa only [not_forall, not_lt, not_le] using not_congr lsub_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lt_lsub_iff
  条件: {ι} {f : ι -> 序数} {a}
  结论: a < lsub f ↔ 存在 i, a <= f i
  证明: by
  simpa only [not_forall, not_lt, not_le] using not_congr lsub_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: lsub_le_iff, not_congr, not_forall, not_le, not_lt
-/
theorem lt_lsub_iff {ι} {f : ι -> Ordinal} {a} : a < lsub f ↔ exists i, a <= f i := by
  simpa only [not_forall, not_lt, not_le] using not_congr lsub_le_iff

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `iSup_le_lsub` / 定理 `iSup_le_lsub`

English:
theorem iSup_le_lsub
  given: {ι} (f : ι -> Ordinal)
  statement: iSup f <= lsub f
  proof: Ordinal.iSup_le fun i => (lt_lsub f i).le

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 iSup_le_lsub
  条件: {ι} (f : ι -> 序数)
  结论: iSup f <= lsub f
  证明: Ordinal.iSup_le fun i => (lt_lsub f i).le

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: Ordinal, Ordinal.iSup_le, iSup_le, lt_lsub
-/
theorem iSup_le_lsub {ι} (f : ι -> Ordinal) : iSup f <= lsub f :=
  Ordinal.iSup_le fun i => (lt_lsub f i).le

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_le_succ_iSup` / 定理 `lsub_le_succ_iSup`

English:
theorem lsub_le_succ_iSup
  given: {ι} (f : ι -> Ordinal)
  statement: lsub f <= succ (iSup f)
  proof: lsub_le fun i => lt_succ_iff.2 (Ordinal.le_iSup f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_le_succ_iSup
  条件: {ι} (f : ι -> 序数)
  结论: lsub f <= succ (iSup f)
  证明: lsub_le fun i => lt_succ_iff.2 (Ordinal.le_iSup f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: Ordinal, Ordinal.le_iSup, le_iSup, lsub_le, lt_succ_iff
-/
theorem lsub_le_succ_iSup {ι} (f : ι -> Ordinal) : lsub f <= succ (iSup f) :=
  lsub_le fun i => lt_succ_iff.2 (Ordinal.le_iSup f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `iSup_eq_lsub_or_succ_iSup_eq_lsub` / 定理 `iSup_eq_lsub_or_succ_iSup_eq_lsub`

English:
theorem iSup_eq_lsub_or_succ_iSup_eq_lsub
  given: {ι} (f : ι -> Ordinal)
  proof: by
  rcases eq_or_lt_of_le (iSup_le_lsub f) with h | h
  · exact Or.inl h
  · exact Or.inr ((succ_le_of_lt h).antisymm (lsub_le_succ_iSup f))

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 iSup_eq_lsub_or_succ_iSup_eq_lsub
  条件: {ι} (f : ι -> 序数)
  证明: by
  rcases eq_or_lt_of_le (iSup_le_lsub f) with h | h
  · exact Or.inl h
  · exact Or.inr ((succ_le_of_lt h).antisymm (lsub_le_succ_iSup f))

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: Or.inl, Or.inr, antisymm, eq_or_lt_of_le, iSup_le_lsub, lsub_le_succ_iSup, succ_le_of_lt
-/
theorem iSup_eq_lsub_or_succ_iSup_eq_lsub {ι} (f : ι -> Ordinal) :
    iSup f = lsub f ∨ succ (iSup f) = lsub f := by
  rcases eq_or_lt_of_le (iSup_le_lsub f) with h | h
  · exact Or.inl h
  · exact Or.inr ((succ_le_of_lt h).antisymm (lsub_le_succ_iSup f))

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `succ_iSup_le_lsub_iff` / 定理 `succ_iSup_le_lsub_iff`

English:
theorem succ_iSup_le_lsub_iff
  given: {ι} (f : ι -> Ordinal)
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    have := forall_congr' fun i => (Ordinal.le_iSup f i).lt_iff_ne.symm
    exact (succ_le_iff.1 h).ne ((iSup_le_lsub f).antisymm (lsub_le (this.1 hf)))
  rintro ⟨_, hf⟩
  rw [succ_le_iff]; rw [← hf]
  exact lt_lsub _ _

@[deprecated "lsub is deprecate

中文:
定理 succ_iSup_le_lsub_iff
  条件: {ι} (f : ι -> 序数)
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    have := forall_congr' fun i => (Ordinal.le_iSup f i).lt_iff_ne.symm
    exact (succ_le_iff.1 h).ne ((iSup_le_lsub f).antisymm (lsub_le (this.1 hf)))
  rintro ⟨_, hf⟩
  rw [succ_le_iff]; rw [← hf]
  exact lt_lsub _ _

@[deprecated "lsub is deprecate

Depends on / 依赖: Ordinal, Ordinal.le_iSup, antisymm, forall_congr, iSup_le_lsub, le_iSup, lsub_le, lt_iff_ne, lt_iff_ne.symm, lt_lsub, succ_le_iff
-/
theorem succ_iSup_le_lsub_iff {ι} (f : ι -> Ordinal) :
    succ (iSup f) <= lsub f ↔ exists i, f i = iSup f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    have := forall_congr' fun i => (Ordinal.le_iSup f i).lt_iff_ne.symm
    exact (succ_le_iff.1 h).ne ((iSup_le_lsub f).antisymm (lsub_le (this.1 hf)))
  rintro ⟨_, hf⟩
  rw [succ_le_iff]; rw [← hf]
  exact lt_lsub _ _

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `succ_iSup_eq_lsub_iff` / 定理 `succ_iSup_eq_lsub_iff`

English:
theorem succ_iSup_eq_lsub_iff
  given: {ι} (f : ι -> Ordinal)
  proof: (lsub_le_succ_iSup f).ge_iff_eq'.symm.trans (succ_iSup_le_lsub_iff f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 succ_iSup_eq_lsub_iff
  条件: {ι} (f : ι -> 序数)
  证明: (lsub_le_succ_iSup f).ge_iff_eq'.symm.trans (succ_iSup_le_lsub_iff f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: ge_iff_eq, lsub_le_succ_iSup, succ_iSup_le_lsub_iff, symm.trans
-/
theorem succ_iSup_eq_lsub_iff {ι} (f : ι -> Ordinal) :
    succ (iSup f) = lsub f ↔ exists i, f i = iSup f :=
  (lsub_le_succ_iSup f).ge_iff_eq'.symm.trans (succ_iSup_le_lsub_iff f)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `iSup_eq_lsub_iff` / 定理 `iSup_eq_lsub_iff`

English:
theorem iSup_eq_lsub_iff
  given: {ι} (f : ι -> Ordinal)
  proof: by
  refine ⟨fun h => ?_, fun hf => le_antisymm (iSup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => succ_lt_iSup_of_ne_iSup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (succ_iSup_eq_lsub_iff f).2 ⟨i, le_antisymm (Ordinal.le_iSup _ _) hle⟩
  have

中文:
定理 iSup_eq_lsub_iff
  条件: {ι} (f : ι -> 序数)
  证明: by
  refine ⟨fun h => ?_, fun hf => le_antisymm (iSup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => succ_lt_iSup_of_ne_iSup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (succ_iSup_eq_lsub_iff f).2 ⟨i, le_antisymm (Ordinal.le_iSup _ _) hle⟩
  have

Depends on / 依赖: Ordinal, Ordinal.le_iSup, h.symm, iSup_le_lsub, le_antisymm, le_iSup, le_of_eq, lsub_le, lsub_le_iff, lt_succ, succ_iSup_eq_lsub_iff, succ_lt_iSup_of_ne_iSup, this.false
-/
theorem iSup_eq_lsub_iff {ι} (f : ι -> Ordinal) :
    iSup f = lsub f ↔ forall a < lsub f, succ a < lsub f := by
  refine ⟨fun h => ?_, fun hf => le_antisymm (iSup_le_lsub f) (lsub_le fun i => ?_)⟩
  · rw [← h]
    exact fun a => succ_lt_iSup_of_ne_iSup fun i => (lsub_le_iff.1 (le_of_eq h.symm) i).ne
  by_contra! hle
  have heq := (succ_iSup_eq_lsub_iff f).2 ⟨i, le_antisymm (Ordinal.le_iSup _ _) hle⟩
  have :=
    hf _
      (by
        rw [← heq]
        exact lt_succ (iSup f))
  rw [heq] at this
  exact this.false

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `iSup_eq_lsub_iff_lt_iSup` / 定理 `iSup_eq_lsub_iff_lt_iSup`

English:
theorem iSup_eq_lsub_iff_lt_iSup
  given: {ι} (f : ι -> Ordinal)
  proof: ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymm (iSup_le_lsub f) (lsub_le h)⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 iSup_eq_lsub_iff_lt_iSup
  条件: {ι} (f : ι -> 序数)
  证明: ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymm (iSup_le_lsub f) (lsub_le h)⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: iSup_le_lsub, le_antisymm, lsub_le, lt_lsub
-/
theorem iSup_eq_lsub_iff_lt_iSup {ι} (f : ι -> Ordinal) :
    iSup f = lsub f ↔ forall i, f i < iSup f :=
  ⟨fun h i => by
    rw [h]
    apply lt_lsub, fun h => le_antisymm (iSup_le_lsub f) (lsub_le h)⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_empty` / 定理 `lsub_empty`

English:
theorem lsub_empty
  given: {ι} [h : IsEmpty ι] (f : ι -> Ordinal)
  statement: lsub f = 0
  proof: by
  rw [← nonpos_iff_eq_zero]; rw [lsub_le_iff]
  exact h.elim

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_empty
  条件: {ι} [h : 是空 ι] (f : ι -> 序数)
  结论: lsub f = 0
  证明: by
  rw [← nonpos_iff_eq_zero]; rw [lsub_le_iff]
  exact h.elim

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: h.elim, lsub_le_iff, nonpos_iff_eq_zero
-/
theorem lsub_empty {ι} [h : IsEmpty ι] (f : ι -> Ordinal) : lsub f = 0 := by
  rw [← nonpos_iff_eq_zero]; rw [lsub_le_iff]
  exact h.elim

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_pos` / 定理 `lsub_pos`

English:
theorem lsub_pos
  given: {ι} [h : Nonempty ι] (f : ι -> Ordinal)
  statement: 0 < lsub f
  proof: h.elim fun i => (lt_lsub f i).pos

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_pos
  条件: {ι} [h : 非空 ι] (f : ι -> 序数)
  结论: 0 < lsub f
  证明: h.elim fun i => (lt_lsub f i).pos

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: h.elim, lt_lsub
-/
theorem lsub_pos {ι} [h : Nonempty ι] (f : ι -> Ordinal) : 0 < lsub f :=
  h.elim fun i => (lt_lsub f i).pos

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_eq_zero_iff` / 定理 `lsub_eq_zero_iff`

English:
theorem lsub_eq_zero_iff
  given: {ι} (f : ι -> Ordinal)
  proof: by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos.{_, v} _ ⟨i⟩ f
  rw [h] at this
  exact this.false

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_eq_zero_iff
  条件: {ι} (f : ι -> 序数)
  证明: by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos.{_, v} _ ⟨i⟩ f
  rw [h] at this
  exact this.false

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: lsub_empty, lsub_pos, this.false
-/
theorem lsub_eq_zero_iff {ι} (f : ι -> Ordinal) :
    lsub.{_, v} f = 0 ↔ IsEmpty ι := by
  refine ⟨fun h => ⟨fun i => ?_⟩, fun h => @lsub_empty _ h _⟩
  have := @lsub_pos.{_, v} _ ⟨i⟩ f
  rw [h] at this
  exact this.false

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_const` / 定理 `lsub_const`

English:
theorem lsub_const
  given: {ι} [Nonempty ι] (o : Ordinal)
  statement: (lsub fun _ : ι => o) = succ o
  proof: ciSup_const

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_const
  条件: {ι} [非空 ι] (o : 序数)
  结论: (lsub fun _ : ι => o) = succ o
  证明: ciSup_const

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: ciSup_const
-/
theorem lsub_const {ι} [Nonempty ι] (o : Ordinal) : (lsub fun _ : ι => o) = succ o :=
  ciSup_const

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_unique` / 定理 `lsub_unique`

English:
theorem lsub_unique
  given: {ι} [Unique ι] (f : ι -> Ordinal)
  statement: lsub f = succ (f default)
  proof: ciSup_unique

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_unique
  条件: {ι} [唯一 ι] (f : ι -> 序数)
  结论: lsub f = succ (f default)
  证明: ciSup_unique

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: ciSup_unique
-/
theorem lsub_unique {ι} [Unique ι] (f : ι -> Ordinal) : lsub f = succ (f default) :=
  ciSup_unique

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_le_of_range_subset` / 定理 `lsub_le_of_range_subset`

English:
theorem lsub_le_of_range_subset
  statement: {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal}
  proof: csSup_le_csSup' bddAbove_of_small (by convert! Set.image_mono h <;> apply Set.range_comp)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_le_of_range_subset
  结论: {ι ι'} {f : ι -> 序数} {g : ι' -> 序数}
  证明: csSup_le_csSup' bddAbove_of_small (by convert! Set.image_mono h <;> apply Set.range_comp)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: Set.image_mono, Set.range_comp, bddAbove_of_small, convert, csSup_le_csSup, image_mono, range_comp
-/
theorem lsub_le_of_range_subset {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal}
    (h : Set.range f subseteq Set.range g) : lsub.{u, max v w} f <= lsub.{v, max u w} g :=
  csSup_le_csSup' bddAbove_of_small (by convert! Set.image_mono h <;> apply Set.range_comp)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_eq_of_range_eq` / 定理 `lsub_eq_of_range_eq`

English:
theorem lsub_eq_of_range_eq
  statement: {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal}
  proof: (lsub_le_of_range_subset.{u, v, w} h.le).antisymm (lsub_le_of_range_subset.{v, u, w} h.ge)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_eq_of_range_eq
  结论: {ι ι'} {f : ι -> 序数} {g : ι' -> 序数}
  证明: (lsub_le_of_range_subset.{u, v, w} h.le).antisymm (lsub_le_of_range_subset.{v, u, w} h.ge)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: antisymm, h.ge, h.le, lsub_le_of_range_subset
-/
theorem lsub_eq_of_range_eq {ι ι'} {f : ι -> Ordinal} {g : ι' -> Ordinal}
    (h : Set.range f = Set.range g) : lsub.{u, max v w} f = lsub.{v, max u w} g :=
  (lsub_le_of_range_subset.{u, v, w} h.le).antisymm (lsub_le_of_range_subset.{v, u, w} h.ge)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_sum` / 定理 `lsub_sum`

English:
theorem lsub_sum
  given: {α : Type u} {β : Type v} (f : α oplus β -> Ordinal)
  proof: iSup_sum _

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_sum
  条件: {α : 类型u} {β : 类型v} (f : α oplus β -> 序数)
  证明: iSup_sum _

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: iSup_sum
-/
theorem lsub_sum {α : Type u} {β : Type v} (f : α oplus β -> Ordinal) :
    lsub.{max u v, w} f =
      max (lsub.{u, max v w} fun a => f (Sum.inl a)) (lsub.{v, max u w} fun b => f (Sum.inr b)) :=
  iSup_sum _

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_notMem_range` / 定理 `lsub_notMem_range`

English:
theorem lsub_notMem_range
  given: {ι} (f : ι -> Ordinal)
  proof: fun ⟨i, h⟩ =>
  h.not_lt (lt_lsub f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 lsub_notMem_range
  条件: {ι} (f : ι -> 序数)
  证明: fun ⟨i, h⟩ =>
  h.not_lt (lt_lsub f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
-/
theorem lsub_notMem_range {ι} (f : ι -> Ordinal) :
    lsub f ∉ Set.range f := fun ⟨i, h⟩ =>
  h.not_lt (lt_lsub f i)

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `nonempty_compl_range` / 定理 `nonempty_compl_range`

English:
theorem nonempty_compl_range
  given: {ι : Type u} (f : ι -> Ordinal.{max u v})
  statement: (Set.range f)ᶜ.Nonempty
  proof: ⟨_, lsub_notMem_range f⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

中文:
定理 nonempty_compl_range
  条件: {ι : 类型u} (f : ι -> 序数.{最大值 u v})
  结论: (集合.range f)ᶜ.非空
  证明: ⟨_, lsub_notMem_range f⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]

Depends on / 依赖: lsub_notMem_range
-/
theorem nonempty_compl_range {ι : Type u} (f : ι -> Ordinal.{max u v}) : (Set.range f)ᶜ.Nonempty :=
  ⟨_, lsub_notMem_range f⟩

@[deprecated "lsub is deprecated" (since := "2026-03-27")]
/--
theorem `lsub_typein` / 定理 `lsub_typein`

English:
theorem lsub_typein
  given: (o : Ordinal)
  statement: lsub.{u, u} (typein (α := o.ToType) (· < ·)) = o
  proof: (lsub_le.{u, u} typein_lt_self).antisymm
    (by
      by_contra! h
      have h := h.trans_eq (type_toType o).symm
      simpa [typein_enum] using lt_lsub.{u, u} (typein (· < ·)) (enum (· < ·) ⟨_, h⟩))

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-27")]

中文:
定理 lsub_typein
  条件: (o : 序数)
  结论: lsub.{u, u} (typein (α := o.ToType) (· < ·)) = o
  证明: (lsub_le.{u, u} typein_lt_self).antisymm
    (by
      by_contra! h
      have h := h.trans_eq (type_toType o).symm
      simpa [typein_enum] using lt_lsub.{u, u} (typein (· < ·)) (enum (· < ·) ⟨_, h⟩))

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-27")]

Depends on / 依赖: ToType, o.ToType
-/
theorem lsub_typein (o : Ordinal) : lsub.{u, u} (typein (α := o.ToType) (· < ·)) = o :=
  (lsub_le.{u, u} typein_lt_self).antisymm
    (by
      by_contra! h
      have h := h.trans_eq (type_toType o).symm
      simpa [typein_enum] using lt_lsub.{u, u} (typein (· < ·)) (enum (· < ·) ⟨_, h⟩))

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-27")]
/--
theorem `iSup_typein_limit` / 定理 `iSup_typein_limit`

English:
theorem iSup_typein_limit
  given: {o : Ordinal.{u}} (ho : forall a, a < o -> succ a < o)
  proof: by
  replace ho : IsSuccPrelimit o := by rwa [isSuccPrelimit_iff_succ_lt]
  rw [iSup]; rw [PrincipalSeg.range_eq]
  simpa [Iio_def] using ho.sSup_Iio

@[deprecated csSup_Iic (since := "2026-03-27")]

中文:
定理 iSup_typein_limit
  条件: {o : 序数.{u}} (ho : 对任意 a, a < o -> succ a < o)
  证明: by
  replace ho : IsSuccPrelimit o := by rwa [isSuccPrelimit_iff_succ_lt]
  rw [iSup]; rw [PrincipalSeg.range_eq]
  simpa [Iio_def] using ho.sSup_Iio

@[deprecated csSup_Iic (since := "2026-03-27")]

Depends on / 依赖: Iio_def, IsSuccPrelimit, PrincipalSeg, PrincipalSeg.range_eq, ho.sSup_Iio, isSuccPrelimit_iff_succ_lt, range_eq, replace, sSup_Iio
-/
theorem iSup_typein_limit {o : Ordinal.{u}} (ho : forall a, a < o -> succ a < o) :
    iSup (typein ((· < ·) : o.ToType -> o.ToType -> Prop)) = o := by
  replace ho : IsSuccPrelimit o := by rwa [isSuccPrelimit_iff_succ_lt]
  rw [iSup]; rw [PrincipalSeg.range_eq]
  simpa [Iio_def] using ho.sSup_Iio

@[deprecated csSup_Iic (since := "2026-03-27")]
/--
theorem `iSup_typein_succ` / 定理 `iSup_typein_succ`

English:
theorem iSup_typein_succ
  given: {o : Ordinal}
  proof: by
  rw [← csSup_Iic (a := o)]; rw [iSup]; rw [PrincipalSeg.range_eq]
  congr
  simp

中文:
定理 iSup_typein_succ
  条件: {o : 序数}
  证明: by
  rw [← csSup_Iic (a := o)]; rw [iSup]; rw [PrincipalSeg.range_eq]
  congr
  simp

Depends on / 依赖: PrincipalSeg, PrincipalSeg.range_eq, csSup_Iic, range_eq
-/
theorem iSup_typein_succ {o : Ordinal} :
    iSup (typein ((· < ·) : (succ o).ToType -> (succ o).ToType -> Prop)) = o := by
  rw [← csSup_Iic (a := o)]; rw [iSup]; rw [PrincipalSeg.range_eq]
  congr
  simp

end lsub

section blsub

/-- The least strict upper bound of a family of ordinals indexed by the set of ordinals less than
some `o : Ordinal.{u}`. -/
@[deprecated "write `⨆ i : Iio o, f i + 1` instead." (since := "2026-03-23")]
/--
Definition of `blsub` / `blsub` 的定义

English:
definition blsub
  signature: (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v})
  body: bsup.{_, v} o fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定义 blsub
  签名: (o : 序数.{u}) (f : 对任意 a < o, 序数.{最大值 u v})
  定义体: bsup.{_, v} o fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
-/
def blsub (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v}) : Ordinal.{max u v} :=
  bsup.{_, v} o fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_eq_blsub` / 定理 `bsup_eq_blsub`

English:
theorem bsup_eq_blsub
  given: (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v})
  proof: rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_eq_blsub
  条件: (o : 序数.{u}) (f : 对任意 a < o, 序数.{最大值 u v})
  证明: rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
-/
theorem bsup_eq_blsub (o : Ordinal.{u}) (f : forall a < o, Ordinal.{max u v}) :
    (bsup.{_, v} o fun a ha => succ (f a ha)) = blsub.{_, v} o f :=
  rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `lsub_eq_blsub'` / 定理 `lsub_eq_blsub'`

English:
theorem lsub_eq_blsub'
  statement: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho : type r = o)
  proof: iSup'_eq_bsup r ho fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 lsub_eq_blsub'
  结论: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r] {o} (ho : type r = o)
  证明: iSup'_eq_bsup r ho fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: _eq_bsup
-/
theorem lsub_eq_blsub' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r] {o} (ho : type r = o)
    (f : forall a < o, Ordinal) : lsub (familyOfBFamily' r ho f) = blsub o f :=
  iSup'_eq_bsup r ho fun a ha => succ (f a ha)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `lsub_eq_lsub` / 定理 `lsub_eq_lsub`

English:
theorem lsub_eq_lsub
  statement: {ι ι' : Type u} (r : ι -> ι -> Prop) (r' : ι' -> ι' -> Prop) [IsWellOrder ι r]
  proof: by
  rw [lsub_eq_blsub']; rw [lsub_eq_blsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 lsub_eq_lsub
  结论: {ι ι' : 类型u} (r : ι -> ι -> 命题) (r' : ι' -> ι' -> 命题) [是良序 ι r]
  证明: by
  rw [lsub_eq_blsub']; rw [lsub_eq_blsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: lsub_eq_blsub
-/
theorem lsub_eq_lsub {ι ι' : Type u} (r : ι -> ι -> Prop) (r' : ι' -> ι' -> Prop) [IsWellOrder ι r]
    [IsWellOrder ι' r'] {o} (ho : type r = o) (ho' : type r' = o)
    (f : forall a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily' r ho f) = lsub.{_, v} (familyOfBFamily' r' ho' f) := by
  rw [lsub_eq_blsub']; rw [lsub_eq_blsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `lsub_eq_blsub` / 定理 `lsub_eq_blsub`

English:
theorem lsub_eq_blsub
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: lsub_eq_blsub' _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 lsub_eq_blsub
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: lsub_eq_blsub' _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: lsub_eq_blsub
-/
theorem lsub_eq_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    lsub.{_, v} (familyOfBFamily o f) = blsub.{_, v} o f :=
  lsub_eq_blsub' _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_eq_lsub'` / 定理 `blsub_eq_lsub'`

English:
theorem blsub_eq_lsub'
  statement: {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r]
  proof: bsup'_eq_iSup r (succ ∘ f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_eq_lsub'
  结论: {ι : 类型u} (r : ι -> ι -> 命题) [是良序 ι r]
  证明: bsup'_eq_iSup r (succ ∘ f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: _eq_iSup
-/
theorem blsub_eq_lsub' {ι : Type u} (r : ι -> ι -> Prop) [IsWellOrder ι r]
    (f : ι -> Ordinal.{max u v}) : blsub.{_, v} _ (bfamilyOfFamily' r f) = lsub.{_, v} f :=
  bsup'_eq_iSup r (succ ∘ f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_eq_blsub` / 定理 `blsub_eq_blsub`

English:
theorem blsub_eq_blsub
  statement: {ι : Type u} (r r' : ι -> ι -> Prop) [IsWellOrder ι r] [IsWellOrder ι r']
  proof: by
  rw [blsub_eq_lsub']; rw [blsub_eq_lsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_eq_blsub
  结论: {ι : 类型u} (r r' : ι -> ι -> 命题) [是良序 ι r] [是良序 ι r']
  证明: by
  rw [blsub_eq_lsub']; rw [blsub_eq_lsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_eq_lsub
-/
theorem blsub_eq_blsub {ι : Type u} (r r' : ι -> ι -> Prop) [IsWellOrder ι r] [IsWellOrder ι r']
    (f : ι -> Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily' r f) = blsub.{_, v} _ (bfamilyOfFamily' r' f) := by
  rw [blsub_eq_lsub']; rw [blsub_eq_lsub']

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_eq_lsub` / 定理 `blsub_eq_lsub`

English:
theorem blsub_eq_lsub
  given: {ι : Type u} (f : ι -> Ordinal.{max u v})
  proof: blsub_eq_lsub' _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_eq_lsub
  条件: {ι : 类型u} (f : ι -> 序数.{最大值 u v})
  证明: blsub_eq_lsub' _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_eq_lsub
-/
theorem blsub_eq_lsub {ι : Type u} (f : ι -> Ordinal.{max u v}) :
    blsub.{_, v} _ (bfamilyOfFamily f) = lsub.{_, v} f :=
  blsub_eq_lsub' _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_congr` / 定理 `blsub_congr`

English:
theorem blsub_congr
  given: {o₁ o₂ : Ordinal.{u}} (f : forall a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂)
  proof: by
  subst ho
  rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_congr
  条件: {o₁ o₂ : 序数.{u}} (f : 对任意 a < o₁, 序数.{最大值 u v}) (ho : o₁ = o₂)
  证明: by
  subst ho
  rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
-/
theorem blsub_congr {o₁ o₂ : Ordinal.{u}} (f : forall a < o₁, Ordinal.{max u v}) (ho : o₁ = o₂) :
    blsub.{_, v} o₁ f = blsub.{_, v} o₂ fun a h => f a (h.trans_eq ho.symm) := by
  subst ho
  rfl

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_le_iff` / 定理 `blsub_le_iff`

English:
theorem blsub_le_iff
  given: {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}} {a}
  proof: by
  convert! bsup_le_iff.{_, v} (f := fun a ha => succ (f a ha)) (a := a) using 2
  simp_rw [succ_le_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_le_iff
  条件: {o : 序数.{u}} {f : 对任意 a < o, 序数.{最大值 u v}} {a}
  证明: by
  convert! bsup_le_iff.{_, v} (f := fun a ha => succ (f a ha)) (a := a) using 2
  simp_rw [succ_le_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_le_iff, convert, simp_rw, succ_le_iff
-/
theorem blsub_le_iff {o : Ordinal.{u}} {f : forall a < o, Ordinal.{max u v}} {a} :
    blsub.{_, v} o f <= a ↔ forall i h, f i h < a := by
  convert! bsup_le_iff.{_, v} (f := fun a ha => succ (f a ha)) (a := a) using 2
  simp_rw [succ_le_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_le` / 定理 `blsub_le`

English:
theorem blsub_le
  given: {o : Ordinal} {f : forall b < o, Ordinal} {a}
  statement: (forall i h, f i h < a) -> blsub o f <= a
  proof: blsub_le_iff.2

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_le
  条件: {o : 序数} {f : 对任意 b < o, 序数} {a}
  结论: (对任意 i h, f i h < a) -> blsub o f <= a
  证明: blsub_le_iff.2

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le_iff
-/
theorem blsub_le {o : Ordinal} {f : forall b < o, Ordinal} {a} : (forall i h, f i h < a) -> blsub o f <= a :=
  blsub_le_iff.2

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `lt_blsub` / 定理 `lt_blsub`

English:
theorem lt_blsub
  given: {o} (f : forall a < o, Ordinal) (i h)
  statement: f i h < blsub o f
  proof: blsub_le_iff.1 le_rfl _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 lt_blsub
  条件: {o} (f : 对任意 a < o, 序数) (i h)
  结论: f i h < blsub o f
  证明: blsub_le_iff.1 le_rfl _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le_iff, le_rfl
-/
theorem lt_blsub {o} (f : forall a < o, Ordinal) (i h) : f i h < blsub o f :=
  blsub_le_iff.1 le_rfl _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `lt_blsub_iff` / 定理 `lt_blsub_iff`

English:
theorem lt_blsub_iff
  given: {o : Ordinal.{u}} {f : forall b < o, Ordinal.{max u v}} {a}
  proof: by
  simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff.{_, v} _ f a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 lt_blsub_iff
  条件: {o : 序数.{u}} {f : 对任意 b < o, 序数.{最大值 u v}} {a}
  证明: by
  simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff.{_, v} _ f a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le_iff, not_congr, not_forall, not_le, not_lt
-/
theorem lt_blsub_iff {o : Ordinal.{u}} {f : forall b < o, Ordinal.{max u v}} {a} :
    a < blsub.{_, v} o f ↔ exists i hi, a <= f i hi := by
  simpa only [not_forall, not_lt, not_le] using not_congr (@blsub_le_iff.{_, v} _ f a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_le_blsub` / 定理 `bsup_le_blsub`

English:
theorem bsup_le_blsub
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: bsup_le fun i h => (lt_blsub f i h).le

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_le_blsub
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: bsup_le fun i h => (lt_blsub f i h).le

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_le, lt_blsub
-/
theorem bsup_le_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f <= blsub.{_, v} o f :=
  bsup_le fun i h => (lt_blsub f i h).le

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_le_bsup_succ` / 定理 `blsub_le_bsup_succ`

English:
theorem blsub_le_bsup_succ
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: blsub_le fun i h => lt_succ_iff.2 (le_bsup f i h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_le_bsup_succ
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: blsub_le fun i h => lt_succ_iff.2 (le_bsup f i h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le, le_bsup, lt_succ_iff
-/
theorem blsub_le_bsup_succ {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    blsub.{_, v} o f <= succ (bsup.{_, v} o f) :=
  blsub_le fun i h => lt_succ_iff.2 (le_bsup f i h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_eq_blsub_or_succ_bsup_eq_blsub` / 定理 `bsup_eq_blsub_or_succ_bsup_eq_blsub`

English:
theorem bsup_eq_blsub_or_succ_bsup_eq_blsub
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: by
  rw [← iSup_eq_bsup]; rw [← lsub_eq_blsub]
  exact iSup_eq_lsub_or_succ_iSup_eq_lsub _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_eq_blsub_or_succ_bsup_eq_blsub
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: by
  rw [← iSup_eq_bsup]; rw [← lsub_eq_blsub]
  exact iSup_eq_lsub_or_succ_iSup_eq_lsub _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: iSup_eq_bsup, iSup_eq_lsub_or_succ_iSup_eq_lsub, lsub_eq_blsub
-/
theorem bsup_eq_blsub_or_succ_bsup_eq_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ∨ succ (bsup.{_, v} o f) = blsub.{_, v} o f := by
  rw [← iSup_eq_bsup]; rw [← lsub_eq_blsub]
  exact iSup_eq_lsub_or_succ_iSup_eq_lsub _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_succ_le_blsub` / 定理 `bsup_succ_le_blsub`

English:
theorem bsup_succ_le_blsub
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact
      ne_of_lt (succ_le_iff.1 h)
        (le_antisymm (bsup_le_blsub f) (blsub_le (lt_bsup_of_ne_bsup.1 hf)))
  rintro ⟨_, _, hf⟩
  rw [succ_le_iff]; rw [← hf]
  exact lt_blsub _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")

中文:
定理 bsup_succ_le_blsub
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact
      ne_of_lt (succ_le_iff.1 h)
        (le_antisymm (bsup_le_blsub f) (blsub_le (lt_bsup_of_ne_bsup.1 hf)))
  rintro ⟨_, _, hf⟩
  rw [succ_le_iff]; rw [← hf]
  exact lt_blsub _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")

Depends on / 依赖: blsub_le, bsup_le_blsub, le_antisymm, lt_blsub, lt_bsup_of_ne_bsup, ne_of_lt, succ_le_iff
-/
theorem bsup_succ_le_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) <= blsub.{_, v} o f ↔ exists i hi, f i hi = bsup.{_, v} o f := by
  refine ⟨fun h => ?_, ?_⟩
  · by_contra! hf
    exact
      ne_of_lt (succ_le_iff.1 h)
        (le_antisymm (bsup_le_blsub f) (blsub_le (lt_bsup_of_ne_bsup.1 hf)))
  rintro ⟨_, _, hf⟩
  rw [succ_le_iff]; rw [← hf]
  exact lt_blsub _ _ _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_succ_eq_blsub` / 定理 `bsup_succ_eq_blsub`

English:
theorem bsup_succ_eq_blsub
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: (blsub_le_bsup_succ f).ge_iff_eq'.symm.trans (bsup_succ_le_blsub f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_succ_eq_blsub
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: (blsub_le_bsup_succ f).ge_iff_eq'.symm.trans (bsup_succ_le_blsub f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le_bsup_succ, bsup_succ_le_blsub, ge_iff_eq, symm.trans
-/
theorem bsup_succ_eq_blsub {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    succ (bsup.{_, v} o f) = blsub.{_, v} o f ↔ exists i hi, f i hi = bsup.{_, v} o f :=
  (blsub_le_bsup_succ f).ge_iff_eq'.symm.trans (bsup_succ_le_blsub f)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_eq_blsub_iff_succ` / 定理 `bsup_eq_blsub_iff_succ`

English:
theorem bsup_eq_blsub_iff_succ
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: by
  rw [← iSup_eq_bsup]; rw [← lsub_eq_blsub]
  apply iSup_eq_lsub_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_eq_blsub_iff_succ
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: by
  rw [← iSup_eq_bsup]; rw [← lsub_eq_blsub]
  apply iSup_eq_lsub_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: iSup_eq_bsup, iSup_eq_lsub_iff, lsub_eq_blsub
-/
theorem bsup_eq_blsub_iff_succ {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ forall a < blsub.{_, v} o f, succ a < blsub.{_, v} o f := by
  rw [← iSup_eq_bsup]; rw [← lsub_eq_blsub]
  apply iSup_eq_lsub_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_eq_blsub_iff_lt_bsup` / 定理 `bsup_eq_blsub_iff_lt_bsup`

English:
theorem bsup_eq_blsub_iff_lt_bsup
  given: {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v})
  proof: ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_eq_blsub_iff_lt_bsup
  条件: {o : 序数.{u}} (f : 对任意 a < o, 序数.{最大值 u v})
  证明: ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le, bsup_le_blsub, le_antisymm, lt_blsub
-/
theorem bsup_eq_blsub_iff_lt_bsup {o : Ordinal.{u}} (f : forall a < o, Ordinal.{max u v}) :
    bsup.{_, v} o f = blsub.{_, v} o f ↔ forall i hi, f i hi < bsup.{_, v} o f :=
  ⟨fun h i => by
    rw [h]
    apply lt_blsub, fun h => le_antisymm (bsup_le_blsub f) (blsub_le h)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_eq_blsub_of_lt_succ_limit` / 定理 `bsup_eq_blsub_of_lt_succ_limit`

English:
theorem bsup_eq_blsub_of_lt_succ_limit
  statement: {o : Ordinal.{u}} (ho : IsSuccLimit o)
  proof: by
  rw [bsup_eq_blsub_iff_lt_bsup]
  exact fun i hi => (hf i hi).trans_le (le_bsup f _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_eq_blsub_of_lt_succ_limit
  结论: {o : 序数.{u}} (ho : 是SuccLimit o)
  证明: by
  rw [bsup_eq_blsub_iff_lt_bsup]
  exact fun i hi => (hf i hi).trans_le (le_bsup f _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_eq_blsub_iff_lt_bsup, le_bsup, trans_le
-/
theorem bsup_eq_blsub_of_lt_succ_limit {o : Ordinal.{u}} (ho : IsSuccLimit o)
    {f : forall a < o, Ordinal.{max u v}} (hf : forall a ha, f a ha < f (succ a) (ho.succ_lt ha)) :
    bsup.{_, v} o f = blsub.{_, v} o f := by
  rw [bsup_eq_blsub_iff_lt_bsup]
  exact fun i hi => (hf i hi).trans_le (le_bsup f _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_succ_of_mono` / 定理 `blsub_succ_of_mono`

English:
theorem blsub_succ_of_mono
  statement: {o : Ordinal.{u}} {f : forall a < succ o, Ordinal.{max u v}}
  proof: bsup_succ_of_mono fun {_ _} hi hj h => succ_le_succ (hf hi hj h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_succ_of_mono
  结论: {o : 序数.{u}} {f : 对任意 a < succ o, 序数.{最大值 u v}}
  证明: bsup_succ_of_mono fun {_ _} hi hj h => succ_le_succ (hf hi hj h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_succ_of_mono, succ_le_succ
-/
theorem blsub_succ_of_mono {o : Ordinal.{u}} {f : forall a < succ o, Ordinal.{max u v}}
    (hf : forall {i j} (hi hj), i <= j -> f i hi <= f j hj) : blsub.{_, v} _ f = succ (f o (lt_succ o)) :=
  bsup_succ_of_mono fun {_ _} hi hj h => succ_le_succ (hf hi hj h)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_eq_zero_iff` / 定理 `blsub_eq_zero_iff`

English:
theorem blsub_eq_zero_iff
  given: {o} {f : forall a < o, Ordinal}
  statement: blsub o f = 0 ↔ o = 0
  proof: by
  rw [← lsub_eq_blsub]; rw [lsub_eq_zero_iff]
  exact isEmpty_toType_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_eq_zero_iff
  条件: {o} {f : 对任意 a < o, 序数}
  结论: blsub o f = 0 ↔ o = 0
  证明: by
  rw [← lsub_eq_blsub]; rw [lsub_eq_zero_iff]
  exact isEmpty_toType_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: isEmpty_toType_iff, lsub_eq_blsub, lsub_eq_zero_iff
-/
theorem blsub_eq_zero_iff {o} {f : forall a < o, Ordinal} : blsub o f = 0 ↔ o = 0 := by
  rw [← lsub_eq_blsub]; rw [lsub_eq_zero_iff]
  exact isEmpty_toType_iff

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_zero` / 定理 `blsub_zero`

English:
theorem blsub_zero
  given: (f : forall a < (0 : Ordinal), Ordinal)
  statement: blsub 0 f = 0
  proof: by rw [blsub_eq_zero_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_zero
  条件: (f : 对任意 a < (0 : 序数), 序数)
  结论: blsub 0 f = 0
  证明: by rw [blsub_eq_zero_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_eq_zero_iff
-/
theorem blsub_zero (f : forall a < (0 : Ordinal), Ordinal) : blsub 0 f = 0 := by rw [blsub_eq_zero_iff]

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_pos` / 定理 `blsub_pos`

English:
theorem blsub_pos
  given: {o : Ordinal} (ho : 0 < o) (f : forall a < o, Ordinal)
  statement: 0 < blsub o f
  proof: (lt_blsub f 0 ho).pos

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_pos
  条件: {o : 序数} (ho : 0 < o) (f : 对任意 a < o, 序数)
  结论: 0 < blsub o f
  证明: (lt_blsub f 0 ho).pos

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: lt_blsub
-/
theorem blsub_pos {o : Ordinal} (ho : 0 < o) (f : forall a < o, Ordinal) : 0 < blsub o f :=
  (lt_blsub f 0 ho).pos

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_type` / 定理 `blsub_type`

English:
theorem blsub_type
  statement: {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r]
  proof: eq_of_forall_ge_iff fun o => by
    rw [blsub_le_iff]; rw [lsub_le_iff]
    exact ⟨fun H b => H _ _, fun H i h => by simpa only [typein_enum] using H (enum r ⟨i, h⟩)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_type
  结论: {α : 类型u} (r : α -> α -> 命题) [是良序 α r]
  证明: eq_of_forall_ge_iff fun o => by
    rw [blsub_le_iff]; rw [lsub_le_iff]
    exact ⟨fun H b => H _ _, fun H i h => by simpa only [typein_enum] using H (enum r ⟨i, h⟩)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: blsub_le_iff, eq_of_forall_ge_iff, lsub_le_iff, typein_enum
-/
theorem blsub_type {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r]
    (f : forall a < type r, Ordinal.{max u v}) :
    blsub.{_, v} (type r) f = lsub.{_, v} fun a => f (typein r a) (typein_lt_type _ _) :=
  eq_of_forall_ge_iff fun o => by
    rw [blsub_le_iff]; rw [lsub_le_iff]
    exact ⟨fun H b => H _ _, fun H i h => by simpa only [typein_enum] using H (enum r ⟨i, h⟩)⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_const` / 定理 `blsub_const`

English:
theorem blsub_const
  given: {o : Ordinal} (ho : o != 0) (a : Ordinal)
  proof: bsup_const.{u, v} ho (succ a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_const
  条件: {o : 序数} (ho : o != 0) (a : 序数)
  证明: bsup_const.{u, v} ho (succ a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_const
-/
theorem blsub_const {o : Ordinal} (ho : o != 0) (a : Ordinal) :
    (blsub.{u, v} o fun _ _ => a) = succ a :=
  bsup_const.{u, v} ho (succ a)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_one` / 定理 `blsub_one`

English:
theorem blsub_one
  given: (f : forall a < (1 : Ordinal), Ordinal)
  statement: blsub 1 f = succ (f 0 zero_lt_one)
  proof: bsup_one _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_one
  条件: (f : 对任意 a < (1 : 序数), 序数)
  结论: blsub 1 f = succ (f 0 zero_lt_one)
  证明: bsup_one _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_one
-/
theorem blsub_one (f : forall a < (1 : Ordinal), Ordinal) : blsub 1 f = succ (f 0 zero_lt_one) :=
  bsup_one _

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_id` / 定理 `blsub_id`

English:
theorem blsub_id
  statement: forall o, (blsub.{u, u} o fun x _ => x) = o
  proof: lsub_typein

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-23")]

中文:
定理 blsub_id
  结论: 对任意 o, (blsub.{u, u} o fun x _ => x) = o
  证明: lsub_typein

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-23")]

Depends on / 依赖: lsub_typein
-/
theorem blsub_id : forall o, (blsub.{u, u} o fun x _ => x) = o :=
  lsub_typein

@[deprecated IsSuccPrelimit.sSup_Iio (since := "2026-03-23")]
/--
theorem `bsup_id_limit` / 定理 `bsup_id_limit`

English:
theorem bsup_id_limit
  given: {o : Ordinal}
  statement: (forall a < o, succ a < o) -> (bsup.{u, u} o fun x _ => x) = o
  proof: iSup_typein_limit

@[deprecated csSup_Iic (since := "2026-03-23")]

中文:
定理 bsup_id_limit
  条件: {o : 序数}
  结论: (对任意 a < o, succ a < o) -> (bsup.{u, u} o fun x _ => x) = o
  证明: iSup_typein_limit

@[deprecated csSup_Iic (since := "2026-03-23")]

Depends on / 依赖: iSup_typein_limit
-/
theorem bsup_id_limit {o : Ordinal} : (forall a < o, succ a < o) -> (bsup.{u, u} o fun x _ => x) = o :=
  iSup_typein_limit

@[deprecated csSup_Iic (since := "2026-03-23")]
/--
theorem `bsup_id_add_one` / 定理 `bsup_id_add_one`

English:
theorem bsup_id_add_one
  given: (o)
  statement: (bsup.{u, u} (o + 1) fun x _ => x) = o
  proof: iSup_typein_succ

@[deprecated csSup_Iic (since := "2026-03-23")]

中文:
定理 bsup_id_add_one
  条件: (o)
  结论: (bsup.{u, u} (o + 1) fun x _ => x) = o
  证明: iSup_typein_succ

@[deprecated csSup_Iic (since := "2026-03-23")]

Depends on / 依赖: iSup_typein_succ
-/
theorem bsup_id_add_one (o) : (bsup.{u, u} (o + 1) fun x _ => x) = o :=
  iSup_typein_succ

@[deprecated csSup_Iic (since := "2026-03-23")]
/--
theorem `bsup_id_succ` / 定理 `bsup_id_succ`

English:
theorem bsup_id_succ
  given: (o)
  statement: (bsup.{u, u} (succ o) fun x _ => x) = o
  proof: iSup_typein_succ

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_id_succ
  条件: (o)
  结论: (bsup.{u, u} (succ o) fun x _ => x) = o
  证明: iSup_typein_succ

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: iSup_typein_succ
-/
theorem bsup_id_succ (o) : (bsup.{u, u} (succ o) fun x _ => x) = o :=
  iSup_typein_succ

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_le_of_brange_subset` / 定理 `blsub_le_of_brange_subset`

English:
theorem blsub_le_of_brange_subset
  statement: {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
  proof: bsup_le_of_brange_subset.{u, v, w} fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc'] at hb'
    exact ⟨c, hc, hb'⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_le_of_brange_subset
  结论: {o o'} {f : 对任意 a < o, 序数} {g : 对任意 a < o', 序数}
  证明: bsup_le_of_brange_subset.{u, v, w} fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc'] at hb'
    exact ⟨c, hc, hb'⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_le_of_brange_subset, simp_rw
-/
theorem blsub_le_of_brange_subset {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
    (h : brange o f subseteq brange o' g) : blsub.{u, max v w} o f <= blsub.{v, max u w} o' g :=
  bsup_le_of_brange_subset.{u, v, w} fun a ⟨b, hb, hb'⟩ => by
    obtain ⟨c, hc, hc'⟩ := h ⟨b, hb, rfl⟩
    simp_rw [← hc'] at hb'
    exact ⟨c, hc, hb'⟩

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_eq_of_brange_eq` / 定理 `blsub_eq_of_brange_eq`

English:
theorem blsub_eq_of_brange_eq
  statement: {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
  proof: (blsub_le_of_brange_subset.{u, v, w} h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 blsub_eq_of_brange_eq
  结论: {o o'} {f : 对任意 a < o, 序数} {g : 对任意 a < o', 序数}
  证明: (blsub_le_of_brange_subset.{u, v, w} h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: antisymm, blsub_le_of_brange_subset, h.ge, h.le
-/
theorem blsub_eq_of_brange_eq {o o'} {f : forall a < o, Ordinal} {g : forall a < o', Ordinal}
    (h : { o | exists i hi, f i hi = o } = { o | exists i hi, g i hi = o }) :
    blsub.{u, max v w} o f = blsub.{v, max u w} o' g :=
  (blsub_le_of_brange_subset.{u, v, w} h.le).antisymm (blsub_le_of_brange_subset.{v, u, w} h.ge)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `bsup_comp` / 定理 `bsup_comp`

English:
theorem bsup_comp
  statement: {o o' : Ordinal.{max u v}} {f : forall a < o, Ordinal.{max u v w}}
  proof: by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

中文:
定理 bsup_comp
  结论: {o o' : 序数.{最大值 u v}} {f : 对任意 a < o, 序数.{最大值 u v w}}
  证明: by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]

Depends on / 依赖: bsup_le, le_antisymm, le_bsup, lt_blsub_iff
-/
theorem bsup_comp {o o' : Ordinal.{max u v}} {f : forall a < o, Ordinal.{max u v w}}
    (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj) {g : forall a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (bsup.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = bsup.{_, w} o f := by
  apply le_antisymm <;> refine bsup_le fun i hi => ?_
  · apply le_bsup
  · rw [← hg, lt_blsub_iff] at hi
    rcases hi with ⟨j, hj, hj'⟩
    exact (hf _ _ hj').trans (le_bsup _ _ _)

@[deprecated "blsub is deprecated" (since := "2026-03-23")]
/--
theorem `blsub_comp` / 定理 `blsub_comp`

English:
theorem blsub_comp
  statement: {o o' : Ordinal.{max u v}} {f : forall a < o, Ordinal.{max u v w}}
  proof: @bsup_comp.{u, v, w} o _ (fun a ha => succ (f a ha))
    (fun {_ _} _ _ h => succ_le_succ_iff.2 (hf _ _ h)) g hg

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]

中文:
定理 blsub_comp
  结论: {o o' : 序数.{最大值 u v}} {f : 对任意 a < o, 序数.{最大值 u v w}}
  证明: @bsup_comp.{u, v, w} o _ (fun a ha => succ (f a ha))
    (fun {_ _} _ _ h => succ_le_succ_iff.2 (hf _ _ h)) g hg

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]

Depends on / 依赖: bsup_comp, succ_le_succ_iff
-/
theorem blsub_comp {o o' : Ordinal.{max u v}} {f : forall a < o, Ordinal.{max u v w}}
    (hf : forall {i j} (hi) (hj), i <= j -> f i hi <= f j hj) {g : forall a < o', Ordinal.{max u v}}
    (hg : blsub.{_, u} o' g = o) :
    (blsub.{_, w} o' fun a ha => f (g a ha) (by rw [← hg]; apply lt_blsub)) = blsub.{_, w} o f :=
  @bsup_comp.{u, v, w} o _ (fun a ha => succ (f a ha))
    (fun {_ _} _ _ h => succ_le_succ_iff.2 (hf _ _ h)) g hg

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]
/--
theorem `IsNormal.bsup_eq` / 定理 `IsNormal.bsup_eq`

English:
theorem IsNormal.bsup_eq
  statement: {f : Ordinal.{u} -> Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
  proof: by
  rw [← IsNormal.bsup.{u]; rw [u]; rw [v} H (fun x _ => x) h.ne_bot]; rw [bsup_id_limit fun _ => h.succ_lt]

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]

中文:
定理 是正规.bsup_eq
  结论: {f : 序数.{u} -> 序数.{最大值 u v}} (H : 是正规 f) {o : 序数.{u}}
  证明: by
  rw [← IsNormal.bsup.{u]; rw [u]; rw [v} H (fun x _ => x) h.ne_bot]; rw [bsup_id_limit fun _ => h.succ_lt]

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]

Depends on / 依赖: IsNormal, IsNormal.bsup, bsup_id_limit, h.ne_bot, h.succ_lt, ne_bot, succ_lt
-/
theorem IsNormal.bsup_eq {f : Ordinal.{u} -> Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsSuccLimit o) : (Ordinal.bsup.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup.{u]; rw [u]; rw [v} H (fun x _ => x) h.ne_bot]; rw [bsup_id_limit fun _ => h.succ_lt]

@[deprecated IsNormal.apply_of_isSuccLimit (since := "2026-03-23")]
/--
theorem `IsNormal.blsub_eq` / 定理 `IsNormal.blsub_eq`

English:
theorem IsNormal.blsub_eq
  statement: {f : Ordinal.{u} -> Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
  proof: by
  rw [← IsNormal.bsup_eq.{u]; rw [v} H h]; rw [bsup_eq_blsub_of_lt_succ_limit h]
  exact fun a _ => H.strictMono (lt_succ a)

@[deprecated isNormal_iff (since := "2026-03-23")]

中文:
定理 是正规.blsub_eq
  结论: {f : 序数.{u} -> 序数.{最大值 u v}} (H : 是正规 f) {o : 序数.{u}}
  证明: by
  rw [← IsNormal.bsup_eq.{u]; rw [v} H h]; rw [bsup_eq_blsub_of_lt_succ_limit h]
  exact fun a _ => H.strictMono (lt_succ a)

@[deprecated isNormal_iff (since := "2026-03-23")]

Depends on / 依赖: H.strictMono, IsNormal, IsNormal.bsup_eq, bsup_eq, bsup_eq_blsub_of_lt_succ_limit, lt_succ, strictMono
-/
theorem IsNormal.blsub_eq {f : Ordinal.{u} -> Ordinal.{max u v}} (H : IsNormal f) {o : Ordinal.{u}}
    (h : IsSuccLimit o) : (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [← IsNormal.bsup_eq.{u]; rw [v} H h]; rw [bsup_eq_blsub_of_lt_succ_limit h]
  exact fun a _ => H.strictMono (lt_succ a)

@[deprecated isNormal_iff (since := "2026-03-23")]
/--
theorem `isNormal_iff_lt_succ_and_bsup_eq` / 定理 `isNormal_iff_lt_succ_and_bsup_eq`

English:
theorem isNormal_iff_lt_succ_and_bsup_eq
  given: {f : Ordinal.{u} -> Ordinal.{max u v}}
  proof: ⟨fun h => ⟨fun a => h.strictMono (lt_succ a), @IsNormal.bsup_eq f h⟩, fun ⟨h₁, h₂⟩ =>
    .of_succ_lt h₁ fun ho => by
      rw [← h₂ _ ho]
      simpa [IsLUB, upperBounds, lowerBounds, IsLeast, bsup_le_iff] using le_bsup _⟩

@[deprecated isNormal_iff (since := "2026-03-23")]

中文:
定理 isNormal_iff_lt_succ_and_bsup_eq
  条件: {f : 序数.{u} -> 序数.{最大值 u v}}
  证明: ⟨fun h => ⟨fun a => h.strictMono (lt_succ a), @IsNormal.bsup_eq f h⟩, fun ⟨h₁, h₂⟩ =>
    .of_succ_lt h₁ fun ho => by
      rw [← h₂ _ ho]
      simpa [IsLUB, upperBounds, lowerBounds, IsLeast, bsup_le_iff] using le_bsup _⟩

@[deprecated isNormal_iff (since := "2026-03-23")]

Depends on / 依赖: IsLeast, IsNormal, IsNormal.bsup_eq, bsup_eq, bsup_le_iff, h.strictMono, le_bsup, lowerBounds, lt_succ, of_succ_lt, strictMono, upperBounds
-/
theorem isNormal_iff_lt_succ_and_bsup_eq {f : Ordinal.{u} -> Ordinal.{max u v}} :
    IsNormal f ↔ (forall a, f a < f (succ a)) ∧
      forall o, IsSuccLimit o -> (bsup.{_, v} o fun x _ => f x) = f o :=
  ⟨fun h => ⟨fun a => h.strictMono (lt_succ a), @IsNormal.bsup_eq f h⟩, fun ⟨h₁, h₂⟩ =>
    .of_succ_lt h₁ fun ho => by
      rw [← h₂ _ ho]
      simpa [IsLUB, upperBounds, lowerBounds, IsLeast, bsup_le_iff] using le_bsup _⟩

@[deprecated isNormal_iff (since := "2026-03-23")]
/--
theorem `isNormal_iff_lt_succ_and_blsub_eq` / 定理 `isNormal_iff_lt_succ_and_blsub_eq`

English:
theorem isNormal_iff_lt_succ_and_blsub_eq
  given: {f : Ordinal.{u} -> Ordinal.{max u v}}
  proof: by
  rw [isNormal_iff_lt_succ_and_bsup_eq.{u]; rw [v}]; rw [and_congr_right_iff]
  intro h
  constructor <;> intro H o ho <;> have := H o ho <;>
    rwa [← bsup_eq_blsub_of_lt_succ_limit ho fun a _ => h a] at *

中文:
定理 isNormal_iff_lt_succ_and_blsub_eq
  条件: {f : 序数.{u} -> 序数.{最大值 u v}}
  证明: by
  rw [isNormal_iff_lt_succ_and_bsup_eq.{u]; rw [v}]; rw [and_congr_right_iff]
  intro h
  constructor <;> intro H o ho <;> have := H o ho <;>
    rwa [← bsup_eq_blsub_of_lt_succ_limit ho fun a _ => h a] at *

Depends on / 依赖: and_congr_right_iff, bsup_eq_blsub_of_lt_succ_limit, isNormal_iff_lt_succ_and_bsup_eq
-/
theorem isNormal_iff_lt_succ_and_blsub_eq {f : Ordinal.{u} -> Ordinal.{max u v}} :
    IsNormal f ↔ (forall a, f a < f (succ a)) ∧
      forall o, IsSuccLimit o -> (blsub.{_, v} o fun x _ => f x) = f o := by
  rw [isNormal_iff_lt_succ_and_bsup_eq.{u]; rw [v}]; rw [and_congr_right_iff]
  intro h
  constructor <;> intro H o ho <;> have := H o ho <;>
    rwa [← bsup_eq_blsub_of_lt_succ_limit ho fun a _ => h a] at *

end blsub

end Ordinal



/--
theorem `not_surjective_of_ordinal` / 定理 `not_surjective_of_ordinal`

English:
theorem not_surjective_of_ordinal
  given: {α : Type*} [Small.{u} α] (f : α -> Ordinal.{u})
  proof: by
  intro h
  obtain ⟨a, ha⟩ := h (⨆ i, succ (f i))
  apply ha.not_lt
  rw [Ordinal.lt_iSup_iff]
  exact ⟨a, Order.lt_succ _⟩

中文:
定理 not_surjective_of_ordinal
  条件: {α : 类型} [Small.{u} α] (f : α -> 序数.{u})
  证明: by
  intro h
  obtain ⟨a, ha⟩ := h (⨆ i, succ (f i))
  apply ha.not_lt
  rw [Ordinal.lt_iSup_iff]
  exact ⟨a, Order.lt_succ _⟩

Depends on / 依赖: Order.lt_succ, Ordinal, Ordinal.lt_iSup_iff, ha.not_lt, lt_iSup_iff, lt_succ, not_lt
-/
theorem not_surjective_of_ordinal {α : Type*} [Small.{u} α] (f : α -> Ordinal.{u}) :
    ¬ Surjective f := by
  intro h
  obtain ⟨a, ha⟩ := h (⨆ i, succ (f i))
  apply ha.not_lt
  rw [Ordinal.lt_iSup_iff]
  exact ⟨a, Order.lt_succ _⟩

/--
theorem `not_injective_of_ordinal` / 定理 `not_injective_of_ordinal`

English:
theorem not_injective_of_ordinal
  given: {α : Type*} [Small.{u} α] (f : Ordinal.{u} -> α)
  proof: fun h => not_surjective_of_ordinal _ (invFun_surjective h)

中文:
定理 not_injective_of_ordinal
  条件: {α : 类型} [Small.{u} α] (f : 序数.{u} -> α)
  证明: fun h => not_surjective_of_ordinal _ (invFun_surjective h)

Depends on / 依赖: invFun_surjective, not_surjective_of_ordinal
-/
theorem not_injective_of_ordinal {α : Type*} [Small.{u} α] (f : Ordinal.{u} -> α) :
    ¬ Injective f := fun h => not_surjective_of_ordinal _ (invFun_surjective h)

/--
theorem `not_small_ordinal` / 定理 `not_small_ordinal`

English:
theorem not_small_ordinal
  statement: ¬Small.{u} Ordinal.{max u v}
  proof: fun h =>
  @not_injective_of_ordinal _ h _ fun _a _b => Ordinal.lift_inj.{v, u}.1

中文:
定理 not_small_ordinal
  结论: ¬Small.{u} 序数.{最大值 u v}
  证明: fun h =>
  @not_injective_of_ordinal _ h _ fun _a _b => Ordinal.lift_inj.{v, u}.1
-/
theorem not_small_ordinal : ¬Small.{u} Ordinal.{max u v} := fun h =>
  @not_injective_of_ordinal _ h _ fun _a _b => Ordinal.lift_inj.{v, u}.1

/--
Instance `Ordinal.uncountable` / 实例 `Ordinal.uncountable`

English:
instance Ordinal.uncountable
  signature: : Uncountable Ordinal.{u}
  body: Uncountable.of_not_small not_small_ordinal.{u}

中文:
实例 序数.uncountable
  签名: : 不可数 序数.{u}
  定义体: Uncountable.of_not_small not_small_ordinal.{u}

Depends on / 依赖: Uncountable, Uncountable.of_not_small, not_small_ordinal, of_not_small
-/
instance Ordinal.uncountable : Uncountable Ordinal.{u} :=
  Uncountable.of_not_small not_small_ordinal.{u}

/--
theorem `Ordinal.not_bddAbove_compl_of_small` / 定理 `Ordinal.not_bddAbove_compl_of_small`

English:
theorem Ordinal.not_bddAbove_compl_of_small
  given: (s : Set Ordinal.{u}) [hs : Small.{u} s]
  proof: by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self]; rw [small_univ_iff] at this
  exact not_small_ordinal this

中文:
定理 序数.not_bddAbove_compl_of_small
  条件: (s : 集合 序数.{u}) [hs : Small.{u} s]
  证明: by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self]; rw [small_univ_iff] at this
  exact not_small_ordinal this

Depends on / 依赖: bddAbove_iff_small, not_small_ordinal, small_union, small_univ_iff, union_compl_self
-/
theorem Ordinal.not_bddAbove_compl_of_small (s : Set Ordinal.{u}) [hs : Small.{u} s] :
    ¬BddAbove sᶜ := by
  rw [bddAbove_iff_small]
  intro h
  have := small_union s sᶜ
  rw [union_compl_self]; rw [small_univ_iff] at this
  exact not_small_ordinal this

namespace Ordinal

/-! ### Casting naturals into ordinals, compatibility with operations -/

@[simp]
/--
theorem `iSup_natCast` / 定理 `iSup_natCast`

English:
theorem iSup_natCast
  statement: iSup Nat.cast = ω
  proof: (Ordinal.iSup_le fun n => (natCast_lt_omega0 n).le).antisymm omega0_le.2 Ordinal.le_iSup _

中文:
定理 iSup_natCast
  结论: iSup 自然数.cast = ω
  证明: (Ordinal.iSup_le fun n => (natCast_lt_omega0 n).le).antisymm omega0_le.2 Ordinal.le_iSup _

Depends on / 依赖: Ordinal, Ordinal.iSup_le, Ordinal.le_iSup, antisymm, iSup_le, le_iSup, natCast_lt_omega0, omega0_le
-/
theorem iSup_natCast : iSup Nat.cast = ω :=
(Ordinal.iSup_le fun n => (natCast_lt_omega0 n).le).antisymm omega0_le.2 Ordinal.le_iSup _

/--
theorem `apply_omega0_of_isNormal` / 定理 `apply_omega0_of_isNormal`

English:
theorem apply_omega0_of_isNormal
  given: {f : Ordinal.{u} -> Ordinal.{v}} (hf : IsNormal f)
  proof: by
  rw [← iSup_natCast]; rw [hf.map_iSup bddAbove_of_small]

@[simp]

中文:
定理 apply_omega0_of_isNormal
  条件: {f : 序数.{u} -> 序数.{v}} (hf : 是正规 f)
  证明: by
  rw [← iSup_natCast]; rw [hf.map_iSup bddAbove_of_small]

@[simp]

Depends on / 依赖: bddAbove_of_small, hf.map_iSup, iSup_natCast, map_iSup
-/
theorem apply_omega0_of_isNormal {f : Ordinal.{u} -> Ordinal.{v}} (hf : IsNormal f) :
    ⨆ n : Nat, f n = f ω := by
  rw [← iSup_natCast]; rw [hf.map_iSup bddAbove_of_small]

@[simp]
/--
theorem `add_iSup` / 定理 `add_iSup`

English:
theorem add_iSup
  given: (o : Ordinal.{u}) {ι} [Small.{u} ι] [Nonempty ι] (f : ι -> Ordinal)
  proof: (isNormal_add_right o).map_iSup bddAbove_of_small

@[simp]

中文:
定理 add_iSup
  条件: (o : 序数.{u}) {ι} [Small.{u} ι] [非空 ι] (f : ι -> 序数)
  证明: (isNormal_add_right o).map_iSup bddAbove_of_small

@[simp]

Depends on / 依赖: bddAbove_of_small, isNormal_add_right, map_iSup
-/
theorem add_iSup (o : Ordinal.{u}) {ι} [Small.{u} ι] [Nonempty ι] (f : ι -> Ordinal) :
    o + ⨆ i, f i = ⨆ i, o + f i :=
  (isNormal_add_right o).map_iSup bddAbove_of_small

@[simp]
/--
theorem `add_sSup` / 定理 `add_sSup`

English:
theorem add_sSup
  given: (o : Ordinal.{u}) {s : Set Ordinal} [Small.{u} s] (hs : s.Nonempty)
  proof: (isNormal_add_right o).map_sSup hs bddAbove_of_small

@[simp]

中文:
定理 add_sSup
  条件: (o : 序数.{u}) {s : 集合 序数} [Small.{u} s] (hs : s.非空)
  证明: (isNormal_add_right o).map_sSup hs bddAbove_of_small

@[simp]

Depends on / 依赖: bddAbove_of_small, isNormal_add_right, map_sSup
-/
theorem add_sSup (o : Ordinal.{u}) {s : Set Ordinal} [Small.{u} s] (hs : s.Nonempty) :
    o + sSup s = sSup ((o + ·) '' s) :=
  (isNormal_add_right o).map_sSup hs bddAbove_of_small

@[simp]
/--
lemma `mul_sSup` / 引理 `mul_sSup`

English:
lemma mul_sSup
  given: (o : Ordinal) (s : Set Ordinal)
  statement: o * sSup s = sSup ((o * ·) '' s)
  proof: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases eq_zero_or_pos o with (rfl | ho)
  · simp [hs.image_const]
  by_cases bdd : BddAbove s
  · exact (isNormal_mul_right ho).map_sSup hs bdd
  · rw [csSup_of_not_bddAbove bdd, csSup_empty, csSup_of_not_bddAbove]
    · simp
    exact fu

中文:
引理 mul_sSup
  条件: (o : 序数) (s : 集合 序数)
  结论: o * sSup s = sSup ((o * ·) '' s)
  证明: by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases eq_zero_or_pos o with (rfl | ho)
  · simp [hs.image_const]
  by_cases bdd : BddAbove s
  · exact (isNormal_mul_right ho).map_sSup hs bdd
  · rw [csSup_of_not_bddAbove bdd, csSup_empty, csSup_of_not_bddAbove]
    · simp
    exact fu

Depends on / 依赖: BddAbove, csSup_empty, csSup_of_not_bddAbove, eq_empty_or_nonempty, eq_zero_or_pos, hs.image_const, image_const, isNormal_mul_right, le_mul_right, map_sSup, s.eq_empty_or_nonempty, x.le_mul_right
-/
lemma mul_sSup (o : Ordinal) (s : Set Ordinal) : o * sSup s = sSup ((o * ·) '' s) := by
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp
  rcases eq_zero_or_pos o with (rfl | ho)
  · simp [hs.image_const]
  by_cases bdd : BddAbove s
  · exact (isNormal_mul_right ho).map_sSup hs bdd
  · rw [csSup_of_not_bddAbove bdd, csSup_empty, csSup_of_not_bddAbove]
    · simp
    exact fun ⟨u, hu⟩ => bdd ⟨u, fun x hx => (x.le_mul_right ho).trans (hu ⟨x, hx, rfl⟩)⟩

@[simp]
/--
lemma `mul_iSup` / 引理 `mul_iSup`

English:
lemma mul_iSup
  given: (o : Ordinal) {ι} (f : ι -> Ordinal)
  statement: o * ⨆ i, f i = ⨆ i, o * f i
  proof: by
  rw [← sSup_range]; rw [mul_sSup]; rw [← Set.range_comp']; rw [sSup_range]

@[simp]

中文:
引理 mul_iSup
  条件: (o : 序数) {ι} (f : ι -> 序数)
  结论: o * ⨆ i, f i = ⨆ i, o * f i
  证明: by
  rw [← sSup_range]; rw [mul_sSup]; rw [← Set.range_comp']; rw [sSup_range]

@[simp]

Depends on / 依赖: Set.range_comp, mul_sSup, range_comp, sSup_range
-/
lemma mul_iSup (o : Ordinal) {ι} (f : ι -> Ordinal) : o * ⨆ i, f i = ⨆ i, o * f i := by
  rw [← sSup_range]; rw [mul_sSup]; rw [← Set.range_comp']; rw [sSup_range]

@[simp]
/--
theorem `iSup_add_natCast` / 定理 `iSup_add_natCast`

English:
theorem iSup_add_natCast
  given: (o : Ordinal)
  statement: ⨆ n : Nat, o + n = o + ω
  proof: by
  rw [← iSup_natCast]; rw [Ordinal.add_iSup]

@[simp]

中文:
定理 iSup_add_natCast
  条件: (o : 序数)
  结论: ⨆ n : 自然数, o + n = o + ω
  证明: by
  rw [← iSup_natCast]; rw [Ordinal.add_iSup]

@[simp]

Depends on / 依赖: Ordinal, Ordinal.add_iSup, add_iSup, iSup_natCast
-/
theorem iSup_add_natCast (o : Ordinal) : ⨆ n : Nat, o + n = o + ω := by
  rw [← iSup_natCast]; rw [Ordinal.add_iSup]

@[simp]
/--
theorem `iSup_mul_natCast` / 定理 `iSup_mul_natCast`

English:
theorem iSup_mul_natCast
  given: (o : Ordinal)
  statement: ⨆ n : Nat, o * n = o * ω
  proof: by
  rw [← iSup_natCast]; rw [Ordinal.mul_iSup]

中文:
定理 iSup_mul_natCast
  条件: (o : 序数)
  结论: ⨆ n : 自然数, o * n = o * ω
  证明: by
  rw [← iSup_natCast]; rw [Ordinal.mul_iSup]

Depends on / 依赖: Ordinal, Ordinal.mul_iSup, iSup_natCast, mul_iSup
-/
theorem iSup_mul_natCast (o : Ordinal) : ⨆ n : Nat, o * n = o * ω := by
  rw [← iSup_natCast]; rw [Ordinal.mul_iSup]

end Ordinal
