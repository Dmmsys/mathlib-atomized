/-
Copyright (c) 2020 Mathieu Guay-Paquet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathieu Guay-Paquet
-/
module

public import Mathlib.Order.Ideal

/-!
# Order filters

## Main definitions

Throughout this file, `P` is at least a preorder, but some sections require more structure,
such as a bottom element, a top element, or a join-semilattice structure.

- `Order.PFilter P`: The type of nonempty, downward directed, upward closed subsets of `P`.
               This is dual to `Order.Ideal`, so it simply wraps `Order.Ideal Pᵒᵈ`.
- `Order.IsPFilter P`: a predicate for when a `Set P` is a filter.

Note the relation between `Order/Filter` and `Order/PFilter`: for any type `α`,
`Filter α` represents the same mathematical object as `PFilter (Set α)`.

## References

- <https://en.wikipedia.org/wiki/Filter_(mathematics)>

## Tags

pfilter, filter, ideal, dual

-/

@[expose] public section

open OrderDual

namespace Order

/--
Definition of `PFilter` / `PFilter` 的定义

English:
structure PFilter
  parameters: (P : Type*) [Preorder P]
  axioms and operations (1):
    - dual : Ideal Pᵒᵈ

中文:
结构 PFilter
  参数: (P : 类型) [Preorder P]
  公理与运算 (1 个):
    - dual : Ideal Pᵒᵈ
-/
structure PFilter (P : Type*) [Preorder P] where
  dual : Ideal Pᵒᵈ

variable {P : Type*}

/--
Definition of `IsPFilter` / `IsPFilter` 的定义

English:
definition IsPFilter
  signature: [Preorder P] (F : Set P)
  body: IsIdeal (OrderDual.ofDual ⁻¹' F)

中文:
定义 IsPFilter
  签名: [Preorder P] (F : Set P)
  定义体: IsIdeal (OrderDual.ofDual ⁻¹' F)

Depends on / 依赖: IsIdeal, OrderDual, OrderDual.ofDual, ofDual
-/
def IsPFilter [Preorder P] (F : Set P) : Prop :=
  IsIdeal (OrderDual.ofDual ⁻¹' F)

/--
theorem `IsPFilter.of_def` / 定理 `IsPFilter.of_def`

English:
theorem IsPFilter.of_def
  statement: [Preorder P] {F : Set P} (nonempty : F.Nonempty)
  proof: ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩

中文:
定理 IsPFilter.of_def
  结论: [Preorder P] {F : Set P} (nonempty : F.Nonempty)
  证明: ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩

Depends on / 依赖: directed, mem_of_le, nonempty
-/
theorem IsPFilter.of_def [Preorder P] {F : Set P} (nonempty : F.Nonempty)
    (directed : DirectedOn (· >= ·) F) (mem_of_le : forall {x y : P}, x <= y -> x in F -> y in F) :
    IsPFilter F :=
  ⟨fun _ _ _ _ => mem_of_le ‹_› ‹_›, nonempty, directed⟩

/--
Definition of `IsPFilter.toPFilter` / `IsPFilter.toPFilter` 的定义

English:
definition IsPFilter.toPFilter
  signature: [Preorder P] {F : Set P} (h : IsPFilter F)
  body: ⟨h.toIdeal⟩

中文:
定义 IsPFilter.toPFilter
  签名: [Preorder P] {F : Set P} (h : IsPFilter F)
  定义体: ⟨h.toIdeal⟩

Depends on / 依赖: h.toIdeal, toIdeal
-/
def IsPFilter.toPFilter [Preorder P] {F : Set P} (h : IsPFilter F) : PFilter P :=
  ⟨h.toIdeal⟩

namespace PFilter

section Preorder

variable [Preorder P] {x y : P} (F s t : PFilter P)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: P] : Inhabited (PFilter P)
  body: ⟨⟨default⟩⟩

中文:
实例 [Inhabited
  签名: P] : Inhabited (PFilter P)
  定义体: ⟨⟨default⟩⟩
-/
instance [Inhabited P] : Inhabited (PFilter P) := ⟨⟨default⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (PFilter P) P
  body: toDual ⁻¹' F.dual.carrier
coe_injective := fun ⟨_⟩ ⟨_⟩ h => congr_arg mk Ideal.ext h

中文:
实例 :
  签名: SetLike (PFilter P) P
  定义体: toDual ⁻¹' F.dual.carrier
coe_injective := fun ⟨_⟩ ⟨_⟩ h => congr_arg mk Ideal.ext h

Depends on / 依赖: F.dual.carrier, carrier, toDual
-/
instance : SetLike (PFilter P) P where
  coe F := toDual ⁻¹' F.dual.carrier
coe_injective := fun ⟨_⟩ ⟨_⟩ h => congr_arg mk Ideal.ext h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (PFilter P)
  body: .ofSetLike (PFilter P) P

中文:
实例 :
  签名: PartialOrder (PFilter P)
  定义体: .ofSetLike (PFilter P) P

Depends on / 依赖: PFilter, ofSetLike
-/
instance : PartialOrder (PFilter P) := .ofSetLike (PFilter P) P

/--
theorem `isPFilter` / 定理 `isPFilter`

English:
theorem isPFilter
  statement: IsPFilter (F : Set P)
  proof: F.dual.isIdeal

中文:
定理 isPFilter
  结论: IsPFilter (F : Set P)
  证明: F.dual.isIdeal

Depends on / 依赖: F.dual.isIdeal, isIdeal
-/
theorem isPFilter : IsPFilter (F : Set P) := F.dual.isIdeal

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  statement: (F : Set P).Nonempty
  proof: F.dual.nonempty

中文:
定理 nonempty
  结论: (F : Set P).Nonempty
  证明: F.dual.nonempty
-/
protected theorem nonempty : (F : Set P).Nonempty := F.dual.nonempty

/--
theorem `directed` / 定理 `directed`

English:
theorem directed
  statement: DirectedOn (· >= ·) (F : Set P)
  proof: F.dual.directed

中文:
定理 directed
  结论: DirectedOn (· >= ·) (F : Set P)
  证明: F.dual.directed

Depends on / 依赖: F.dual.directed, directed
-/
theorem directed : DirectedOn (· >= ·) (F : Set P) := F.dual.directed

/--
theorem `mem_of_le` / 定理 `mem_of_le`

English:
theorem mem_of_le
  given: {F : PFilter P}
  statement: x <= y -> x in F -> y in F
  proof: fun h => F.dual.lower h

中文:
定理 mem_of_le
  条件: {F : PFilter P}
  结论: x <= y -> x in F -> y in F
  证明: fun h => F.dual.lower h

Depends on / 依赖: F.dual.lower
-/
theorem mem_of_le {F : PFilter P} : x <= y -> x in F -> y in F := fun h => F.dual.lower h

/-- Two filters are equal when their underlying sets are equal. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (h : (s : Set P) = t)
  statement: s = t
  proof: SetLike.ext' h

@[trans]

中文:
定理 ext
  条件: (h : (s : Set P) = t)
  结论: s = t
  证明: SetLike.ext' h

@[trans]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext (h : (s : Set P) = t) : s = t := SetLike.ext' h

@[trans]
/--
theorem `mem_of_mem_of_le` / 定理 `mem_of_mem_of_le`

English:
theorem mem_of_mem_of_le
  given: {F G : PFilter P} (hx : x in F) (hle : F <= G)
  statement: x in G
  proof: hle hx

中文:
定理 mem_of_mem_of_le
  条件: {F G : PFilter P} (hx : x in F) (hle : F <= G)
  结论: x in G
  证明: hle hx
-/
theorem mem_of_mem_of_le {F G : PFilter P} (hx : x in F) (hle : F <= G) : x in G :=
  hle hx

/--
Definition of `principal` / `principal` 的定义

English:
definition principal
  signature: (p : P)
  body: ⟨Ideal.principal (toDual p)⟩

@[simp]

中文:
定义 principal
  签名: (p : P)
  定义体: ⟨Ideal.principal (toDual p)⟩

@[simp]

Depends on / 依赖: Ideal.principal, principal, toDual
-/
def principal (p : P) : PFilter P :=
  ⟨Ideal.principal (toDual p)⟩

@[simp]
/--
theorem `mem_mk` / 定理 `mem_mk`

English:
theorem mem_mk
  given: (x : P) (I : Ideal Pᵒᵈ)
  statement: x in (⟨I⟩ : PFilter P) ↔ toDual x in I
  proof: Iff.rfl

@[simp]

中文:
定理 mem_mk
  条件: (x : P) (I : Ideal Pᵒᵈ)
  结论: x in (⟨I⟩ : PFilter P) ↔ toDual x in I
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem mem_mk (x : P) (I : Ideal Pᵒᵈ) : x in (⟨I⟩ : PFilter P) ↔ toDual x in I :=
  Iff.rfl

@[simp]
/--
theorem `principal_le_iff` / 定理 `principal_le_iff`

English:
theorem principal_le_iff
  given: {F : PFilter P}
  statement: principal x <= F ↔ x in F
  proof: Ideal.principal_le_iff (x := toDual x)

中文:
定理 principal_le_iff
  条件: {F : PFilter P}
  结论: principal x <= F ↔ x in F
  证明: Ideal.principal_le_iff (x := toDual x)

Depends on / 依赖: Ideal.principal_le_iff, principal_le_iff, toDual
-/
theorem principal_le_iff {F : PFilter P} : principal x <= F ↔ x in F :=
  Ideal.principal_le_iff (x := toDual x)

/--
theorem `mem_principal` / 定理 `mem_principal`

English:
theorem mem_principal
  statement: x in principal y ↔ y <= x
  proof: Iff.rfl

中文:
定理 mem_principal
  结论: x in principal y ↔ y <= x
  证明: Iff.rfl
-/
@[simp] theorem mem_principal : x in principal y ↔ y <= x := Iff.rfl

/--
theorem `principal_le_principal_iff` / 定理 `principal_le_principal_iff`

English:
theorem principal_le_principal_iff
  given: {p q : P}
  statement: principal q <= principal p ↔ p <= q
  proof: by simp

中文:
定理 principal_le_principal_iff
  条件: {p q : P}
  结论: principal q <= principal p ↔ p <= q
  证明: by simp
-/
theorem principal_le_principal_iff {p q : P} : principal q <= principal p ↔ p <= q := by simp

-- defeq abuse
/--
theorem `antitone_principal` / 定理 `antitone_principal`

English:
theorem antitone_principal
  statement: Antitone (principal : P -> PFilter P)
  proof: fun _ _ =>
  principal_le_principal_iff.2

中文:
定理 antitone_principal
  结论: Antitone (principal : P -> PFilter P)
  证明: fun _ _ =>
  principal_le_principal_iff.2
-/
theorem antitone_principal : Antitone (principal : P -> PFilter P) := fun _ _ =>
  principal_le_principal_iff.2

end Preorder

section OrderTop

variable [Preorder P] [OrderTop P] {F : PFilter P}

/--
theorem `top_mem` / 定理 `top_mem`

English:
theorem top_mem
  statement: ⊤ in F
  proof: Ideal.bot_mem _

中文:
定理 top_mem
  结论: ⊤ in F
  证明: Ideal.bot_mem _
-/
@[simp] theorem top_mem : ⊤ in F := Ideal.bot_mem _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: OrderBot (PFilter P)
  body: ⟨⊥⟩
  bot_le F := (bot_le : ⊥ <= F.dual)

中文:
实例 :
  签名: OrderBot (PFilter P)
  定义体: ⟨⊥⟩
  bot_le F := (bot_le : ⊥ <= F.dual)
-/
instance : OrderBot (PFilter P) where
  bot := ⟨⊥⟩
  bot_le F := (bot_le : ⊥ <= F.dual)

end OrderTop

/-- There is a top filter when `P` has a bottom element. -/
instance {P} [Preorder P] [OrderBot P] : OrderTop (PFilter P) where
  top := ⟨⊤⟩
  le_top F := (le_top : F.dual <= ⊤)

section SemilatticeInf

variable [SemilatticeInf P] {x y : P} {F : PFilter P}

/--
theorem `inf_mem` / 定理 `inf_mem`

English:
theorem inf_mem
  given: (hx : x in F) (hy : y in F)
  statement: x ⊓ y in F
  proof: Ideal.sup_mem hx hy

@[simp]

中文:
定理 inf_mem
  条件: (hx : x in F) (hy : y in F)
  结论: x ⊓ y in F
  证明: Ideal.sup_mem hx hy

@[simp]

Depends on / 依赖: Ideal.sup_mem, sup_mem
-/
theorem inf_mem (hx : x in F) (hy : y in F) : x ⊓ y in F :=
  Ideal.sup_mem hx hy

@[simp]
/--
theorem `inf_mem_iff` / 定理 `inf_mem_iff`

English:
theorem inf_mem_iff
  statement: x ⊓ y in F ↔ x in F ∧ y in F
  proof: Ideal.sup_mem_iff

中文:
定理 inf_mem_iff
  结论: x ⊓ y in F ↔ x in F ∧ y in F
  证明: Ideal.sup_mem_iff

Depends on / 依赖: Ideal.sup_mem_iff, IsJacobsonRing, KrullDimLE, Ring.KrullDimLE, sup_mem_iff
-/
theorem inf_mem_iff : x ⊓ y in F ↔ x in F ∧ y in F :=
  Ideal.sup_mem_iff

end SemilatticeInf

section CompleteSemilatticeInf

variable [CompleteSemilatticeInf P]

/--
theorem `sInf_gc` / 定理 `sInf_gc`

English:
theorem sInf_gc
  proof: fun x F => by simp only [le_sInf_iff, SetLike.mem_coe, toDual_le, SetLike.le_def, mem_principal]

中文:
定理 sInf_gc
  证明: fun x F => by simp only [le_sInf_iff, SetLike.mem_coe, toDual_le, SetLike.le_def, mem_principal]

Depends on / 依赖: SetLike, SetLike.le_def, SetLike.mem_coe, le_def, le_sInf_iff, mem_coe, mem_principal, toDual_le
-/
theorem sInf_gc :
    GaloisConnection (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
  fun x F => by simp only [le_sInf_iff, SetLike.mem_coe, toDual_le, SetLike.le_def, mem_principal]

/--
Definition of `infGi` / `infGi` 的定义

English:
definition infGi
  signature: :
  body: sInf_gc.toGaloisCoinsertion fun _ => sInf_le mem_principal.2 le_rfl

中文:
定义 infGi
  签名: :
  定义体: sInf_gc.toGaloisCoinsertion fun _ => sInf_le mem_principal.2 le_rfl

Depends on / 依赖: le_rfl, mem_principal, sInf_gc, sInf_gc.toGaloisCoinsertion, sInf_le, toGaloisCoinsertion
-/
def infGi :
    GaloisCoinsertion (fun x => toDual (principal x)) fun F => sInf (ofDual F : PFilter P) :=
sInf_gc.toGaloisCoinsertion fun _ => sInf_le mem_principal.2 le_rfl

end CompleteSemilatticeInf

end PFilter

end Order
