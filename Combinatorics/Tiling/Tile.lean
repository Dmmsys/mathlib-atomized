/-
Copyright (c) 2026 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Finite
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.GroupTheory.Coset.Defs

/-!
# Tiles for tilings

This file defines some basic concepts related to individual tiles for tilings in a discrete context
(with definitions in a continuous context to be developed separately but analogously).

Work in the field of tilings does not generally try to define or state things in any kind of maximal
generality, so it is necessary to adapt definitions and statements from the literature to produce
something that seems appropriately general for mathlib, covering a wide range of tiling-related
concepts found in the literature. Nevertheless, further generalization may prove of use as this work
is extended in future.

We work in the context of a space `X` acted on by a group `G`; the action is not required to be
faithful, although typically it is. In a discrete context, tiles are expected to cover the space, or
a subset of it being tiled when working with tilings not of the whole space, and the tiles are
pairwise disjoint. In a continuous context, definitions in the literature vary; the tiles may be
closed and cover the space with interiors required to be disjoint (as used by Grünbaum and Shephard
or Goodman-Strauss), or they may be required to be measurable and to partition it up to null sets
(as used by Greenfeld and Tao).

In general we are concerned not with a tiling in isolation but with tilings by some protoset of
tiles; thus we make definitions in the context of such a protoset, where copies of the tiles in the
tiling must be images of those tiles under the action of an element of the given group.

Where there are matching rules that say what combinations of tiles are considered as valid, these
are provided as separate hypotheses where required. Tiles in a protoset are commonly considered in
the literature to be marked in some way. When this is simply to distinguish two otherwise identical
tiles, this is represented by the use of different indices in the protoset. When this is to give a
tile fewer symmetries than it would otherwise have under the action of the given group, this is
represented by the symmetries specified in the `Prototile` being less than its full stabilizer.

The group `G` is throughout here a multiplicative group. Additive groups are also used in the
literature, typically when based on `ℤ`; to support the use of additive groups, `to_additive` could
be used with the theory here.

## Main definitions

* `Prototile G X`: A prototile in `X` as acted on by `G`, carrying the information of a subgroup of
  the stabilizer that says when two copies of the prototile are considered the same.

* `Protoset G X ιₚ`: An indexed family of prototiles.

* `PlacedTile ps`: An image of a tile in the protoset `ps`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
* [Chaim Goodman-Strauss, *Open Questions in Tiling*][GoodmanStrauss2000]
* [Rachel Greenfeld and Terence Tao, *A counterexample to the periodic tiling
  conjecture*][GreenfeldTao2024]
-/


@[expose] public section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X ιₚ : Type*} [Group G] [MulAction G X]

variable (G X) in
/-- A `Prototile G X` describes a tile in `X`, copies of which under elements of `G` may be used in
tilings. Two copies related by an element of `symmetries` are considered the same; two copies not so
related, even if they have the same points, are considered distinct. -/
/-
**DiscreteTiling.Prototile** 是 Mathlib 中的一个归纳类型，位于命名空间 `DiscreteTiling`。
形式化陈述：(G : Type u_1) → (X : Type u_2) → [inst : Group G] → [MulAction G X] → Typ
e (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Prototile G X` describes a tile in `X`, copies of which under elements of `G`
 may be used in
tilings. Two copies related by an element of `symmetries` are considered the sam
e; two copies not so
related, even if they have the same points, are considered distinct.
-/
@[ext] structure Prototile where
  /-- The points in the prototile. Use the coercion to `Set X`, or `∈` on the `Prototile`, rather
      than using `carrier` directly. The coercion cannot use `SetLike` because it does not satisfy
      `coe_injective`. -/
  carrier : Set X
  /-- The group elements considered to be symmetries of the prototile. -/
  symmetries : Subgroup (MulAction.stabilizer G carrier)

namespace Prototile

/-
**DiscreteTiling.Prototile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.Prototile`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Prototile G X) where
  default := ⟨∅, ⊥⟩
/-
**DiscreteTiling.Prototile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.Prototile`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (Prototile G X) (Set X) where
  coe := Prototile.carrier

attribute [coe] carrier
/-
**DiscreteTiling.Prototile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.Prototile`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership X (Prototile G X) where
  mem p x := x ∈ (p : Set X)
/-
**DiscreteTiling.Prototile.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteTiling.Prot
otile`。
形式化陈述：coe_mk (c s) : (⟨c, s⟩ : Prototile G X) = c
参数：c s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (c s) : (⟨c, s⟩ : Prototile G X) = c := rfl
/-
**DiscreteTiling.Prototile.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTiling.Pro
totile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} [inst : Group G] [inst_1 : MulAction G X] 
{x : X} {p : DiscreteTiling.Prototile G X},   x ∈ ↑p ↔ x ∈ p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_coe {x : X} {p : Prototile G X} : x ∈ (p : Set X) ↔ x ∈ p := Iff.rfl

end Prototile

variable (G X ιₚ) in
/-- A `Protoset G X ιₚ` is an indexed family of `Prototile G X`. This is a separate definition
rather than just using plain functions to facilitate defining associated API that can be used with
dot notation. -/
/-
**DiscreteTiling.Protoset** 是 Mathlib 中的一个归纳类型，位于命名空间 `DiscreteTiling`。
形式化陈述：(G : Type u_1) → (X : Type u_2) → Type u_3 → [inst : Group G] → [MulAction
 G X] → Type (max (max u_1 u_2) u_3)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Protoset G X ιₚ` is an indexed family of `Prototile G X`. This is a separate 
definition
rather than just using plain functions to facilitate defining associated API tha
t can be used with
dot notation.
-/
@[ext] structure Protoset where
  /-- The tiles in the protoset. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₚ → Prototile G X

namespace Protoset

/-
**DiscreteTiling.Protoset.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.Protoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Protoset G X ιₚ) where
  default := ⟨fun _ ↦ default⟩
/-
**DiscreteTiling.Protoset.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.Protoset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Protoset G X ιₚ) (fun _ ↦ ιₚ → Prototile G X) where
  coe := tiles

attribute [coe] tiles
/-
**DiscreteTiling.Protoset.coe_mk** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteTiling.Proto
set`。
形式化陈述：coe_mk (t) : (⟨t⟩ : Protoset G X ιₚ) = t
参数：t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk (t) : (⟨t⟩ : Protoset G X ιₚ) = t := rfl
/-
**DiscreteTiling.Protoset.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTiling.Prot
oset`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps₁ ps₂ : DiscreteTiling.Protoset G X ιₚ}, ↑ps₁ = ↑ps₂ ↔ ps₁ 
= ps₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `DiscreteTiling.Protoset.ext_iff`：∀ {G : Type u_1} {X : Type u_2} {ιₚ : T
ype u_3} {inst : Group G} {inst_1 : MulAction G X}   {x y : DiscreteTiling.Proto
set G X ιₚ}, x = y ↔ …
-/
@[simp, norm_cast] lemma coe_inj {ps₁ ps₂ : Protoset G X ιₚ} :
    (ps₁ : ιₚ → Prototile G X) = ps₂ ↔ ps₁ = ps₂ :=
  Protoset.ext_iff.symm
/-
**DiscreteTiling.Protoset.coe_injective** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteTilin
g.Protoset`。
形式化陈述：coe_injective : Injective (Protoset.tiles : Protoset G X ιₚ -> ιₚ -> Proto
tile G X)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `DiscreteTiling.Protoset.coe_inj`：∀ {G : Type u_1} {X : Type u_2} {ιₚ : T
ype u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps₁ ps₂ : DiscreteTiling.P
rotoset G X ιₚ}, ↑ps₁…
-/
lemma coe_injective : Injective (Protoset.tiles : Protoset G X ιₚ → ιₚ → Prototile G X) :=
  fun _ _ ↦ coe_inj.1

end Protoset

variable {ps : Protoset G X ιₚ}

variable (ps) in
/-- A `PlacedTile ps` is an image of a tile in the protoset `p` under an element of the group `G`.
This is represented using a quotient so that images under group elements differing only by a
symmetry of the tile are equal. -/
/-
**DiscreteTiling.PlacedTile** 是 Mathlib 中的一个归纳类型，位于命名空间 `DiscreteTiling`。
形式化陈述：{G : Type u_1} →   {X : Type u_2} →     {ιₚ : Type u_3} → [inst : Group G]
 → [inst_1 : MulAction G X] → DiscreteTiling.Protoset G X ιₚ → Type (max u_1 u_3
)
参数：max u_1 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `PlacedTile ps` is an image of a tile in the protoset `p` under an element of 
the group `G`.
This is represented using a quotient so that images under group elements differi
ng only by a
symmetry of the tile are equal.
-/
@[ext] structure PlacedTile where
  /-- The index of the tile in the protoset. -/
  index : ιₚ
  /-- The group elements under which this tile is an image. -/
  groupElts : G ⧸ ((ps index).symmetries.map <| Subgroup.subtype _)

namespace PlacedTile

/-
**DiscreteTiling.PlacedTile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.PlacedTil
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nonempty ιₚ] : Nonempty (PlacedTile ps) := ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

/-- An induction principle to deduce results for `PlacedTile` from those given an index and an
element of `G`, used with `induction pt using PlacedTile.induction_on`. -/
/-
**DiscreteTiling.PlacedTile.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTili
ng.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} {ppt : DiscreteTiling.Pl
acedTile ps → Prop} (pt : DiscreteTiling.PlacedTile ps),   (∀ (i : ιₚ) (gx : G),
 ppt { index := i, groupElts := ↑gx }) → ppt pt
参数：pt : DiscreteTiling.PlacedTile ps；∀ (i : ιₚ) (gx : G), ppt { index := i, grou
pElts := ↑gx }。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q

--- 原说明 ---
An induction principle to deduce results for `PlacedTile` from those given an in
dex and an
element of `G`, used with `induction pt using PlacedTile.induction_on`.
-/
@[elab_as_elim] protected lemma induction_on {ppt : PlacedTile ps → Prop} (pt : PlacedTile ps)
    (h : ∀ i : ιₚ, ∀ gx : G, ppt ⟨i, gx⟩) : ppt pt := by
  rcases pt with ⟨i, gx⟩
  induction gx using Quotient.inductionOn
  apply h

/-- An alternative extensionality principle for `PlacedTile` that avoids `HEq`, using existence of a
common group element. -/
/-
**DiscreteTiling.PlacedTile.ext_iff_of_exists** 是 Mathlib 中的一个引理，位于命名空间 `Discret
eTiling.PlacedTile`。
形式化陈述：ext_iff_of_exists {pt₁ pt₂ : PlacedTile ps} : pt₁ = pt₂ ↔ pt₁.index = pt₂.
index ∧ exists g, ⟦g⟧ = pt₁.groupElts ∧ ⟦g⟧ = pt₂.groupElts
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
· 使用定理 `DiscreteTiling.PlacedTile.ext`：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Typ
e u_3} {inst : Group G} {inst_1 : MulAction G X}   {ps : DiscreteTiling.Protoset
 G X ιₚ} {x y : Dis…
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
An alternative extensionality principle for `PlacedTile` that avoids `HEq`, usin
g existence of a
common group element.
-/
lemma ext_iff_of_exists {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧ ∃ g, ⟦g⟧ = pt₁.groupElts ∧ ⟦g⟧ = pt₂.groupElts := by
  refine ⟨fun h ↦ ?_, fun ⟨h, g, hg₁, hg₂⟩ ↦ ?_⟩
  · subst h
    simp only [and_self, true_and]
    refine ⟨pt₁.groupElts.out, ?_⟩
    rw [Quotient.out_eq]
  · rcases pt₁ with ⟨i₁, g₁⟩
    rcases pt₂ with ⟨i₂, g₂⟩
    dsimp only at h
    subst h
    ext
    · rfl
    · exact heq_of_eq (hg₁.symm.trans hg₂)

/-- An alternative extensionality principle for `PlacedTile` that avoids `HEq`, using equality of
quotient preimages. -/
/-
**DiscreteTiling.PlacedTile.ext_iff_of_preimage** 是 Mathlib 中的一个引理，位于命名空间 `Discr
eteTiling.PlacedTile`。
形式化陈述：ext_iff_of_preimage {pt₁ pt₂ : PlacedTile ps} : pt₁ = pt₂ ↔ pt₁.index = pt
₂.index ∧ (Quotient.mk _) ⁻¹' {pt₁.groupElts} = (Quotient.mk _) ⁻¹' {pt₂.groupEl
ts}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `DiscreteTiling.PlacedTile.ext`：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Typ
e u_3} {inst : Group G} {inst_1 : MulAction G X}   {ps : DiscreteTiling.Protoset
 G X ιₚ} {x y : Dis…
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.singleton_eq_singleton_iff`：singleton_eq_singleton_iff {x y : α} : {
x} = ({y} : Set α) ↔ x = y
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `Set.preimage_eq_preimage`：preimage_eq_preimage {f : β -> α} (hf : Surjec
tive f) : f ⁻¹' s = f ⁻¹' t ↔ s = t
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''

--- 原说明 ---
An alternative extensionality principle for `PlacedTile` that avoids `HEq`, usin
g equality of
quotient preimages.
-/
lemma ext_iff_of_preimage {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧
      (Quotient.mk _) ⁻¹' {pt₁.groupElts} = (Quotient.mk _) ⁻¹' {pt₂.groupElts} := by
  refine ⟨fun h ↦ ?_, fun ⟨hi, hq⟩ ↦ ?_⟩
  · subst h
    simp only [and_self]
  · rcases pt₁ with ⟨i₁, g₁⟩
    rcases pt₂ with ⟨i₂, g₂⟩
    dsimp only at hi
    subst hi
    ext
    · rfl
    · exact heq_of_eq (Set.singleton_eq_singleton_iff.1
        ((Set.preimage_eq_preimage Quotient.mk''_surjective).1 hq))

/-- Coercion from a `PlacedTile` to a set of points. Use the coercion rather than using `coeSet`
directly. -/
/-
**DiscreteTiling.PlacedTile.coeSet** 是 Mathlib 中的一个定义，位于命名空间 `DiscreteTiling.Pla
cedTile`。
形式化陈述：{G : Type u_1} →   {X : Type u_2} →     {ιₚ : Type u_3} →       [inst : Gr
oup G] →         [inst_1 : MulAction G X] → {ps : DiscreteTiling.Protoset G X ιₚ
} → DiscreteTiling.PlacedTile ps → Set X
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a `PlacedTile` to a set of points. Use the coercion rather than us
ing `coeSet`
directly.
-/
@[coe] def coeSet (pt : PlacedTile ps) : Set X :=
  Quotient.liftOn' pt.groupElts (fun g ↦ g • (ps pt.index : Set X))
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      rw [eq_comm, ← inv_smul_eq_iff, smul_smul, ← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r
/-
**DiscreteTiling.PlacedTile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.PlacedTil
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (PlacedTile ps) (Set X) where
  coe := coeSet
/-
**DiscreteTiling.PlacedTile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.PlacedTil
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Membership X (PlacedTile ps) where
  mem p x := x ∈ (p : Set X)
/-
**DiscreteTiling.PlacedTile.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTiling.Pl
acedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} {x : X} {pt : DiscreteTi
ling.PlacedTile ps}, x ∈ ↑pt ↔ x ∈ pt
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_coe {x : X} {pt : PlacedTile ps} : x ∈ (pt : Set X) ↔ x ∈ pt := Iff.rfl
/-
**DiscreteTiling.PlacedTile.coe_mk_mk** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteTiling.
PlacedTile`。
形式化陈述：coe_mk_mk (i : ιₚ) (g : G) : (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : Set 
X)
参数：i : ιₚ；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk_mk (i : ιₚ) (g : G) : (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl
/-
**DiscreteTiling.PlacedTile.coe_mk_coe** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteTiling
.PlacedTile`。
形式化陈述：coe_mk_coe (i : ιₚ) (g : G) : (⟨i, g⟩ : PlacedTile ps) = g • (ps i : Set X
)
参数：i : ιₚ；g : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_mk_coe (i : ιₚ) (g : G) : (⟨i, g⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl
/-
**DiscreteTiling.PlacedTile.coe_nonempty_iff** 是 Mathlib 中的一个引理，位于命名空间 `Discrete
Tiling.PlacedTile`。
形式化陈述：coe_nonempty_iff {pt : PlacedTile ps} : (pt : Set X).Nonempty ↔ (ps pt.ind
ex : Set X).Nonempty
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `Quotient.liftOn'_mk''`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (
f : α → φ) (h : ∀ (a b : α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).li
ftOn' f h =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_nonempty_iff {pt : PlacedTile ps} :
    (pt : Set X).Nonempty ↔ (ps pt.index : Set X).Nonempty := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq', Quotient.liftOn'_mk'']
  simp
/-
**DiscreteTiling.PlacedTile.coe_mk_nonempty_iff** 是 Mathlib 中的一个定理，位于命名空间 `Discr
eteTiling.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} {i : ιₚ}   (g : G ⧸ Subg
roup.map (MulAction.stabilizer G ↑(↑ps i)).subtype (↑ps i).symmetries),   (↑{ in
dex := i, groupElts := g }).Nonempty ↔ (↑(↑ps i)).Nonempty
参数：g : G ⧸ Subgroup.map (MulAction.stabilizer G ↑(↑ps i)).subtype (↑ps i).symmet
ries；↑{ index := i, groupElts := g }；↑(↑ps i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiscreteTiling.PlacedTile.coe_nonempty_iff`：coe_nonempty_iff {pt : Place
dTile ps} : (pt : Set X).Nonempty ↔ (ps pt.index : Set X).Nonempty
-/
@[simp] lemma coe_mk_nonempty_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Nonempty ↔ (ps i : Set X).Nonempty :=
  coe_nonempty_iff
/-
**DiscreteTiling.PlacedTile.coe_finite_iff** 是 Mathlib 中的一个引理，位于命名空间 `DiscreteTi
ling.PlacedTile`。
形式化陈述：coe_finite_iff {pt : PlacedTile ps} : (pt : Set X).Finite ↔ (ps pt.index :
 Set X).Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.out_eq'`：out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q
· 使用定理 `Quotient.liftOn'_mk''`：∀ {α : Sort u_1} {φ : Sort u_4} {s₁ : Setoid α} (
f : α → φ) (h : ∀ (a b : α), s₁ a b → f a = f b) (x : α),   (Quotient.mk'' x).li
ftOn' f h =…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coe_finite_iff {pt : PlacedTile ps} :
    (pt : Set X).Finite ↔ (ps pt.index : Set X).Finite := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq', Quotient.liftOn'_mk'']
  simp
/-
**DiscreteTiling.PlacedTile.coe_mk_finite_iff** 是 Mathlib 中的一个定理，位于命名空间 `Discret
eTiling.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} {i : ιₚ}   (g : G ⧸ Subg
roup.map (MulAction.stabilizer G ↑(↑ps i)).subtype (↑ps i).symmetries),   (↑{ in
dex := i, groupElts := g }).Finite ↔ (↑(↑ps i)).Finite
参数：g : G ⧸ Subgroup.map (MulAction.stabilizer G ↑(↑ps i)).subtype (↑ps i).symmet
ries；↑{ index := i, groupElts := g }；↑(↑ps i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DiscreteTiling.PlacedTile.coe_finite_iff`：coe_finite_iff {pt : PlacedTil
e ps} : (pt : Set X).Finite ↔ (ps pt.index : Set X).Finite
-/
@[simp] lemma coe_mk_finite_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Finite ↔ (ps i : Set X).Finite :=
  coe_finite_iff
/-
**DiscreteTiling.PlacedTile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.PlacedTil
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul G (PlacedTile ps) where
  smul g pt := Quotient.liftOn' pt.groupElts (fun h ↦ ⟨pt.index, g * h⟩)
    fun a b r ↦ by
      rw [QuotientGroup.leftRel_eq] at r
      refine PlacedTile.ext rfl ?_
      simpa [QuotientGroup.eq, ← mul_assoc] using r
/-
**DiscreteTiling.PlacedTile.smul_mk_mk** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTiling
.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} (g h : G) (i : ιₚ),   g 
• { index := i, groupElts := ⟦h⟧ } = { index := i, groupElts := ↑(g * h) }
参数：g h : G；i : ιₚ；g * h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_mk_mk (g h : G) (i : ιₚ) : g • (⟨i, ⟦h⟧⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl
/-
**DiscreteTiling.PlacedTile.smul_mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTilin
g.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} (g h : G) (i : ιₚ),   g 
• { index := i, groupElts := ↑h } = { index := i, groupElts := ↑(g * h) }
参数：g h : G；i : ιₚ；g * h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma smul_mk_coe (g h : G) (i : ιₚ) : g • (⟨i, h⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl
/-
**DiscreteTiling.PlacedTile.smul_index** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTiling
.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} (g : G) (pt : DiscreteTi
ling.PlacedTile ps), (g • pt).index = pt.index
参数：g : G；pt : DiscreteTiling.PlacedTile ps；g • pt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTiling.PlacedTile.induction_on`：∀ {G : Type u_1} {X : Type u_2} 
{ιₚ : Type u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps : DiscreteTiling
.Protoset G X ιₚ} {ppt : Dis…
-/
@[simp] lemma smul_index (g : G) (pt : PlacedTile ps) : (g • pt).index = pt.index := by
  induction pt using PlacedTile.induction_on
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**DiscreteTiling.PlacedTile.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `DiscreteTiling.P
lacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} (g : G) (pt : DiscreteTi
ling.PlacedTile ps), ↑(g • pt) = g • ↑pt
参数：g : G；pt : DiscreteTiling.PlacedTile ps；g • pt。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DiscreteTiling.PlacedTile.induction_on`：∀ {G : Type u_1} {X : Type u_2} 
{ιₚ : Type u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps : DiscreteTiling
.Protoset G X ιₚ} {ppt : Dis…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coe_smul (g : G) (pt : PlacedTile ps) :
    (g • pt : PlacedTile ps) = g • (pt : Set X) := by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]
/-
**DiscreteTiling.PlacedTile.** 是 Mathlib 中的一个实例，位于命名空间 `DiscreteTiling.PlacedTil
e`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulAction G (PlacedTile ps) where
  __ : SMul G (PlacedTile ps) := inferInstance
  one_smul pt := by
    induction pt using PlacedTile.induction_on
    simp
  mul_smul x y pt := by
    induction pt using PlacedTile.induction_on
    simp [mul_assoc]
/-
**DiscreteTiling.PlacedTile.smul_mem_smul_iff** 是 Mathlib 中的一个定理，位于命名空间 `Discret
eTiling.PlacedTile`。
形式化陈述：∀ {G : Type u_1} {X : Type u_2} {ιₚ : Type u_3} [inst : Group G] [inst_1 :
 MulAction G X]   {ps : DiscreteTiling.Protoset G X ιₚ} (g : G) {x : X} {pt : Di
screteTiling.PlacedTile ps}, g • x ∈ g • pt ↔ x ∈ pt
参数：g : G。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DiscreteTiling.PlacedTile.mem_coe`：∀ {G : Type u_1} {X : Type u_2} {ιₚ :
 Type u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps : DiscreteTiling.Prot
oset G X ιₚ} {x : X} {p…
· 使用定理 `DiscreteTiling.PlacedTile.coe_smul`：∀ {G : Type u_1} {X : Type u_2} {ιₚ 
: Type u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps : DiscreteTiling.Pro
toset G X ιₚ} (g : G) (p…
· 使用定理 `Set.smul_mem_smul_set_iff`：smul_mem_smul_set_iff : a • x in a • s ↔ x in
 s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma smul_mem_smul_iff (g : G) {x : X} {pt : PlacedTile ps} : g • x ∈ g • pt ↔ x ∈ pt := by
  rw [← mem_coe, coe_smul, Set.smul_mem_smul_set_iff, mem_coe]
/-
**DiscreteTiling.PlacedTile.mem_smul_iff_smul_inv_mem** 是 Mathlib 中的一个引理，位于命名空间 
`DiscreteTiling.PlacedTile`。
形式化陈述：mem_smul_iff_smul_inv_mem {g : G} {x : X} {pt : PlacedTile ps} : x in g • 
pt ↔ g⁻¹ • x in pt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DiscreteTiling.PlacedTile.coe_smul`：∀ {G : Type u_1} {X : Type u_2} {ιₚ 
: Type u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps : DiscreteTiling.Pro
toset G X ιₚ} (g : G) (p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_smul_iff_smul_inv_mem {g : G} {x : X} {pt : PlacedTile ps} :
    x ∈ g • pt ↔ g⁻¹ • x ∈ pt := by
  simp_rw [← mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]
/-
**DiscreteTiling.PlacedTile.mem_inv_smul_iff_smul_mem** 是 Mathlib 中的一个引理，位于命名空间 
`DiscreteTiling.PlacedTile`。
形式化陈述：mem_inv_smul_iff_smul_mem {g : G} {x : X} {pt : PlacedTile ps} : x in g⁻¹ 
• pt ↔ g • x in pt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `DiscreteTiling.PlacedTile.coe_smul`：∀ {G : Type u_1} {X : Type u_2} {ιₚ 
: Type u_3} [inst : Group G] [inst_1 : MulAction G X]   {ps : DiscreteTiling.Pro
toset G X ιₚ} (g : G) (p…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_inv_smul_iff_smul_mem {g : G} {x : X} {pt : PlacedTile ps} :
    x ∈ g⁻¹ • pt ↔ g • x ∈ pt := by
  simp_rw [← mem_coe, coe_smul, Set.mem_inv_smul_set_iff]

end PlacedTile

end DiscreteTiling

