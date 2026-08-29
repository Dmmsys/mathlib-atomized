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
/--
Definition of `Prototile` / `Prototile` 的定义

English:
structure Prototile
  parameters: where
  axioms and operations (2):
    - carrier : Set X
    - symmetries : Subgroup (MulAction.stabilizer G carrier)

中文:
结构 Prototile
  参数: where
  公理与运算 (2 个):
    - carrier : 集合 X
    - symmetries : 子群 (乘法作用.stabilizer G carrier)
-/
@[ext] structure Prototile where
  /-- The points in the prototile. Use the coercion to `Set X`, or `∈` on the `Prototile`, rather
      than using `carrier` directly. The coercion cannot use `SetLike` because it does not satisfy
      `coe_injective`. -/
  carrier : Set X
  /-- The group elements considered to be symmetries of the prototile. -/
  symmetries : Subgroup (MulAction.stabilizer G carrier)

namespace Prototile

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Prototile G X)
  body: ⟨∅, ⊥⟩

中文:
实例 :
  签名: 可居 (Prototile G X)
  定义体: ⟨∅, ⊥⟩
-/
instance : Inhabited (Prototile G X) where
  default := ⟨∅, ⊥⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (Prototile G X) (Set X)
  body: Prototile.carrier

中文:
实例 :
  签名: CoeOut (Prototile G X) (集合 X)
  定义体: Prototile.carrier

Depends on / 依赖: Prototile, Prototile.carrier, carrier
-/
instance : CoeOut (Prototile G X) (Set X) where
  coe := Prototile.carrier

attribute [coe] carrier

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership X (Prototile G X)
  body: x in (p : Set X)

中文:
实例 :
  签名: Membership X (Prototile G X)
  定义体: x in (p : Set X)
-/
instance : Membership X (Prototile G X) where
  mem p x := x in (p : Set X)

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (c s)
  statement: (⟨c, s⟩ : Prototile G X) = c
  proof: rfl

中文:
引理 coe_mk
  条件: (c s)
  结论: (⟨c, s⟩ : Prototile G X) = c
  证明: rfl
-/
lemma coe_mk (c s) : (⟨c, s⟩ : Prototile G X) = c := rfl

/--
lemma `mem_coe` / 引理 `mem_coe`

English:
lemma mem_coe
  given: {x : X} {p : Prototile G X}
  statement: x in (p : Set X) ↔ x in p
  proof: Iff.rfl

中文:
引理 mem_coe
  条件: {x : X} {p : Prototile G X}
  结论: x in (p : 集合 X) ↔ x in p
  证明: Iff.rfl
-/
@[simp] lemma mem_coe {x : X} {p : Prototile G X} : x in (p : Set X) ↔ x in p := Iff.rfl

end Prototile

variable (G X ιₚ) in
/--
Definition of `Protoset` / `Protoset` 的定义

English:
structure Protoset
  parameters: where
  axioms and operations (1):
    - tiles : ιₚ -> Prototile G X

中文:
结构 Protoset
  参数: where
  公理与运算 (1 个):
    - tiles : ιₚ -> Prototile G X
-/
@[ext] structure Protoset where
  /-- The tiles in the protoset. Use the coercion to a function rather than using `tiles`
      directly. -/
  tiles : ιₚ -> Prototile G X

namespace Protoset

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Protoset G X ιₚ)
  body: ⟨fun _ => default⟩

中文:
实例 :
  签名: 可居 (Protoset G X ιₚ)
  定义体: ⟨fun _ => default⟩
-/
instance : Inhabited (Protoset G X ιₚ) where
  default := ⟨fun _ => default⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Protoset G X ιₚ) (fun _ => ιₚ -> Prototile G X)
  body: tiles

中文:
实例 :
  签名: CoeFun (Protoset G X ιₚ) (fun _ => ιₚ -> Prototile G X)
  定义体: tiles
-/
instance : CoeFun (Protoset G X ιₚ) (fun _ => ιₚ -> Prototile G X) where
  coe := tiles

attribute [coe] tiles

/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (t)
  statement: (⟨t⟩ : Protoset G X ιₚ) = t
  proof: rfl

中文:
引理 coe_mk
  条件: (t)
  结论: (⟨t⟩ : Protoset G X ιₚ) = t
  证明: rfl
-/
lemma coe_mk (t) : (⟨t⟩ : Protoset G X ιₚ) = t := rfl

/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  given: {ps₁ ps₂ : Protoset G X ιₚ}
  proof: Protoset.ext_iff.symm

中文:
引理 coe_inj
  条件: {ps₁ ps₂ : Protoset G X ιₚ}
  证明: Protoset.ext_iff.symm
-/
@[simp, norm_cast] lemma coe_inj {ps₁ ps₂ : Protoset G X ιₚ} :
    (ps₁ : ιₚ -> Prototile G X) = ps₂ ↔ ps₁ = ps₂ :=
  Protoset.ext_iff.symm

/--
lemma `coe_injective` / 引理 `coe_injective`

English:
lemma coe_injective
  statement: Injective (Protoset.tiles : Protoset G X ιₚ -> ιₚ -> Prototile G X)
  proof: fun _ _ => coe_inj.1

中文:
引理 coe_injective
  结论: 单射 (Protoset.tiles : Protoset G X ιₚ -> ιₚ -> Prototile G X)
  证明: fun _ _ => coe_inj.1

Depends on / 依赖: coe_inj
-/
lemma coe_injective : Injective (Protoset.tiles : Protoset G X ιₚ -> ιₚ -> Prototile G X) :=
  fun _ _ => coe_inj.1

end Protoset

variable {ps : Protoset G X ιₚ}

variable (ps) in
/--
Definition of `PlacedTile` / `PlacedTile` 的定义

English:
structure PlacedTile
  parameters: where
  axioms and operations (2):
    - index : ιₚ
    - groupElts : G ⧸ ((ps index).symmetries.map <| Subgroup.subtype _)

中文:
结构 PlacedTile
  参数: where
  公理与运算 (2 个):
    - index : ιₚ
    - groupElts : G ⧸ ((ps index).symmetries.map <| 子群.subtype _)
-/
@[ext] structure PlacedTile where
  /-- The index of the tile in the protoset. -/
  index : ιₚ
  /-- The group elements under which this tile is an image. -/
  groupElts : G ⧸ ((ps index).symmetries.map <| Subgroup.subtype _)

namespace PlacedTile

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: ιₚ] : Nonempty (PlacedTile ps)
  body: ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

中文:
实例 [非空
  签名: ιₚ] : 非空 (PlacedTile ps)
  定义体: ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary
-/
instance [Nonempty ιₚ] : Nonempty (PlacedTile ps) := ⟨⟨Classical.arbitrary _, (1 : G)⟩⟩

/--
lemma `induction_on` / 引理 `induction_on`

English:
lemma induction_on
  statement: {ppt : PlacedTile ps -> Prop} (pt : PlacedTile ps)
  proof: by
  rcases pt with ⟨i, gx⟩
  induction gx using Quotient.inductionOn
  apply h

中文:
引理 induction_on
  结论: {ppt : PlacedTile ps -> 命题} (pt : PlacedTile ps)
  证明: by
  rcases pt with ⟨i, gx⟩
  induction gx using Quotient.inductionOn
  apply h
-/
@[elab_as_elim] protected lemma induction_on {ppt : PlacedTile ps -> Prop} (pt : PlacedTile ps)
    (h : forall i : ιₚ, forall gx : G, ppt ⟨i, gx⟩) : ppt pt := by
  rcases pt with ⟨i, gx⟩
  induction gx using Quotient.inductionOn
  apply h

/--
lemma `ext_iff_of_exists` / 引理 `ext_iff_of_exists`

English:
lemma ext_iff_of_exists
  given: {pt₁ pt₂ : PlacedTile ps}
  proof: by
  refine ⟨fun h => ?_, fun ⟨h, g, hg₁, hg₂⟩ => ?_⟩
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

中文:
引理 ext_iff_of_存在
  条件: {pt₁ pt₂ : PlacedTile ps}
  证明: by
  refine ⟨fun h => ?_, fun ⟨h, g, hg₁, hg₂⟩ => ?_⟩
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

Depends on / 依赖: Quotient, Quotient.out_eq, and_self, groupElts, groupElts.out, heq_of_eq, out_eq, symm.trans, true_and
-/
lemma ext_iff_of_exists {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧ exists g, ⟦g⟧ = pt₁.groupElts ∧ ⟦g⟧ = pt₂.groupElts := by
  refine ⟨fun h => ?_, fun ⟨h, g, hg₁, hg₂⟩ => ?_⟩
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

/--
lemma `ext_iff_of_preimage` / 引理 `ext_iff_of_preimage`

English:
lemma ext_iff_of_preimage
  given: {pt₁ pt₂ : PlacedTile ps}
  proof: by
  refine ⟨fun h => ?_, fun ⟨hi, hq⟩ => ?_⟩
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

中文:
引理 ext_iff_of_preimage
  条件: {pt₁ pt₂ : PlacedTile ps}
  证明: by
  refine ⟨fun h => ?_, fun ⟨hi, hq⟩ => ?_⟩
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

Depends on / 依赖: Quotient, Quotient.mk, Set.preimage_eq_preimage, Set.singleton_eq_singleton_iff, _surjective, and_self, heq_of_eq, preimage_eq_preimage, singleton_eq_singleton_iff
-/
lemma ext_iff_of_preimage {pt₁ pt₂ : PlacedTile ps} :
    pt₁ = pt₂ ↔ pt₁.index = pt₂.index ∧
      (Quotient.mk _) ⁻¹' {pt₁.groupElts} = (Quotient.mk _) ⁻¹' {pt₂.groupElts} := by
  refine ⟨fun h => ?_, fun ⟨hi, hq⟩ => ?_⟩
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

/--
Definition of `coeSet` / `coeSet` 的定义

English:
definition coeSet
  signature: (pt : PlacedTile ps)
  body: Quotient.liftOn' pt.groupElts (fun g => g • (ps pt.index : Set X))
    fun a b r => by
      rw [QuotientGroup.leftRel_eq] at r
      rw [eq_comm]; rw [← inv_smul_eq_iff]; rw [smul_smul]; rw [← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r

中文:
定义 coeSet
  签名: (pt : PlacedTile ps)
  定义体: Quotient.liftOn' pt.groupElts (fun g => g • (ps pt.index : Set X))
    fun a b r => by
      rw [QuotientGroup.leftRel_eq] at r
      rw [eq_comm]; rw [← inv_smul_eq_iff]; rw [smul_smul]; rw [← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r
-/
@[coe] def coeSet (pt : PlacedTile ps) : Set X :=
  Quotient.liftOn' pt.groupElts (fun g => g • (ps pt.index : Set X))
    fun a b r => by
      rw [QuotientGroup.leftRel_eq] at r
      rw [eq_comm]; rw [← inv_smul_eq_iff]; rw [smul_smul]; rw [← MulAction.mem_stabilizer_iff]
      exact SetLike.le_def.1 (Subgroup.map_subtype_le _) r

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (PlacedTile ps) (Set X)
  body: coeSet

中文:
实例 :
  签名: CoeOut (PlacedTile ps) (集合 X)
  定义体: coeSet

Depends on / 依赖: coeSet
-/
instance : CoeOut (PlacedTile ps) (Set X) where
  coe := coeSet

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Membership X (PlacedTile ps)
  body: x in (p : Set X)

中文:
实例 :
  签名: Membership X (PlacedTile ps)
  定义体: x in (p : Set X)
-/
instance : Membership X (PlacedTile ps) where
  mem p x := x in (p : Set X)

/--
lemma `mem_coe` / 引理 `mem_coe`

English:
lemma mem_coe
  given: {x : X} {pt : PlacedTile ps}
  statement: x in (pt : Set X) ↔ x in pt
  proof: Iff.rfl

中文:
引理 mem_coe
  条件: {x : X} {pt : PlacedTile ps}
  结论: x in (pt : 集合 X) ↔ x in pt
  证明: Iff.rfl
-/
@[simp] lemma mem_coe {x : X} {pt : PlacedTile ps} : x in (pt : Set X) ↔ x in pt := Iff.rfl

/--
lemma `coe_mk_mk` / 引理 `coe_mk_mk`

English:
lemma coe_mk_mk
  given: (i : ιₚ) (g : G)
  statement: (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : Set X)
  proof: rfl

中文:
引理 coe_mk_mk
  条件: (i : ιₚ) (g : G)
  结论: (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : 集合 X)
  证明: rfl
-/
lemma coe_mk_mk (i : ιₚ) (g : G) : (⟨i, ⟦g⟧⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl

/--
lemma `coe_mk_coe` / 引理 `coe_mk_coe`

English:
lemma coe_mk_coe
  given: (i : ιₚ) (g : G)
  statement: (⟨i, g⟩ : PlacedTile ps) = g • (ps i : Set X)
  proof: rfl

中文:
引理 coe_mk_coe
  条件: (i : ιₚ) (g : G)
  结论: (⟨i, g⟩ : PlacedTile ps) = g • (ps i : 集合 X)
  证明: rfl
-/
lemma coe_mk_coe (i : ιₚ) (g : G) : (⟨i, g⟩ : PlacedTile ps) = g • (ps i : Set X) := rfl

/--
lemma `coe_nonempty_iff` / 引理 `coe_nonempty_iff`

English:
lemma coe_nonempty_iff
  given: {pt : PlacedTile ps}
  proof: by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq']; rw [Quotient.liftOn'_mk'']
  simp

中文:
引理 coe_nonempty_iff
  条件: {pt : PlacedTile ps}
  证明: by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq']; rw [Quotient.liftOn'_mk'']
  simp

Depends on / 依赖: Quotient, Quotient.liftOn, coeSet, groupElts, groupElts.out_eq, liftOn, out_eq
-/
lemma coe_nonempty_iff {pt : PlacedTile ps} :
    (pt : Set X).Nonempty ↔ (ps pt.index : Set X).Nonempty := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq']; rw [Quotient.liftOn'_mk'']
  simp

/--
lemma `coe_mk_nonempty_iff` / 引理 `coe_mk_nonempty_iff`

English:
lemma coe_mk_nonempty_iff
  given: {i : ιₚ} (g)
  proof: coe_nonempty_iff

中文:
引理 coe_mk_nonempty_iff
  条件: {i : ιₚ} (g)
  证明: coe_nonempty_iff
-/
@[simp] lemma coe_mk_nonempty_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Nonempty ↔ (ps i : Set X).Nonempty :=
  coe_nonempty_iff

/--
lemma `coe_finite_iff` / 引理 `coe_finite_iff`

English:
lemma coe_finite_iff
  given: {pt : PlacedTile ps}
  proof: by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq']; rw [Quotient.liftOn'_mk'']
  simp

中文:
引理 coe_finite_iff
  条件: {pt : PlacedTile ps}
  证明: by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq']; rw [Quotient.liftOn'_mk'']
  simp

Depends on / 依赖: Quotient, Quotient.liftOn, coeSet, groupElts, groupElts.out_eq, liftOn, out_eq
-/
lemma coe_finite_iff {pt : PlacedTile ps} :
    (pt : Set X).Finite ↔ (ps pt.index : Set X).Finite := by
  rcases pt with ⟨index, groupElts⟩
  simp only [coeSet]
  rw [← groupElts.out_eq']; rw [Quotient.liftOn'_mk'']
  simp

/--
lemma `coe_mk_finite_iff` / 引理 `coe_mk_finite_iff`

English:
lemma coe_mk_finite_iff
  given: {i : ιₚ} (g)
  proof: coe_finite_iff

中文:
引理 coe_mk_finite_iff
  条件: {i : ιₚ} (g)
  证明: coe_finite_iff
-/
@[simp] lemma coe_mk_finite_iff {i : ιₚ} (g) :
    ((⟨i, g⟩ : PlacedTile ps) : Set X).Finite ↔ (ps i : Set X).Finite :=
  coe_finite_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul G (PlacedTile ps)
  body: Quotient.liftOn' pt.groupElts (fun h => ⟨pt.index, g * h⟩)
    fun a b r => by
      rw [QuotientGroup.leftRel_eq] at r
      refine PlacedTile.ext rfl ?_
      simpa [QuotientGroup.eq, ← mul_assoc] using r

中文:
实例 :
  签名: 标量乘法 G (PlacedTile ps)
  定义体: Quotient.liftOn' pt.groupElts (fun h => ⟨pt.index, g * h⟩)
    fun a b r => by
      rw [QuotientGroup.leftRel_eq] at r
      refine PlacedTile.ext rfl ?_
      simpa [QuotientGroup.eq, ← mul_assoc] using r

Depends on / 依赖: Quotient, Quotient.liftOn, groupElts, liftOn, pt.groupElts, pt.index
-/
instance : SMul G (PlacedTile ps) where
  smul g pt := Quotient.liftOn' pt.groupElts (fun h => ⟨pt.index, g * h⟩)
    fun a b r => by
      rw [QuotientGroup.leftRel_eq] at r
      refine PlacedTile.ext rfl ?_
      simpa [QuotientGroup.eq, ← mul_assoc] using r

/--
lemma `smul_mk_mk` / 引理 `smul_mk_mk`

English:
lemma smul_mk_mk
  given: (g h : G) (i : ιₚ)
  statement: g • (⟨i, ⟦h⟧⟩ : PlacedTile ps) = ⟨i, g * h⟩
  proof: rfl

中文:
引理 smul_mk_mk
  条件: (g h : G) (i : ιₚ)
  结论: g • (⟨i, ⟦h⟧⟩ : PlacedTile ps) = ⟨i, g * h⟩
  证明: rfl
-/
@[simp] lemma smul_mk_mk (g h : G) (i : ιₚ) : g • (⟨i, ⟦h⟧⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl

/--
lemma `smul_mk_coe` / 引理 `smul_mk_coe`

English:
lemma smul_mk_coe
  given: (g h : G) (i : ιₚ)
  statement: g • (⟨i, h⟩ : PlacedTile ps) = ⟨i, g * h⟩
  proof: rfl

中文:
引理 smul_mk_coe
  条件: (g h : G) (i : ιₚ)
  结论: g • (⟨i, h⟩ : PlacedTile ps) = ⟨i, g * h⟩
  证明: rfl
-/
@[simp] lemma smul_mk_coe (g h : G) (i : ιₚ) : g • (⟨i, h⟩ : PlacedTile ps) = ⟨i, g * h⟩ := rfl

/--
lemma `smul_index` / 引理 `smul_index`

English:
lemma smul_index
  given: (g : G) (pt : PlacedTile ps)
  statement: (g • pt).index = pt.index
  proof: by
  induction pt using PlacedTile.induction_on
  rfl

中文:
引理 smul_index
  条件: (g : G) (pt : PlacedTile ps)
  结论: (g • pt).index = pt.index
  证明: by
  induction pt using PlacedTile.induction_on
  rfl
-/
@[simp] lemma smul_index (g : G) (pt : PlacedTile ps) : (g • pt).index = pt.index := by
  induction pt using PlacedTile.induction_on
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coe_smul` / 引理 `coe_smul`

English:
lemma coe_smul
  given: (g : G) (pt : PlacedTile ps)
  proof: by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]

中文:
引理 coe_smul
  条件: (g : G) (pt : PlacedTile ps)
  证明: by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]
-/
@[simp] lemma coe_smul (g : G) (pt : PlacedTile ps) :
    (g • pt : PlacedTile ps) = g • (pt : Set X) := by
  induction pt using PlacedTile.induction_on
  simp [coeSet, mul_smul]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulAction G (PlacedTile ps)
  body: inferInstance
  one_smul pt := by
    induction pt using PlacedTile.induction_on
    simp
  mul_smul x y pt := by
    induction pt using PlacedTile.induction_on
    simp [mul_assoc]

中文:
实例 :
  签名: 乘法作用 G (PlacedTile ps)
  定义体: inferInstance
  one_smul pt := by
    induction pt using PlacedTile.induction_on
    simp
  mul_smul x y pt := by
    induction pt using PlacedTile.induction_on
    simp [mul_assoc]
-/
instance : MulAction G (PlacedTile ps) where
  __ : SMul G (PlacedTile ps) := inferInstance
  one_smul pt := by
    induction pt using PlacedTile.induction_on
    simp
  mul_smul x y pt := by
    induction pt using PlacedTile.induction_on
    simp [mul_assoc]

/--
lemma `smul_mem_smul_iff` / 引理 `smul_mem_smul_iff`

English:
lemma smul_mem_smul_iff
  given: (g : G) {x : X} {pt : PlacedTile ps}
  statement: g • x in g • pt ↔ x in pt
  proof: by
  rw [← mem_coe]; rw [coe_smul]; rw [Set.smul_mem_smul_set_iff]; rw [mem_coe]

中文:
引理 smul_mem_smul_iff
  条件: (g : G) {x : X} {pt : PlacedTile ps}
  结论: g • x in g • pt ↔ x in pt
  证明: by
  rw [← mem_coe]; rw [coe_smul]; rw [Set.smul_mem_smul_set_iff]; rw [mem_coe]
-/
@[simp] lemma smul_mem_smul_iff (g : G) {x : X} {pt : PlacedTile ps} : g • x in g • pt ↔ x in pt := by
  rw [← mem_coe]; rw [coe_smul]; rw [Set.smul_mem_smul_set_iff]; rw [mem_coe]

/--
lemma `mem_smul_iff_smul_inv_mem` / 引理 `mem_smul_iff_smul_inv_mem`

English:
lemma mem_smul_iff_smul_inv_mem
  given: {g : G} {x : X} {pt : PlacedTile ps}
  proof: by
  simp_rw [← mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]

中文:
引理 mem_smul_iff_smul_inv_mem
  条件: {g : G} {x : X} {pt : PlacedTile ps}
  证明: by
  simp_rw [← mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]

Depends on / 依赖: Set.mem_smul_set_iff_inv_smul_mem, coe_smul, mem_coe, mem_smul_set_iff_inv_smul_mem, simp_rw
-/
lemma mem_smul_iff_smul_inv_mem {g : G} {x : X} {pt : PlacedTile ps} :
    x in g • pt ↔ g⁻¹ • x in pt := by
  simp_rw [← mem_coe, coe_smul, Set.mem_smul_set_iff_inv_smul_mem]

/--
lemma `mem_inv_smul_iff_smul_mem` / 引理 `mem_inv_smul_iff_smul_mem`

English:
lemma mem_inv_smul_iff_smul_mem
  given: {g : G} {x : X} {pt : PlacedTile ps}
  proof: by
  simp_rw [← mem_coe, coe_smul, Set.mem_inv_smul_set_iff]

中文:
引理 mem_inv_smul_iff_smul_mem
  条件: {g : G} {x : X} {pt : PlacedTile ps}
  证明: by
  simp_rw [← mem_coe, coe_smul, Set.mem_inv_smul_set_iff]

Depends on / 依赖: Set.mem_inv_smul_set_iff, coe_smul, mem_coe, mem_inv_smul_set_iff, simp_rw
-/
lemma mem_inv_smul_iff_smul_mem {g : G} {x : X} {pt : PlacedTile ps} :
    x in g⁻¹ • pt ↔ g • x in pt := by
  simp_rw [← mem_coe, coe_smul, Set.mem_inv_smul_set_iff]

end PlacedTile

end DiscreteTiling
