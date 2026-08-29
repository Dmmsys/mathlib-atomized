/-
Copyright (c) 2022 Michael Blyth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Blyth
-/
module

public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Subspaces of Projective Space

In this file we define subspaces of a projective space, and show that the subspaces of a projective
space form a complete lattice under inclusion.

## Implementation Details

A subspace of a projective space ℙ K V is defined to be a structure consisting of a subset of
ℙ K V such that if two nonzero vectors in V determine points in ℙ K V which are in the subset, and
the sum of the two vectors is nonzero, then the point determined by the sum of the two vectors is
also in the subset.

## Results

- There is a Galois insertion between the subsets of points of a projective space
  and the subspaces of the projective space, which is given by taking the span of the set of points.
- The subspaces of a projective space form a complete lattice under inclusion.
- There is a one-to-one order-preserving correspondence between subspaces of a
  projective space and the submodules of the underlying vector space.
-/

@[expose] public section


variable (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]

namespace Projectivization

open scoped LinearAlgebra.Projectivization

/-- A subspace of a projective space is a structure consisting of a set of points such that:
If two nonzero vectors determine points which are in the set, and the sum of the two vectors is
nonzero, then the point determined by the sum is also in the set. -/
@[ext]
/--
Definition of `Subspace` / `Subspace` 的定义

English:
structure Subspace
  parameters: where
  axioms and operations (2):
    - carrier : Set (ℙ K V)
    - mem_add'((v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0)) : mk K v hv in carrier -> mk K w hw in carrier -> mk K (v + w) hvw in carrier

中文:
结构 Subspace
  参数: where
  公理与运算 (2 个):
    - carrier : Set (ℙ K V)
    - mem_add'((v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0)) : mk K v hv in carrier -> mk K w hw in carrier -> mk K (v + w) hvw in carrier
-/
structure Subspace where
  /-- The set of points. -/
  carrier : Set (ℙ K V)
  /-- The addition rule. -/
  mem_add' (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0) :
    mk K v hv in carrier -> mk K w hw in carrier -> mk K (v + w) hvw in carrier

namespace Subspace

variable {K V}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (Subspace K V) (ℙ K V)
  body: carrier
  coe_injective A B := by
    cases A
    cases B
    simp

中文:
实例 :
  签名: SetLike (Subspace K V) (ℙ K V)
  定义体: carrier
  coe_injective A B := by
    cases A
    cases B
    simp

Depends on / 依赖: carrier
-/
instance : SetLike (Subspace K V) (ℙ K V) where
  coe := carrier
  coe_injective A B := by
    cases A
    cases B
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Subspace K V)
  body: .ofSetLike (Subspace K V) (ℙ K V)

@[simp]

中文:
实例 :
  签名: PartialOrder (Subspace K V)
  定义体: .ofSetLike (Subspace K V) (ℙ K V)

@[simp]

Depends on / 依赖: Subspace, ofSetLike
-/
instance : PartialOrder (Subspace K V) := .ofSetLike (Subspace K V) (ℙ K V)

@[simp]
/--
theorem `mem_carrier_iff` / 定理 `mem_carrier_iff`

English:
theorem mem_carrier_iff
  given: (A : Subspace K V) (x : ℙ K V)
  statement: x in A.carrier ↔ x in A
  proof: Iff.refl _

中文:
定理 mem_carrier_iff
  条件: (A : Subspace K V) (x : ℙ K V)
  结论: x in A.carrier ↔ x in A
  证明: Iff.refl _

Depends on / 依赖: Iff.refl
-/
theorem mem_carrier_iff (A : Subspace K V) (x : ℙ K V) : x in A.carrier ↔ x in A :=
  Iff.refl _

/--
theorem `mem_add` / 定理 `mem_add`

English:
theorem mem_add
  given: (T : Subspace K V) (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0)
  proof: T.mem_add' v w hv hw hvw

中文:
定理 mem_add
  条件: (T : Subspace K V) (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0)
  证明: T.mem_add' v w hv hw hvw

Depends on / 依赖: T.mem_add, mem_add
-/
theorem mem_add (T : Subspace K V) (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0) :
    Projectivization.mk K v hv in T ->
      Projectivization.mk K w hw in T -> Projectivization.mk K (v + w) hvw in T :=
  T.mem_add' v w hv hw hvw

/--
Inductive type `spanCarrier` / 归纳类型 `spanCarrier`

English:
inductive spanCarrier
  parameters: (S : Set (ℙ K V))
  constructors (2):
    - of: (x : ℙ K V) (hx : x in S) : spanCarrier S x
    - mem_add: (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0) : spanCarrier S (Projectivization.mk K v hv) -> spanCarrier S (Projectivization.mk K w hw) -> spanCarrier S (Projectivization.mk K (v + w) hvw)

中文:
归纳类型 spanCarrier
  参数: (S : Set (ℙ K V))
  构造子 (2 个):
    - of: (x : ℙ K V) (hx : x in S) : spanCarrier S x
    - mem_add: (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0) : spanCarrier S (Projectivization.mk K v hv) -> spanCarrier S (Projectivization.mk K w hw) -> spanCarrier S (Projectivization.mk K (v + w) hvw)
-/
inductive spanCarrier (S : Set (ℙ K V)) : Set (ℙ K V)
  | of (x : ℙ K V) (hx : x in S) : spanCarrier S x
  | mem_add (v w : V) (hv : v != 0) (hw : w != 0) (hvw : v + w != 0) :
      spanCarrier S (Projectivization.mk K v hv) ->
      spanCarrier S (Projectivization.mk K w hw) -> spanCarrier S (Projectivization.mk K (v + w) hvw)

/--
Definition of `span` / `span` 的定义

English:
definition span
  signature: (S : Set (ℙ K V))
  body: spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw

中文:
定义 span
  签名: (S : Set (ℙ K V))
  定义体: spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw

Depends on / 依赖: spanCarrier
-/
def span (S : Set (ℙ K V)) : Subspace K V where
  carrier := spanCarrier S
  mem_add' v w hv hw hvw := spanCarrier.mem_add v w hv hw hvw

/--
theorem `subset_span` / 定理 `subset_span`

English:
theorem subset_span
  given: (S : Set (ℙ K V))
  statement: S subseteq span S
  proof: fun _x hx => spanCarrier.of _ hx

中文:
定理 subset_span
  条件: (S : Set (ℙ K V))
  结论: S subseteq span S
  证明: fun _x hx => spanCarrier.of _ hx

Depends on / 依赖: spanCarrier, spanCarrier.of
-/
theorem subset_span (S : Set (ℙ K V)) : S subseteq span S := fun _x hx => spanCarrier.of _ hx

/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (span : Set (ℙ K V) -> Subspace K V) SetLike.coe where
  body: span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx with
      | of => apply h; assumption
      | mem_add => apply B.mem_add; assumption'⟩
  le_l_u _ := subset_span _
  choice_eq _ _ := rfl

中文:
定义 gi
  签名: : GaloisInsertion (span : Set (ℙ K V) -> Subspace K V) SetLike.coe where
  定义体: span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx with
      | of => apply h; assumption
      | mem_add => apply B.mem_add; assumption'⟩
  le_l_u _ := subset_span _
  choice_eq _ _ := rfl
-/
def gi : GaloisInsertion (span : Set (ℙ K V) -> Subspace K V) SetLike.coe where
  choice S _hS := span S
  gc A B :=
    ⟨fun h => le_trans (subset_span _) h, by
      intro h x hx
      induction hx with
      | of => apply h; assumption
      | mem_add => apply B.mem_add; assumption'⟩
  le_l_u _ := subset_span _
  choice_eq _ _ := rfl

/-- The span of a subspace is the subspace. -/
@[simp]
/--
theorem `span_coe` / 定理 `span_coe`

English:
theorem span_coe
  given: (W : Subspace K V)
  statement: span ↑W = W
  proof: GaloisInsertion.l_u_eq gi W

中文:
定理 span_coe
  条件: (W : Subspace K V)
  结论: span ↑W = W
  证明: GaloisInsertion.l_u_eq gi W

Depends on / 依赖: GaloisInsertion, GaloisInsertion.l_u_eq, l_u_eq
-/
theorem span_coe (W : Subspace K V) : span ↑W = W :=
  GaloisInsertion.l_u_eq gi W

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (Subspace K V)
  body: ⟨fun A B =>
    ⟨A ⊓ B, fun _v _w hv hw _hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

中文:
实例 instInf
  签名: : Min (Subspace K V)
  定义体: ⟨fun A B =>
    ⟨A ⊓ B, fun _v _w hv hw _hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

Depends on / 依赖: A.mem_add, B.mem_add, _hvw, mem_add
-/
instance instInf : Min (Subspace K V) :=
  ⟨fun A B =>
    ⟨A ⊓ B, fun _v _w hv hw _hvw h1 h2 =>
      ⟨A.mem_add _ _ hv hw _ h1.1 h2.1, B.mem_add _ _ hv hw _ h1.2 h2.2⟩⟩⟩

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet (Subspace K V)
  body: ⟨fun A =>
    ⟨sInf (SetLike.coe '' A), fun v w hv hw hvw h1 h2 t => by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩

中文:
实例 instInfSet
  签名: : InfSet (Subspace K V)
  定义体: ⟨fun A =>
    ⟨sInf (SetLike.coe '' A), fun v w hv hw hvw h1 h2 t => by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩

Depends on / 依赖: SetLike, SetLike.coe, mem_add, s.mem_add
-/
instance instInfSet : InfSet (Subspace K V) :=
  ⟨fun A =>
    ⟨sInf (SetLike.coe '' A), fun v w hv hw hvw h1 h2 t => by
      rintro ⟨s, hs, rfl⟩
      exact s.mem_add v w hv hw _ (h1 s ⟨s, hs, rfl⟩) (h2 s ⟨s, hs, rfl⟩)⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Subspace K V)
  body: { __ := completeLatticeOfInf (Subspace K V)
      (by
        refine fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => ?_⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx)
    inf_le_left := fun A B _ hx => (@inf_le_left _ _ A B) hx
    inf_le_right := fun A B _ hx => (@inf_le_righ

中文:
实例 :
  签名: CompleteLattice (Subspace K V)
  定义体: { __ := completeLatticeOfInf (Subspace K V)
      (by
        refine fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => ?_⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx)
    inf_le_left := fun A B _ hx => (@inf_le_left _ _ A B) hx
    inf_le_right := fun A B _ hx => (@inf_le_righ

Depends on / 依赖: Subspace, completeLatticeOfInf, inf_le_left, inf_le_right, le_inf
-/
instance : CompleteLattice (Subspace K V) :=
  { __ := completeLatticeOfInf (Subspace K V)
      (by
        refine fun s => ⟨fun a ha x hx => hx _ ⟨a, ha, rfl⟩, fun a ha x hx E => ?_⟩
        rintro ⟨E, hE, rfl⟩
        exact ha hE hx)
    inf_le_left := fun A B _ hx => (@inf_le_left _ _ A B) hx
    inf_le_right := fun A B _ hx => (@inf_le_right _ _ A B) hx
    le_inf := fun _ _ _ h1 h2 _ hx => (le_inf h1 h2) hx }

/--
Instance `subspaceInhabited` / 实例 `subspaceInhabited`

English:
instance subspaceInhabited
  signature: : Inhabited (Subspace K V) where default
  body: ⊤

中文:
实例 subspaceInhabited
  签名: : Inhabited (Subspace K V) where default
  定义体: ⊤
-/
instance subspaceInhabited : Inhabited (Subspace K V) where default := ⊤

/-- The span of the empty set is the bottom of the lattice of subspaces. -/
@[simp]
/--
theorem `span_empty` / 定理 `span_empty`

English:
theorem span_empty
  statement: span (∅ : Set (ℙ K V)) = ⊥
  proof: gi.gc.l_bot

中文:
定理 span_empty
  结论: span (∅ : Set (ℙ K V)) = ⊥
  证明: gi.gc.l_bot

Depends on / 依赖: gi.gc.l_bot, l_bot
-/
theorem span_empty : span (∅ : Set (ℙ K V)) = ⊥ := gi.gc.l_bot

/-- The span of the entire projective space is the top of the lattice of subspaces. -/
@[simp]
/--
theorem `span_univ` / 定理 `span_univ`

English:
theorem span_univ
  statement: span (Set.univ : Set (ℙ K V)) = ⊤
  proof: by
  rw [eq_top_iff]; rw [SetLike.le_def]
  intro x _hx
  exact subset_span _ (Set.mem_univ x)

中文:
定理 span_univ
  结论: span (Set.univ : Set (ℙ K V)) = ⊤
  证明: by
  rw [eq_top_iff]; rw [SetLike.le_def]
  intro x _hx
  exact subset_span _ (Set.mem_univ x)

Depends on / 依赖: Set.mem_univ, SetLike, SetLike.le_def, eq_top_iff, le_def, mem_univ, subset_span
-/
theorem span_univ : span (Set.univ : Set (ℙ K V)) = ⊤ := by
  rw [eq_top_iff]; rw [SetLike.le_def]
  intro x _hx
  exact subset_span _ (Set.mem_univ x)

/--
theorem `span_le_subspace_iff` / 定理 `span_le_subspace_iff`

English:
theorem span_le_subspace_iff
  given: {S : Set (ℙ K V)} {W : Subspace K V}
  statement: span S <= W ↔ S subseteq W
  proof: gi.gc S W

中文:
定理 span_le_subspace_iff
  条件: {S : Set (ℙ K V)} {W : Subspace K V}
  结论: span S <= W ↔ S subseteq W
  证明: gi.gc S W

Depends on / 依赖: gi.gc
-/
theorem span_le_subspace_iff {S : Set (ℙ K V)} {W : Subspace K V} : span S <= W ↔ S subseteq W :=
  gi.gc S W

/-- If a set of points is a subset of another set of points, then its span will be contained in the
span of that set. -/
@[gcongr, mono]
/--
theorem `monotone_span` / 定理 `monotone_span`

English:
theorem monotone_span
  statement: Monotone (span : Set (ℙ K V) -> Subspace K V)
  proof: gi.gc.monotone_l

@[gcongr]

中文:
定理 monotone_span
  结论: Monotone (span : Set (ℙ K V) -> Subspace K V)
  证明: gi.gc.monotone_l

@[gcongr]

Depends on / 依赖: gi.gc.monotone_l, monotone_l
-/
theorem monotone_span : Monotone (span : Set (ℙ K V) -> Subspace K V) :=
  gi.gc.monotone_l

@[gcongr]
/--
lemma `span_le_span` / 引理 `span_le_span`

English:
lemma span_le_span
  given: {s t : Set (ℙ K V)} (hst : s subseteq t)
  statement: span s <= span t
  proof: monotone_span hst

中文:
引理 span_le_span
  条件: {s t : Set (ℙ K V)} (hst : s subseteq t)
  结论: span s <= span t
  证明: monotone_span hst

Depends on / 依赖: monotone_span
-/
lemma span_le_span {s t : Set (ℙ K V)} (hst : s subseteq t) : span s <= span t := monotone_span hst

/--
theorem `subset_span_trans` / 定理 `subset_span_trans`

English:
theorem subset_span_trans
  given: {S T U : Set (ℙ K V)} (hST : S subseteq span T) (hTU : T subseteq span U)
  proof: gi.gc.le_u_l_trans hST hTU

中文:
定理 subset_span_trans
  条件: {S T U : Set (ℙ K V)} (hST : S subseteq span T) (hTU : T subseteq span U)
  证明: gi.gc.le_u_l_trans hST hTU

Depends on / 依赖: gi.gc.le_u_l_trans, le_u_l_trans
-/
theorem subset_span_trans {S T U : Set (ℙ K V)} (hST : S subseteq span T) (hTU : T subseteq span U) :
    S subseteq span U :=
  gi.gc.le_u_l_trans hST hTU

/--
theorem `span_union` / 定理 `span_union`

English:
theorem span_union
  given: (S T : Set (ℙ K V))
  statement: span (S union T) = span S ⊔ span T
  proof: (@gi K V _ _ _).gc.l_sup

中文:
定理 span_union
  条件: (S T : Set (ℙ K V))
  结论: span (S union T) = span S ⊔ span T
  证明: (@gi K V _ _ _).gc.l_sup

Depends on / 依赖: gc.l_sup, l_sup
-/
theorem span_union (S T : Set (ℙ K V)) : span (S union T) = span S ⊔ span T :=
  (@gi K V _ _ _).gc.l_sup

/--
theorem `span_iUnion` / 定理 `span_iUnion`

English:
theorem span_iUnion
  given: {ι} (s : ι -> Set (ℙ K V))
  statement: span (⋃ i, s i) = ⨆ i, span (s i)
  proof: (@gi K V _ _ _).gc.l_iSup

中文:
定理 span_iUnion
  条件: {ι} (s : ι -> Set (ℙ K V))
  结论: span (⋃ i, s i) = ⨆ i, span (s i)
  证明: (@gi K V _ _ _).gc.l_iSup

Depends on / 依赖: gc.l_iSup, l_iSup
-/
theorem span_iUnion {ι} (s : ι -> Set (ℙ K V)) : span (⋃ i, s i) = ⨆ i, span (s i) :=
  (@gi K V _ _ _).gc.l_iSup

/--
theorem `sup_span` / 定理 `sup_span`

English:
theorem sup_span
  given: {S : Set (ℙ K V)} {W : Subspace K V}
  statement: W ⊔ span S = span (W union S)
  proof: by
  rw [span_union]; rw [span_coe]

中文:
定理 sup_span
  条件: {S : Set (ℙ K V)} {W : Subspace K V}
  结论: W ⊔ span S = span (W union S)
  证明: by
  rw [span_union]; rw [span_coe]

Depends on / 依赖: span_coe, span_union
-/
theorem sup_span {S : Set (ℙ K V)} {W : Subspace K V} : W ⊔ span S = span (W union S) := by
  rw [span_union]; rw [span_coe]

/--
theorem `span_sup` / 定理 `span_sup`

English:
theorem span_sup
  given: {S : Set (ℙ K V)} {W : Subspace K V}
  statement: span S ⊔ W = span (S union W)
  proof: by
  rw [span_union]; rw [span_coe]

中文:
定理 span_sup
  条件: {S : Set (ℙ K V)} {W : Subspace K V}
  结论: span S ⊔ W = span (S union W)
  证明: by
  rw [span_union]; rw [span_coe]

Depends on / 依赖: span_coe, span_union
-/
theorem span_sup {S : Set (ℙ K V)} {W : Subspace K V} : span S ⊔ W = span (S union W) := by
  rw [span_union]; rw [span_coe]

/--
theorem `mem_span` / 定理 `mem_span`

English:
theorem mem_span
  given: {S : Set (ℙ K V)} (u : ℙ K V)
  proof: by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩

中文:
定理 mem_span
  条件: {S : Set (ℙ K V)} (u : ℙ K V)
  证明: by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩

Depends on / 依赖: le_refl, simp_rw, span_le_subspace_iff
-/
theorem mem_span {S : Set (ℙ K V)} (u : ℙ K V) :
    u in span S ↔ forall W : Subspace K V, S subseteq W -> u in W := by
  simp_rw [← span_le_subspace_iff]
  exact ⟨fun hu W hW => hW hu, fun W => W (span S) (le_refl _)⟩

/--
theorem `span_eq_sInf` / 定理 `span_eq_sInf`

English:
theorem span_eq_sInf
  given: {S : Set (ℙ K V)}
  statement: span S = sInf { W : Subspace K V| S subseteq W }
  proof: by
  ext x
  simp_rw [mem_carrier_iff, mem_span x]
  refine ⟨fun hx => ?_, fun hx W hW => ?_⟩
  · rintro W ⟨T, hT, rfl⟩
    exact hx T hT
  · exact (@sInf_le _ _ { W : Subspace K V | S subseteq ↑W } W hW) hx

中文:
定理 span_eq_sInf
  条件: {S : Set (ℙ K V)}
  结论: span S = sInf { W : Subspace K V| S subseteq W }
  证明: by
  ext x
  simp_rw [mem_carrier_iff, mem_span x]
  refine ⟨fun hx => ?_, fun hx W hW => ?_⟩
  · rintro W ⟨T, hT, rfl⟩
    exact hx T hT
  · exact (@sInf_le _ _ { W : Subspace K V | S subseteq ↑W } W hW) hx

Depends on / 依赖: Subspace, mem_carrier_iff, mem_span, sInf_le, simp_rw, subseteq
-/
theorem span_eq_sInf {S : Set (ℙ K V)} : span S = sInf { W : Subspace K V| S subseteq W } := by
  ext x
  simp_rw [mem_carrier_iff, mem_span x]
  refine ⟨fun hx => ?_, fun hx W hW => ?_⟩
  · rintro W ⟨T, hT, rfl⟩
    exact hx T hT
  · exact (@sInf_le _ _ { W : Subspace K V | S subseteq ↑W } W hW) hx

/--
theorem `span_eq_of_le` / 定理 `span_eq_of_le`

English:
theorem span_eq_of_le
  given: {S : Set (ℙ K V)} {W : Subspace K V} (hS : S subseteq W) (hW : W <= span S)
  proof: le_antisymm (span_le_subspace_iff.mpr hS) hW

中文:
定理 span_eq_of_le
  条件: {S : Set (ℙ K V)} {W : Subspace K V} (hS : S subseteq W) (hW : W <= span S)
  证明: le_antisymm (span_le_subspace_iff.mpr hS) hW

Depends on / 依赖: le_antisymm, span_le_subspace_iff, span_le_subspace_iff.mpr
-/
theorem span_eq_of_le {S : Set (ℙ K V)} {W : Subspace K V} (hS : S subseteq W) (hW : W <= span S) :
    span S = W :=
  le_antisymm (span_le_subspace_iff.mpr hS) hW

/--
theorem `span_eq_span_iff` / 定理 `span_eq_span_iff`

English:
theorem span_eq_span_iff
  given: {S T : Set (ℙ K V)}
  statement: span S = span T ↔ S subseteq span T ∧ T subseteq span S
  proof: ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

中文:
定理 span_eq_span_iff
  条件: {S T : Set (ℙ K V)}
  结论: span S = span T ↔ S subseteq span T ∧ T subseteq span S
  证明: ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

Depends on / 依赖: h.symm, le_antisymm, span_le_subspace_iff, subset_span
-/
theorem span_eq_span_iff {S T : Set (ℙ K V)} : span S = span T ↔ S subseteq span T ∧ T subseteq span S :=
  ⟨fun h => ⟨h ▸ subset_span S, h.symm ▸ subset_span T⟩, fun h =>
    le_antisymm (span_le_subspace_iff.2 h.1) (span_le_subspace_iff.2 h.2)⟩

/--
Definition of `submodule` / `submodule` 的定义

English:
definition submodule
  signature: : Projectivization.Subspace K V ≃o Submodule K V where
  body: { carrier := {x | (h : x != 0) -> Projectivization.mk K x h in s.carrier}
    add_mem' {x y} hx₁ hy₁ := by
      rcases eq_or_ne x 0 with rfl | hx₂
      · rwa [zero_add]
      rcases eq_or_ne y 0 with rfl | hy₂
      · rwa [add_zero]
      intro hxy
      exact s.mem_add _ _ hx₂ hy₂ hxy (hx₁ hx₂) (

中文:
定义 submodule
  签名: : Projectivization.Subspace K V ≃o Submodule K V where
  定义体: { carrier := {x | (h : x != 0) -> Projectivization.mk K x h in s.carrier}
    add_mem' {x y} hx₁ hy₁ := by
      rcases eq_or_ne x 0 with rfl | hx₂
      · rwa [zero_add]
      rcases eq_or_ne y 0 with rfl | hy₂
      · rwa [add_zero]
      intro hxy
      exact s.mem_add _ _ hx₂ hy₂ hxy (hx₁ hx₂) (

Depends on / 依赖: Projectivization, Projectivization.lift, Projectivization.mk, Projectivization.mk_eq_mk_iff, Set.ofPred, add_mem, add_zero, carrier, convert, eq_or_ne, h.irrefl.elim, invFun, irrefl, mem_add, mk_eq_mk_iff, ofPred, right_ne_zero_of_smul, s.carrier, s.mem_add, smul_mem
-/
def submodule : Projectivization.Subspace K V ≃o Submodule K V where
  toFun s :=
  { carrier := {x | (h : x != 0) -> Projectivization.mk K x h in s.carrier}
    add_mem' {x y} hx₁ hy₁ := by
      rcases eq_or_ne x 0 with rfl | hx₂
      · rwa [zero_add]
      rcases eq_or_ne y 0 with rfl | hy₂
      · rwa [add_zero]
      intro hxy
      exact s.mem_add _ _ hx₂ hy₂ hxy (hx₁ hx₂) (hy₁ hy₂)
    zero_mem' h := h.irrefl.elim
    smul_mem' c x h₁ h₂ := by
      convert! h₁ (right_ne_zero_of_smul h₂) using 1
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨c, rfl⟩ }
  invFun s :=
  { carrier := Set.ofPred <| Projectivization.lift (↑· in s) <| by
      rintro ⟨-, h⟩ ⟨y, -⟩ c rfl
exact Iff.eq s.smul_mem_iff left_ne_zero_of_smul h
    mem_add' _ _ _ _ _ h₁ h₂ := s.add_mem h₁ h₂ }
  left_inv s := by
    ext ⟨x, hx⟩
    exact ⟨fun h => h hx, fun h _ => h⟩
  right_inv s := by
    ext x
    suffices x = 0 -> x in s by
      simpa [imp_iff_not_or]
    rintro rfl
    exact s.zero_mem
  map_rel_iff'.mp h₁ := Projectivization.ind fun _ hx h₂ => h₁ (fun _ => h₂) hx
map_rel_iff'.mpr h₁ _ h₂ hx := h₁ h₂ hx

@[simp]
/--
theorem `mem_submodule_iff` / 定理 `mem_submodule_iff`

English:
theorem mem_submodule_iff
  given: (s : Projectivization.Subspace K V) {v : V} (hv : v != 0)
  proof: ⟨fun h => h hv, fun h _ => h⟩

@[simp]

中文:
定理 mem_submodule_iff
  条件: (s : Projectivization.Subspace K V) {v : V} (hv : v != 0)
  证明: ⟨fun h => h hv, fun h _ => h⟩

@[simp]
-/
theorem mem_submodule_iff (s : Projectivization.Subspace K V) {v : V} (hv : v != 0) :
    v in submodule s ↔ Projectivization.mk K v hv in s :=
  ⟨fun h => h hv, fun h _ => h⟩

@[simp]
/--
lemma `bot_coe` / 引理 `bot_coe`

English:
lemma bot_coe
  statement: ((⊥ : Subspace K V) : Set (Projectivization K V)) = ∅
  proof: by
  ext x
  simp only [SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
  induction x using ind with | h v hv =>
  rwa [← Subspace.mem_submodule_iff _ hv, Subspace.submodule.map_bot, Submodule.mem_bot]

中文:
引理 bot_coe
  结论: ((⊥ : Subspace K V) : Set (Projectivization K V)) = ∅
  证明: by
  ext x
  simp only [SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
  induction x using ind with | h v hv =>
  rwa [← Subspace.mem_submodule_iff _ hv, Subspace.submodule.map_bot, Submodule.mem_bot]

Depends on / 依赖: Set.mem_empty_iff_false, SetLike, SetLike.mem_coe, Submodule, Submodule.mem_bot, Subspace, Subspace.mem_submodule_iff, Subspace.submodule.map_bot, iff_false, map_bot, mem_bot, mem_coe, mem_empty_iff_false, mem_submodule_iff, submodule
-/
lemma bot_coe : ((⊥ : Subspace K V) : Set (Projectivization K V)) = ∅ := by
  ext x
  simp only [SetLike.mem_coe, Set.mem_empty_iff_false, iff_false]
  induction x using ind with | h v hv =>
  rwa [← Subspace.mem_submodule_iff _ hv, Subspace.submodule.map_bot, Submodule.mem_bot]

end Subspace

end Projectivization

namespace Submodule

open scoped LinearAlgebra.Projectivization

variable {K V}

/--
Definition of `projectivization` / `projectivization` 的定义

English:
abbreviation projectivization
  signature: : Submodule K V ≃o Projectivization.Subspace K V
  body: Projectivization.Subspace.submodule.symm

@[simp]

中文:
缩写 projectivization
  签名: : Submodule K V ≃o Projectivization.Subspace K V
  定义体: Projectivization.Subspace.submodule.symm

@[simp]

Depends on / 依赖: Projectivization, Projectivization.Subspace.submodule.symm, Subspace, submodule
-/
abbrev projectivization : Submodule K V ≃o Projectivization.Subspace K V :=
  Projectivization.Subspace.submodule.symm

@[simp]
/--
theorem `mk_mem_projectivization_iff` / 定理 `mk_mem_projectivization_iff`

English:
theorem mk_mem_projectivization_iff
  given: (s : Submodule K V) {v : V} (hv : v != 0)
  proof: Iff.rfl

中文:
定理 mk_mem_projectivization_iff
  条件: (s : Submodule K V) {v : V} (hv : v != 0)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem mk_mem_projectivization_iff (s : Submodule K V) {v : V} (hv : v != 0) :
    Projectivization.mk K v hv in s.projectivization ↔ v in s := Iff.rfl

/--
theorem `mem_projectivization_iff_submodule_le` / 定理 `mem_projectivization_iff_submodule_le`

English:
theorem mem_projectivization_iff_submodule_le
  given: (s : Submodule K V) (x : ℙ K V)
  proof: by
  cases x
  rw [mk_mem_projectivization_iff]; rw [Projectivization.submodule_mk]; rw [Submodule.span_singleton_le_iff_mem]

中文:
定理 mem_projectivization_iff_submodule_le
  条件: (s : Submodule K V) (x : ℙ K V)
  证明: by
  cases x
  rw [mk_mem_projectivization_iff]; rw [Projectivization.submodule_mk]; rw [Submodule.span_singleton_le_iff_mem]

Depends on / 依赖: Projectivization, Projectivization.submodule_mk, Submodule, Submodule.span_singleton_le_iff_mem, mk_mem_projectivization_iff, span_singleton_le_iff_mem, submodule_mk
-/
theorem mem_projectivization_iff_submodule_le (s : Submodule K V) (x : ℙ K V) :
    x in s.projectivization ↔ x.submodule <= s := by
  cases x
  rw [mk_mem_projectivization_iff]; rw [Projectivization.submodule_mk]; rw [Submodule.span_singleton_le_iff_mem]

end Submodule
