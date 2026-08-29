/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Anatole Dedecker
-/
module

public import Mathlib.Analysis.Convex.Quasiconvex
public import Mathlib.Order.SaddlePoint
public import Mathlib.Topology.Instances.EReal.Lemmas

/-! # Formalization of Sion's version of the von Neumann minimax theorem

## Statements

`Sion.exists_isSaddlePointOn` :
Let `X` and `Y` be convex subsets of topological vector spaces `E` and `F`,
`X` being moreover compact,
and let `f : X × Y → ℝ` be a function such that
- for all `x ∈ X`, `f(x, ⬝)` is upper semicontinuous and quasiconcave
- for all `y ∈ Y`, `f(⬝, y)` is lower semicontinuous and quasiconvex
Then `⊓ x, ⊔ y, f (x, y) = ⊔ y, ⊓ x f (x, y)`.

The classical case of the theorem assumes that `f` is continuous,
`f(x, ⬝)` is concave, `f(⬝, y)` is convex.

As a particular case, one get the von Neumann theorem where
`f` is bilinear and `E`, `F` are finite dimensional.

We follow the proof of [Komiya (1988)][Komiya-1988].

## Remark on implementation

  * The essential part of the proof holds for a function
  `f : X → Y → β`, where `β` is a complete dense linear order.
  * We have written part of it for just a dense linear order,

  * On the other hand, if the theorem holds for such `β`,
  it must hold for any linear order, for the reason that
  any linear order embeds into a complete dense linear order.
  Although one can construct such an embedding using the Dedekind-Mac Neille completion,
  this result does not seem to be known to Mathlib.

  * When `β` is `ℝ`, one can use `Real.toEReal` and one gets a proof for `ℝ`.

## TODO

- Spell out the particular case of von Neumann theorem.

- Use the Dedekind MacNeille completion of a linear order to simplify
  the statement of `DMCompletion.exists_isSaddlePointOn`.

## References

- [Neumann, John von (1928).
  ”Zur Theorie der Gesellschaftsspiele”. *Mathematische Annalen* 100 (1): 295‑320][vonNeumann-1928]

- [Sion, Maurice (1958).
  ”On general minimax theorems”. *Pacific Journal of Mathematics* 8 (1): 171‑76.][Sion-1958]

- [Komiya, Hidetoshi (1988).
  “Elementary Proof for Sion’s Minimax Theorem”. *Kodai Mathematical Journal* 11 (1).][Komiya-1988]

-/

open Set Filter

namespace Sion

section LinearOrder

variable {E F : Type*} {β : Type*} [LinearOrder β]
    (X : Set E) (Y : Set F) (f : E -> F -> β)

/--
Definition of `sublevelLeft` / `sublevelLeft` 的定义

English:
definition sublevelLeft
  signature: (b : β) (z : F)
  body: (fun x => f x z) ∘ (fun x => ↑x) ⁻¹' Iic b

中文:
定义 sublevelLeft
  签名: (b : β) (z : F)
  定义体: (fun x => f x z) ∘ (fun x => ↑x) ⁻¹' Iic b
-/
def sublevelLeft (b : β) (z : F) : Set X :=
  (fun x => f x z) ∘ (fun x => ↑x) ⁻¹' Iic b

variable {X Y f}

/--
theorem `mem_sublevelLeft_iff` / 定理 `mem_sublevelLeft_iff`

English:
theorem mem_sublevelLeft_iff
  given: {b : β} {y : Y} {x : X}
  proof: by simp [sublevelLeft]

中文:
定理 mem_sublevelLeft_iff
  条件: {b : β} {y : Y} {x : X}
  证明: by simp [sublevelLeft]

Depends on / 依赖: sublevelLeft
-/
theorem mem_sublevelLeft_iff {b : β} {y : Y} {x : X} :
    x in sublevelLeft X f b y ↔ f x y <= b := by simp [sublevelLeft]

/--
theorem `monotone_sublevelLeft` / 定理 `monotone_sublevelLeft`

English:
theorem monotone_sublevelLeft
  given: {u v : β} (y : Y) (h : u <= v)
  proof: fun _ hxu => le_trans hxu h

中文:
定理 monotone_sublevelLeft
  条件: {u v : β} (y : Y) (h : u <= v)
  证明: fun _ hxu => le_trans hxu h

Depends on / 依赖: le_trans
-/
theorem monotone_sublevelLeft {u v : β} (y : Y) (h : u <= v) :
    sublevelLeft X f u y subseteq sublevelLeft X f v y :=
  fun _ hxu => le_trans hxu h

/--
theorem `disjoint_sublevelLeft` / 定理 `disjoint_sublevelLeft`

English:
theorem disjoint_sublevelLeft
  statement: {a : E} {b : β} {y y' : Y}
  proof: by
  rw [Set.disjoint_iff]
  rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
  apply hb.not_ge
  grw [ha x hx]
  simpa using ⟨hx1, hx2⟩

中文:
定理 disjoint_sublevelLeft
  结论: {a : E} {b : β} {y y' : Y}
  证明: by
  rw [Set.disjoint_iff]
  rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
  apply hb.not_ge
  grw [ha x hx]
  simpa using ⟨hx1, hx2⟩

Depends on / 依赖: Set.disjoint_iff, disjoint_iff, hb.not_ge, not_ge
-/
theorem disjoint_sublevelLeft {a : E} {b : β} {y y' : Y}
    (ha : forall x in X, f a y ⊔ f a y' <= f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y') :
    Disjoint (sublevelLeft X f b y) (sublevelLeft X f b y') := by
  rw [Set.disjoint_iff]
  rintro ⟨x, hx⟩ ⟨hx1, hx2⟩
  apply hb.not_ge
  grw [ha x hx]
  simpa using ⟨hx1, hx2⟩

/--
theorem `nonempty_sublevelLeft` / 定理 `nonempty_sublevelLeft`

English:
theorem nonempty_sublevelLeft
  statement: [TopologicalSpace E]
  proof: by
  rcases y with ⟨y, hy⟩
  obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy y hy)
  obtain ⟨x', hx', hx'b⟩ := h y hy
  exact ⟨⟨x, hx⟩, le_trans (hx_le hx') hx'b⟩

中文:
定理 nonempty_sublevelLeft
  结论: [拓扑空间 E]
  证明: by
  rcases y with ⟨y, hy⟩
  obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy y hy)
  obtain ⟨x', hx', hx'b⟩ := h y hy
  exact ⟨⟨x, hx⟩, le_trans (hx_le hx') hx'b⟩

Depends on / 依赖: LowerSemicontinuousOn, LowerSemicontinuousOn.exists_isMinOn, exists_isMinOn, hx_le, le_trans, ne_X
-/
theorem nonempty_sublevelLeft [TopologicalSpace E]
    (ne_X : X.Nonempty) (kX : IsCompact X)
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (y : Y) {b : β} (h : forall y in Y, exists x in X, f x y <= b) :
    (sublevelLeft X f b y).Nonempty := by
  rcases y with ⟨y, hy⟩
  obtain ⟨x, hx, hx_le⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy y hy)
  obtain ⟨x', hx', hx'b⟩ := h y hy
  exact ⟨⟨x, hx⟩, le_trans (hx_le hx') hx'b⟩

/--
theorem `isClosed_sublevelLeft` / 定理 `isClosed_sublevelLeft`

English:
theorem isClosed_sublevelLeft
  statement: [TopologicalSpace E]
  proof: by
  specialize hfy y.val y.prop
  rw [← lowerSemicontinuous_restrict_iff]; rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
  exact hfy b

中文:
定理 isClosed_sublevelLeft
  结论: [拓扑空间 E]
  证明: by
  specialize hfy y.val y.prop
  rw [← lowerSemicontinuous_restrict_iff]; rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
  exact hfy b

Depends on / 依赖: lowerSemicontinuous_iff_isClosed_preimage, lowerSemicontinuous_restrict_iff, specialize, y.prop, y.val
-/
theorem isClosed_sublevelLeft [TopologicalSpace E]
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (b : β) (y : Y) :
    IsClosed (sublevelLeft X f b y) := by
  specialize hfy y.val y.prop
  rw [← lowerSemicontinuous_restrict_iff]; rw [lowerSemicontinuous_iff_isClosed_preimage] at hfy
  exact hfy b

/--
theorem `isPreconnected_sublevelLeft` / 定理 `isPreconnected_sublevelLeft`

English:
theorem isPreconnected_sublevelLeft
  statement: [TopologicalSpace E]
  proof: (hfy' y.val y.prop).isPreconnected_preimage_subtype

中文:
定理 isPreconnected_sublevelLeft
  结论: [拓扑空间 E]
  证明: (hfy' y.val y.prop).isPreconnected_preimage_subtype

Depends on / 依赖: isPreconnected_preimage_subtype, y.prop, y.val
-/
theorem isPreconnected_sublevelLeft [TopologicalSpace E]
    [AddCommGroup E] [Module Real E] [IsTopologicalAddGroup E]
    [ContinuousSMul Real E]
    (hfy' : forall y in Y, QuasiconvexOn Real X (fun x => f x y))
    (b : β) (y : Y) :
    IsPreconnected (sublevelLeft X f b y) :=
  (hfy' y.val y.prop).isPreconnected_preimage_subtype

/--
theorem `sublevelLeft_subset_union` / 定理 `sublevelLeft_subset_union`

English:
theorem sublevelLeft_subset_union
  statement: [AddCommGroup F] [Module Real F]
  proof: fun x hx => by
    simp only [Set.mem_union, mem_sublevelLeft_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y ⊓ f x y')
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨y.prop, inf_le_left⟩ ⟨y'.prop, inf_le_right⟩ z.prop
    exact le_trans hfx'.2 hx

中文:
定理 sublevelLeft_subset_union
  结论: [加法交换群 F] [模 实数 F]
  证明: fun x hx => by
    simp only [Set.mem_union, mem_sublevelLeft_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y ⊓ f x y')
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨y.prop, inf_le_left⟩ ⟨y'.prop, inf_le_right⟩ z.prop
    exact le_trans hfx'.2 hx

Depends on / 依赖: Set.mem_union, convex_iff_segment_subset, inf_le_iff, inf_le_left, inf_le_right, le_trans, mem_sublevelLeft_iff, mem_union, specialize, y.prop, z.prop
-/
theorem sublevelLeft_subset_union [AddCommGroup F] [Module Real F]
    (hfx' : forall x in X, QuasiconcaveOn Real Y fun y => f x y)
    (b : β) (y y' : Y) (z : segment Real y.val y'.val) :
    sublevelLeft X f b z subseteq sublevelLeft X f b y union sublevelLeft X f b y' := fun x hx => by
    simp only [Set.mem_union, mem_sublevelLeft_iff, ← inf_le_iff]
    specialize hfx' x x.2 (f x y ⊓ f x y')
    rw [convex_iff_segment_subset] at hfx'
    specialize hfx' ⟨y.prop, inf_le_left⟩ ⟨y'.prop, inf_le_right⟩ z.prop
    exact le_trans hfx'.2 hx

/--
theorem `sublevelLeft_subset_or` / 定理 `sublevelLeft_subset_or`

English:
theorem sublevelLeft_subset_or
  statement: [TopologicalSpace E] [AddCommGroup E]
  proof: by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_sublevelLeft hfy' b ⟨z, cY.segment_subset y.prop y'.prop z.prop⟩)
    _ _ (isClosed_sublevelLeft hfy b y) (isClosed_sublevelLeft hfy b y')
    (sublevelLeft_subset_union hfx' b y y' z)
  simp [(disjoint_sublevelLeft ha hb).inter_eq]

中文:
定理 sublevelLeft_subset_or
  结论: [拓扑空间 E] [加法交换群 E]
  证明: by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_sublevelLeft hfy' b ⟨z, cY.segment_subset y.prop y'.prop z.prop⟩)
    _ _ (isClosed_sublevelLeft hfy b y) (isClosed_sublevelLeft hfy b y')
    (sublevelLeft_subset_union hfx' b y y' z)
  simp [(disjoint_sublevelLeft ha hb).inter_eq]

Depends on / 依赖: cY.segment_subset, disjoint_sublevelLeft, inter_eq, isClosed_sublevelLeft, isPreconnected_iff_subset_of_disjoint_closed, isPreconnected_iff_subset_of_disjoint_closed.mp, isPreconnected_sublevelLeft, segment_subset, sublevelLeft_subset_union, y.prop, z.prop
-/
theorem sublevelLeft_subset_or [TopologicalSpace E] [AddCommGroup E]
    [IsTopologicalAddGroup E] [Module Real E] [ContinuousSMul Real E]
    [AddCommGroup F] [Module Real F]
    (hfx' : forall x in X, QuasiconcaveOn Real Y fun y => f x y)
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : forall y in Y, QuasiconvexOn Real X fun x => f x y)
    (cY : Convex Real Y)
    (a : E) (b : β) (y y' : Y)
    (ha : forall x in X, f a y ⊔ f a y' <= f x y ⊔ f x y')
    (hb : b < f a y ⊔ f a y')
    (z : segment Real y.val y'.val) :
    sublevelLeft X f b z subseteq sublevelLeft X f b y ∨
      sublevelLeft X f b z subseteq sublevelLeft X f b y' := by
  apply isPreconnected_iff_subset_of_disjoint_closed.mp
    (isPreconnected_sublevelLeft hfy' b ⟨z, cY.segment_subset y.prop y'.prop z.prop⟩)
    _ _ (isClosed_sublevelLeft hfy b y) (isClosed_sublevelLeft hfy b y')
    (sublevelLeft_subset_union hfx' b y y' z)
  simp [(disjoint_sublevelLeft ha hb).inter_eq]

variable [TopologicalSpace E] [AddCommGroup E] [Module Real E]
    [IsTopologicalAddGroup E] [ContinuousSMul Real E]
    (ne_X : X.Nonempty) (kX : IsCompact X)
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : forall y in Y, QuasiconvexOn Real X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module Real F]
    (cY : Convex Real Y) (kY : IsCompact Y)
    (hfx : forall x in X, UpperSemicontinuousOn (fun y : F => f x y) Y)
    (hfx' : forall x in X, QuasiconcaveOn Real Y fun y => f x y)

variable (X Y f) in
/--
Definition of `setOfPred_sublevelLeft_subset` / `setOfPred_sublevelLeft_subset` 的定义

English:
definition setOfPred_sublevelLeft_subset
  signature: (b b' : β) (y y' : Y)
  body: {z | sublevelLeft X f b z subseteq sublevelLeft X f b' y}

@[deprecated (since := "2026-07-09")]
alias setOf_sublevelLeft_subset := setOfPred_sublevelLeft_subset

include ne_X kX hfx hfx' cY hfy hfy' in

中文:
定义 setOfPred_sublevelLeft_subset
  签名: (b b' : β) (y y' : Y)
  定义体: {z | sublevelLeft X f b z subseteq sublevelLeft X f b' y}

@[deprecated (since := "2026-07-09")]
alias setOf_sublevelLeft_subset := setOfPred_sublevelLeft_subset

include ne_X kX hfx hfx' cY hfy hfy' in

Depends on / 依赖: sublevelLeft, subseteq
-/
def setOfPred_sublevelLeft_subset (b b' : β) (y y' : Y) : Set (segment Real y.val y'.val) :=
    {z | sublevelLeft X f b z subseteq sublevelLeft X f b' y}

@[deprecated (since := "2026-07-09")]
alias setOf_sublevelLeft_subset := setOfPred_sublevelLeft_subset

include ne_X kX hfx hfx' cY hfy hfy' in
/--
theorem `isClosed_setOfPred_sublevelLeft_subset` / 定理 `isClosed_setOfPred_sublevelLeft_subset`

English:
theorem isClosed_setOfPred_sublevelLeft_subset
  proof: by
  set J := setOfPred_sublevelLeft_subset X Y f b b' y y'
  -- Write `J` for `setOfPred_sublevelLeft_subset X Y f b b' y y'`.
  rw [isClosed_iff_clusterPt]
  /- Let `z in segment ℝ y y'` be a cluster point of `J`;
     we have to show that `z ∈ J`, i.e `sublevelLeft t z ⊆ sublevelLeft t' y1`.
     Let `x ∈ sublevelLeft t z` and let us prove that `x ∈ sublevelLeft X f b' y`. -/
  intro z hz x hx
  suffices exists z' in setOfPred_sublevelLeft_subset X Y f b b' y y', x in sublevelLeft X f b' (z' : F) by
    obtain ⟨z', hz', hxz'⟩ := this
    /- We need to prove `x ∈ sublevelLeft X f b' y`.
       Assume that there is `z' ∈ J` such that `x ∈ sublevelLeft b' z'`.
       It suffices to prove that `sublevelLeft X f b' z' ⊆ sublevelLeft X f b' y`.` -/
    suffices sublevelLeft X f b' z' subseteq sublevelLeft X f b' y from this hxz'
    /- Otherwise, using `sublevelLeft_subset_or`, we see that
       `sublevelLeft X f b' z' ⊆ sublevelLeft t' y'`
       hence `x ∈ sublevelLeft t' y ∩ sublevelLeft t' y' = ∅`, a contradiction. -/
    apply (sublevelLeft_subset_or hfx' hfy hfy' cY a b' y y' ha hb' z').resolve_right
    intro hz'2
    have hz'Y : (z' : F) in Y := (convex_iff_segment_subset.mp cY) y.prop y'.prop z'.prop
    apply (nonempty_sublevelLeft ne_X kX hfy ⟨z', hz'Y⟩ hb).not_subset_empty
    rw [← (disjoint_sublevelLeft ha hb').inter_eq]
    apply subset_inter hz'
    grw [monotone_sublevelLeft _ hbb'.le, hz'2]
  /- In sequential language, pretend that `z = lim z n`, with `z n ∈ J`.
     Since `x ∈ sublevelLeft X f b z`, we have `f x z ≤ b < b'`.
     Since `f x ·` is upper semicontinuous, we would have `f x (z n) < b'` for `n` large enough,
     hence `x ∈ sublevelLeft X f b' (z n)` for `n` large enough. -/
  -- The first step is to rewrite `hfy` (lower semicontinuity of `f (⬝, y)`) into an `∀ᶠ`-form
  simp_rw [upperSemicontinuousOn_iff, upperSemicontinuousWithinAt_iff] at hfx
  specialize hfx x.val x.prop z (cY.segment_subset y.prop y'.prop z.prop) b' (hx.trans_lt hbb')
  -- We rewrite the assumption that `z` is a cluster point of `J` into an `∃ᶠ`-form
  rw [clusterPt_principal_subtype_iff_frequently (cY.segment_subset y.prop y'.prop)] at hz
  suffices forallᶠ z' : F in nhdsWithin z Y,
    (exists hz' : z' in segment Real y.val y'.val,
      (⟨z', hz'⟩ : segment Real y.val y'.val) in setOfPred_sublevelLeft_subset X Y f b b' y y') ->
      exists hz' : z' in segment Real y.val y'.val, x in sublevelLeft X f b' z'
        ∧ (⟨z', hz'⟩ : segment Real y.val y'.val) in setOfPred_sublevelLeft_subset X Y f b b' y y' by
.exists obtain ⟨z', hz', hxz'1, hxz'2⟩ := hz.mp this
    exact ⟨⟨z', hz'⟩, ⟨hxz'2, hxz'1⟩⟩
exact hfx.mp .of_forall fun z hzt' ⟨hz, hz'⟩ => ⟨hz, ⟨hzt'.le, hz'⟩⟩

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_sublevelLeft_subset := isClosed_setOfPred_sublevelLeft_subset

中文:
定理 isClosed_setOfPred_sublevelLeft_subset
  证明: by
  set J := setOfPred_sublevelLeft_subset X Y f b b' y y'
  -- Write `J` for `setOfPred_sublevelLeft_subset X Y f b b' y y'`.
  rw [isClosed_iff_clusterPt]
  /- Let `z in segment ℝ y y'` be a cluster point of `J`;
     we have to show that `z ∈ J`, i.e `sublevelLeft t z ⊆ sublevelLeft t' y1`.
     Let `x ∈ sublevelLeft t z` and let us prove that `x ∈ sublevelLeft X f b' y`. -/
  intro z hz x hx
  suffices exists z' in setOfPred_sublevelLeft_subset X Y f b b' y y', x in sublevelLeft X f b' (z' : F) by
    obtain ⟨z', hz', hxz'⟩ := this
    /- We need to prove `x ∈ sublevelLeft X f b' y`.
       Assume that there is `z' ∈ J` such that `x ∈ sublevelLeft b' z'`.
       It suffices to prove that `sublevelLeft X f b' z' ⊆ sublevelLeft X f b' y`.` -/
    suffices sublevelLeft X f b' z' subseteq sublevelLeft X f b' y from this hxz'
    /- Otherwise, using `sublevelLeft_subset_or`, we see that
       `sublevelLeft X f b' z' ⊆ sublevelLeft t' y'`
       hence `x ∈ sublevelLeft t' y ∩ sublevelLeft t' y' = ∅`, a contradiction. -/
    apply (sublevelLeft_subset_or hfx' hfy hfy' cY a b' y y' ha hb' z').resolve_right
    intro hz'2
    have hz'Y : (z' : F) in Y := (convex_iff_segment_subset.mp cY) y.prop y'.prop z'.prop
    apply (nonempty_sublevelLeft ne_X kX hfy ⟨z', hz'Y⟩ hb).not_subset_empty
    rw [← (disjoint_sublevelLeft ha hb').inter_eq]
    apply subset_inter hz'
    grw [monotone_sublevelLeft _ hbb'.le, hz'2]
  /- In sequential language, pretend that `z = lim z n`, with `z n ∈ J`.
     Since `x ∈ sublevelLeft X f b z`, we have `f x z ≤ b < b'`.
     Since `f x ·` is upper semicontinuous, we would have `f x (z n) < b'` for `n` large enough,
     hence `x ∈ sublevelLeft X f b' (z n)` for `n` large enough. -/
  -- The first step is to rewrite `hfy` (lower semicontinuity of `f (⬝, y)`) into an `∀ᶠ`-form
  simp_rw [upperSemicontinuousOn_iff, upperSemicontinuousWithinAt_iff] at hfx
  specialize hfx x.val x.prop z (cY.segment_subset y.prop y'.prop z.prop) b' (hx.trans_lt hbb')
  -- We rewrite the assumption that `z` is a cluster point of `J` into an `∃ᶠ`-form
  rw [clusterPt_principal_subtype_iff_frequently (cY.segment_subset y.prop y'.prop)] at hz
  suffices forallᶠ z' : F in nhdsWithin z Y,
    (exists hz' : z' in segment Real y.val y'.val,
      (⟨z', hz'⟩ : segment Real y.val y'.val) in setOfPred_sublevelLeft_subset X Y f b b' y y') ->
      exists hz' : z' in segment Real y.val y'.val, x in sublevelLeft X f b' z'
        ∧ (⟨z', hz'⟩ : segment Real y.val y'.val) in setOfPred_sublevelLeft_subset X Y f b b' y y' by
.exists obtain ⟨z', hz', hxz'1, hxz'2⟩ := hz.mp this
    exact ⟨⟨z', hz'⟩, ⟨hxz'2, hxz'1⟩⟩
exact hfx.mp .of_forall fun z hzt' ⟨hz, hz'⟩ => ⟨hz, ⟨hzt'.le, hz'⟩⟩

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_sublevelLeft_subset := isClosed_setOfPred_sublevelLeft_subset

Depends on / 依赖: setOfPred_sublevelLeft_subset
-/
theorem isClosed_setOfPred_sublevelLeft_subset
    (a : E) (b b' : β) (y y' : Y)
    (ha : forall x in X, f a y ⊔ f a y' <= f x y ⊔ f x y')
    (hb : forall y in Y, exists x in X, f x y <= b)
    (hb' : b' < f a y ⊔ f a y')
    (hbb' : b < b') :
    IsClosed (setOfPred_sublevelLeft_subset X Y f b b' y y') := by
  set J := setOfPred_sublevelLeft_subset X Y f b b' y y'
  -- Write `J` for `setOfPred_sublevelLeft_subset X Y f b b' y y'`.
  rw [isClosed_iff_clusterPt]
  /- Let `z in segment ℝ y y'` be a cluster point of `J`;
     we have to show that `z ∈ J`, i.e `sublevelLeft t z ⊆ sublevelLeft t' y1`.
     Let `x ∈ sublevelLeft t z` and let us prove that `x ∈ sublevelLeft X f b' y`. -/
  intro z hz x hx
  suffices exists z' in setOfPred_sublevelLeft_subset X Y f b b' y y', x in sublevelLeft X f b' (z' : F) by
    obtain ⟨z', hz', hxz'⟩ := this
    /- We need to prove `x ∈ sublevelLeft X f b' y`.
       Assume that there is `z' ∈ J` such that `x ∈ sublevelLeft b' z'`.
       It suffices to prove that `sublevelLeft X f b' z' ⊆ sublevelLeft X f b' y`.` -/
    suffices sublevelLeft X f b' z' subseteq sublevelLeft X f b' y from this hxz'
    /- Otherwise, using `sublevelLeft_subset_or`, we see that
       `sublevelLeft X f b' z' ⊆ sublevelLeft t' y'`
       hence `x ∈ sublevelLeft t' y ∩ sublevelLeft t' y' = ∅`, a contradiction. -/
    apply (sublevelLeft_subset_or hfx' hfy hfy' cY a b' y y' ha hb' z').resolve_right
    intro hz'2
    have hz'Y : (z' : F) in Y := (convex_iff_segment_subset.mp cY) y.prop y'.prop z'.prop
    apply (nonempty_sublevelLeft ne_X kX hfy ⟨z', hz'Y⟩ hb).not_subset_empty
    rw [← (disjoint_sublevelLeft ha hb').inter_eq]
    apply subset_inter hz'
    grw [monotone_sublevelLeft _ hbb'.le, hz'2]
  /- In sequential language, pretend that `z = lim z n`, with `z n ∈ J`.
     Since `x ∈ sublevelLeft X f b z`, we have `f x z ≤ b < b'`.
     Since `f x ·` is upper semicontinuous, we would have `f x (z n) < b'` for `n` large enough,
     hence `x ∈ sublevelLeft X f b' (z n)` for `n` large enough. -/
  -- The first step is to rewrite `hfy` (lower semicontinuity of `f (⬝, y)`) into an `∀ᶠ`-form
  simp_rw [upperSemicontinuousOn_iff, upperSemicontinuousWithinAt_iff] at hfx
  specialize hfx x.val x.prop z (cY.segment_subset y.prop y'.prop z.prop) b' (hx.trans_lt hbb')
  -- We rewrite the assumption that `z` is a cluster point of `J` into an `∃ᶠ`-form
  rw [clusterPt_principal_subtype_iff_frequently (cY.segment_subset y.prop y'.prop)] at hz
  suffices forallᶠ z' : F in nhdsWithin z Y,
    (exists hz' : z' in segment Real y.val y'.val,
      (⟨z', hz'⟩ : segment Real y.val y'.val) in setOfPred_sublevelLeft_subset X Y f b b' y y') ->
      exists hz' : z' in segment Real y.val y'.val, x in sublevelLeft X f b' z'
        ∧ (⟨z', hz'⟩ : segment Real y.val y'.val) in setOfPred_sublevelLeft_subset X Y f b b' y y' by
.exists obtain ⟨z', hz', hxz'1, hxz'2⟩ := hz.mp this
    exact ⟨⟨z', hz'⟩, ⟨hxz'2, hxz'1⟩⟩
exact hfx.mp .of_forall fun z hzt' ⟨hz, hz'⟩ => ⟨hz, ⟨hzt'.le, hz'⟩⟩

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_sublevelLeft_subset := isClosed_setOfPred_sublevelLeft_subset

variable [DenselyOrdered β]
variable [IsTopologicalAddGroup F] [ContinuousSMul Real F]

include ne_X kX hfx hfx' cY hfy hfy' in
public theorem exists_lt_iInf_of_lt_iInf_of_sup
    {y1 : F} (hy1 : y1 in Y) {y2 : F} (hy2 : y2 in Y) {t : β}
    (ht : forall x in X, t < f x y1 ⊔ f x y2) :
    exists y0 in Y, forall x in X, t < f x y0 := by
  by_contra! hinfi_le
.exists_isMinOn ne_X kX obtain ⟨a, ha, ha'⟩ := (hfy y1 hy1).sup (hfy y2 hy2)
  obtain ⟨t', htt', ht'⟩ := exists_between (ht a ha)
  lift y1 to Y using hy1
  lift y2 to Y using hy2
  let J1 := setOfPred_sublevelLeft_subset X Y f t t' y1 y2
  have mem_J1_iff (z : segment Real (y1 : F) y2) :
      z in J1 ↔ sublevelLeft X f t z subseteq sublevelLeft X f t' y1 := by
    simp [J1, setOfPred_sublevelLeft_subset]
  let φ : segment Real (y1 : F) y2 ≃ₜ segment Real (y2 : F) y1 := .setCongr (segment_symm Real (y1 : F) y2)
  let J2 := φ ⁻¹' (setOfPred_sublevelLeft_subset X Y f t t' y2 y1)
  have mem_J2_iff (z : segment Real (y1 : F) y2) :
      z in J2 ↔ sublevelLeft X f t z subseteq sublevelLeft X f t' y2 := by
    simp [J2, setOfPred_sublevelLeft_subset, φ, Homeomorph.setCongr]
  have h_mem_Y (z : segment Real (y1 : F) y2) : (z : F) in Y := cY.segment_subset y1.2 y2.2 z.prop
  have hJ1J2 : J1 inter J2 = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    simp only [mem_inter_iff, mem_J1_iff, mem_J2_iff]
    intro z ⟨hz1, hz2⟩
    apply (nonempty_sublevelLeft ne_X kX hfy ⟨z, h_mem_Y z⟩ hinfi_le).not_subset_empty
    simpa using Set.disjoint_of_subset hz1 hz2 (disjoint_sublevelLeft ha' ht')
  have hJ1_union_J2 : J1 union J2 = segment Real (y1 : F) y2 := by
    refine subset_antisymm (by simp) fun z hz => ?_
    lift z to segment Real (y1 : F) y2 using hz
    refine ⟨z, ?_, rfl⟩
.imp apply sublevelLeft_subset_or hfx' hfy hfy' cY a t' y1 y2 ha' ht' z
      (fun h1 => ?_) (fun h2 => ?_)
    · grw [mem_J1_iff, (monotone_sublevelLeft ⟨(z : F), h_mem_Y z⟩ htt'.le), h1]
    · grw [mem_J2_iff, (monotone_sublevelLeft ⟨(z : F), h_mem_Y z⟩ htt'.le), h2]
  have : IsPreconnected (Set.univ : Set (segment Real (y1 : F) y2)) := by
    simpa [← Topology.IsInducing.subtypeVal.isPreconnected_image] using
      (convex_segment (y1 : F) y2).isPreconnected
  have hJ1 : IsClosed J1 := isClosed_setOfPred_sublevelLeft_subset ne_X kX hfy hfy'
    cY hfx hfx' a t t' y1 y2 ha' hinfi_le ht' htt'
  have hJ2 : IsClosed J2 := by
    simp only [sup_comm (f _ y1)] at ha' ht'
    simpa [J2, sup_comm] using isClosed_setOfPred_sublevelLeft_subset ne_X kX hfy hfy'
      cY hfx hfx' a t t' y2 y1 ha' hinfi_le ht' htt'
  have h_univ : univ subseteq J1 union J2 :=
.mp by simp [hJ1_union_J2] image_subset_image_iff Subtype.val_injective
  have h_inter : univ inter (J1 inter J2) = ∅ := by simp [hJ1J2]
  rw [isPreconnected_iff_subset_of_disjoint_closed] at this
  rw [eq_empty_iff_forall_notMem] at hJ1J2
  obtain (h1 | h2) := this J1 J2 hJ1 hJ2 h_univ h_inter
  · refine hJ1J2 ⟨y2, right_mem_segment Real (y1 : F) y2⟩ ⟨h1 (Set.mem_univ _), ?_⟩
    grw [mem_J2_iff, monotone_sublevelLeft y2 htt'.le]
  · refine hJ1J2 ⟨y1, left_mem_segment Real (y1 : F) y2⟩ ⟨?_, h2 (Set.mem_univ _)⟩
    grw [mem_J1_iff, monotone_sublevelLeft y1 htt'.le]

variable (cX : Convex Real X)

include ne_X cX cY kX hfx hfx' hfy hfy' in
public theorem exists_lt_iInf_of_lt_iInf_of_finite
    {s : Set F} (hs : s.Finite) (hsY : s subseteq Y)
    {t : β} (ht : forall x in X, exists y in s, t < f x y) :
    exists y0 in Y, forall x in X, t < f x y0 := by
  induction s, hs using Set.Finite.induction_on
    generalizing X with
  | empty => simpa using ht _ ne_X.choose_spec
  | @insert b s _ hs hrec => -- insert case
    have hb : (b in Y) := hsY (mem_insert b s)
    let X' := X inter (fun x => f x b) ⁻¹' Iic t
    rcases Set.eq_empty_or_nonempty X' with X'_e | X'_ne
    · -- When `X'` is empty, we may set `y0 := b`
      use b, hb
      simpa [X', Set.eq_empty_iff_forall_notMem] using X'_e
    -- the nonempty case
    have hX'X : X' subseteq X := inter_subset_left
    have kX' : IsCompact X' := (hfy b hb).isCompact_inter_preimage_Iic kX t
    have cX' : Convex Real X' := hfy' b hb t
    specialize hrec X'_ne kX'
      (fun y hy => LowerSemicontinuousOn.mono (hfy y hy) hX'X)
      (fun y hy => cX'.quasiconvexOn_restrict (hfy' y hy) hX'X)
      (fun x hx' => hfx x (hX'X hx'))
      (fun x hx' => hfx' x (hX'X hx'))
      cX'
    have ht_lt : forall x in X', exists y in s, t < f x y := by
        /- otherwise, if infi x ∈ X', supr y ∈ s f x y ≤ t
          then for every t' > t, there is x ∈ X' such that supr y ∈ s f x y ≤ t',
          since x ∈ X' and t ≤ t', we have supr y ∈ insert b s f x y ≤ t',
          hence infi x ∈ X, supr y ∈ insert b s, f x y ≤ t',
          so that infi x ∈ X, supr y ∈ insert b s, f x y ≤ t. -/
      intro x hx
      obtain ⟨y, hy, h⟩ := ht x hx.1
      rcases hy with rfl | hy
      · simp [h.not_ge hx.2]
      · exact ⟨y, hy, h⟩
    obtain ⟨y1, hy1, hty1⟩ := hrec (by grw [subset_insert b s, hsY]) ht_lt
    refine exists_lt_iInf_of_lt_iInf_of_sup ne_X kX hfy hfy' cY hfx hfx' hb hy1 fun x hx => ?_
    by_cases hx' : x in X'
    · exact (hty1 x hx').trans_le (le_sup_right)
    · apply lt_of_lt_of_le _ (le_sup_left)
      rw [← not_le]
      exact fun h => hx' ⟨hx, h⟩

include ne_X cX cY kX hfx hfx' hfy hfy' in
/-- A minimax theorem without completeness, using `IsGLB` and `IsLUB`. -/
public theorem minimax
    (sup_y : E -> β) (hsup_y : forall x in X, IsLUB {f x y | y in Y} (sup_y x))
    (inf_sup : β) (hinf_sup : IsGLB {sup_y x | x in X} inf_sup)
    (inf_x : F -> β) (hinf_x : forall y in Y, IsGLB {f x y | x in X} (inf_x y))
    (sup_inf : β) (hsup_inf : IsLUB {inf_x y | y in Y} sup_inf) :
    inf_sup = sup_inf := by
  apply symm
  apply le_antisymm
  -- the obvious inequality
  · rw [le_isGLB_iff hinf_sup, mem_lowerBounds]
    rintro _ ⟨x, hx, rfl⟩
    rw [isLUB_le_iff hsup_inf]; rw [mem_upperBounds]
    rintro _ ⟨y, hy, rfl⟩
    trans f x y
    · exact (hinf_x y hy).1 ⟨x, hx, rfl⟩
    · exact (hsup_y x hx).1 ⟨y, hy, rfl⟩
  -- the delicate inequality
  rcases eq_empty_or_nonempty Y with ⟨rfl⟩ | ne_Y
  · -- the case when `Y` is empty is trivial
    simp only [mem_empty_iff_false, IsEmpty.forall_iff, implies_true, false_and, exists_const,
      ofPred_false, isLUB_empty_iff] at *
    replace hsup_y : forall x in X, sup_y x = sup_inf :=
      fun x hx => le_antisymm (hsup_y x hx sup_inf) (hsup_inf (sup_y x))
.le suffices {t | exists x in X, sup_y x = t} = {sup_inf} from (this ▸ hinf_sup).unique (by simp)
    ext t
    simp only [mem_ofPred_eq, mem_singleton_iff]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hsup_y x hx
    · rintro rfl
      exact ⟨_, ne_X.choose_spec, hsup_y _ ne_X.choose_spec⟩
  -- when `Y` is not empty
  rw [← forall_lt_iff_le]
  intro t ht
  have : exists s : Finset Y, forall x in X, exists i in s, t < f x i := by
    rw [← LowerSemicontinuousOn.inter_biInter_preimage_Iic_eq_empty_iff_exists_finset kX hfy]
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hx, hx'⟩
    simp only [mem_iInter, mem_preimage, mem_Iic] at hx'
    rw [lt_isGLB_iff hinf_sup] at ht
    obtain ⟨c, hc, htc⟩ := ht
    simp only [mem_lowerBounds, mem_ofPred_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂] at hc
    apply not_le.mpr htc (le_trans (hc x hx) _)
    rw [isLUB_le_iff (hsup_y x hx)]; rw [mem_upperBounds]
    aesop
  obtain ⟨s, hs⟩ := this
  have hs' (x) (hx : x in X) : exists y in Subtype.val '' (s : Set Y), t < f x y := by
    obtain ⟨i, hi, hi'⟩ := hs x hx
    use i.val
    simp [hi, hi']
  choose y0 hy0 ht0 using exists_lt_iInf_of_lt_iInf_of_finite
        ne_X kX hfy hfy' cY hfx hfx' cX
        (t := t)
        (toFinite _) (Subtype.coe_image_subset Y ↑s)
  simp only [lt_isLUB_iff hsup_inf, mem_ofPred_eq, exists_exists_and_eq_and]
  use y0 hs', hy0 hs'
  specialize ht0 hs'
  obtain ⟨a, ha, h⟩ := LowerSemicontinuousOn.exists_isMinOn ne_X kX (hfy (y0 hs') (hy0 hs'))
  apply lt_of_lt_of_le (ht0 a ha)
  simpa [le_isGLB_iff (hinf_x (y0 hs') (hy0 hs')), mem_lowerBounds]

variable (ne_Y : Y.Nonempty) (kY : IsCompact Y)
include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form) -/
public theorem exists_isSaddlePointOn' :
    exists a in X, exists b in Y, IsSaddlePointOn X Y f a b := by
  have hmax_y (x) (hx : x in X) : exists y in Y, IsMaxOn (f x) Y y := (hfx x hx).exists_isMaxOn ne_Y kY
  choose! η η_mem η_max using hmax_y
  have hlsc : LowerSemicontinuousOn (fun x => f x (η x)) X :=
    lowerSemicontinuousOn_of_forall_isMaxOn_and_mem hfy η_mem η_max
  obtain ⟨a, ha, ha'⟩ : exists a in X, IsMinOn (fun x => f x (η x)) X a := hlsc.exists_isMinOn ne_X kX
  use a, ha
  have hmin_x (y) (hy : y in Y) : exists x in X, IsMinOn (f · y) X x := (hfy y hy).exists_isMinOn ne_X kX
  choose! ξ ξ_mem ξ_min using hmin_x
  have husc := upperSemicontinuousOn_of_forall_isMinOn_and_mem hfx ξ_mem ξ_min
  obtain ⟨b, hb, hb'⟩ : exists b in Y, IsMaxOn (fun y => f (ξ y) y) Y b := husc.exists_isMaxOn ne_Y kY
  use b, hb
  intro x hx y hy
  calc f a y <= f a (η a) := isMaxOn_iff.mp (η_max a ha) y hy
    _ = f (ξ b) b :=
      minimax ne_X kX hfy hfy' cY hfx hfx' cX
        _ (fun x hx => (η_max x hx).isLUB (η_mem x hx))
        _ (ha'.isGLB ha)
        _ (fun y hy => (ξ_min y hy).isGLB (ξ_mem y hy))
        _ (hb'.isLUB hb)
    _ <= f x b := isMinOn_iff.mp (ξ_min b hb) x hx

end LinearOrder

section CompleteLinearOrder

variable {E F β : Type*} [CompleteLinearOrder β] [DenselyOrdered β]
variable {X : Set E} {Y : Set F} {f : E -> F -> β}
variable [TopologicalSpace E] [AddCommGroup E] [Module Real E]
    [IsTopologicalAddGroup E] [ContinuousSMul Real E]
    (ne_X : X.Nonempty) (cX : Convex Real X) (kX : IsCompact X)
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : forall y in Y, QuasiconvexOn Real X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module Real F]
  [IsTopologicalAddGroup F] [ContinuousSMul Real F]
  (cY : Convex Real Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : forall x in X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : forall x in X, QuasiconcaveOn Real Y fun y => f x y)

include ne_X cX cY kX hfx hfx' hfy hfy' in
/-- A minimax theorem in inf-sup form, for complete linear orders. -/
public theorem minimax' : (⨅ x in X, ⨆ y in Y, f x y) = ⨆ y in Y, ⨅ x in X, f x y :=
  minimax ne_X kX hfy hfy' cY hfx hfx' cX
   _ (fun _ _ => isLUB_biSup) _ isGLB_biInf _ (fun _ _ => isGLB_biInf) _ isLUB_biSup

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The Sion-von Neumann minimax theorem (saddle point form),
case of complete linear orders. -/
public theorem exists_saddlePointOn' :
    exists a in X, exists b in Y, IsSaddlePointOn X Y f a b := by
  have hlsc : LowerSemicontinuousOn (fun x => ⨆ y in Y, f x y) X := fun x hx => by
    apply lowerSemicontinuousWithinAt_iSup
    intro i
    exact lowerSemicontinuousWithinAt_iSup fun i_1 => hfy i i_1 x hx
  have husc : UpperSemicontinuousOn (fun y => ⨅ x in X, f x y) Y := fun y hy => by
    apply upperSemicontinuousWithinAt_iInf
    intro i
    exact upperSemicontinuousWithinAt_iInf fun i_1 => hfx i i_1 y hy
  obtain ⟨a, ha, ha'⟩ := LowerSemicontinuousOn.exists_isMinOn
   ne_X kX hlsc
  obtain ⟨b, hb, hb'⟩ := UpperSemicontinuousOn.exists_isMaxOn ne_Y kY husc
  use a, ha, b, hb
  rw [isSaddlePointOn_iff' ha hb]
  refine le_trans (le_iInf₂ ha') ?_
  refine le_trans ?_ (iSup₂_le_iff.mpr hb')
  rw [minimax' ne_X cX kX hfy hfy' cY hfx hfx']

end CompleteLinearOrder

section DedekindMacNeille

variable {E F β γ : Type*} [LinearOrder β]

variable {X : Set E} {Y : Set F} {f : E -> F -> β}
variable [TopologicalSpace E] [AddCommGroup E] [Module Real E]
    [IsTopologicalAddGroup E] [ContinuousSMul Real E]
    (ne_X : X.Nonempty) (cX : Convex Real X) (kX : IsCompact X)
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : forall y in Y, QuasiconvexOn Real X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module Real F]
  [IsTopologicalAddGroup F] [ContinuousSMul Real F]
  (cY : Convex Real Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : forall x in X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : forall x in X, QuasiconcaveOn Real Y fun y => f x y)

/- The following lines essentially assume that `β` has a densely ordered completion.
(The Dedekind MacNeille completion is not densely ordered unless `β` is.) -/
variable [TopologicalSpace β] [OrderTopology β]
variable {γ : Type*} [CompleteLinearOrder γ] [DenselyOrdered γ]
  [TopologicalSpace γ] [OrderTopology γ]
  {ι : β ↪o γ} (hι : Continuous ι)

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' hι in
/-- The minimax theorem, in the saddle point form,
when `β` is given a Dedekind-MacNeille completion `ι : β ↪o γ` -/
public theorem DMCompletion.exists_isSaddlePointOn :
  exists a in X, exists b in Y, IsSaddlePointOn X Y f a b := by
  -- Reduce to the cae of EReal-valued functions
  let φ : E -> F -> γ := fun x y => ι (f x y)
  -- suffices : ∃ a ∈ X, ∃ b ∈ Y, IsSaddlePointOn X Y φ a b
  have hφx (x) (hx : x in X) : UpperSemicontinuousOn (fun y => φ x y) Y := by
    convert! Continuous.comp_upperSemicontinuousOn hι (hfx x hx) ι.monotone
  have hφx' (x) (hx : x in X) : QuasiconcaveOn Real Y fun y => φ x y := by
    convert! (hfx' x hx).monotone_comp ι.monotone
  have hφy (y) (hy : y in Y) : LowerSemicontinuousOn (fun x => φ x y) X := by
    convert! Continuous.comp_lowerSemicontinuousOn hι (hfy y hy) ι.monotone
  have hφy' (y) (hy : y in Y) : QuasiconvexOn Real X fun x => φ x y := by
    convert! (hfy' y hy).monotone_comp ι.monotone
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_isSaddlePointOn' ne_X kX hφy hφy' cY kY hφx hφx' cX ne_Y
  use a, ha, b, hb
  intro x hx y hy
  simpa only [OrderEmbedding.le_iff_le, φ] using hab x hx y hy

end DedekindMacNeille

section Real

variable {E F : Type*}
variable {X : Set E} {Y : Set F} {f : E -> F -> Real}
variable [TopologicalSpace E] [AddCommGroup E] [Module Real E]
    [IsTopologicalAddGroup E] [ContinuousSMul Real E]
    (ne_X : X.Nonempty) (cX : Convex Real X) (kX : IsCompact X)
    (hfy : forall y in Y, LowerSemicontinuousOn (fun x : E => f x y) X)
    (hfy' : forall y in Y, QuasiconvexOn Real X fun x => f x y)

variable [TopologicalSpace F] [AddCommGroup F] [Module Real F]
  [IsTopologicalAddGroup F] [ContinuousSMul Real F]
  (cY : Convex Real Y) (ne_Y : Y.Nonempty) (kY : IsCompact Y)
  (hfx : forall x in X, UpperSemicontinuousOn (fun y : F => f x y) Y)
  (hfx' : forall x in X, QuasiconcaveOn Real Y fun y => f x y)

include ne_X ne_Y cX cY kX kY hfx hfx' hfy hfy' in
/-- The minimax theorem, in the saddle point form -/
public theorem exists_isSaddlePointOn :
    exists a in X, exists b in Y, IsSaddlePointOn X Y f a b :=
  DMCompletion.exists_isSaddlePointOn ne_X cX kX hfy hfy' cY ne_Y kY hfx hfx'
    (ι := EReal.orderEmbedding) (hι := continuous_coe_real_ereal)

end Real

end Sion
