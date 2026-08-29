/-
Copyright (c) 2019 Jean Lo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean Lo, Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.Bornology.Absorbs
/-!
# Local convexity

This file defines absorbent and balanced sets.

An absorbent set is one that "surrounds" the origin. The idea is made precise by requiring that any
point belongs to all large enough scalings of the set. This is the vector world analog of a
topological neighborhood of the origin.

A balanced set is one that is everywhere around the origin. This means that `a • s ⊆ s` for all `a`
of norm less than `1`.

## Main declarations

For a module over a normed ring:
* `Absorbs`: A set `s` absorbs a set `t` if all large scalings of `s` contain `t`.
* `Absorbent`: A set `s` is absorbent if every point eventually belongs to all large scalings of
  `s`.
* `Balanced`: A set `s` is balanced if `a • s ⊆ s` for all `a` of norm less than `1`.

## Main Results
* `Absorbent.submodule_eq_top` shows that when the base field is nontrivially normed, an absorbent
  submodule is actually the whole space. As an application, we show in
  `Absorbent.subset_image_iff_surjective` that a linear function is surjective if and only if its
  image contains an absorbent set.

## References

* [H. H. Schaefer, *Topological Vector Spaces*][schaefer1966]

## Tags

absorbent, balanced, locally convex, LCTVS
-/

@[expose] public section

assert_not_exists NormedSpace

open Set
open scoped Pointwise Topology

variable {𝕜 𝕝 E F : Type*} {ι : Sort*} {κ : ι -> Sort*}

section SeminormedRing

variable [SeminormedRing 𝕜]

section SMul

variable [SMul 𝕜 E] {s A B : Set E}

variable (𝕜) in
/--
Definition of `Balanced` / `Balanced` 的定义

English:
definition Balanced
  signature: (A : Set E)
  body: forall a : 𝕜, ‖a‖ <= 1 -> a • A subseteq A

中文:
定义 Balanced
  签名: (A : 集合 E)
  定义体: forall a : 𝕜, ‖a‖ <= 1 -> a • A subseteq A

Depends on / 依赖: subseteq
-/
def Balanced (A : Set E) :=
  forall a : 𝕜, ‖a‖ <= 1 -> a • A subseteq A

/--
lemma `absorbs_iff_norm` / 引理 `absorbs_iff_norm`

English:
lemma absorbs_iff_norm
  statement: Absorbs 𝕜 A B ↔ exists r, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
  proof: Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans by simp only [true_and]; rfl

alias ⟨_, Absorbs.of_norm⟩ := absorbs_iff_norm

中文:
引理 absorbs_iff_norm
  结论: Absorbs 𝕜 A B ↔ 存在 r, 对任意 c : 𝕜, r <= ‖c‖ -> B subseteq c • A
  证明: Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans by simp only [true_and]; rfl

alias ⟨_, Absorbs.of_norm⟩ := absorbs_iff_norm

Depends on / 依赖: Filter, Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans, atTop_basis, cobounded_of_norm, eventually_iff, true_and
-/
lemma absorbs_iff_norm : Absorbs 𝕜 A B ↔ exists r, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A :=
Filter.atTop_basis.cobounded_of_norm.eventually_iff.trans by simp only [true_and]; rfl

alias ⟨_, Absorbs.of_norm⟩ := absorbs_iff_norm

/--
lemma `Absorbs.exists_pos` / 引理 `Absorbs.exists_pos`

English:
lemma Absorbs.exists_pos
  given: (h : Absorbs 𝕜 A B)
  statement: exists r > 0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
  proof: let ⟨r, hr₁, hr⟩ := (Filter.atTop_basis' 1).cobounded_of_norm.eventually_iff.1 h
  ⟨r, one_pos.trans_le hr₁, hr⟩

中文:
引理 Absorbs.存在_pos
  条件: (h : Absorbs 𝕜 A B)
  结论: 存在 r > 0, 对任意 c : 𝕜, r <= ‖c‖ -> B subseteq c • A
  证明: let ⟨r, hr₁, hr⟩ := (Filter.atTop_basis' 1).cobounded_of_norm.eventually_iff.1 h
  ⟨r, one_pos.trans_le hr₁, hr⟩

Depends on / 依赖: Filter, Filter.atTop_basis, atTop_basis, cobounded_of_norm, cobounded_of_norm.eventually_iff, eventually_iff, one_pos, one_pos.trans_le, trans_le
-/
lemma Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A :=
  let ⟨r, hr₁, hr⟩ := (Filter.atTop_basis' 1).cobounded_of_norm.eventually_iff.1 h
  ⟨r, one_pos.trans_le hr₁, hr⟩

/--
theorem `balanced_iff_smul_mem` / 定理 `balanced_iff_smul_mem`

English:
theorem balanced_iff_smul_mem
  statement: Balanced 𝕜 s ↔ forall ⦃a : 𝕜⦄, ‖a‖ <= 1 -> forall ⦃x : E⦄, x in s -> a • x in s
  proof: forall₂_congr fun _a _ha => smul_set_subset_iff

alias ⟨Balanced.smul_mem, _⟩ := balanced_iff_smul_mem

中文:
定理 balanced_iff_smul_mem
  结论: Balanced 𝕜 s ↔ 对任意 ⦃a : 𝕜⦄, ‖a‖ <= 1 -> 对任意 ⦃x : E⦄, x in s -> a • x in s
  证明: forall₂_congr fun _a _ha => smul_set_subset_iff

alias ⟨Balanced.smul_mem, _⟩ := balanced_iff_smul_mem

Depends on / 依赖: smul_set_subset_iff
-/
theorem balanced_iff_smul_mem : Balanced 𝕜 s ↔ forall ⦃a : 𝕜⦄, ‖a‖ <= 1 -> forall ⦃x : E⦄, x in s -> a • x in s :=
  forall₂_congr fun _a _ha => smul_set_subset_iff

alias ⟨Balanced.smul_mem, _⟩ := balanced_iff_smul_mem

/--
theorem `balanced_iff_closedBall_smul` / 定理 `balanced_iff_closedBall_smul`

English:
theorem balanced_iff_closedBall_smul
  statement: Balanced 𝕜 s ↔ Metric.closedBall (0 : 𝕜) 1 • s subseteq s
  proof: by
  simp [balanced_iff_smul_mem, smul_subset_iff]

@[simp]

中文:
定理 balanced_iff_closedBall_smul
  结论: Balanced 𝕜 s ↔ Metric.closedBall (0 : 𝕜) 1 • s subseteq s
  证明: by
  simp [balanced_iff_smul_mem, smul_subset_iff]

@[simp]

Depends on / 依赖: balanced_iff_smul_mem, smul_subset_iff
-/
theorem balanced_iff_closedBall_smul : Balanced 𝕜 s ↔ Metric.closedBall (0 : 𝕜) 1 • s subseteq s := by
  simp [balanced_iff_smul_mem, smul_subset_iff]

@[simp]
/--
theorem `balanced_empty` / 定理 `balanced_empty`

English:
theorem balanced_empty
  statement: Balanced 𝕜 (∅ : Set E)
  proof: fun _ _ => by rw [smul_set_empty]

@[simp]

中文:
定理 balanced_empty
  结论: Balanced 𝕜 (∅ : 集合 E)
  证明: fun _ _ => by rw [smul_set_empty]

@[simp]

Depends on / 依赖: smul_set_empty
-/
theorem balanced_empty : Balanced 𝕜 (∅ : Set E) := fun _ _ => by rw [smul_set_empty]

@[simp]
/--
theorem `balanced_univ` / 定理 `balanced_univ`

English:
theorem balanced_univ
  statement: Balanced 𝕜 (univ : Set E)
  proof: fun _a _ha => subset_univ _

中文:
定理 balanced_univ
  结论: Balanced 𝕜 (univ : 集合 E)
  证明: fun _a _ha => subset_univ _

Depends on / 依赖: subset_univ
-/
theorem balanced_univ : Balanced 𝕜 (univ : Set E) := fun _a _ha => subset_univ _

/--
theorem `Balanced.union` / 定理 `Balanced.union`

English:
theorem Balanced.union
  given: (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B)
  statement: Balanced 𝕜 (A union B)
  proof: fun _a ha =>
smul_set_union.subset.trans union_subset_union (hA _ ha) hB _ ha

中文:
定理 Balanced.union
  条件: (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B)
  结论: Balanced 𝕜 (A union B)
  证明: fun _a ha =>
smul_set_union.subset.trans union_subset_union (hA _ ha) hB _ ha
-/
theorem Balanced.union (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A union B) := fun _a ha =>
smul_set_union.subset.trans union_subset_union (hA _ ha) hB _ ha

/--
theorem `Balanced.inter` / 定理 `Balanced.inter`

English:
theorem Balanced.inter
  given: (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B)
  statement: Balanced 𝕜 (A inter B)
  proof: fun _a ha =>
smul_set_inter_subset.trans inter_subset_inter (hA _ ha) hB _ ha

中文:
定理 Balanced.inter
  条件: (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B)
  结论: Balanced 𝕜 (A inter B)
  证明: fun _a ha =>
smul_set_inter_subset.trans inter_subset_inter (hA _ ha) hB _ ha
-/
theorem Balanced.inter (hA : Balanced 𝕜 A) (hB : Balanced 𝕜 B) : Balanced 𝕜 (A inter B) := fun _a ha =>
smul_set_inter_subset.trans inter_subset_inter (hA _ ha) hB _ ha

/--
theorem `balanced_iUnion` / 定理 `balanced_iUnion`

English:
theorem balanced_iUnion
  given: {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i))
  statement: Balanced 𝕜 (⋃ i, f i)
  proof: fun _a ha => (smul_set_iUnion _ _).subset.trans iUnion_mono fun _ => h _ _ ha

中文:
定理 balanced_iUnion
  条件: {f : ι -> 集合 E} (h : 对任意 i, Balanced 𝕜 (f i))
  结论: Balanced 𝕜 (⋃ i, f i)
  证明: fun _a ha => (smul_set_iUnion _ _).subset.trans iUnion_mono fun _ => h _ _ ha

Depends on / 依赖: iUnion_mono, smul_set_iUnion, subset, subset.trans
-/
theorem balanced_iUnion {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋃ i, f i) :=
fun _a ha => (smul_set_iUnion _ _).subset.trans iUnion_mono fun _ => h _ _ ha

/--
theorem `balanced_iUnion₂` / 定理 `balanced_iUnion₂`

English:
theorem balanced_iUnion₂
  given: {f : forall i, κ i -> Set E} (h : forall i j, Balanced 𝕜 (f i j))
  proof: balanced_iUnion fun _ => balanced_iUnion h _

中文:
定理 balanced_iUnion₂
  条件: {f : 对任意 i, κ i -> 集合 E} (h : 对任意 i j, Balanced 𝕜 (f i j))
  证明: balanced_iUnion fun _ => balanced_iUnion h _

Depends on / 依赖: OrderDual, OrderDual.instHasSolidNorm, balanced_iUnion, instHasSolidNorm
-/
theorem balanced_iUnion₂ {f : forall i, κ i -> Set E} (h : forall i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋃ (i) (j), f i j) :=
balanced_iUnion fun _ => balanced_iUnion h _

/--
theorem `Balanced.sInter` / 定理 `Balanced.sInter`

English:
theorem Balanced.sInter
  given: {S : Set (Set E)} (h : forall s in S, Balanced 𝕜 s)
  statement: Balanced 𝕜 (⋂₀ S)
  proof: fun _ _ => (smul_set_sInter_subset ..).trans (fun _ _ => by aesop)

中文:
定理 Balanced.集合交集
  条件: {S : 集合 (集合 E)} (h : 对任意 s in S, Balanced 𝕜 s)
  结论: Balanced 𝕜 (⋂₀ S)
  证明: fun _ _ => (smul_set_sInter_subset ..).trans (fun _ _ => by aesop)

Depends on / 依赖: smul_set_sInter_subset
-/
theorem Balanced.sInter {S : Set (Set E)} (h : forall s in S, Balanced 𝕜 s) : Balanced 𝕜 (⋂₀ S) :=
  fun _ _ => (smul_set_sInter_subset ..).trans (fun _ _ => by aesop)

/--
theorem `balanced_iInter` / 定理 `balanced_iInter`

English:
theorem balanced_iInter
  given: {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i))
  statement: Balanced 𝕜 (⋂ i, f i)
  proof: fun _a ha => (smul_set_iInter_subset _ _).trans iInter_mono fun _ => h _ _ ha

中文:
定理 balanced_i整数er
  条件: {f : ι -> 集合 E} (h : 对任意 i, Balanced 𝕜 (f i))
  结论: Balanced 𝕜 (⋂ i, f i)
  证明: fun _a ha => (smul_set_iInter_subset _ _).trans iInter_mono fun _ => h _ _ ha

Depends on / 依赖: iInter_mono, smul_set_iInter_subset
-/
theorem balanced_iInter {f : ι -> Set E} (h : forall i, Balanced 𝕜 (f i)) : Balanced 𝕜 (⋂ i, f i) :=
fun _a ha => (smul_set_iInter_subset _ _).trans iInter_mono fun _ => h _ _ ha

/--
theorem `balanced_iInter₂` / 定理 `balanced_iInter₂`

English:
theorem balanced_iInter₂
  given: {f : forall i, κ i -> Set E} (h : forall i j, Balanced 𝕜 (f i j))
  proof: balanced_iInter fun _ => balanced_iInter h _

中文:
定理 balanced_i整数er₂
  条件: {f : 对任意 i, κ i -> 集合 E} (h : 对任意 i j, Balanced 𝕜 (f i j))
  证明: balanced_iInter fun _ => balanced_iInter h _

Depends on / 依赖: balanced_iInter
-/
theorem balanced_iInter₂ {f : forall i, κ i -> Set E} (h : forall i j, Balanced 𝕜 (f i j)) :
    Balanced 𝕜 (⋂ (i) (j), f i j) :=
balanced_iInter fun _ => balanced_iInter h _

/--
theorem `Balanced.mulActionHom_preimage` / 定理 `Balanced.mulActionHom_preimage`

English:
theorem Balanced.mulActionHom_preimage
  statement: [SMul 𝕜 F] {s : Set F} (hs : Balanced 𝕜 s)
  proof: fun a ha x ⟨y,⟨hy₁,hy₂⟩⟩ => by
  rw [mem_preimage]; rw [← hy₂]; rw [map_smul]
  exact hs a ha (smul_mem_smul_set hy₁)

中文:
定理 Balanced.mulActionHom_preimage
  结论: [标量乘法 𝕜 F] {s : 集合 F} (hs : Balanced 𝕜 s)
  证明: fun a ha x ⟨y,⟨hy₁,hy₂⟩⟩ => by
  rw [mem_preimage]; rw [← hy₂]; rw [map_smul]
  exact hs a ha (smul_mem_smul_set hy₁)

Depends on / 依赖: map_smul, mem_preimage, smul_mem_smul_set
-/
theorem Balanced.mulActionHom_preimage [SMul 𝕜 F] {s : Set F} (hs : Balanced 𝕜 s)
    (f : E ->[𝕜] F) : Balanced 𝕜 (f ⁻¹' s) := fun a ha x ⟨y,⟨hy₁,hy₂⟩⟩ => by
  rw [mem_preimage]; rw [← hy₂]; rw [map_smul]
  exact hs a ha (smul_mem_smul_set hy₁)

variable [SMul 𝕝 E] [SMulCommClass 𝕜 𝕝 E]

/--
theorem `Balanced.smul` / 定理 `Balanced.smul`

English:
theorem Balanced.smul
  given: (a : 𝕝) (hs : Balanced 𝕜 s)
  statement: Balanced 𝕜 (a • s)
  proof: fun _b hb =>
(smul_comm _ _ _).subset.trans smul_set_mono hs _ hb

中文:
定理 Balanced.smul
  条件: (a : 𝕝) (hs : Balanced 𝕜 s)
  结论: Balanced 𝕜 (a • s)
  证明: fun _b hb =>
(smul_comm _ _ _).subset.trans smul_set_mono hs _ hb
-/
theorem Balanced.smul (a : 𝕝) (hs : Balanced 𝕜 s) : Balanced 𝕜 (a • s) := fun _b hb =>
(smul_comm _ _ _).subset.trans smul_set_mono hs _ hb

end SMul

section Module

variable [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/--
theorem `Balanced.neg` / 定理 `Balanced.neg`

English:
theorem Balanced.neg
  statement: Balanced 𝕜 s -> Balanced 𝕜 (-s)
  proof: forall₂_imp fun _ _ h => (smul_set_neg _ _).subset.trans neg_subset_neg.2 h

@[simp]

中文:
定理 Balanced.neg
  结论: Balanced 𝕜 s -> Balanced 𝕜 (-s)
  证明: forall₂_imp fun _ _ h => (smul_set_neg _ _).subset.trans neg_subset_neg.2 h

@[simp]

Depends on / 依赖: ContinuousInf, HasSolidNorm, HasSolidNorm.continuousInf, continuousInf, continuous_fst, continuous_fst.tendsto, continuous_iff_continuousAt, continuous_snd, continuous_snd.tendsto, convert, neg_subset_neg, norm.add, norm_inf_sub_inf_le_add_norm, norm_nonneg, smul_set_neg, squeeze_zero, subset, subset.trans, tendsto, tendsto_const_nhds
-/
theorem Balanced.neg : Balanced 𝕜 s -> Balanced 𝕜 (-s) :=
forall₂_imp fun _ _ h => (smul_set_neg _ _).subset.trans neg_subset_neg.2 h

@[simp]
/--
theorem `balanced_neg` / 定理 `balanced_neg`

English:
theorem balanced_neg
  statement: Balanced 𝕜 (-s) ↔ Balanced 𝕜 s
  proof: ⟨fun h => neg_neg s ▸ h.neg, fun h => h.neg⟩

中文:
定理 balanced_neg
  结论: Balanced 𝕜 (-s) ↔ Balanced 𝕜 s
  证明: ⟨fun h => neg_neg s ▸ h.neg, fun h => h.neg⟩

Depends on / 依赖: HasSolidNorm, HasSolidNorm.continuousSup, continuousSup, h.neg, neg_neg
-/
theorem balanced_neg : Balanced 𝕜 (-s) ↔ Balanced 𝕜 s :=
  ⟨fun h => neg_neg s ▸ h.neg, fun h => h.neg⟩

/--
theorem `Balanced.neg_mem_iff` / 定理 `Balanced.neg_mem_iff`

English:
theorem Balanced.neg_mem_iff
  given: [NormOneClass 𝕜] (h : Balanced 𝕜 s) {x : E}
  statement: -x in s ↔ x in s
  proof: ⟨fun hx => by simpa using h.smul_mem (a := -1) (by simp) hx,
    fun hx => by simpa using h.smul_mem (a := -1) (by simp) hx⟩

中文:
定理 Balanced.neg_mem_iff
  条件: [NormOne类 𝕜] (h : Balanced 𝕜 s) {x : E}
  结论: -x in s ↔ x in s
  证明: ⟨fun hx => by simpa using h.smul_mem (a := -1) (by simp) hx,
    fun hx => by simpa using h.smul_mem (a := -1) (by simp) hx⟩

Depends on / 依赖: HasSolidNorm, HasSolidNorm.toTopologicalLattice, TopologicalLattice, h.smul_mem, smul_mem, toTopologicalLattice
-/
theorem Balanced.neg_mem_iff [NormOneClass 𝕜] (h : Balanced 𝕜 s) {x : E} : -x in s ↔ x in s :=
  ⟨fun hx => by simpa using h.smul_mem (a := -1) (by simp) hx,
    fun hx => by simpa using h.smul_mem (a := -1) (by simp) hx⟩

/--
theorem `Balanced.neg_eq` / 定理 `Balanced.neg_eq`

English:
theorem Balanced.neg_eq
  given: [NormOneClass 𝕜] (h : Balanced 𝕜 s)
  statement: -s = s
  proof: Set.ext fun _ => h.neg_mem_iff

中文:
定理 Balanced.neg_eq
  条件: [NormOne类 𝕜] (h : Balanced 𝕜 s)
  结论: -s = s
  证明: Set.ext fun _ => h.neg_mem_iff

Depends on / 依赖: Set.ext, h.neg_mem_iff, neg_mem_iff
-/
theorem Balanced.neg_eq [NormOneClass 𝕜] (h : Balanced 𝕜 s) : -s = s :=
  Set.ext fun _ => h.neg_mem_iff

/--
theorem `Balanced.add` / 定理 `Balanced.add`

English:
theorem Balanced.add
  given: (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t)
  statement: Balanced 𝕜 (s + t)
  proof: fun _a ha =>
(smul_add _ _ _).subset.trans add_subset_add (hs _ ha) ht _ ha

中文:
定理 Balanced.add
  条件: (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t)
  结论: Balanced 𝕜 (s + t)
  证明: fun _a ha =>
(smul_add _ _ _).subset.trans add_subset_add (hs _ ha) ht _ ha
-/
theorem Balanced.add (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s + t) := fun _a ha =>
(smul_add _ _ _).subset.trans add_subset_add (hs _ ha) ht _ ha

/--
theorem `Balanced.sub` / 定理 `Balanced.sub`

English:
theorem Balanced.sub
  given: (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t)
  statement: Balanced 𝕜 (s - t)
  proof: by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

中文:
定理 Balanced.sub
  条件: (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t)
  结论: Balanced 𝕜 (s - t)
  证明: by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

Depends on / 依赖: hs.add, ht.neg, simp_rw, sub_eq_add_neg
-/
theorem Balanced.sub (hs : Balanced 𝕜 s) (ht : Balanced 𝕜 t) : Balanced 𝕜 (s - t) := by
  simp_rw [sub_eq_add_neg]
  exact hs.add ht.neg

/--
theorem `balanced_zero` / 定理 `balanced_zero`

English:
theorem balanced_zero
  statement: Balanced 𝕜 (0 : Set E)
  proof: fun _a _ha => (smul_zero _).subset

中文:
定理 balanced_zero
  结论: Balanced 𝕜 (0 : 集合 E)
  证明: fun _a _ha => (smul_zero _).subset

Depends on / 依赖: smul_zero, subset
-/
theorem balanced_zero : Balanced 𝕜 (0 : Set E) := fun _a _ha => (smul_zero _).subset

end Module

end SeminormedRing

section NormedDivisionRing

variable [NormedDivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}

/--
theorem `absorbs_iff_eventually_nhdsNE_zero` / 定理 `absorbs_iff_eventually_nhdsNE_zero`

English:
theorem absorbs_iff_eventually_nhdsNE_zero
  proof: by
  rw [absorbs_iff_eventually_cobounded_mapsTo]; rw [← Filter.inv_cobounded₀]; rfl

alias ⟨Absorbs.eventually_nhdsNE_zero, _⟩ := absorbs_iff_eventually_nhdsNE_zero

中文:
定理 absorbs_iff_eventually_nhdsNE_zero
  证明: by
  rw [absorbs_iff_eventually_cobounded_mapsTo]; rw [← Filter.inv_cobounded₀]; rfl

alias ⟨Absorbs.eventually_nhdsNE_zero, _⟩ := absorbs_iff_eventually_nhdsNE_zero

Depends on / 依赖: Filter, Filter.inv_cobounded, absorbs_iff_eventually_cobounded_mapsTo
-/
theorem absorbs_iff_eventually_nhdsNE_zero :
    Absorbs 𝕜 s t ↔ forallᶠ c : 𝕜 in 𝓝[!=] 0, MapsTo (c • ·) t s := by
  rw [absorbs_iff_eventually_cobounded_mapsTo]; rw [← Filter.inv_cobounded₀]; rfl

alias ⟨Absorbs.eventually_nhdsNE_zero, _⟩ := absorbs_iff_eventually_nhdsNE_zero

/--
theorem `absorbent_iff_eventually_nhdsNE_zero` / 定理 `absorbent_iff_eventually_nhdsNE_zero`

English:
theorem absorbent_iff_eventually_nhdsNE_zero
  proof: forall_congr' fun x => by simp only [absorbs_iff_eventually_nhdsNE_zero, mapsTo_singleton]

alias ⟨Absorbent.eventually_nhdsNE_zero, _⟩ := absorbent_iff_eventually_nhdsNE_zero

中文:
定理 absorbent_iff_eventually_nhdsNE_zero
  证明: forall_congr' fun x => by simp only [absorbs_iff_eventually_nhdsNE_zero, mapsTo_singleton]

alias ⟨Absorbent.eventually_nhdsNE_zero, _⟩ := absorbent_iff_eventually_nhdsNE_zero

Depends on / 依赖: absorbs_iff_eventually_nhdsNE_zero, forall_congr, mapsTo_singleton
-/
theorem absorbent_iff_eventually_nhdsNE_zero :
    Absorbent 𝕜 s ↔ forall x : E, forallᶠ c : 𝕜 in 𝓝[!=] 0, c • x in s :=
  forall_congr' fun x => by simp only [absorbs_iff_eventually_nhdsNE_zero, mapsTo_singleton]

alias ⟨Absorbent.eventually_nhdsNE_zero, _⟩ := absorbent_iff_eventually_nhdsNE_zero

/--
theorem `absorbs_iff_eventually_nhds_zero` / 定理 `absorbs_iff_eventually_nhds_zero`

English:
theorem absorbs_iff_eventually_nhds_zero
  given: (h₀ : 0 in s)
  proof: by
  rw [← nhdsNE_sup_pure]; rw [Filter.eventually_sup]; rw [Filter.eventually_pure]; rw [← absorbs_iff_eventually_nhdsNE_zero]; rw [and_iff_left]
  intro x _
  simpa only [zero_smul]

中文:
定理 absorbs_iff_eventually_nhds_zero
  条件: (h₀ : 0 in s)
  证明: by
  rw [← nhdsNE_sup_pure]; rw [Filter.eventually_sup]; rw [Filter.eventually_pure]; rw [← absorbs_iff_eventually_nhdsNE_zero]; rw [and_iff_left]
  intro x _
  simpa only [zero_smul]

Depends on / 依赖: Filter, Filter.eventually_pure, Filter.eventually_sup, absorbs_iff_eventually_nhdsNE_zero, and_iff_left, eventually_pure, eventually_sup, nhdsNE_sup_pure, zero_smul
-/
theorem absorbs_iff_eventually_nhds_zero (h₀ : 0 in s) :
    Absorbs 𝕜 s t ↔ forallᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s := by
  rw [← nhdsNE_sup_pure]; rw [Filter.eventually_sup]; rw [Filter.eventually_pure]; rw [← absorbs_iff_eventually_nhdsNE_zero]; rw [and_iff_left]
  intro x _
  simpa only [zero_smul]

/--
theorem `Absorbs.eventually_nhds_zero` / 定理 `Absorbs.eventually_nhds_zero`

English:
theorem Absorbs.eventually_nhds_zero
  given: (h : Absorbs 𝕜 s t) (h₀ : 0 in s)
  proof: (absorbs_iff_eventually_nhds_zero h₀).1 h

中文:
定理 Absorbs.eventually_nhds_zero
  条件: (h : Absorbs 𝕜 s t) (h₀ : 0 in s)
  证明: (absorbs_iff_eventually_nhds_zero h₀).1 h

Depends on / 依赖: absorbs_iff_eventually_nhds_zero
-/
theorem Absorbs.eventually_nhds_zero (h : Absorbs 𝕜 s t) (h₀ : 0 in s) :
    forallᶠ c : 𝕜 in 𝓝 0, MapsTo (c • ·) t s :=
  (absorbs_iff_eventually_nhds_zero h₀).1 h

variable [NormedRing 𝕝] [Module 𝕜 𝕝] [NormSMulClass 𝕜 𝕝] [SMulWithZero 𝕝 E] [IsScalarTower 𝕜 𝕝 E]
  {a b : 𝕜} {x : E}

/--
theorem `Balanced.smul_mono` / 定理 `Balanced.smul_mono`

English:
theorem Balanced.smul_mono
  given: (hs : Balanced 𝕝 s) {a : 𝕝} (h : ‖a‖ <= ‖b‖)
  statement: a • s subseteq b • s
  proof: by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero, norm_le_zero_iff] at h
    simp only [h, ← image_smul, zero_smul, Subset.rfl]
  · calc
      a • s = b • (b⁻¹ • a) • s := by rw [smul_assoc, smul_inv_smul₀ hb]
_ subseteq b • s := smul_set_mono hs _ by
        rw [norm_smul]; rw [norm_inv]; rw 

中文:
定理 Balanced.smul_mono
  条件: (hs : Balanced 𝕝 s) {a : 𝕝} (h : ‖a‖ <= ‖b‖)
  结论: a • s subseteq b • s
  证明: by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero, norm_le_zero_iff] at h
    simp only [h, ← image_smul, zero_smul, Subset.rfl]
  · calc
      a • s = b • (b⁻¹ • a) • s := by rw [smul_assoc, smul_inv_smul₀ hb]
_ subseteq b • s := smul_set_mono hs _ by
        rw [norm_smul]; rw [norm_inv]; rw 

Depends on / 依赖: Subset, Subset.rfl, div_eq_inv_mul, eq_or_ne, image_smul, norm_inv, norm_le_zero_iff, norm_nonneg, norm_smul, norm_zero, smul_assoc, smul_set_mono, subseteq, zero_smul
-/
theorem Balanced.smul_mono (hs : Balanced 𝕝 s) {a : 𝕝} (h : ‖a‖ <= ‖b‖) : a • s subseteq b • s := by
  obtain rfl | hb := eq_or_ne b 0
  · rw [norm_zero, norm_le_zero_iff] at h
    simp only [h, ← image_smul, zero_smul, Subset.rfl]
  · calc
      a • s = b • (b⁻¹ • a) • s := by rw [smul_assoc, smul_inv_smul₀ hb]
_ subseteq b • s := smul_set_mono hs _ by
        rw [norm_smul]; rw [norm_inv]; rw [← div_eq_inv_mul]
        exact div_le_one_of_le₀ h (norm_nonneg _)

/--
theorem `Balanced.smul_mem_mono` / 定理 `Balanced.smul_mem_mono`

English:
theorem Balanced.smul_mem_mono
  statement: [SMulCommClass 𝕝 𝕜 E] (hs : Balanced 𝕝 s) {b : 𝕝}
  proof: by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp_all
  · calc
      (a⁻¹ • b) • a • x in s := by
        refine hs.smul_mem ?_ ha
        rw [norm_smul]; rw [norm_inv]; rw [← div_eq_inv_mul]
        exact div_le_one_of_le₀ hba (norm_nonneg _)
      (a⁻¹ • b) • a • x = b • x := by rw [smul_comm, smul

中文:
定理 Balanced.smul_mem_mono
  结论: [标量交换类 𝕝 𝕜 E] (hs : Balanced 𝕝 s) {b : 𝕝}
  证明: by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp_all
  · calc
      (a⁻¹ • b) • a • x in s := by
        refine hs.smul_mem ?_ ha
        rw [norm_smul]; rw [norm_inv]; rw [← div_eq_inv_mul]
        exact div_le_one_of_le₀ hba (norm_nonneg _)
      (a⁻¹ • b) • a • x = b • x := by rw [smul_comm, smul

Depends on / 依赖: div_eq_inv_mul, eq_or_ne, hs.smul_mem, norm_inv, norm_nonneg, norm_smul, smul_assoc, smul_comm, smul_mem
-/
theorem Balanced.smul_mem_mono [SMulCommClass 𝕝 𝕜 E] (hs : Balanced 𝕝 s) {b : 𝕝}
    (ha : a • x in s) (hba : ‖b‖ <= ‖a‖) : b • x in s := by
  rcases eq_or_ne a 0 with rfl | ha₀
  · simp_all
  · calc
      (a⁻¹ • b) • a • x in s := by
        refine hs.smul_mem ?_ ha
        rw [norm_smul]; rw [norm_inv]; rw [← div_eq_inv_mul]
        exact div_le_one_of_le₀ hba (norm_nonneg _)
      (a⁻¹ • b) • a • x = b • x := by rw [smul_comm, smul_assoc, smul_inv_smul₀ ha₀]

/--
theorem `Balanced.subset_smul` / 定理 `Balanced.subset_smul`

English:
theorem Balanced.subset_smul
  given: (hs : Balanced 𝕜 s) (ha : 1 <= ‖a‖)
  statement: s subseteq a • s
  proof: by
  rw [← @norm_one 𝕜] at ha; simpa using hs.smul_mono ha

中文:
定理 Balanced.subset_smul
  条件: (hs : Balanced 𝕜 s) (ha : 1 <= ‖a‖)
  结论: s subseteq a • s
  证明: by
  rw [← @norm_one 𝕜] at ha; simpa using hs.smul_mono ha

Depends on / 依赖: HasSolidNorm, HasSolidNorm.orderClosedTopology, hs.smul_mono, norm_one, orderClosedTopology, smul_mono
-/
theorem Balanced.subset_smul (hs : Balanced 𝕜 s) (ha : 1 <= ‖a‖) : s subseteq a • s := by
  rw [← @norm_one 𝕜] at ha; simpa using hs.smul_mono ha

/--
theorem `Balanced.smul_congr` / 定理 `Balanced.smul_congr`

English:
theorem Balanced.smul_congr
  given: (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖)
  statement: a • s = b • s
  proof: (hs.smul_mono h.le).antisymm (hs.smul_mono h.ge)

中文:
定理 Balanced.smul_congr
  条件: (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖)
  结论: a • s = b • s
  证明: (hs.smul_mono h.le).antisymm (hs.smul_mono h.ge)

Depends on / 依赖: antisymm, h.ge, h.le, hs.smul_mono, smul_mono
-/
theorem Balanced.smul_congr (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • s = b • s :=
  (hs.smul_mono h.le).antisymm (hs.smul_mono h.ge)

/--
theorem `Balanced.smul_eq` / 定理 `Balanced.smul_eq`

English:
theorem Balanced.smul_eq
  given: (hs : Balanced 𝕜 s) (ha : ‖a‖ = 1)
  statement: a • s = s
  proof: (hs _ ha.le).antisymm hs.subset_smul ha.ge

中文:
定理 Balanced.smul_eq
  条件: (hs : Balanced 𝕜 s) (ha : ‖a‖ = 1)
  结论: a • s = s
  证明: (hs _ ha.le).antisymm hs.subset_smul ha.ge

Depends on / 依赖: antisymm, ha.ge, ha.le, hs.subset_smul, subset_smul
-/
theorem Balanced.smul_eq (hs : Balanced 𝕜 s) (ha : ‖a‖ = 1) : a • s = s :=
(hs _ ha.le).antisymm hs.subset_smul ha.ge

/--
theorem `Balanced.absorbs_self` / 定理 `Balanced.absorbs_self`

English:
theorem Balanced.absorbs_self
  given: (hs : Balanced 𝕜 s)
  statement: Absorbs 𝕜 s s
  proof: .of_norm ⟨1, fun _ => hs.subset_smul⟩

中文:
定理 Balanced.absorbs_self
  条件: (hs : Balanced 𝕜 s)
  结论: Absorbs 𝕜 s s
  证明: .of_norm ⟨1, fun _ => hs.subset_smul⟩

Depends on / 依赖: hs.subset_smul, of_norm, subset_smul
-/
theorem Balanced.absorbs_self (hs : Balanced 𝕜 s) : Absorbs 𝕜 s s :=
  .of_norm ⟨1, fun _ => hs.subset_smul⟩

end NormedDivisionRing

section NormedField

variable [NormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s A : Set E} {x : E} {a b : 𝕜}

/--
theorem `Balanced.smul_mem_iff` / 定理 `Balanced.smul_mem_iff`

English:
theorem Balanced.smul_mem_iff
  given: (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖)
  statement: a • x in s ↔ b • x in s
  proof: ⟨(hs.smul_mem_mono · h.ge), (hs.smul_mem_mono · h.le)⟩

中文:
定理 Balanced.smul_mem_iff
  条件: (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖)
  结论: a • x in s ↔ b • x in s
  证明: ⟨(hs.smul_mem_mono · h.ge), (hs.smul_mem_mono · h.le)⟩

Depends on / 依赖: h.ge, h.le, hs.smul_mem_mono, smul_mem_mono
-/
theorem Balanced.smul_mem_iff (hs : Balanced 𝕜 s) (h : ‖a‖ = ‖b‖) : a • x in s ↔ b • x in s :=
  ⟨(hs.smul_mem_mono · h.ge), (hs.smul_mem_mono · h.le)⟩

variable [TopologicalSpace E] [ContinuousSMul 𝕜 E]

/--
theorem `absorbent_nhds_zero` / 定理 `absorbent_nhds_zero`

English:
theorem absorbent_nhds_zero
  given: (hA : A in 𝓝 (0 : E))
  statement: Absorbent 𝕜 A
  proof: absorbent_iff_inv_smul.2 fun _ => Filter.tendsto_inv₀_cobounded.zero_smul_const _ hA

中文:
定理 absorbent_nhds_zero
  条件: (hA : A in 𝓝 (0 : E))
  结论: Absorbent 𝕜 A
  证明: absorbent_iff_inv_smul.2 fun _ => Filter.tendsto_inv₀_cobounded.zero_smul_const _ hA

Depends on / 依赖: Filter, Filter.tendsto_inv, _cobounded.zero_smul_const, absorbent_iff_inv_smul, zero_smul_const
-/
theorem absorbent_nhds_zero (hA : A in 𝓝 (0 : E)) : Absorbent 𝕜 A :=
  absorbent_iff_inv_smul.2 fun _ => Filter.tendsto_inv₀_cobounded.zero_smul_const _ hA

/--
theorem `Balanced.zero_insert_interior` / 定理 `Balanced.zero_insert_interior`

English:
theorem Balanced.zero_insert_interior
  given: (hA : Balanced 𝕜 A)
  proof: by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts [subset_union_left, ⟨0, Or.inl rfl⟩]
  · rw [← image_smul, image_insert_eq, smul_zero]
    apply insert_subset_insert
    exact ((isOpenMap_smul₀ h).mapsTo_interior <| hA.smul_mem ha).image_subset

中文:
定理 Balanced.zero_insert_interior
  条件: (hA : Balanced 𝕜 A)
  证明: by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts [subset_union_left, ⟨0, Or.inl rfl⟩]
  · rw [← image_smul, image_insert_eq, smul_zero]
    apply insert_subset_insert
    exact ((isOpenMap_smul₀ h).mapsTo_interior <| hA.smul_mem ha).image_subset

Depends on / 依赖: Or.inl, eq_or_ne, exacts, hA.smul_mem, image_insert_eq, image_smul, image_subset, insert_subset_insert, mapsTo_interior, smul_mem, smul_zero, subset_union_left, zero_smul_set
-/
theorem Balanced.zero_insert_interior (hA : Balanced 𝕜 A) :
    Balanced 𝕜 (insert 0 (interior A)) := by
  intro a ha
  obtain rfl | h := eq_or_ne a 0
  · rw [zero_smul_set]
    exacts [subset_union_left, ⟨0, Or.inl rfl⟩]
  · rw [← image_smul, image_insert_eq, smul_zero]
    apply insert_subset_insert
    exact ((isOpenMap_smul₀ h).mapsTo_interior <| hA.smul_mem ha).image_subset

/--
theorem `Balanced.interior` / 定理 `Balanced.interior`

English:
theorem Balanced.interior
  given: (hA : Balanced 𝕜 A) (h : (0 : E) in interior A)
  proof: by
  rw [← insert_eq_self.2 h]
  exact hA.zero_insert_interior

中文:
定理 Balanced.interior
  条件: (hA : Balanced 𝕜 A) (h : (0 : E) in interior A)
  证明: by
  rw [← insert_eq_self.2 h]
  exact hA.zero_insert_interior
-/
protected theorem Balanced.interior (hA : Balanced 𝕜 A) (h : (0 : E) in interior A) :
    Balanced 𝕜 (interior A) := by
  rw [← insert_eq_self.2 h]
  exact hA.zero_insert_interior

/--
theorem `Balanced.closure` / 定理 `Balanced.closure`

English:
theorem Balanced.closure
  given: (hA : Balanced 𝕜 A)
  statement: Balanced 𝕜 (closure A)
  proof: fun _a ha =>
(image_closure_subset_closure_image <| continuous_const_smul _).trans
closure_mono hA _ ha

中文:
定理 Balanced.closure
  条件: (hA : Balanced 𝕜 A)
  结论: Balanced 𝕜 (closure A)
  证明: fun _a ha =>
(image_closure_subset_closure_image <| continuous_const_smul _).trans
closure_mono hA _ ha
-/
protected theorem Balanced.closure (hA : Balanced 𝕜 A) : Balanced 𝕜 (closure A) := fun _a ha =>
(image_closure_subset_closure_image <| continuous_const_smul _).trans
closure_mono hA _ ha

end NormedField

section NontriviallyNormedField

variable [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E] {s : Set E}

variable [PartialOrder 𝕜] in
/--
theorem `Balanced.convexHull` / 定理 `Balanced.convexHull`

English:
theorem Balanced.convexHull
  given: (hs : Balanced 𝕜 s)
  statement: Balanced 𝕜 (convexHull 𝕜 s)
  proof: by
  suffices Convex 𝕜 { x | forall a : 𝕜, ‖a‖ <= 1 -> a • x in convexHull 𝕜 s } by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine fun a ha x hx => convexHull_min ?_ this hx a ha
    exact fun y hy a ha => subset_convexHull 𝕜 s (hs ha hy)
  intro x hx y hy u v hu hv huv a ha
  rw [smul_add]; rw [

中文:
定理 Balanced.convexHull
  条件: (hs : Balanced 𝕜 s)
  结论: Balanced 𝕜 (convexHull 𝕜 s)
  证明: by
  suffices Convex 𝕜 { x | forall a : 𝕜, ‖a‖ <= 1 -> a • x in convexHull 𝕜 s } by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine fun a ha x hx => convexHull_min ?_ this hx a ha
    exact fun y hy a ha => subset_convexHull 𝕜 s (hs ha hy)
  intro x hx y hy u v hu hv huv a ha
  rw [smul_add]; rw [
-/
protected theorem Balanced.convexHull (hs : Balanced 𝕜 s) : Balanced 𝕜 (convexHull 𝕜 s) := by
  suffices Convex 𝕜 { x | forall a : 𝕜, ‖a‖ <= 1 -> a • x in convexHull 𝕜 s } by
    rw [balanced_iff_smul_mem] at hs ⊢
    refine fun a ha x hx => convexHull_min ?_ this hx a ha
    exact fun y hy a ha => subset_convexHull 𝕜 s (hs ha hy)
  intro x hx y hy u v hu hv huv a ha
  rw [smul_add]; rw [← smul_comm u]; rw [← smul_comm v]
  exact convex_convexHull 𝕜 s (hx a ha) (hy a ha) hu hv huv

variable {S : Type*} [SetLike S E] [SMulMemClass S 𝕜 E]

/--
theorem `Absorbent.eq_univ_of_smulMemClass` / 定理 `Absorbent.eq_univ_of_smulMemClass`

English:
theorem Absorbent.eq_univ_of_smulMemClass
  given: {V : S} (hV : Absorbent 𝕜 (V : Set E))
  proof: by
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨c, hc, hc'⟩ :=
    ((absorbent_iff_eventually_nhdsNE_zero.mp hV x).and eventually_mem_nhdsWithin).exists
  rw [← inv_smul_smul₀ hc' x]
  exact SMulMemClass.smul_mem c⁻¹ hc

中文:
定理 Absorbent.eq_univ_of_smulMemClass
  条件: {V : S} (hV : Absorbent 𝕜 (V : 集合 E))
  证明: by
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨c, hc, hc'⟩ :=
    ((absorbent_iff_eventually_nhdsNE_zero.mp hV x).and eventually_mem_nhdsWithin).exists
  rw [← inv_smul_smul₀ hc' x]
  exact SMulMemClass.smul_mem c⁻¹ hc

Depends on / 依赖: SMulMemClass, SMulMemClass.smul_mem, absorbent_iff_eventually_nhdsNE_zero, absorbent_iff_eventually_nhdsNE_zero.mp, eq_univ_iff_forall, eventually_mem_nhdsWithin, smul_mem
-/
theorem Absorbent.eq_univ_of_smulMemClass {V : S} (hV : Absorbent 𝕜 (V : Set E)) :
    (V : Set E) = univ := by
  rw [eq_univ_iff_forall]
  intro x
  obtain ⟨c, hc, hc'⟩ :=
    ((absorbent_iff_eventually_nhdsNE_zero.mp hV x).and eventually_mem_nhdsWithin).exists
  rw [← inv_smul_smul₀ hc' x]
  exact SMulMemClass.smul_mem c⁻¹ hc

/--
theorem `Absorbent.submodule_eq_top` / 定理 `Absorbent.submodule_eq_top`

English:
theorem Absorbent.submodule_eq_top
  given: {V : Submodule 𝕜 E} (hV : Absorbent 𝕜 (V : Set E))
  proof: (StrictMono.apply_eq_top_iff (α := Submodule 𝕜 E) (β := Set E) (fun _ _ a_1 => a_1)).mp
  hV.eq_univ_of_smulMemClass

中文:
定理 Absorbent.submodule_eq_top
  条件: {V : 子模 𝕜 E} (hV : Absorbent 𝕜 (V : 集合 E))
  证明: (StrictMono.apply_eq_top_iff (α := Submodule 𝕜 E) (β := Set E) (fun _ _ a_1 => a_1)).mp
  hV.eq_univ_of_smulMemClass

Depends on / 依赖: StrictMono, StrictMono.apply_eq_top_iff, Submodule, apply_eq_top_iff
-/
theorem Absorbent.submodule_eq_top {V : Submodule 𝕜 E} (hV : Absorbent 𝕜 (V : Set E)) :
    V = ⊤ := (StrictMono.apply_eq_top_iff (α := Submodule 𝕜 E) (β := Set E) (fun _ _ a_1 => a_1)).mp
  hV.eq_univ_of_smulMemClass

variable {F 𝕜₂ : Type*} [Semiring 𝕜₂] {σ : 𝕜₂ ->+* 𝕜}
variable [AddCommGroup F] [Module 𝕜₂ F]

/--
theorem `Absorbent.subset_range_iff_surjective` / 定理 `Absorbent.subset_range_iff_surjective`

English:
theorem Absorbent.subset_range_iff_surjective
  statement: [RingHomSurjective σ] {f : F ->ₛₗ[σ] E} {s : Set E}
  proof: ⟨fun hs_sub => LinearMap.range_eq_top.mp ((hs_abs.mono hs_sub).submodule_eq_top), fun h a _ => h a⟩

中文:
定理 Absorbent.subset_range_iff_surjective
  结论: [RingHomSurjective σ] {f : F ->ₛₗ[σ] E} {s : 集合 E}
  证明: ⟨fun hs_sub => LinearMap.range_eq_top.mp ((hs_abs.mono hs_sub).submodule_eq_top), fun h a _ => h a⟩

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mp, hs_abs, hs_abs.mono, hs_sub, range_eq_top, submodule_eq_top
-/
theorem Absorbent.subset_range_iff_surjective [RingHomSurjective σ] {f : F ->ₛₗ[σ] E} {s : Set E}
    (hs_abs : Absorbent 𝕜 s) : s subseteq f.range ↔ (⇑f).Surjective :=
  ⟨fun hs_sub => LinearMap.range_eq_top.mp ((hs_abs.mono hs_sub).submodule_eq_top), fun h a _ => h a⟩

end NontriviallyNormedField

section Real

variable [AddCommGroup E] [Module Real E] {s : Set E}

/--
theorem `balanced_iff_neg_mem` / 定理 `balanced_iff_neg_mem`

English:
theorem balanced_iff_neg_mem
  given: (hs : Convex Real s)
  statement: Balanced Real s ↔ forall ⦃x⦄, x in s -> -x in s
  proof: by
  refine ⟨fun h x => h.neg_mem_iff.2, fun h a ha => smul_set_subset_iff.2 fun x hx => ?_⟩
  rw [Real.norm_eq_abs]; rw [abs_le] at ha
  rw [show a = -((1 - a) / 2) + (a - -1) / 2 by ring]; rw [add_smul]; rw [neg_smul]; rw [← smul_neg]
  exact hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_l

中文:
定理 balanced_iff_neg_mem
  条件: (hs : 凸 实数 s)
  结论: Balanced 实数 s ↔ 对任意 ⦃x⦄, x in s -> -x in s
  证明: by
  refine ⟨fun h x => h.neg_mem_iff.2, fun h a ha => smul_set_subset_iff.2 fun x hx => ?_⟩
  rw [Real.norm_eq_abs]; rw [abs_le] at ha
  rw [show a = -((1 - a) / 2) + (a - -1) / 2 by ring]; rw [add_smul]; rw [neg_smul]; rw [← smul_neg]
  exact hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_l

Depends on / 依赖: Real.norm_eq_abs, abs_le, add_smul, div_nonneg, h.neg_mem_iff, neg_mem_iff, neg_smul, norm_eq_abs, smul_neg, smul_set_subset_iff, sub_nonneg_of_le, zero_le_two
-/
theorem balanced_iff_neg_mem (hs : Convex Real s) : Balanced Real s ↔ forall ⦃x⦄, x in s -> -x in s := by
  refine ⟨fun h x => h.neg_mem_iff.2, fun h a ha => smul_set_subset_iff.2 fun x hx => ?_⟩
  rw [Real.norm_eq_abs]; rw [abs_le] at ha
  rw [show a = -((1 - a) / 2) + (a - -1) / 2 by ring]; rw [add_smul]; rw [neg_smul]; rw [← smul_neg]
  exact hs (h hx) hx (div_nonneg (sub_nonneg_of_le ha.2) zero_le_two)
    (div_nonneg (sub_nonneg_of_le ha.1) zero_le_two) (by ring)

/--
theorem `Balanced.starConvex` / 定理 `Balanced.starConvex`

English:
theorem Balanced.starConvex
  given: (hs : Balanced Real s)
  statement: StarConvex Real 0 s
  proof: starConvex_zero_iff.2 fun _ hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)

中文:
定理 Balanced.starConvex
  条件: (hs : Balanced 实数 s)
  结论: StarConvex 实数 0 s
  证明: starConvex_zero_iff.2 fun _ hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)

Depends on / 依赖: Real.norm_of_nonneg, norm_of_nonneg, smul_mem_smul_set, starConvex_zero_iff
-/
theorem Balanced.starConvex (hs : Balanced Real s) : StarConvex Real 0 s :=
  starConvex_zero_iff.2 fun _ hx a ha₀ ha₁ =>
    hs _ (by rwa [Real.norm_of_nonneg ha₀]) (smul_mem_smul_set hx)

end Real
