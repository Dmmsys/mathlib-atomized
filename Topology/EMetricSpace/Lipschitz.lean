/-
Copyright (c) 2018 Rohan Mitta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rohan Mitta, Kevin Buzzard, Alistair Tucker, Johannes Hölzl, Yury Kudryashov, Winston Yin
-/
module

public import Mathlib.Algebra.Group.End
public import Mathlib.Tactic.Finiteness
public import Mathlib.Topology.EMetricSpace.Diam

/-!
# Lipschitz continuous functions

A map `f : α → β` between two (extended) metric spaces is called *Lipschitz continuous*
with constant `K ≥ 0` if for all `x, y` we have `edist (f x) (f y) ≤ K * edist x y`.
For a metric space, the latter inequality is equivalent to `dist (f x) (f y) ≤ K * dist x y`.
There is also a version asserting this inequality only for `x` and `y` in some set `s`.
Finally, `f : α → β` is called *locally Lipschitz continuous* if each `x : α` has a neighbourhood
on which `f` is Lipschitz continuous (with some constant).

In this file we provide various ways to prove that various combinations of Lipschitz continuous
functions are Lipschitz continuous. We also prove that Lipschitz continuous functions are
uniformly continuous, and that locally Lipschitz functions are continuous.

## Main definitions and lemmas

* `LipschitzWith K f`: states that `f` is Lipschitz with constant `K : ℝ≥0`
* `LipschitzOnWith K f s`: states that `f` is Lipschitz with constant `K : ℝ≥0` on a set `s`
* `LipschitzWith.uniformContinuous`: a Lipschitz function is uniformly continuous
* `LipschitzOnWith.uniformContinuousOn`: a function which is Lipschitz on a set `s` is uniformly
  continuous on `s`.
* `LocallyLipschitz f`: states that `f` is locally Lipschitz
* `LocallyLipschitzOn f s`: states that `f` is locally Lipschitz on `s`.
* `LocallyLipschitz.continuous`: a locally Lipschitz function is continuous.


## Implementation notes

The parameter `K` has type `ℝ≥0`. This way we avoid conjunction in the definition and have
coercions both to `ℝ` and `ℝ≥0∞`. Constructors whose names end with `'` take `K : ℝ` as an
argument, and return `LipschitzWith (Real.toNNReal K) f`.
-/

@[expose] public section

universe u v w x

open Filter Function Set Topology NNReal ENNReal Bornology

variable {α : Type u} {β : Type v} {γ : Type w} {ι : Type x}

section PseudoEMetricSpace
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {K : Real>=0} {s t : Set α} {f : α -> β}

/--
Definition of `LipschitzWith` / `LipschitzWith` 的定义

English:
definition LipschitzWith
  signature: (K : Real>=0) (f : α -> β)
  body: forall x y, edist (f x) (f y) <= K * edist x y

中文:
定义 LipschitzWith
  签名: (K : 实数>=0) (f : α -> β)
  定义体: forall x y, edist (f x) (f y) <= K * edist x y
-/
def LipschitzWith (K : Real>=0) (f : α -> β) := forall x y, edist (f x) (f y) <= K * edist x y

/--
Definition of `LipschitzOnWith` / `LipschitzOnWith` 的定义

English:
definition LipschitzOnWith
  signature: (K : Real>=0) (f : α -> β) (s : Set α)
  body: forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> edist (f x) (f y) <= K * edist x y

中文:
定义 LipschitzOnWith
  签名: (K : 实数>=0) (f : α -> β) (s : Set α)
  定义体: forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> edist (f x) (f y) <= K * edist x y
-/
def LipschitzOnWith (K : Real>=0) (f : α -> β) (s : Set α) :=
  forall ⦃x⦄, x in s -> forall ⦃y⦄, y in s -> edist (f x) (f y) <= K * edist x y

/--
Definition of `LocallyLipschitz` / `LocallyLipschitz` 的定义

English:
definition LocallyLipschitz
  signature: (f : α -> β)
  body: forall x, exists K, exists t in 𝓝 x, LipschitzOnWith K f t

中文:
定义 LocallyLipschitz
  签名: (f : α -> β)
  定义体: forall x, exists K, exists t in 𝓝 x, LipschitzOnWith K f t

Depends on / 依赖: LipschitzOnWith
-/
def LocallyLipschitz (f : α -> β) : Prop := forall x, exists K, exists t in 𝓝 x, LipschitzOnWith K f t

/--
Definition of `LocallyLipschitzOn` / `LocallyLipschitzOn` 的定义

English:
definition LocallyLipschitzOn
  signature: (s : Set α) (f : α -> β)
  body: forall ⦃x⦄, x in s -> exists K, exists t in 𝓝[s] x, LipschitzOnWith K f t

中文:
定义 LocallyLipschitzOn
  签名: (s : Set α) (f : α -> β)
  定义体: forall ⦃x⦄, x in s -> exists K, exists t in 𝓝[s] x, LipschitzOnWith K f t

Depends on / 依赖: LipschitzOnWith
-/
def LocallyLipschitzOn (s : Set α) (f : α -> β) : Prop :=
  forall ⦃x⦄, x in s -> exists K, exists t in 𝓝[s] x, LipschitzOnWith K f t

/-- Every function is Lipschitz on the empty set (with any Lipschitz constant). -/
@[simp]
/--
theorem `lipschitzOnWith_empty` / 定理 `lipschitzOnWith_empty`

English:
theorem lipschitzOnWith_empty
  given: (K : Real>=0) (f : α -> β)
  statement: LipschitzOnWith K f ∅
  proof: fun _ => False.elim

中文:
定理 lipschitzOnWith_empty
  条件: (K : 实数>=0) (f : α -> β)
  结论: LipschitzOnWith K f ∅
  证明: fun _ => False.elim

Depends on / 依赖: False.elim
-/
theorem lipschitzOnWith_empty (K : Real>=0) (f : α -> β) : LipschitzOnWith K f ∅ := fun _ => False.elim

/--
lemma `locallyLipschitzOn_empty` / 引理 `locallyLipschitzOn_empty`

English:
lemma locallyLipschitzOn_empty
  given: (f : α -> β)
  statement: LocallyLipschitzOn ∅ f
  proof: fun _ => False.elim

中文:
引理 locallyLipschitzOn_empty
  条件: (f : α -> β)
  结论: LocallyLipschitzOn ∅ f
  证明: fun _ => False.elim
-/
@[simp] lemma locallyLipschitzOn_empty (f : α -> β) : LocallyLipschitzOn ∅ f := fun _ => False.elim

/--
theorem `LipschitzOnWith.mono` / 定理 `LipschitzOnWith.mono`

English:
theorem LipschitzOnWith.mono
  given: (hf : LipschitzOnWith K f t) (h : s subseteq t)
  statement: LipschitzOnWith K f s
  proof: fun _x x_in _y y_in => hf (h x_in) (h y_in)

中文:
定理 LipschitzOnWith.mono
  条件: (hf : LipschitzOnWith K f t) (h : s subseteq t)
  结论: LipschitzOnWith K f s
  证明: fun _x x_in _y y_in => hf (h x_in) (h y_in)

Depends on / 依赖: x_in, y_in
-/
theorem LipschitzOnWith.mono (hf : LipschitzOnWith K f t) (h : s subseteq t) : LipschitzOnWith K f s :=
  fun _x x_in _y y_in => hf (h x_in) (h y_in)

/--
lemma `LocallyLipschitzOn.mono` / 引理 `LocallyLipschitzOn.mono`

English:
lemma LocallyLipschitzOn.mono
  given: (hf : LocallyLipschitzOn t f) (h : s subseteq t)
  statement: LocallyLipschitzOn s f
  proof: fun x hx => by obtain ⟨K, u, hu, hfu⟩ := hf (h hx); exact ⟨K, u, nhdsWithin_mono _ h hu, hfu⟩

中文:
引理 LocallyLipschitzOn.mono
  条件: (hf : LocallyLipschitzOn t f) (h : s subseteq t)
  结论: LocallyLipschitzOn s f
  证明: fun x hx => by obtain ⟨K, u, hu, hfu⟩ := hf (h hx); exact ⟨K, u, nhdsWithin_mono _ h hu, hfu⟩

Depends on / 依赖: nhdsWithin_mono
-/
lemma LocallyLipschitzOn.mono (hf : LocallyLipschitzOn t f) (h : s subseteq t) : LocallyLipschitzOn s f :=
  fun x hx => by obtain ⟨K, u, hu, hfu⟩ := hf (h hx); exact ⟨K, u, nhdsWithin_mono _ h hu, hfu⟩

/--
lemma `lipschitzOnWith_univ` / 引理 `lipschitzOnWith_univ`

English:
lemma lipschitzOnWith_univ
  statement: LipschitzOnWith K f univ ↔ LipschitzWith K f
  proof: by
  simp [LipschitzOnWith, LipschitzWith]

中文:
引理 lipschitzOnWith_univ
  结论: LipschitzOnWith K f univ ↔ LipschitzWith K f
  证明: by
  simp [LipschitzOnWith, LipschitzWith]
-/
@[simp] lemma lipschitzOnWith_univ : LipschitzOnWith K f univ ↔ LipschitzWith K f := by
  simp [LipschitzOnWith, LipschitzWith]

/--
lemma `locallyLipschitzOn_univ` / 引理 `locallyLipschitzOn_univ`

English:
lemma locallyLipschitzOn_univ
  statement: LocallyLipschitzOn univ f ↔ LocallyLipschitz f
  proof: by
  simp [LocallyLipschitzOn, LocallyLipschitz]

中文:
引理 locallyLipschitzOn_univ
  结论: LocallyLipschitzOn univ f ↔ LocallyLipschitz f
  证明: by
  simp [LocallyLipschitzOn, LocallyLipschitz]
-/
@[simp] lemma locallyLipschitzOn_univ : LocallyLipschitzOn univ f ↔ LocallyLipschitz f := by
  simp [LocallyLipschitzOn, LocallyLipschitz]

/--
lemma `LocallyLipschitz.locallyLipschitzOn` / 引理 `LocallyLipschitz.locallyLipschitzOn`

English:
lemma LocallyLipschitz.locallyLipschitzOn
  given: (h : LocallyLipschitz f)
  proof: (locallyLipschitzOn_univ.2 h).mono s.subset_univ

中文:
引理 LocallyLipschitz.locallyLipschitzOn
  条件: (h : LocallyLipschitz f)
  证明: (locallyLipschitzOn_univ.2 h).mono s.subset_univ
-/
protected lemma LocallyLipschitz.locallyLipschitzOn (h : LocallyLipschitz f) :
    LocallyLipschitzOn s f := (locallyLipschitzOn_univ.2 h).mono s.subset_univ

/--
theorem `lipschitzOnWith_iff_restrict` / 定理 `lipschitzOnWith_iff_restrict`

English:
theorem lipschitzOnWith_iff_restrict
  proof: by
  simp [LipschitzOnWith, LipschitzWith]

中文:
定理 lipschitzOnWith_iff_restrict
  证明: by
  simp [LipschitzOnWith, LipschitzWith]

Depends on / 依赖: LipschitzOnWith, LipschitzWith
-/
theorem lipschitzOnWith_iff_restrict :
    LipschitzOnWith K f s ↔ LipschitzWith K (s.domRestrict f) := by
  simp [LipschitzOnWith, LipschitzWith]

/--
lemma `lipschitzOnWith_restrict` / 引理 `lipschitzOnWith_restrict`

English:
lemma lipschitzOnWith_restrict
  given: {t : Set s}
  proof: by
  simp [LipschitzOnWith]

中文:
引理 lipschitzOnWith_restrict
  条件: {t : Set s}
  证明: by
  simp [LipschitzOnWith]

Depends on / 依赖: LipschitzOnWith
-/
lemma lipschitzOnWith_restrict {t : Set s} :
    LipschitzOnWith K (s.domRestrict f) t ↔ LipschitzOnWith K f (s inter Subtype.val '' t) := by
  simp [LipschitzOnWith]

/--
lemma `locallyLipschitzOn_iff_restrict` / 引理 `locallyLipschitzOn_iff_restrict`

English:
lemma locallyLipschitzOn_iff_restrict
  proof: by
  simp only [LocallyLipschitzOn, LocallyLipschitz, SetCoe.forall',
    lipschitzOnWith_restrict,
    nhds_subtype_eq_comap_nhdsWithin, mem_comap]
  congr! with x K
  constructor
  · rintro ⟨t, ht, hft⟩
exact ⟨_, ⟨t, ht, Subset.rfl⟩, hft.mono inter_subset_right.trans image_preimage_subset ..⟩
  · 

中文:
引理 locallyLipschitzOn_iff_restrict
  证明: by
  simp only [LocallyLipschitzOn, LocallyLipschitz, SetCoe.forall',
    lipschitzOnWith_restrict,
    nhds_subtype_eq_comap_nhdsWithin, mem_comap]
  congr! with x K
  constructor
  · rintro ⟨t, ht, hft⟩
exact ⟨_, ⟨t, ht, Subset.rfl⟩, hft.mono inter_subset_right.trans image_preimage_subset ..⟩
  · 

Depends on / 依赖: Filter, Filter.inter_mem, LocallyLipschitz, LocallyLipschitzOn, SetCoe, SetCoe.forall, Subset, Subset.rfl, hft.mono, image_preimage_subset, inter_mem, inter_subset_right, inter_subset_right.trans, lipschitzOnWith_restrict, mem_comap, nhds_subtype_eq_comap_nhdsWithin, self_mem_nhdsWithin
-/
lemma locallyLipschitzOn_iff_restrict :
    LocallyLipschitzOn s f ↔ LocallyLipschitz (s.domRestrict f) := by
  simp only [LocallyLipschitzOn, LocallyLipschitz, SetCoe.forall',
    lipschitzOnWith_restrict,
    nhds_subtype_eq_comap_nhdsWithin, mem_comap]
  congr! with x K
  constructor
  · rintro ⟨t, ht, hft⟩
exact ⟨_, ⟨t, ht, Subset.rfl⟩, hft.mono inter_subset_right.trans image_preimage_subset ..⟩
  · rintro ⟨t, ⟨u, hu, hut⟩, hft⟩
    exact ⟨s inter u, Filter.inter_mem self_mem_nhdsWithin hu,
      hft.mono fun x hx => ⟨hx.1, ⟨x, hx.1⟩, hut hx.2, rfl⟩⟩

alias ⟨LipschitzOnWith.to_restrict, _⟩ := lipschitzOnWith_iff_restrict
alias ⟨LocallyLipschitzOn.restrict, _⟩ := locallyLipschitzOn_iff_restrict

/--
lemma `Set.MapsTo.lipschitzOnWith_iff_restrict` / 引理 `Set.MapsTo.lipschitzOnWith_iff_restrict`

English:
lemma Set.MapsTo.lipschitzOnWith_iff_restrict
  given: {t : Set β} (h : MapsTo f s t)
  proof: _root_.lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.mapsToRestrict, _⟩ := Set.MapsTo.lipschitzOnWith_iff_restrict

中文:
引理 Set.MapsTo.lipschitzOnWith_iff_restrict
  条件: {t : Set β} (h : MapsTo f s t)
  证明: _root_.lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.mapsToRestrict, _⟩ := Set.MapsTo.lipschitzOnWith_iff_restrict

Depends on / 依赖: _root_, _root_.lipschitzOnWith_iff_restrict, lipschitzOnWith_iff_restrict
-/
lemma Set.MapsTo.lipschitzOnWith_iff_restrict {t : Set β} (h : MapsTo f s t) :
    LipschitzOnWith K f s ↔ LipschitzWith K (h.restrict f s t) :=
  _root_.lipschitzOnWith_iff_restrict

alias ⟨LipschitzOnWith.mapsToRestrict, _⟩ := Set.MapsTo.lipschitzOnWith_iff_restrict

end PseudoEMetricSpace

namespace LipschitzWith

open Metric

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : Real>=0} {f : α -> β} {x y : α} {r : Real>=0∞} {s : Set α}

/--
theorem `lipschitzOnWith` / 定理 `lipschitzOnWith`

English:
theorem lipschitzOnWith
  given: (h : LipschitzWith K f)
  statement: LipschitzOnWith K f s
  proof: fun x _ y _ => h x y

中文:
定理 lipschitzOnWith
  条件: (h : LipschitzWith K f)
  结论: LipschitzOnWith K f s
  证明: fun x _ y _ => h x y
-/
protected theorem lipschitzOnWith (h : LipschitzWith K f) : LipschitzOnWith K f s :=
  fun x _ y _ => h x y

/--
theorem `edist_le_mul` / 定理 `edist_le_mul`

English:
theorem edist_le_mul
  given: (h : LipschitzWith K f) (x y : α)
  statement: edist (f x) (f y) <= K * edist x y
  proof: h x y

中文:
定理 edist_le_mul
  条件: (h : LipschitzWith K f) (x y : α)
  结论: edist (f x) (f y) <= K * edist x y
  证明: h x y
-/
theorem edist_le_mul (h : LipschitzWith K f) (x y : α) : edist (f x) (f y) <= K * edist x y :=
  h x y

/--
theorem `edist_le_mul_of_le` / 定理 `edist_le_mul_of_le`

English:
theorem edist_le_mul_of_le
  given: (h : LipschitzWith K f) (hr : edist x y <= r)
  proof: (h x y).trans mul_right_mono hr

中文:
定理 edist_le_mul_of_le
  条件: (h : LipschitzWith K f) (hr : edist x y <= r)
  证明: (h x y).trans mul_right_mono hr

Depends on / 依赖: mul_right_mono
-/
theorem edist_le_mul_of_le (h : LipschitzWith K f) (hr : edist x y <= r) :
    edist (f x) (f y) <= K * r :=
(h x y).trans mul_right_mono hr

/--
theorem `edist_lt_mul_of_lt` / 定理 `edist_lt_mul_of_lt`

English:
theorem edist_lt_mul_of_lt
  given: (h : LipschitzWith K f) (hK : K != 0) (hr : edist x y < r)
  proof: by grw [h x y]; gcongr; simp

中文:
定理 edist_lt_mul_of_lt
  条件: (h : LipschitzWith K f) (hK : K != 0) (hr : edist x y < r)
  证明: by grw [h x y]; gcongr; simp
-/
theorem edist_lt_mul_of_lt (h : LipschitzWith K f) (hK : K != 0) (hr : edist x y < r) :
    edist (f x) (f y) < K * r := by grw [h x y]; gcongr; simp

/--
theorem `mapsTo_closedEBall` / 定理 `mapsTo_closedEBall`

English:
theorem mapsTo_closedEBall
  given: (h : LipschitzWith K f) (x : α) (r : Real>=0∞)
  proof: fun _y hy => h.edist_le_mul_of_le hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

中文:
定理 mapsTo_closedEBall
  条件: (h : LipschitzWith K f) (x : α) (r : 实数>=0∞)
  证明: fun _y hy => h.edist_le_mul_of_le hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

Depends on / 依赖: edist_le_mul_of_le, h.edist_le_mul_of_le
-/
theorem mapsTo_closedEBall (h : LipschitzWith K f) (x : α) (r : Real>=0∞) :
    MapsTo f (closedEBall x r) (closedEBall (f x) (K * r)) := fun _y hy => h.edist_le_mul_of_le hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_closedBall := mapsTo_closedEBall

/--
theorem `mapsTo_eball` / 定理 `mapsTo_eball`

English:
theorem mapsTo_eball
  given: (h : LipschitzWith K f) (hK : K != 0) (x : α) (r : Real>=0∞)
  proof: fun _y hy => h.edist_lt_mul_of_lt hK hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

中文:
定理 mapsTo_eball
  条件: (h : LipschitzWith K f) (hK : K != 0) (x : α) (r : 实数>=0∞)
  证明: fun _y hy => h.edist_lt_mul_of_lt hK hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

Depends on / 依赖: edist_lt_mul_of_lt, h.edist_lt_mul_of_lt
-/
theorem mapsTo_eball (h : LipschitzWith K f) (hK : K != 0) (x : α) (r : Real>=0∞) :
    MapsTo f (eball x r) (eball (f x) (K * r)) := fun _y hy => h.edist_lt_mul_of_lt hK hy

@[deprecated (since := "2026-01-24")]
alias mapsTo_emetric_ball := mapsTo_eball

/--
theorem `edist_lt_top` / 定理 `edist_lt_top`

English:
theorem edist_lt_top
  given: (hf : LipschitzWith K f) {x y : α} (h : edist x y != ⊤)
  proof: (hf x y).trans_lt (by finiteness)

中文:
定理 edist_lt_top
  条件: (hf : LipschitzWith K f) {x y : α} (h : edist x y != ⊤)
  证明: (hf x y).trans_lt (by finiteness)

Depends on / 依赖: finiteness, trans_lt
-/
theorem edist_lt_top (hf : LipschitzWith K f) {x y : α} (h : edist x y != ⊤) :
    edist (f x) (f y) < ⊤ :=
  (hf x y).trans_lt (by finiteness)

/--
theorem `mul_edist_le` / 定理 `mul_edist_le`

English:
theorem mul_edist_le
  given: (h : LipschitzWith K f) (x y : α)
  proof: by
  rw [mul_comm]; rw [← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (h x y)

中文:
定理 mul_edist_le
  条件: (h : LipschitzWith K f) (x y : α)
  证明: by
  rw [mul_comm]; rw [← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (h x y)

Depends on / 依赖: ENNReal, ENNReal.div_le_of_le_mul, div_eq_mul_inv, div_le_of_le_mul, mul_comm
-/
theorem mul_edist_le (h : LipschitzWith K f) (x y : α) :
    (K⁻¹ : Real>=0∞) * edist (f x) (f y) <= edist x y := by
  rw [mul_comm]; rw [← div_eq_mul_inv]
  exact ENNReal.div_le_of_le_mul' (h x y)

/--
theorem `of_edist_le` / 定理 `of_edist_le`

English:
theorem of_edist_le
  given: (h : forall x y, edist (f x) (f y) <= edist x y)
  statement: LipschitzWith 1 f
  proof: fun x y => by simp only [ENNReal.coe_one, one_mul, h]

中文:
定理 of_edist_le
  条件: (h : 对任意 x y, edist (f x) (f y) <= edist x y)
  结论: LipschitzWith 1 f
  证明: fun x y => by simp only [ENNReal.coe_one, one_mul, h]
-/
protected theorem of_edist_le (h : forall x y, edist (f x) (f y) <= edist x y) : LipschitzWith 1 f :=
  fun x y => by simp only [ENNReal.coe_one, one_mul, h]

/--
theorem `weaken` / 定理 `weaken`

English:
theorem weaken
  given: (hf : LipschitzWith K f) {K' : Real>=0} (h : K <= K')
  statement: LipschitzWith K' f
  proof: fun x y => le_trans (hf x y) mul_left_mono (ENNReal.coe_le_coe.2 h)

中文:
定理 weaken
  条件: (hf : LipschitzWith K f) {K' : 实数>=0} (h : K <= K')
  结论: LipschitzWith K' f
  证明: fun x y => le_trans (hf x y) mul_left_mono (ENNReal.coe_le_coe.2 h)
-/
protected theorem weaken (hf : LipschitzWith K f) {K' : Real>=0} (h : K <= K') : LipschitzWith K' f :=
fun x y => le_trans (hf x y) mul_left_mono (ENNReal.coe_le_coe.2 h)

/--
theorem `ediam_image_le` / 定理 `ediam_image_le`

English:
theorem ediam_image_le
  given: (hf : LipschitzWith K f) (s : Set α)
  proof: by
  apply Metric.ediam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (Metric.edist_le_ediam_of_mem hx hy)

中文:
定理 ediam_image_le
  条件: (hf : LipschitzWith K f) (s : Set α)
  证明: by
  apply Metric.ediam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (Metric.edist_le_ediam_of_mem hx hy)

Depends on / 依赖: Metric, Metric.ediam_le, Metric.edist_le_ediam_of_mem, ediam_le, edist_le_ediam_of_mem, edist_le_mul_of_le, hf.edist_le_mul_of_le
-/
theorem ediam_image_le (hf : LipschitzWith K f) (s : Set α) :
    Metric.ediam (f '' s) <= K * Metric.ediam s := by
  apply Metric.ediam_le
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact hf.edist_le_mul_of_le (Metric.edist_le_ediam_of_mem hx hy)

/--
theorem `edist_lt_of_edist_lt_div` / 定理 `edist_lt_of_edist_lt_div`

English:
theorem edist_lt_of_edist_lt_div
  statement: (hf : LipschitzWith K f) {x y : α} {d : Real>=0∞}
  proof: calc
    edist (f x) (f y) <= K * edist x y := hf x y
    _ < d := ENNReal.mul_lt_of_lt_div' h

中文:
定理 edist_lt_of_edist_lt_div
  结论: (hf : LipschitzWith K f) {x y : α} {d : 实数>=0∞}
  证明: calc
    edist (f x) (f y) <= K * edist x y := hf x y
    _ < d := ENNReal.mul_lt_of_lt_div' h

Depends on / 依赖: ENNReal, ENNReal.mul_lt_of_lt_div, mul_lt_of_lt_div
-/
theorem edist_lt_of_edist_lt_div (hf : LipschitzWith K f) {x y : α} {d : Real>=0∞}
    (h : edist x y < d / K) : edist (f x) (f y) < d :=
  calc
    edist (f x) (f y) <= K * edist x y := hf x y
    _ < d := ENNReal.mul_lt_of_lt_div' h

/--
theorem `uniformContinuous` / 定理 `uniformContinuous`

English:
theorem uniformContinuous
  given: (hf : LipschitzWith K f)
  statement: UniformContinuous f
  proof: EMetric.uniformContinuous_iff.2 fun ε εpos =>
    ⟨ε / K, ENNReal.div_pos_iff.2 ⟨ne_of_gt εpos, ENNReal.coe_ne_top⟩, hf.edist_lt_of_edist_lt_div⟩

中文:
定理 uniformContinuous
  条件: (hf : LipschitzWith K f)
  结论: UniformContinuous f
  证明: EMetric.uniformContinuous_iff.2 fun ε εpos =>
    ⟨ε / K, ENNReal.div_pos_iff.2 ⟨ne_of_gt εpos, ENNReal.coe_ne_top⟩, hf.edist_lt_of_edist_lt_div⟩
-/
protected theorem uniformContinuous (hf : LipschitzWith K f) : UniformContinuous f :=
  EMetric.uniformContinuous_iff.2 fun ε εpos =>
    ⟨ε / K, ENNReal.div_pos_iff.2 ⟨ne_of_gt εpos, ENNReal.coe_ne_top⟩, hf.edist_lt_of_edist_lt_div⟩

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: (hf : LipschitzWith K f)
  statement: Continuous f
  proof: hf.uniformContinuous.continuous

中文:
定理 continuous
  条件: (hf : LipschitzWith K f)
  结论: Continuous f
  证明: hf.uniformContinuous.continuous
-/
protected theorem continuous (hf : LipschitzWith K f) : Continuous f :=
  hf.uniformContinuous.continuous

/--
theorem `const` / 定理 `const`

English:
theorem const
  given: (b : β)
  statement: LipschitzWith 0 fun _ : α => b
  proof: fun x y => by
  simp only [edist_self, zero_le]

中文:
定理 const
  条件: (b : β)
  结论: LipschitzWith 0 fun _ : α => b
  证明: fun x y => by
  simp only [edist_self, zero_le]
-/
protected theorem const (b : β) : LipschitzWith 0 fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

/--
theorem `const'` / 定理 `const'`

English:
theorem const'
  given: (b : β) {K : Real>=0}
  statement: LipschitzWith K fun _ : α => b
  proof: fun x y => by
  simp only [edist_self, zero_le]

@[simp]

中文:
定理 const'
  条件: (b : β) {K : 实数>=0}
  结论: LipschitzWith K fun _ : α => b
  证明: fun x y => by
  simp only [edist_self, zero_le]

@[simp]
-/
protected theorem const' (b : β) {K : Real>=0} : LipschitzWith K fun _ : α => b := fun x y => by
  simp only [edist_self, zero_le]

@[simp]
/--
lemma `zero_iff` / 引理 `zero_iff`

English:
lemma zero_iff
  given: {β : Type*} [EMetricSpace β] (f : α -> β)
  statement: LipschitzWith 0 f ↔ forall x y, f x = f y
  proof: by
  simp [LipschitzWith]

中文:
引理 zero_iff
  条件: {β : 类型} [EMetricSpace β] (f : α -> β)
  结论: LipschitzWith 0 f ↔ 对任意 x y, f x = f y
  证明: by
  simp [LipschitzWith]

Depends on / 依赖: LipschitzWith
-/
lemma zero_iff {β : Type*} [EMetricSpace β] (f : α -> β) : LipschitzWith 0 f ↔ forall x y, f x = f y := by
  simp [LipschitzWith]

/--
theorem `id` / 定理 `id`

English:
theorem id
  statement: LipschitzWith 1 (@id α)
  proof: LipschitzWith.of_edist_le fun _ _ => le_rfl

中文:
定理 id
  结论: LipschitzWith 1 (@id α)
  证明: LipschitzWith.of_edist_le fun _ _ => le_rfl
-/
protected theorem id : LipschitzWith 1 (@id α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl

/--
theorem `subtype_val` / 定理 `subtype_val`

English:
theorem subtype_val
  given: (s : Set α)
  statement: LipschitzWith 1 (Subtype.val : s -> α)
  proof: LipschitzWith.of_edist_le fun _ _ => le_rfl

中文:
定理 subtype_val
  条件: (s : Set α)
  结论: LipschitzWith 1 (Subtype.val : s -> α)
  证明: LipschitzWith.of_edist_le fun _ _ => le_rfl
-/
protected theorem subtype_val (s : Set α) : LipschitzWith 1 (Subtype.val : s -> α) :=
  LipschitzWith.of_edist_le fun _ _ => le_rfl

/--
theorem `subtype_mk` / 定理 `subtype_mk`

English:
theorem subtype_mk
  given: (hf : LipschitzWith K f) {p : β -> Prop} (hp : forall x, p (f x))
  proof: hf

中文:
定理 subtype_mk
  条件: (hf : LipschitzWith K f) {p : β -> 命题} (hp : 对任意 x, p (f x))
  证明: hf
-/
theorem subtype_mk (hf : LipschitzWith K f) {p : β -> Prop} (hp : forall x, p (f x)) :
    LipschitzWith K (fun x => ⟨f x, hp x⟩ : α -> { y // p y }) :=
  hf

/--
theorem `eval` / 定理 `eval`

English:
theorem eval
  given: {α : ι -> Type u} [forall i, PseudoEMetricSpace (α i)] [Fintype ι] (i : ι)
  proof: LipschitzWith.of_edist_le fun f g => by convert! edist_le_pi_edist f g i

中文:
定理 eval
  条件: {α : ι -> 类型u} [对任意 i, PseudoEMetricSpace (α i)] [Fintype ι] (i : ι)
  证明: LipschitzWith.of_edist_le fun f g => by convert! edist_le_pi_edist f g i
-/
protected theorem eval {α : ι -> Type u} [forall i, PseudoEMetricSpace (α i)] [Fintype ι] (i : ι) :
    LipschitzWith 1 (Function.eval i : (forall i, α i) -> α i) :=
  LipschitzWith.of_edist_le fun f g => by convert! edist_le_pi_edist f g i

/--
theorem `restrict` / 定理 `restrict`

English:
theorem restrict
  given: (hf : LipschitzWith K f) (s : Set α)
  proof: fun x y => hf x y

中文:
定理 restrict
  条件: (hf : LipschitzWith K f) (s : Set α)
  证明: fun x y => hf x y
-/
protected theorem restrict (hf : LipschitzWith K f) (s : Set α) :
    LipschitzWith K (s.domRestrict f) := fun x y => hf x y

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {Kf Kg : Real>=0} {f : β -> γ} {g : α -> β} (hf : LipschitzWith Kf f)
  proof: fun x y =>
  calc
    edist (f (g x)) (f (g y)) <= Kf * edist (g x) (g y) := hf _ _
    _ <= Kf * (Kg * edist x y) := mul_right_mono (hg _ _)
    _ = (Kf * Kg : Real>=0) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]

中文:
定理 comp
  结论: {Kf Kg : 实数>=0} {f : β -> γ} {g : α -> β} (hf : LipschitzWith Kf f)
  证明: fun x y =>
  calc
    edist (f (g x)) (f (g y)) <= Kf * edist (g x) (g y) := hf _ _
    _ <= Kf * (Kg * edist x y) := mul_right_mono (hg _ _)
    _ = (Kf * Kg : Real>=0) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]
-/
protected theorem comp {Kf Kg : Real>=0} {f : β -> γ} {g : α -> β} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f ∘ g) := fun x y =>
  calc
    edist (f (g x)) (f (g y)) <= Kf * edist (g x) (g y) := hf _ _
    _ <= Kf * (Kg * edist x y) := mul_right_mono (hg _ _)
    _ = (Kf * Kg : Real>=0) * edist x y := by rw [← mul_assoc, ENNReal.coe_mul]

/--
theorem `comp_lipschitzOnWith` / 定理 `comp_lipschitzOnWith`

English:
theorem comp_lipschitzOnWith
  statement: {Kf Kg : Real>=0} {f : β -> γ} {g : α -> β} {s : Set α}
  proof: lipschitzOnWith_iff_restrict.mpr hf.comp hg.to_restrict

中文:
定理 comp_lipschitzOnWith
  结论: {Kf Kg : 实数>=0} {f : β -> γ} {g : α -> β} {s : Set α}
  证明: lipschitzOnWith_iff_restrict.mpr hf.comp hg.to_restrict

Depends on / 依赖: hf.comp, hg.to_restrict, lipschitzOnWith_iff_restrict, lipschitzOnWith_iff_restrict.mpr, to_restrict
-/
theorem comp_lipschitzOnWith {Kf Kg : Real>=0} {f : β -> γ} {g : α -> β} {s : Set α}
    (hf : LipschitzWith Kf f) (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (Kf * Kg) (f ∘ g) s :=
lipschitzOnWith_iff_restrict.mpr hf.comp hg.to_restrict

/--
theorem `prod_fst` / 定理 `prod_fst`

English:
theorem prod_fst
  statement: LipschitzWith 1 (@Prod.fst α β)
  proof: LipschitzWith.of_edist_le fun _ _ => le_max_left _ _

中文:
定理 prod_fst
  结论: LipschitzWith 1 (@Prod.fst α β)
  证明: LipschitzWith.of_edist_le fun _ _ => le_max_left _ _
-/
protected theorem prod_fst : LipschitzWith 1 (@Prod.fst α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_left _ _

/--
theorem `prod_snd` / 定理 `prod_snd`

English:
theorem prod_snd
  statement: LipschitzWith 1 (@Prod.snd α β)
  proof: LipschitzWith.of_edist_le fun _ _ => le_max_right _ _

中文:
定理 prod_snd
  结论: LipschitzWith 1 (@Prod.snd α β)
  证明: LipschitzWith.of_edist_le fun _ _ => le_max_right _ _
-/
protected theorem prod_snd : LipschitzWith 1 (@Prod.snd α β) :=
  LipschitzWith.of_edist_le fun _ _ => le_max_right _ _

/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  statement: {f : α -> β} {Kf : Real>=0} (hf : LipschitzWith Kf f) {g : α -> γ} {Kg : Real>=0}
  proof: by
  intro x y
  rw [ENNReal.coe_mono.map_max]; rw [Prod.edist_eq]; rw [max_mul]
  exact max_le_max (hf x y) (hg x y)

中文:
定理 prodMk
  结论: {f : α -> β} {Kf : 实数>=0} (hf : LipschitzWith Kf f) {g : α -> γ} {Kg : 实数>=0}
  证明: by
  intro x y
  rw [ENNReal.coe_mono.map_max]; rw [Prod.edist_eq]; rw [max_mul]
  exact max_le_max (hf x y) (hg x y)
-/
protected theorem prodMk {f : α -> β} {Kf : Real>=0} (hf : LipschitzWith Kf f) {g : α -> γ} {Kg : Real>=0}
    (hg : LipschitzWith Kg g) : LipschitzWith (max Kf Kg) fun x => (f x, g x) := by
  intro x y
  rw [ENNReal.coe_mono.map_max]; rw [Prod.edist_eq]; rw [max_mul]
  exact max_le_max (hf x y) (hg x y)

/--
theorem `prodMk_left` / 定理 `prodMk_left`

English:
theorem prodMk_left
  given: (a : α)
  statement: LipschitzWith 1 (Prod.mk a : β -> α × β)
  proof: by
  simpa only [max_eq_right zero_le_one] using! (LipschitzWith.const a).prodMk LipschitzWith.id

中文:
定理 prodMk_left
  条件: (a : α)
  结论: LipschitzWith 1 (Prod.mk a : β -> α × β)
  证明: by
  simpa only [max_eq_right zero_le_one] using! (LipschitzWith.const a).prodMk LipschitzWith.id
-/
protected theorem prodMk_left (a : α) : LipschitzWith 1 (Prod.mk a : β -> α × β) := by
  simpa only [max_eq_right zero_le_one] using! (LipschitzWith.const a).prodMk LipschitzWith.id

/--
theorem `prodMk_right` / 定理 `prodMk_right`

English:
theorem prodMk_right
  given: (b : β)
  statement: LipschitzWith 1 fun a : α => (a, b)
  proof: by
  simpa only [max_eq_left zero_le_one] using! LipschitzWith.id.prodMk (LipschitzWith.const b)

中文:
定理 prodMk_right
  条件: (b : β)
  结论: LipschitzWith 1 fun a : α => (a, b)
  证明: by
  simpa only [max_eq_left zero_le_one] using! LipschitzWith.id.prodMk (LipschitzWith.const b)
-/
protected theorem prodMk_right (b : β) : LipschitzWith 1 fun a : α => (a, b) := by
  simpa only [max_eq_left zero_le_one] using! LipschitzWith.id.prodMk (LipschitzWith.const b)

/--
theorem `uncurry` / 定理 `uncurry`

English:
theorem uncurry
  statement: {f : α -> β -> γ} {Kα Kβ : Real>=0} (hα : forall b, LipschitzWith Kα fun a => f a b)
  proof: by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [Function.uncurry, ENNReal.coe_add, add_mul]
  apply le_trans (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_trans (hα _ _ _) <| mul_right_mono <| le_max_left _ _)
      (le_trans (hβ _ _ _) <| mul_right_mono <| le_max_right _ _)

中文:
定理 uncurry
  结论: {f : α -> β -> γ} {Kα Kβ : 实数>=0} (hα : 对任意 b, LipschitzWith Kα fun a => f a b)
  证明: by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [Function.uncurry, ENNReal.coe_add, add_mul]
  apply le_trans (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_trans (hα _ _ _) <| mul_right_mono <| le_max_left _ _)
      (le_trans (hβ _ _ _) <| mul_right_mono <| le_max_right _ _)
-/
protected theorem uncurry {f : α -> β -> γ} {Kα Kβ : Real>=0} (hα : forall b, LipschitzWith Kα fun a => f a b)
    (hβ : forall a, LipschitzWith Kβ (f a)) : LipschitzWith (Kα + Kβ) (Function.uncurry f) := by
  rintro ⟨a₁, b₁⟩ ⟨a₂, b₂⟩
  simp only [Function.uncurry, ENNReal.coe_add, add_mul]
  apply le_trans (edist_triangle _ (f a₂ b₁) _)
  exact
    add_le_add (le_trans (hα _ _ _) <| mul_right_mono <| le_max_left _ _)
      (le_trans (hβ _ _ _) <| mul_right_mono <| le_max_right _ _)

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: {f : α -> α} (hf : LipschitzWith K f)
  statement: forall n, LipschitzWith (K ^ n) f^[n]

中文:
定理 iterate
  条件: {f : α -> α} (hf : LipschitzWith K f)
  结论: 对任意 n, LipschitzWith (K ^ n) f^[n]
-/
protected theorem iterate {f : α -> α} (hf : LipschitzWith K f) : forall n, LipschitzWith (K ^ n) f^[n]
  | 0 => by simpa only [pow_zero] using! LipschitzWith.id
  | n + 1 => by rw [pow_succ]; exact (LipschitzWith.iterate hf n).comp hf

/--
theorem `edist_iterate_succ_le_geometric` / 定理 `edist_iterate_succ_le_geometric`

English:
theorem edist_iterate_succ_le_geometric
  given: {f : α -> α} (hf : LipschitzWith K f) (x n)
  proof: by
  rw [iterate_succ]; rw [mul_comm]
  simpa only [ENNReal.coe_pow] using! (hf.iterate n) x (f x)

中文:
定理 edist_iterate_succ_le_geometric
  条件: {f : α -> α} (hf : LipschitzWith K f) (x n)
  证明: by
  rw [iterate_succ]; rw [mul_comm]
  simpa only [ENNReal.coe_pow] using! (hf.iterate n) x (f x)

Depends on / 依赖: ENNReal, ENNReal.coe_pow, coe_pow, hf.iterate, iterate, iterate_succ, mul_comm
-/
theorem edist_iterate_succ_le_geometric {f : α -> α} (hf : LipschitzWith K f) (x n) :
    edist (f^[n] x) (f^[n + 1] x) <= edist x (f x) * (K : Real>=0∞) ^ n := by
  rw [iterate_succ]; rw [mul_comm]
  simpa only [ENNReal.coe_pow] using! (hf.iterate n) x (f x)

/--
theorem `mul_end` / 定理 `mul_end`

English:
theorem mul_end
  statement: {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f)
  proof: hf.comp hg

中文:
定理 mul_end
  结论: {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f)
  证明: hf.comp hg
-/
protected theorem mul_end {f g : Function.End α} {Kf Kg} (hf : LipschitzWith Kf f)
    (hg : LipschitzWith Kg g) : LipschitzWith (Kf * Kg) (f * g : Function.End α) :=
  hf.comp hg

/--
theorem `list_prod` / 定理 `list_prod`

English:
theorem list_prod
  statement: (f : ι -> Function.End α) (K : ι -> Real>=0)

中文:
定理 list_prod
  结论: (f : ι -> Function.End α) (K : ι -> 实数>=0)
-/
protected theorem list_prod (f : ι -> Function.End α) (K : ι -> Real>=0)
    (h : forall i, LipschitzWith (K i) (f i)) : forall l : List ι, LipschitzWith (l.map K).prod (l.map f).prod
  | [] => by simpa using! LipschitzWith.id
  | i::l => by
    simp only [List.map_cons, List.prod_cons]
    exact (h i).mul_end (LipschitzWith.list_prod f K h l)

/--
theorem `pow_end` / 定理 `pow_end`

English:
theorem pow_end
  given: {f : Function.End α} {K} (h : LipschitzWith K f)

中文:
定理 pow_end
  条件: {f : Function.End α} {K} (h : LipschitzWith K f)
-/
protected theorem pow_end {f : Function.End α} {K} (h : LipschitzWith K f) :
    forall n : Nat, LipschitzWith (K ^ n) (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using! LipschitzWith.id
  | n + 1 => by
    rw [pow_succ]; rw [pow_succ]
    exact (LipschitzWith.pow_end h n).mul_end h

end LipschitzWith

namespace LipschitzOnWith

variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ]
variable {K : Real>=0} {s : Set α} {f : α -> β}

@[simp]
/--
lemma `zero_iff` / 引理 `zero_iff`

English:
lemma zero_iff
  given: {β : Type*} [EMetricSpace β] (f : α -> β)
  proof: by
  simp [LipschitzOnWith]

中文:
引理 zero_iff
  条件: {β : 类型} [EMetricSpace β] (f : α -> β)
  证明: by
  simp [LipschitzOnWith]

Depends on / 依赖: LipschitzOnWith
-/
lemma zero_iff {β : Type*} [EMetricSpace β] (f : α -> β) :
    LipschitzOnWith 0 f s ↔ forall x in s, forall y in s, f x = f y := by
  simp [LipschitzOnWith]

/--
theorem `uniformContinuousOn` / 定理 `uniformContinuousOn`

English:
theorem uniformContinuousOn
  given: (hf : LipschitzOnWith K f s)
  statement: UniformContinuousOn f s
  proof: uniformContinuousOn_iff_restrict.mpr hf.to_restrict.uniformContinuous

中文:
定理 uniformContinuousOn
  条件: (hf : LipschitzOnWith K f s)
  结论: UniformContinuousOn f s
  证明: uniformContinuousOn_iff_restrict.mpr hf.to_restrict.uniformContinuous
-/
protected theorem uniformContinuousOn (hf : LipschitzOnWith K f s) : UniformContinuousOn f s :=
  uniformContinuousOn_iff_restrict.mpr hf.to_restrict.uniformContinuous

/--
theorem `continuousOn` / 定理 `continuousOn`

English:
theorem continuousOn
  given: (hf : LipschitzOnWith K f s)
  statement: ContinuousOn f s
  proof: hf.uniformContinuousOn.continuousOn

中文:
定理 continuousOn
  条件: (hf : LipschitzOnWith K f s)
  结论: ContinuousOn f s
  证明: hf.uniformContinuousOn.continuousOn
-/
protected theorem continuousOn (hf : LipschitzOnWith K f s) : ContinuousOn f s :=
  hf.uniformContinuousOn.continuousOn

/--
theorem `weaken` / 定理 `weaken`

English:
theorem weaken
  given: (hf : LipschitzOnWith K f s) {K' : Real>=0} (h : K <= K')
  proof: fun _ hx _ hy => (hf hx hy).trans mul_left_mono (ENNReal.coe_le_coe.2 h)

中文:
定理 weaken
  条件: (hf : LipschitzOnWith K f s) {K' : 实数>=0} (h : K <= K')
  证明: fun _ hx _ hy => (hf hx hy).trans mul_left_mono (ENNReal.coe_le_coe.2 h)
-/
protected theorem weaken (hf : LipschitzOnWith K f s) {K' : Real>=0} (h : K <= K') :
    LipschitzOnWith K' f s :=
fun _ hx _ hy => (hf hx hy).trans mul_left_mono (ENNReal.coe_le_coe.2 h)

/--
theorem `edist_le_mul_of_le` / 定理 `edist_le_mul_of_le`

English:
theorem edist_le_mul_of_le
  statement: (h : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy : y in s)
  proof: (h hx hy).trans mul_right_mono hr

中文:
定理 edist_le_mul_of_le
  结论: (h : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy : y in s)
  证明: (h hx hy).trans mul_right_mono hr

Depends on / 依赖: mul_right_mono
-/
theorem edist_le_mul_of_le (h : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy : y in s)
    {r : Real>=0∞} (hr : edist x y <= r) :
    edist (f x) (f y) <= K * r :=
(h hx hy).trans mul_right_mono hr

/--
theorem `edist_lt_of_edist_lt_div` / 定理 `edist_lt_of_edist_lt_div`

English:
theorem edist_lt_of_edist_lt_div
  statement: (hf : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy : y in s)
  proof: hf.to_restrict.edist_lt_of_edist_lt_div show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd

中文:
定理 edist_lt_of_edist_lt_div
  结论: (hf : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy : y in s)
  证明: hf.to_restrict.edist_lt_of_edist_lt_div show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd

Depends on / 依赖: edist_lt_of_edist_lt_div, hf.to_restrict.edist_lt_of_edist_lt_div, to_restrict
-/
theorem edist_lt_of_edist_lt_div (hf : LipschitzOnWith K f s) {x y : α} (hx : x in s) (hy : y in s)
    {d : Real>=0∞} (hd : edist x y < d / K) : edist (f x) (f y) < d :=
hf.to_restrict.edist_lt_of_edist_lt_div show edist (⟨x, hx⟩ : s) ⟨y, hy⟩ < d / K from hd

/--
theorem `comp` / 定理 `comp`

English:
theorem comp
  statement: {g : β -> γ} {t : Set β} {Kg : Real>=0} (hg : LipschitzOnWith Kg g t)
  proof: lipschitzOnWith_iff_restrict.mpr hg.to_restrict.comp (hf.mapsToRestrict hmaps)

中文:
定理 comp
  结论: {g : β -> γ} {t : Set β} {Kg : 实数>=0} (hg : LipschitzOnWith Kg g t)
  证明: lipschitzOnWith_iff_restrict.mpr hg.to_restrict.comp (hf.mapsToRestrict hmaps)
-/
protected theorem comp {g : β -> γ} {t : Set β} {Kg : Real>=0} (hg : LipschitzOnWith Kg g t)
    (hf : LipschitzOnWith K f s) (hmaps : MapsTo f s t) : LipschitzOnWith (Kg * K) (g ∘ f) s :=
lipschitzOnWith_iff_restrict.mpr hg.to_restrict.comp (hf.mapsToRestrict hmaps)

/--
theorem `prodMk` / 定理 `prodMk`

English:
theorem prodMk
  statement: {g : α -> γ} {Kf Kg : Real>=0} (hf : LipschitzOnWith Kf f s)
  proof: by
  intro _ hx _ hy
  rw [ENNReal.coe_mono.map_max]; rw [Prod.edist_eq]; rw [max_mul]
  exact max_le_max (hf hx hy) (hg hx hy)

中文:
定理 prodMk
  结论: {g : α -> γ} {Kf Kg : 实数>=0} (hf : LipschitzOnWith Kf f s)
  证明: by
  intro _ hx _ hy
  rw [ENNReal.coe_mono.map_max]; rw [Prod.edist_eq]; rw [max_mul]
  exact max_le_max (hf hx hy) (hg hx hy)
-/
protected theorem prodMk {g : α -> γ} {Kf Kg : Real>=0} (hf : LipschitzOnWith Kf f s)
    (hg : LipschitzOnWith Kg g s) : LipschitzOnWith (max Kf Kg) (fun x => (f x, g x)) s := by
  intro _ hx _ hy
  rw [ENNReal.coe_mono.map_max]; rw [Prod.edist_eq]; rw [max_mul]
  exact max_le_max (hf hx hy) (hg hx hy)

/--
theorem `ediam_image2_le` / 定理 `ediam_image2_le`

English:
theorem ediam_image2_le
  statement: (f : α -> β -> γ) {K₁ K₂ : Real>=0} (s : Set α) (t : Set β)
  proof: by
  simp only [Metric.ediam_le_iff, forall_mem_image2]
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
  refine (edist_triangle _ (f a₂ b₁) _).trans ?_
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| mul_ri

中文:
定理 ediam_image2_le
  结论: (f : α -> β -> γ) {K₁ K₂ : 实数>=0} (s : Set α) (t : Set β)
  证明: by
  simp only [Metric.ediam_le_iff, forall_mem_image2]
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
  refine (edist_triangle _ (f a₂ b₁) _).trans ?_
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| mul_ri

Depends on / 依赖: Metric, Metric.ediam_le_iff, Metric.edist_le_ediam_of_mem, add_le_add, ediam_le_iff, edist_le_ediam_of_mem, edist_triangle, forall_mem_image2, mul_right_mono
-/
theorem ediam_image2_le (f : α -> β -> γ) {K₁ K₂ : Real>=0} (s : Set α) (t : Set β)
    (hf₁ : forall b in t, LipschitzOnWith K₁ (f · b) s) (hf₂ : forall a in s, LipschitzOnWith K₂ (f a) t) :
    Metric.ediam (Set.image2 f s t) <= ↑K₁ * Metric.ediam s + ↑K₂ * Metric.ediam t := by
  simp only [Metric.ediam_le_iff, forall_mem_image2]
  intro a₁ ha₁ b₁ hb₁ a₂ ha₂ b₂ hb₂
  refine (edist_triangle _ (f a₂ b₁) _).trans ?_
  exact
    add_le_add
      ((hf₁ b₁ hb₁ ha₁ ha₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem ha₁ ha₂)
      ((hf₂ a₂ ha₂ hb₁ hb₂).trans <| mul_right_mono <| Metric.edist_le_ediam_of_mem hb₁ hb₂)

end LipschitzOnWith

namespace LocallyLipschitz
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] [PseudoEMetricSpace γ] {f : α -> β}

/--
lemma `_root_.LipschitzWith.locallyLipschitz` / 引理 `_root_.LipschitzWith.locallyLipschitz`

English:
lemma _root_.LipschitzWith.locallyLipschitz
  given: {K : Real>=0} (hf : LipschitzWith K f)
  proof: fun _ => ⟨K, univ, Filter.univ_mem, lipschitzOnWith_univ.mpr hf⟩

中文:
引理 _root_.LipschitzWith.locallyLipschitz
  条件: {K : 实数>=0} (hf : LipschitzWith K f)
  证明: fun _ => ⟨K, univ, Filter.univ_mem, lipschitzOnWith_univ.mpr hf⟩
-/
protected lemma _root_.LipschitzWith.locallyLipschitz {K : Real>=0} (hf : LipschitzWith K f) :
    LocallyLipschitz f :=
  fun _ => ⟨K, univ, Filter.univ_mem, lipschitzOnWith_univ.mpr hf⟩

/--
lemma `id` / 引理 `id`

English:
lemma id
  statement: LocallyLipschitz (@id α)
  proof: LipschitzWith.id.locallyLipschitz

中文:
引理 id
  结论: LocallyLipschitz (@id α)
  证明: LipschitzWith.id.locallyLipschitz
-/
protected lemma id : LocallyLipschitz (@id α) := LipschitzWith.id.locallyLipschitz

/--
lemma `const` / 引理 `const`

English:
lemma const
  given: (b : β)
  statement: LocallyLipschitz (fun _ : α => b)
  proof: (LipschitzWith.const b).locallyLipschitz

中文:
引理 const
  条件: (b : β)
  结论: LocallyLipschitz (fun _ : α => b)
  证明: (LipschitzWith.const b).locallyLipschitz
-/
protected lemma const (b : β) : LocallyLipschitz (fun _ : α => b) :=
  (LipschitzWith.const b).locallyLipschitz

/--
theorem `continuous` / 定理 `continuous`

English:
theorem continuous
  given: {f : α -> β} (hf : LocallyLipschitz f)
  statement: Continuous f
  proof: by
  rw [continuous_iff_continuousAt]
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact (hK.continuousOn).continuousAt ht

中文:
定理 continuous
  条件: {f : α -> β} (hf : LocallyLipschitz f)
  结论: Continuous f
  证明: by
  rw [continuous_iff_continuousAt]
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact (hK.continuousOn).continuousAt ht
-/
protected theorem continuous {f : α -> β} (hf : LocallyLipschitz f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases (hf x) with ⟨K, t, ht, hK⟩
  exact (hK.continuousOn).continuousAt ht

/--
lemma `comp` / 引理 `comp`

English:
lemma comp
  statement: {f : β -> γ} {g : α -> β}
  proof: by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  refine ⟨Kf * Kg, t inter g⁻¹' u, inter_mem ht (hg.continuous.continuousAt hu), ?_⟩
  exact hfL.comp (hgL.mono inter_subset_left)
    ((mapsTo_preimage g

中文:
引理 comp
  结论: {f : β -> γ} {g : α -> β}
  证明: by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  refine ⟨Kf * Kg, t inter g⁻¹' u, inter_mem ht (hg.continuous.continuousAt hu), ?_⟩
  exact hfL.comp (hgL.mono inter_subset_left)
    ((mapsTo_preimage g
-/
protected lemma comp {f : β -> γ} {g : α -> β}
    (hf : LocallyLipschitz f) (hg : LocallyLipschitz g) : LocallyLipschitz (f ∘ g) := by
  intro x
  -- g is Lipschitz on t ∋ x, f is Lipschitz on u ∋ g(x)
  rcases hg x with ⟨Kg, t, ht, hgL⟩
  rcases hf (g x) with ⟨Kf, u, hu, hfL⟩
  refine ⟨Kf * Kg, t inter g⁻¹' u, inter_mem ht (hg.continuous.continuousAt hu), ?_⟩
  exact hfL.comp (hgL.mono inter_subset_left)
    ((mapsTo_preimage g u).mono_left inter_subset_right)

/--
lemma `prodMk` / 引理 `prodMk`

English:
lemma prodMk
  given: {f : α -> β} (hf : LocallyLipschitz f) {g : α -> γ} (hg : LocallyLipschitz g)
  proof: by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  refine ⟨max Kf Kg, t₁ inter t₂, Filter.inter_mem h₁t h₂t, ?_⟩
  exact (hfL.mono inter_subset_left).prodMk (hgL.mono inter_subset_right)

中文:
引理 prodMk
  条件: {f : α -> β} (hf : LocallyLipschitz f) {g : α -> γ} (hg : LocallyLipschitz g)
  证明: by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  refine ⟨max Kf Kg, t₁ inter t₂, Filter.inter_mem h₁t h₂t, ?_⟩
  exact (hfL.mono inter_subset_left).prodMk (hgL.mono inter_subset_right)
-/
protected lemma prodMk {f : α -> β} (hf : LocallyLipschitz f) {g : α -> γ} (hg : LocallyLipschitz g) :
    LocallyLipschitz fun x => (f x, g x) := by
  intro x
  rcases hf x with ⟨Kf, t₁, h₁t, hfL⟩
  rcases hg x with ⟨Kg, t₂, h₂t, hgL⟩
  refine ⟨max Kf Kg, t₁ inter t₂, Filter.inter_mem h₁t h₂t, ?_⟩
  exact (hfL.mono inter_subset_left).prodMk (hgL.mono inter_subset_right)

/--
theorem `prodMk_left` / 定理 `prodMk_left`

English:
theorem prodMk_left
  given: (a : α)
  statement: LocallyLipschitz (Prod.mk a : β -> α × β)
  proof: (LipschitzWith.prodMk_left a).locallyLipschitz

中文:
定理 prodMk_left
  条件: (a : α)
  结论: LocallyLipschitz (Prod.mk a : β -> α × β)
  证明: (LipschitzWith.prodMk_left a).locallyLipschitz
-/
protected theorem prodMk_left (a : α) : LocallyLipschitz (Prod.mk a : β -> α × β) :=
  (LipschitzWith.prodMk_left a).locallyLipschitz

/--
theorem `prodMk_right` / 定理 `prodMk_right`

English:
theorem prodMk_right
  given: (b : β)
  statement: LocallyLipschitz (fun a : α => (a, b))
  proof: (LipschitzWith.prodMk_right b).locallyLipschitz

中文:
定理 prodMk_right
  条件: (b : β)
  结论: LocallyLipschitz (fun a : α => (a, b))
  证明: (LipschitzWith.prodMk_right b).locallyLipschitz
-/
protected theorem prodMk_right (b : β) : LocallyLipschitz (fun a : α => (a, b)) :=
  (LipschitzWith.prodMk_right b).locallyLipschitz

/--
theorem `iterate` / 定理 `iterate`

English:
theorem iterate
  given: {f : α -> α} (hf : LocallyLipschitz f)
  statement: forall n, LocallyLipschitz f^[n]

中文:
定理 iterate
  条件: {f : α -> α} (hf : LocallyLipschitz f)
  结论: 对任意 n, LocallyLipschitz f^[n]
-/
protected theorem iterate {f : α -> α} (hf : LocallyLipschitz f) : forall n, LocallyLipschitz f^[n]
  | 0 => by simpa only [pow_zero] using! LocallyLipschitz.id
  | n + 1 => by rw [iterate_add, iterate_one]; exact (hf.iterate n).comp hf

/--
theorem `mul_end` / 定理 `mul_end`

English:
theorem mul_end
  statement: {f g : Function.End α} (hf : LocallyLipschitz f)
  proof: hf.comp hg

中文:
定理 mul_end
  结论: {f g : Function.End α} (hf : LocallyLipschitz f)
  证明: hf.comp hg
-/
protected theorem mul_end {f g : Function.End α} (hf : LocallyLipschitz f)
    (hg : LocallyLipschitz g) : LocallyLipschitz (f * g : Function.End α) := hf.comp hg

/--
theorem `pow_end` / 定理 `pow_end`

English:
theorem pow_end
  given: {f : Function.End α} (h : LocallyLipschitz f)

中文:
定理 pow_end
  条件: {f : Function.End α} (h : LocallyLipschitz f)
-/
protected theorem pow_end {f : Function.End α} (h : LocallyLipschitz f) :
    forall n : Nat, LocallyLipschitz (f ^ n : Function.End α)
  | 0 => by simpa only [pow_zero] using! LocallyLipschitz.id
  | n + 1 => by
    rw [pow_succ]
    exact (h.pow_end n).mul_end h

end LocallyLipschitz

namespace LocallyLipschitzOn
variable [PseudoEMetricSpace α] [PseudoEMetricSpace β] {f : α -> β} {s : Set α}

/--
lemma `continuousOn` / 引理 `continuousOn`

English:
lemma continuousOn
  given: (hf : LocallyLipschitzOn s f)
  statement: ContinuousOn f s
  proof: continuousOn_iff_continuous_domRestrict.2 hf.restrict.continuous

中文:
引理 continuousOn
  条件: (hf : LocallyLipschitzOn s f)
  结论: ContinuousOn f s
  证明: continuousOn_iff_continuous_domRestrict.2 hf.restrict.continuous
-/
protected lemma continuousOn (hf : LocallyLipschitzOn s f) : ContinuousOn f s :=
  continuousOn_iff_continuous_domRestrict.2 hf.restrict.continuous

end LocallyLipschitzOn

/--
theorem `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith` / 定理 `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith`

English:
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
  statement: [PseudoEMetricSpace α]
  proof: by
  rintro ⟨x, y⟩ ⟨hx : x in s, hy : y in t⟩
  refine Metric.nhds_basis_closedEBall.tendsto_right_iff.2 fun ε (ε0 : 0 < ε) => ?_
  replace ε0 : 0 < ε / 2 := ENNReal.half_pos ε0.ne'
  obtain ⟨δ, δpos, hδ⟩ : exists δ : Real>=0, 0 < δ ∧ (δ : Real>=0∞) * ↑(3 * K) < ε / 2 :=
    ENNReal.exists_nnreal_po

中文:
定理 continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
  结论: [PseudoEMetricSpace α]
  证明: by
  rintro ⟨x, y⟩ ⟨hx : x in s, hy : y in t⟩
  refine Metric.nhds_basis_closedEBall.tendsto_right_iff.2 fun ε (ε0 : 0 < ε) => ?_
  replace ε0 : 0 < ε / 2 := ENNReal.half_pos ε0.ne'
  obtain ⟨δ, δpos, hδ⟩ : exists δ : Real>=0, 0 < δ ∧ (δ : Real>=0∞) * ↑(3 * K) < ε / 2 :=
    ENNReal.exists_nnreal_po

Depends on / 依赖: EMetric, EMetric.mem_closure_iff, ENNReal, ENNReal.coe_ne_top, ENNReal.coe_pos, ENNReal.exists_nnreal_pos_mul_lt, ENNReal.half_pos, Metric, Metric.eball, Metric.nhds_basis_closedEBall.tendsto_right_iff, coe_ne_top, coe_pos, exists_nnreal_pos_mul_lt, half_pos, inter_mem_nhdsWithin, mem_closure_iff, nhds_basis_closedEBall, replace, tendsto_right_iff
-/
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s s' : Set α} {t : Set β}
    (hs' : s' subseteq s) (hss' : s subseteq closure s') (K : Real>=0)
    (ha : forall a in s', ContinuousOn (fun y => f (a, y)) t)
    (hb : forall b in t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) := by
  rintro ⟨x, y⟩ ⟨hx : x in s, hy : y in t⟩
  refine Metric.nhds_basis_closedEBall.tendsto_right_iff.2 fun ε (ε0 : 0 < ε) => ?_
  replace ε0 : 0 < ε / 2 := ENNReal.half_pos ε0.ne'
  obtain ⟨δ, δpos, hδ⟩ : exists δ : Real>=0, 0 < δ ∧ (δ : Real>=0∞) * ↑(3 * K) < ε / 2 :=
    ENNReal.exists_nnreal_pos_mul_lt ENNReal.coe_ne_top ε0.ne'
  rw [← ENNReal.coe_pos] at δpos
  rcases EMetric.mem_closure_iff.1 (hss' hx) δ δpos with ⟨x', hx', hxx'⟩
  have A : s inter Metric.eball x δ in 𝓝[s] x :=
    inter_mem_nhdsWithin _ (Metric.eball_mem_nhds _ δpos)
  have B : t inter { b | edist (f (x', b)) (f (x', y)) <= ε / 2 } in 𝓝[t] y :=
    inter_mem self_mem_nhdsWithin (ha x' hx' y hy (Metric.closedEBall_mem_nhds (f (x', y)) ε0))
  filter_upwards [nhdsWithin_prod A B] with ⟨a, b⟩ ⟨⟨has, hax⟩, ⟨hbt, hby⟩⟩
  calc
    edist (f (a, b)) (f (x, y)) <= edist (f (a, b)) (f (x', b)) + edist (f (x', b)) (f (x', y)) +
        edist (f (x', y)) (f (x, y)) := edist_triangle4 _ _ _ _
    _ <= K * (δ + δ) + ε / 2 + K * δ := by
      gcongr
      · refine (hb b hbt).edist_le_mul_of_le has (hs' hx') ?_
        exact (edist_triangle _ _ _).trans (add_le_add (le_of_lt hax) hxx'.le)
      · exact hby
      · exact (hb y hy).edist_le_mul_of_le (hs' hx') hx ((edist_comm _ _).trans_le hxx'.le)
    _ = δ * ↑(3 * K) + ε / 2 := by push_cast; ring
    _ <= ε / 2 + ε / 2 := by gcongr
    _ = ε := ENNReal.add_halves _

/--
theorem `continuousOn_prod_of_continuousOn_lipschitzOnWith` / 定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith`

English:
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith
  statement: [PseudoEMetricSpace α]
  proof: continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
    f Subset.rfl subset_closure K ha hb

中文:
定理 continuousOn_prod_of_continuousOn_lipschitzOnWith
  结论: [PseudoEMetricSpace α]
  证明: continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
    f Subset.rfl subset_closure K ha hb

Depends on / 依赖: Subset, Subset.rfl, continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith, subset_closure
-/
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s : Set α} {t : Set β} (K : Real>=0)
    (ha : forall a in s, ContinuousOn (fun y => f (a, y)) t)
    (hb : forall b in t, LipschitzOnWith K (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith
    f Subset.rfl subset_closure K ha hb

/--
theorem `continuous_prod_of_dense_continuous_lipschitzWith` / 定理 `continuous_prod_of_dense_continuous_lipschitzWith`

English:
theorem continuous_prod_of_dense_continuous_lipschitzWith
  statement: [PseudoEMetricSpace α]
  proof: by
  simp only [← continuousOn_univ, ← univ_prod_univ, ← lipschitzOnWith_univ] at *
  exact continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith f (subset_univ _)
    hs.closure_eq.ge K ha fun b _ => hb b

中文:
定理 continuous_prod_of_dense_continuous_lipschitzWith
  结论: [PseudoEMetricSpace α]
  证明: by
  simp only [← continuousOn_univ, ← univ_prod_univ, ← lipschitzOnWith_univ] at *
  exact continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith f (subset_univ _)
    hs.closure_eq.ge K ha fun b _ => hb b

Depends on / 依赖: closure_eq, continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith, continuousOn_univ, hs.closure_eq.ge, lipschitzOnWith_univ, subset_univ, univ_prod_univ
-/
theorem continuous_prod_of_dense_continuous_lipschitzWith [PseudoEMetricSpace α]
    [TopologicalSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) {s : Set α}
    (hs : Dense s) (ha : forall a in s, Continuous fun y => f (a, y))
    (hb : forall b, LipschitzWith K fun x => f (x, b)) : Continuous f := by
  simp only [← continuousOn_univ, ← univ_prod_univ, ← lipschitzOnWith_univ] at *
  exact continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith f (subset_univ _)
    hs.closure_eq.ge K ha fun b _ => hb b

/--
theorem `continuous_prod_of_continuous_lipschitzWith` / 定理 `continuous_prod_of_continuous_lipschitzWith`

English:
theorem continuous_prod_of_continuous_lipschitzWith
  statement: [PseudoEMetricSpace α] [TopologicalSpace β]
  proof: continuous_prod_of_dense_continuous_lipschitzWith f K dense_univ (fun _ _ => ha _) hb

中文:
定理 continuous_prod_of_continuous_lipschitzWith
  结论: [PseudoEMetricSpace α] [TopologicalSpace β]
  证明: continuous_prod_of_dense_continuous_lipschitzWith f K dense_univ (fun _ _ => ha _) hb

Depends on / 依赖: continuous_prod_of_dense_continuous_lipschitzWith, dense_univ
-/
theorem continuous_prod_of_continuous_lipschitzWith [PseudoEMetricSpace α] [TopologicalSpace β]
    [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) (ha : forall a, Continuous fun y => f (a, y))
    (hb : forall b, LipschitzWith K fun x => f (x, b)) : Continuous f :=
  continuous_prod_of_dense_continuous_lipschitzWith f K dense_univ (fun _ _ => ha _) hb

/--
theorem `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith'` / 定理 `continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith'`

English:
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith'
  statement: [TopologicalSpace α]
  proof: have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith _ ht' htt' K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

中文:
定理 continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith'
  结论: [TopologicalSpace α]
  证明: have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith _ ht' htt' K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

Depends on / 依赖: ContinuousOn, Prod.swap, continuousOn, continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith, continuous_swap, continuous_swap.continuousOn, mapsTo_swap_prod, this.comp
-/
theorem continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s : Set α} {t t' : Set β}
    (ht' : t' subseteq t) (htt' : t subseteq closure t') (K : Real>=0)
    (ha : forall a in s, LipschitzOnWith K (fun y => f (a, y)) t)
    (hb : forall b in t', ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_subset_closure_continuousOn_lipschitzOnWith _ ht' htt' K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

/--
theorem `continuousOn_prod_of_continuousOn_lipschitzOnWith'` / 定理 `continuousOn_prod_of_continuousOn_lipschitzOnWith'`

English:
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith'
  statement: [TopologicalSpace α]
  proof: have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

中文:
定理 continuousOn_prod_of_continuousOn_lipschitzOnWith'
  结论: [TopologicalSpace α]
  证明: have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

Depends on / 依赖: ContinuousOn, Prod.swap, continuousOn, continuousOn_prod_of_continuousOn_lipschitzOnWith, continuous_swap, continuous_swap.continuousOn, mapsTo_swap_prod, this.comp
-/
theorem continuousOn_prod_of_continuousOn_lipschitzOnWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) {s : Set α} {t : Set β} (K : Real>=0)
    (ha : forall a in s, LipschitzOnWith K (fun y => f (a, y)) t)
    (hb : forall b in t, ContinuousOn (fun x => f (x, b)) s) : ContinuousOn f (s ×ˢ t) :=
  have : ContinuousOn (f ∘ Prod.swap) (t ×ˢ s) :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K hb ha
  this.comp continuous_swap.continuousOn (mapsTo_swap_prod _ _)

/--
theorem `continuous_prod_of_dense_continuous_lipschitzWith'` / 定理 `continuous_prod_of_dense_continuous_lipschitzWith'`

English:
theorem continuous_prod_of_dense_continuous_lipschitzWith'
  statement: [TopologicalSpace α]
  proof: have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_dense_continuous_lipschitzWith _ K ht hb ha
  this.comp continuous_swap

中文:
定理 continuous_prod_of_dense_continuous_lipschitzWith'
  结论: [TopologicalSpace α]
  证明: have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_dense_continuous_lipschitzWith _ K ht hb ha
  this.comp continuous_swap

Depends on / 依赖: Continuous, Prod.swap, continuous_prod_of_dense_continuous_lipschitzWith, continuous_swap, this.comp
-/
theorem continuous_prod_of_dense_continuous_lipschitzWith' [TopologicalSpace α]
    [PseudoEMetricSpace β] [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) {t : Set β}
    (ht : Dense t) (ha : forall a, LipschitzWith K fun y => f (a, y))
    (hb : forall b in t, Continuous fun x => f (x, b)) : Continuous f :=
  have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_dense_continuous_lipschitzWith _ K ht hb ha
  this.comp continuous_swap

/--
theorem `continuous_prod_of_continuous_lipschitzWith'` / 定理 `continuous_prod_of_continuous_lipschitzWith'`

English:
theorem continuous_prod_of_continuous_lipschitzWith'
  statement: [TopologicalSpace α] [PseudoEMetricSpace β]
  proof: have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_continuous_lipschitzWith _ K hb ha
  this.comp continuous_swap

中文:
定理 continuous_prod_of_continuous_lipschitzWith'
  结论: [TopologicalSpace α] [PseudoEMetricSpace β]
  证明: have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_continuous_lipschitzWith _ K hb ha
  this.comp continuous_swap

Depends on / 依赖: Continuous, Prod.swap, continuous_prod_of_continuous_lipschitzWith, continuous_swap, this.comp
-/
theorem continuous_prod_of_continuous_lipschitzWith' [TopologicalSpace α] [PseudoEMetricSpace β]
    [PseudoEMetricSpace γ] (f : α × β -> γ) (K : Real>=0) (ha : forall a, LipschitzWith K fun y => f (a, y))
    (hb : forall b, Continuous fun x => f (x, b)) : Continuous f :=
  have : Continuous (f ∘ Prod.swap) :=
    continuous_prod_of_continuous_lipschitzWith _ K hb ha
  this.comp continuous_swap
