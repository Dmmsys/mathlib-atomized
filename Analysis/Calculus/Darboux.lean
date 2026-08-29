/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Darboux's theorem

In this file we prove that the derivative of a differentiable function on an interval takes all
intermediate values. The proof is based on the
[Wikipedia](https://en.wikipedia.org/wiki/Darboux%27s_theorem_(analysis)) page about this theorem.
-/

public section

open Filter Set

open scoped Topology

variable {a b : Real} {f f' : Real -> Real}

/--
theorem `exists_hasDerivWithinAt_eq_of_gt_of_lt` / 定理 `exists_hasDerivWithinAt_eq_of_gt_of_lt`

English:
theorem exists_hasDerivWithinAt_eq_of_gt_of_lt
  statement: (hab : a <= b)
  proof: by
  rcases hab.eq_or_lt with (rfl | hab')
  · exact (lt_asymm hma hmb).elim
  set g : Real -> Real := fun x => f x - m * x
  have hg : forall x in Icc a b, HasDerivWithinAt g (f' x - m) (Icc a b) x := by
    intro x hx
    simpa using! (hf x hx).sub ((hasDerivWithinAt_id x _).const_mul m)
  obtain ⟨c, cmem, hc⟩ : exists c in Icc a b, IsMinOn g (Icc a b) c :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 <| hab) fun x hx => (hg x hx).continuousWithinAt
  have cmem' : c in Ioo a b := by
    rcases cmem.1.eq_or_lt with (rfl | hac)
    -- Show that `c` can't be equal to `a`
    · refine absurd (sub_nonneg.1 <| nonneg_of_mul_nonneg_right ?_ (sub_pos.2 hab'))
        (not_le_of_gt hma)
      have : b - a in posTangentConeAt (Icc a b) a :=
        sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ Subset.rfl)
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg a (left_mem_Icc.2 hab)) this
    rcases cmem.2.eq_or_lt' with (rfl | hcb)
    -- Show that `c` can't be equal to `b`
    · refine absurd (sub_nonpos.1 <| nonpos_of_mul_nonneg_right ?_ (sub_lt_zero.2 hab'))
        (not_le_of_gt hmb)
      have : a - b in posTangentConeAt (Icc a b) b :=
        sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg b (right_mem_Icc.2 hab)) this
    exact ⟨hac, hcb⟩
  use c, cmem'
  rw [← sub_eq_zero]
  have : Icc a b in 𝓝 c := by rwa [← mem_interior_iff_mem_nhds, interior_Icc]
  exact (hc.isLocalMin this).hasDerivAt_eq_zero ((hg c cmem).hasDerivAt this)

中文:
定理 存在_hasDerivWithinAt_eq_of_gt_of_lt
  结论: (hab : a <= b)
  证明: by
  rcases hab.eq_or_lt with (rfl | hab')
  · exact (lt_asymm hma hmb).elim
  set g : Real -> Real := fun x => f x - m * x
  have hg : forall x in Icc a b, HasDerivWithinAt g (f' x - m) (Icc a b) x := by
    intro x hx
    simpa using! (hf x hx).sub ((hasDerivWithinAt_id x _).const_mul m)
  obtain ⟨c, cmem, hc⟩ : exists c in Icc a b, IsMinOn g (Icc a b) c :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 <| hab) fun x hx => (hg x hx).continuousWithinAt
  have cmem' : c in Ioo a b := by
    rcases cmem.1.eq_or_lt with (rfl | hac)
    -- Show that `c` can't be equal to `a`
    · refine absurd (sub_nonneg.1 <| nonneg_of_mul_nonneg_right ?_ (sub_pos.2 hab'))
        (not_le_of_gt hma)
      have : b - a in posTangentConeAt (Icc a b) a :=
        sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ Subset.rfl)
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg a (left_mem_Icc.2 hab)) this
    rcases cmem.2.eq_or_lt' with (rfl | hcb)
    -- Show that `c` can't be equal to `b`
    · refine absurd (sub_nonpos.1 <| nonpos_of_mul_nonneg_right ?_ (sub_lt_zero.2 hab'))
        (not_le_of_gt hmb)
      have : a - b in posTangentConeAt (Icc a b) b :=
        sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg b (right_mem_Icc.2 hab)) this
    exact ⟨hac, hcb⟩
  use c, cmem'
  rw [← sub_eq_zero]
  have : Icc a b in 𝓝 c := by rwa [← mem_interior_iff_mem_nhds, interior_Icc]
  exact (hc.isLocalMin this).hasDerivAt_eq_zero ((hg c cmem).hasDerivAt this)

Depends on / 依赖: HasDerivWithinAt, IsMinOn, const_mul, continuousWithinAt, eq_or_lt, exists_isMinOn, hab.eq_or_lt, hasDerivWithinAt_id, isCompact_Icc, isCompact_Icc.exists_isMinOn, lt_asymm, nonempty_Icc
-/
theorem exists_hasDerivWithinAt_eq_of_gt_of_lt (hab : a <= b)
    (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : f' a < m)
    (hmb : m < f' b) : m in f' '' Ioo a b := by
  rcases hab.eq_or_lt with (rfl | hab')
  · exact (lt_asymm hma hmb).elim
  set g : Real -> Real := fun x => f x - m * x
  have hg : forall x in Icc a b, HasDerivWithinAt g (f' x - m) (Icc a b) x := by
    intro x hx
    simpa using! (hf x hx).sub ((hasDerivWithinAt_id x _).const_mul m)
  obtain ⟨c, cmem, hc⟩ : exists c in Icc a b, IsMinOn g (Icc a b) c :=
    isCompact_Icc.exists_isMinOn (nonempty_Icc.2 <| hab) fun x hx => (hg x hx).continuousWithinAt
  have cmem' : c in Ioo a b := by
    rcases cmem.1.eq_or_lt with (rfl | hac)
    -- Show that `c` can't be equal to `a`
    · refine absurd (sub_nonneg.1 <| nonneg_of_mul_nonneg_right ?_ (sub_pos.2 hab'))
        (not_le_of_gt hma)
      have : b - a in posTangentConeAt (Icc a b) a :=
        sub_mem_posTangentConeAt_of_segment_subset (segment_eq_Icc hab ▸ Subset.rfl)
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg a (left_mem_Icc.2 hab)) this
    rcases cmem.2.eq_or_lt' with (rfl | hcb)
    -- Show that `c` can't be equal to `b`
    · refine absurd (sub_nonpos.1 <| nonpos_of_mul_nonneg_right ?_ (sub_lt_zero.2 hab'))
        (not_le_of_gt hmb)
      have : a - b in posTangentConeAt (Icc a b) b :=
        sub_mem_posTangentConeAt_of_segment_subset (by rw [segment_symm, segment_eq_Icc hab])
      simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self]
        using! hc.localize.hasFDerivWithinAt_nonneg (hg b (right_mem_Icc.2 hab)) this
    exact ⟨hac, hcb⟩
  use c, cmem'
  rw [← sub_eq_zero]
  have : Icc a b in 𝓝 c := by rwa [← mem_interior_iff_mem_nhds, interior_Icc]
  exact (hc.isLocalMin this).hasDerivAt_eq_zero ((hg c cmem).hasDerivAt this)

/--
theorem `exists_hasDerivWithinAt_eq_of_lt_of_gt` / 定理 `exists_hasDerivWithinAt_eq_of_lt_of_gt`

English:
theorem exists_hasDerivWithinAt_eq_of_lt_of_gt
  statement: (hab : a <= b)
  proof: let ⟨c, cmem, hc⟩ :=
    exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma)
      (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩

中文:
定理 存在_hasDerivWithinAt_eq_of_lt_of_gt
  结论: (hab : a <= b)
  证明: let ⟨c, cmem, hc⟩ :=
    exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma)
      (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩

Depends on / 依赖: exists_hasDerivWithinAt_eq_of_gt_of_lt, neg_injective, neg_lt_neg
-/
theorem exists_hasDerivWithinAt_eq_of_lt_of_gt (hab : a <= b)
    (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : m < f' a)
    (hmb : f' b < m) : m in f' '' Ioo a b :=
  let ⟨c, cmem, hc⟩ :=
    exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x hx).neg) (neg_lt_neg hma)
      (neg_lt_neg hmb)
  ⟨c, cmem, neg_injective hc⟩

/--
theorem `Set.OrdConnected.image_hasDerivWithinAt` / 定理 `Set.OrdConnected.image_hasDerivWithinAt`

English:
theorem Set.OrdConnected.image_hasDerivWithinAt
  statement: {s : Set Real} (hs : OrdConnected s)
  proof: by
  apply ordConnected_of_Ioo
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ - m ⟨hma, hmb⟩
  rcases le_total a b with hab | hab
  · have : Icc a b subseteq s := hs.out ha hb
    rcases exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x <| this hx).mono this) hma
        hmb with
      ⟨c, cmem, hc⟩
exact ⟨c, this Ioo_subset_Icc_self cmem, hc⟩
  · have : Icc b a subseteq s := hs.out hb ha
    rcases exists_hasDerivWithinAt_eq_of_lt_of_gt hab (fun x hx => (hf x <| this hx).mono this) hmb
        hma with
      ⟨c, cmem, hc⟩
exact ⟨c, this Ioo_subset_Icc_self cmem, hc⟩

中文:
定理 集合.序连通.image_hasDerivWithinAt
  结论: {s : 集合 实数} (hs : 序连通 s)
  证明: by
  apply ordConnected_of_Ioo
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ - m ⟨hma, hmb⟩
  rcases le_total a b with hab | hab
  · have : Icc a b subseteq s := hs.out ha hb
    rcases exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x <| this hx).mono this) hma
        hmb with
      ⟨c, cmem, hc⟩
exact ⟨c, this Ioo_subset_Icc_self cmem, hc⟩
  · have : Icc b a subseteq s := hs.out hb ha
    rcases exists_hasDerivWithinAt_eq_of_lt_of_gt hab (fun x hx => (hf x <| this hx).mono this) hmb
        hma with
      ⟨c, cmem, hc⟩
exact ⟨c, this Ioo_subset_Icc_self cmem, hc⟩

Depends on / 依赖: Ioo_subset_Icc_self, exists_hasDerivWithinAt_eq_of_gt_of_lt, exists_hasDerivWithinAt_eq_of_lt_of_gt, hs.out, le_total, ordConnected_of_Ioo, subseteq
-/
theorem Set.OrdConnected.image_hasDerivWithinAt {s : Set Real} (hs : OrdConnected s)
    (hf : forall x in s, HasDerivWithinAt f (f' x) s x) : OrdConnected (f' '' s) := by
  apply ordConnected_of_Ioo
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ - m ⟨hma, hmb⟩
  rcases le_total a b with hab | hab
  · have : Icc a b subseteq s := hs.out ha hb
    rcases exists_hasDerivWithinAt_eq_of_gt_of_lt hab (fun x hx => (hf x <| this hx).mono this) hma
        hmb with
      ⟨c, cmem, hc⟩
exact ⟨c, this Ioo_subset_Icc_self cmem, hc⟩
  · have : Icc b a subseteq s := hs.out hb ha
    rcases exists_hasDerivWithinAt_eq_of_lt_of_gt hab (fun x hx => (hf x <| this hx).mono this) hmb
        hma with
      ⟨c, cmem, hc⟩
exact ⟨c, this Ioo_subset_Icc_self cmem, hc⟩

/--
theorem `Set.OrdConnected.image_derivWithin` / 定理 `Set.OrdConnected.image_derivWithin`

English:
theorem Set.OrdConnected.image_derivWithin
  statement: {s : Set Real} (hs : OrdConnected s)
  proof: hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivWithinAt

中文:
定理 集合.序连通.image_derivWithin
  结论: {s : 集合 实数} (hs : 序连通 s)
  证明: hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivWithinAt

Depends on / 依赖: hasDerivWithinAt, hs.image_hasDerivWithinAt, image_hasDerivWithinAt
-/
theorem Set.OrdConnected.image_derivWithin {s : Set Real} (hs : OrdConnected s)
    (hf : DifferentiableOn Real f s) : OrdConnected (derivWithin f s '' s) :=
  hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivWithinAt

/--
theorem `Set.OrdConnected.image_deriv` / 定理 `Set.OrdConnected.image_deriv`

English:
theorem Set.OrdConnected.image_deriv
  statement: {s : Set Real} (hs : OrdConnected s)
  proof: hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt

中文:
定理 集合.序连通.image_deriv
  结论: {s : 集合 实数} (hs : 序连通 s)
  证明: hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt

Depends on / 依赖: hasDerivAt, hasDerivAt.hasDerivWithinAt, hasDerivWithinAt, hs.image_hasDerivWithinAt, image_hasDerivWithinAt
-/
theorem Set.OrdConnected.image_deriv {s : Set Real} (hs : OrdConnected s)
    (hf : forall x in s, DifferentiableAt Real f x) : OrdConnected (deriv f '' s) :=
  hs.image_hasDerivWithinAt fun x hx => (hf x hx).hasDerivAt.hasDerivWithinAt

/--
theorem `Convex.image_hasDerivWithinAt` / 定理 `Convex.image_hasDerivWithinAt`

English:
theorem Convex.image_hasDerivWithinAt
  statement: {s : Set Real} (hs : Convex Real s)
  proof: (hs.ordConnected.image_hasDerivWithinAt hf).convex

中文:
定理 凸.image_hasDerivWithinAt
  结论: {s : 集合 实数} (hs : 凸 实数 s)
  证明: (hs.ordConnected.image_hasDerivWithinAt hf).convex

Depends on / 依赖: convex, hs.ordConnected.image_hasDerivWithinAt, image_hasDerivWithinAt, ordConnected
-/
theorem Convex.image_hasDerivWithinAt {s : Set Real} (hs : Convex Real s)
    (hf : forall x in s, HasDerivWithinAt f (f' x) s x) : Convex Real (f' '' s) :=
  (hs.ordConnected.image_hasDerivWithinAt hf).convex

/--
theorem `Convex.image_derivWithin` / 定理 `Convex.image_derivWithin`

English:
theorem Convex.image_derivWithin
  given: {s : Set Real} (hs : Convex Real s) (hf : DifferentiableOn Real f s)
  proof: (hs.ordConnected.image_derivWithin hf).convex

中文:
定理 凸.image_derivWithin
  条件: {s : 集合 实数} (hs : 凸 实数 s) (hf : DifferentiableOn 实数 f s)
  证明: (hs.ordConnected.image_derivWithin hf).convex

Depends on / 依赖: convex, hs.ordConnected.image_derivWithin, image_derivWithin, ordConnected
-/
theorem Convex.image_derivWithin {s : Set Real} (hs : Convex Real s) (hf : DifferentiableOn Real f s) :
    Convex Real (derivWithin f s '' s) :=
  (hs.ordConnected.image_derivWithin hf).convex

/--
theorem `Convex.image_deriv` / 定理 `Convex.image_deriv`

English:
theorem Convex.image_deriv
  given: {s : Set Real} (hs : Convex Real s) (hf : forall x in s, DifferentiableAt Real f x)
  proof: (hs.ordConnected.image_deriv hf).convex

中文:
定理 凸.image_deriv
  条件: {s : 集合 实数} (hs : 凸 实数 s) (hf : 对任意 x in s, DifferentiableAt 实数 f x)
  证明: (hs.ordConnected.image_deriv hf).convex

Depends on / 依赖: convex, hs.ordConnected.image_deriv, image_deriv, ordConnected
-/
theorem Convex.image_deriv {s : Set Real} (hs : Convex Real s) (hf : forall x in s, DifferentiableAt Real f x) :
    Convex Real (deriv f '' s) :=
  (hs.ordConnected.image_deriv hf).convex

/--
theorem `exists_hasDerivWithinAt_eq_of_ge_of_le` / 定理 `exists_hasDerivWithinAt_eq_of_ge_of_le`

English:
theorem exists_hasDerivWithinAt_eq_of_ge_of_le
  statement: (hab : a <= b)
  proof: (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

中文:
定理 存在_hasDerivWithinAt_eq_of_ge_of_le
  结论: (hab : a <= b)
  证明: (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

Depends on / 依赖: image_hasDerivWithinAt, left_mem_Icc, mem_image_of_mem, ordConnected_Icc, ordConnected_Icc.image_hasDerivWithinAt, right_mem_Icc
-/
theorem exists_hasDerivWithinAt_eq_of_ge_of_le (hab : a <= b)
    (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : f' a <= m)
    (hmb : m <= f' b) : m in f' '' Icc a b :=
  (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

/--
theorem `exists_hasDerivWithinAt_eq_of_le_of_ge` / 定理 `exists_hasDerivWithinAt_eq_of_le_of_ge`

English:
theorem exists_hasDerivWithinAt_eq_of_le_of_ge
  statement: (hab : a <= b)
  proof: (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

中文:
定理 存在_hasDerivWithinAt_eq_of_le_of_ge
  结论: (hab : a <= b)
  证明: (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

Depends on / 依赖: image_hasDerivWithinAt, left_mem_Icc, mem_image_of_mem, ordConnected_Icc, ordConnected_Icc.image_hasDerivWithinAt, right_mem_Icc
-/
theorem exists_hasDerivWithinAt_eq_of_le_of_ge (hab : a <= b)
    (hf : forall x in Icc a b, HasDerivWithinAt f (f' x) (Icc a b) x) {m : Real} (hma : f' a <= m)
    (hmb : m <= f' b) : m in f' '' Icc a b :=
  (ordConnected_Icc.image_hasDerivWithinAt hf).out (mem_image_of_mem _ (left_mem_Icc.2 hab))
    (mem_image_of_mem _ (right_mem_Icc.2 hab)) ⟨hma, hmb⟩

/--
theorem `hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne` / 定理 `hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne`

English:
theorem hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne
  statement: {s : Set Real} (hs : Convex Real s)
  proof: by
  contrapose! hf'
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
  exact (hs.ordConnected.image_hasDerivWithinAt hf).out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩

中文:
定理 hasDerivWithinAt_对任意_lt_or_对任意_gt_of_对任意_ne
  结论: {s : 集合 实数} (hs : 凸 实数 s)
  证明: by
  contrapose! hf'
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
  exact (hs.ordConnected.image_hasDerivWithinAt hf).out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩

Depends on / 依赖: contrapose, hs.ordConnected.image_hasDerivWithinAt, image_hasDerivWithinAt, mem_image_of_mem, ordConnected
-/
theorem hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne {s : Set Real} (hs : Convex Real s)
    (hf : forall x in s, HasDerivWithinAt f (f' x) s x) {m : Real} (hf' : forall x in s, f' x != m) :
    (forall x in s, f' x < m) ∨ forall x in s, m < f' x := by
  contrapose! hf'
  rcases hf' with ⟨⟨b, hb, hmb⟩, ⟨a, ha, hma⟩⟩
  exact (hs.ordConnected.image_hasDerivWithinAt hf).out (mem_image_of_mem f' ha)
    (mem_image_of_mem f' hb) ⟨hma, hmb⟩
