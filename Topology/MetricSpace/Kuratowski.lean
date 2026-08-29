/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Topology.Sets.Compacts

/-!
# The Kuratowski embedding

Any separable metric space can be embedded isometrically in `ℓ^∞(ℕ, ℝ)`.
Any partially defined Lipschitz map into `ℓ^∞` can be extended to the whole space.

-/

@[expose] public section

noncomputable section


open Set Metric TopologicalSpace NNReal ENNReal lp Function

universe u

variable {α : Type u}

namespace KuratowskiEmbedding

/-! ### Any separable metric space can be embedded isometrically in ℓ^∞(ℕ, ℝ) -/


variable {n : Nat} [MetricSpace α] (x : Nat -> α) (a : α)

/--
Definition of `embeddingOfSubset` / `embeddingOfSubset` 的定义

English:
definition embeddingOfSubset
  signature: : ℓ^∞(Nat, Real)
  body: ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩

中文:
定义 embeddingOfSubset
  签名: : ℓ^∞(自然数, 实数)
  定义体: ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩

Depends on / 依赖: abs_dist_sub_le
-/
def embeddingOfSubset : ℓ^∞(Nat, Real) :=
  ⟨fun n => dist a (x n) - dist (x 0) (x n), by
    apply memℓp_infty
    use dist a (x 0)
    rintro - ⟨n, rfl⟩
    exact abs_dist_sub_le _ _ _⟩

/--
theorem `embeddingOfSubset_coe` / 定理 `embeddingOfSubset_coe`

English:
theorem embeddingOfSubset_coe
  statement: embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n)
  proof: rfl

中文:
定理 embeddingOfSubset_coe
  结论: embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n)
  证明: rfl
-/
theorem embeddingOfSubset_coe : embeddingOfSubset x a n = dist a (x n) - dist (x 0) (x n) :=
  rfl

/--
theorem `embeddingOfSubset_dist_le` / 定理 `embeddingOfSubset_dist_le`

English:
theorem embeddingOfSubset_dist_le
  given: (a b : α)
  proof: by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe]
  convert! abs_dist_sub_le a b (x n) using 2
  ring

中文:
定理 embeddingOfSubset_dist_le
  条件: (a b : α)
  证明: by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe]
  convert! abs_dist_sub_le a b (x n) using 2
  ring

Depends on / 依赖: Pi.sub_apply, abs_dist_sub_le, coeFn_sub, convert, dist_eq_norm, dist_nonneg, embeddingOfSubset_coe, lp.coeFn_sub, lp.norm_le_of_forall_le, norm_le_of_forall_le, sub_apply
-/
theorem embeddingOfSubset_dist_le (a b : α) :
    dist (embeddingOfSubset x a) (embeddingOfSubset x b) <= dist a b := by
  rw [dist_eq_norm]
  refine lp.norm_le_of_forall_le dist_nonneg fun n => ?_
  simp only [lp.coeFn_sub, Pi.sub_apply, embeddingOfSubset_coe]
  convert! abs_dist_sub_le a b (x n) using 2
  ring

/--
theorem `embeddingOfSubset_isometry` / 定理 `embeddingOfSubset_isometry`

English:
theorem embeddingOfSubset_isometry
  given: (H : DenseRange x)
  statement: Isometry (embeddingOfSubset x)
  proof: by
  refine Isometry.of_dist_eq fun a b => ?_
  refine (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => ?_)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm

中文:
定理 embeddingOfSubset_isometry
  条件: (H : DenseRange x)
  结论: 等距 (embeddingOfSubset x)
  证明: by
  refine Isometry.of_dist_eq fun a b => ?_
  refine (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => ?_)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm

Depends on / 依赖: Isometry, Isometry.of_dist_eq, antisymm, embeddingOfSubset_dist_le, le_of_forall_pos_le_add, of_dist_eq
-/
theorem embeddingOfSubset_isometry (H : DenseRange x) : Isometry (embeddingOfSubset x) := by
  refine Isometry.of_dist_eq fun a b => ?_
  refine (embeddingOfSubset_dist_le x a b).antisymm (le_of_forall_pos_le_add fun e epos => ?_)
  -- First step: find n with dist a (x n) < e
  rcases Metric.mem_closure_range_iff.1 (H a) (e / 2) (half_pos epos) with ⟨n, hn⟩
  -- Second step: use the norm control at index n to conclude
  have C : dist b (x n) - dist a (x n) = embeddingOfSubset x b n - embeddingOfSubset x a n := by
    simp only [embeddingOfSubset_coe, sub_sub_sub_cancel_right]
  have :=
    calc
      dist a b <= dist a (x n) + dist (x n) b := dist_triangle _ _ _
      _ = 2 * dist a (x n) + (dist b (x n) - dist a (x n)) := by simp [dist_comm]; ring
      _ <= 2 * dist a (x n) + |dist b (x n) - dist a (x n)| := by grw [← le_abs_self]
      _ <= 2 * (e / 2) + |embeddingOfSubset x b n - embeddingOfSubset x a n| := by
        rw [C]
        gcongr
      _ <= 2 * (e / 2) + dist (embeddingOfSubset x b) (embeddingOfSubset x a) := by
        gcongr
        simp only [dist_eq_norm]
        exact lp.norm_apply_le_norm ENNReal.top_ne_zero
          (embeddingOfSubset x b - embeddingOfSubset x a) n
      _ = dist (embeddingOfSubset x b) (embeddingOfSubset x a) + e := by ring
  simpa [dist_comm] using this

/--
theorem `exists_isometric_embedding` / 定理 `exists_isometric_embedding`

English:
theorem exists_isometric_embedding
  given: (α : Type u) [MetricSpace α] [SeparableSpace α]
  proof: by
  rcases (univ : Set α).eq_empty_or_nonempty with h | h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    have : Inhabited α := ⟨basepoint⟩
    have : exists s : Set α, s.Countable

中文:
定理 存在_isometric_embedding
  条件: (α : 类型u) [度量空间 α] [可分空间 α]
  证明: by
  rcases (univ : Set α).eq_empty_or_nonempty with h | h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    have : Inhabited α := ⟨basepoint⟩
    have : exists s : Set α, s.Countable

Depends on / 依赖: Countable, Inhabited, Nonempty, Nonempty.ne_empty, S_countable, S_dense, Set.countable_iff_exists_subset_range, absurd, basepoint, construct, countable_iff_exists_subset_range, eq_empty_or_nonempty, exists_countable_dense, mem_univ, ne_empty, s.Countable, x_range
-/
theorem exists_isometric_embedding (α : Type u) [MetricSpace α] [SeparableSpace α] :
    exists f : α -> ℓ^∞(Nat, Real), Isometry f := by
  rcases (univ : Set α).eq_empty_or_nonempty with h | h
  · use fun _ => 0; intro x; exact absurd h (Nonempty.ne_empty ⟨x, mem_univ x⟩)
  · -- We construct a map x : ℕ → α with dense image
    rcases h with ⟨basepoint⟩
    have : Inhabited α := ⟨basepoint⟩
    have : exists s : Set α, s.Countable ∧ Dense s := exists_countable_dense α
    rcases this with ⟨S, ⟨S_countable, S_dense⟩⟩
    rcases Set.countable_iff_exists_subset_range.1 S_countable with ⟨x, x_range⟩
    -- Use embeddingOfSubset to construct the desired isometry
    exact ⟨embeddingOfSubset x, embeddingOfSubset_isometry x (S_dense.mono x_range)⟩

end KuratowskiEmbedding

open KuratowskiEmbedding

/--
Definition of `kuratowskiEmbedding` / `kuratowskiEmbedding` 的定义

English:
definition kuratowskiEmbedding
  signature: (α : Type u) [MetricSpace α] [SeparableSpace α]
  body: Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)

中文:
定义 kuratowskiEmbedding
  签名: (α : 类型u) [度量空间 α] [可分空间 α]
  定义体: Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)

Depends on / 依赖: Classical, Classical.choose, KuratowskiEmbedding, KuratowskiEmbedding.exists_isometric_embedding, exists_isometric_embedding
-/
def kuratowskiEmbedding (α : Type u) [MetricSpace α] [SeparableSpace α] : α -> ℓ^∞(Nat, Real) :=
  Classical.choose (KuratowskiEmbedding.exists_isometric_embedding α)

/--
theorem `kuratowskiEmbedding.isometry` / 定理 `kuratowskiEmbedding.isometry`

English:
theorem kuratowskiEmbedding.isometry
  given: (α : Type u) [MetricSpace α] [SeparableSpace α]
  proof: Classical.choose_spec (exists_isometric_embedding α)

中文:
定理 kuratowskiEmbedding.isometry
  条件: (α : 类型u) [度量空间 α] [可分空间 α]
  证明: Classical.choose_spec (exists_isometric_embedding α)
-/
protected theorem kuratowskiEmbedding.isometry (α : Type u) [MetricSpace α] [SeparableSpace α] :
    Isometry (kuratowskiEmbedding α) :=
  Classical.choose_spec (exists_isometric_embedding α)

/-- Version of the Kuratowski embedding for nonempty compacts -/
nonrec def NonemptyCompacts.kuratowskiEmbedding (α : Type u) [MetricSpace α] [CompactSpace α]
    [Nonempty α] : NonemptyCompacts ℓ^∞(Nat, Real) where
  carrier := range (kuratowskiEmbedding α)
  isCompact' := isCompact_range (kuratowskiEmbedding.isometry α).continuous
  nonempty' := range_nonempty _

/--
theorem `LipschitzOnWith.extend_lp_infty` / 定理 `LipschitzOnWith.extend_lp_infty`

English:
theorem LipschitzOnWith.extend_lp_infty
  statement: [PseudoMetricSpace α] {s : Set α} {ι : Type*}
  proof: by
  -- Construct the coordinate-wise extensions
  rw [LipschitzOnWith.coordinate] at hfl
  have (i : ι) : exists g : α -> Real, LipschitzWith K g ∧ EqOn (fun x => f x i) g s :=
    LipschitzOnWith.extend_real (hfl i) -- use the nonlinear Hahn-Banach theorem here!
  choose g hgl hgeq using this
  rc

中文:
定理 LipschitzOnWith.extend_lp_infty
  结论: [伪度量空间 α] {s : 集合 α} {ι : 类型}
  证明: by
  -- Construct the coordinate-wise extensions
  rw [LipschitzOnWith.coordinate] at hfl
  have (i : ι) : exists g : α -> Real, LipschitzWith K g ∧ EqOn (fun x => f x i) g s :=
    LipschitzOnWith.extend_real (hfl i) -- use the nonlinear Hahn-Banach theorem here!
  choose g hgl hgeq using this
  rc
-/
theorem LipschitzOnWith.extend_lp_infty [PseudoMetricSpace α] {s : Set α} {ι : Type*}
    {f : α -> ℓ^∞(ι, Real)} {K : Real>=0} (hfl : LipschitzOnWith K f s) :
    exists g : α -> ℓ^∞(ι, Real), LipschitzWith K g ∧ EqOn f g s := by
  -- Construct the coordinate-wise extensions
  rw [LipschitzOnWith.coordinate] at hfl
  have (i : ι) : exists g : α -> Real, LipschitzWith K g ∧ EqOn (fun x => f x i) g s :=
    LipschitzOnWith.extend_real (hfl i) -- use the nonlinear Hahn-Banach theorem here!
  choose g hgl hgeq using this
  rcases s.eq_empty_or_nonempty with rfl | ⟨a₀, ha₀_in_s⟩
  · exact ⟨0, LipschitzWith.const' 0, by simp⟩
  · -- Show that the extensions are uniformly bounded
    have hf_extb : forall a : α, Memℓp (swap g a) ∞ := by
      apply LipschitzWith.uniformly_bounded (swap g) hgl a₀
      use ‖f a₀‖
      rintro - ⟨i, rfl⟩
      simp_rw [← hgeq i ha₀_in_s]
      exact lp.norm_apply_le_norm top_ne_zero (f a₀) i
    -- Construct witness by bundling the function with its certificate of membership in ℓ^∞
    let f_ext' : α -> ℓ^∞(ι, Real) := fun i => ⟨swap g i, hf_extb i⟩
    refine ⟨f_ext', ?_, ?_⟩
    · rw [LipschitzWith.coordinate]
      exact hgl
    · intro a hyp
      ext i
      exact (hgeq i) hyp
