/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Analysis.SpecificLimits.Normed

/-! # Extending a backward bound on a normed group homomorphism from a dense set

Possible TODO (from the PR's review, https://github.com/leanprover-community/mathlib/pull/8498):
"This feels a lot like the second step in the proof of the Banach open mapping theorem
(`exists_preimage_norm_le`) ... wonder if it would be possible to refactor it using one of [the
lemmas in this file]."
-/

public section


open Filter Finset

open Topology

variable {G : Type*} [NormedAddCommGroup G] [CompleteSpace G]
variable {H : Type*} [NormedAddCommGroup H]

/--
theorem `controlled_closure_of_complete` / 定理 `controlled_closure_of_complete`

English:
theorem controlled_closure_of_complete
  statement: {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : Real}
  proof: by
  rintro (h : H) (h_in : h in K.topologicalClosure)
  -- We first get rid of the easy case where `h = 0`.
  by_cases hyp_h : h = 0
  · rw [hyp_h]
    use 0
    simp
  /- The desired preimage will be constructed as the sum of a series. Convergence of
    the series will be guaranteed by completene

中文:
定理 controlled_closure_of_complete
  结论: {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : 实数}
  证明: by
  rintro (h : H) (h_in : h in K.topologicalClosure)
  -- We first get rid of the easy case where `h = 0`.
  by_cases hyp_h : h = 0
  · rw [hyp_h]
    use 0
    simp
  /- The desired preimage will be constructed as the sum of a series. Convergence of
    the series will be guaranteed by completene

Depends on / 依赖: K.topologicalClosure, h_in, topologicalClosure
-/
theorem controlled_closure_of_complete {f : NormedAddGroupHom G H} {K : AddSubgroup H} {C ε : Real}
    (hC : 0 < C) (hε : 0 < ε) (hyp : f.SurjectiveOnWith K C) :
    f.SurjectiveOnWith K.topologicalClosure (C + ε) := by
  rintro (h : H) (h_in : h in K.topologicalClosure)
  -- We first get rid of the easy case where `h = 0`.
  by_cases hyp_h : h = 0
  · rw [hyp_h]
    use 0
    simp
  /- The desired preimage will be constructed as the sum of a series. Convergence of
    the series will be guaranteed by completeness of `G`. We first write `h` as the sum
    of a sequence `v` of elements of `K` which starts close to `h` and then quickly goes to zero.
    The sequence `b` below quantifies this. -/
  set b : Nat -> Real := fun i => (1 / 2) ^ i * (ε * ‖h‖ / 2) / C
  have b_pos (i) : 0 < b i := by positivity
  obtain
    ⟨v : Nat -> H, lim_v : Tendsto (fun n : Nat => ∑ k in range (n + 1), v k) atTop (𝓝 h), v_in :
      forall n, v n in K, hv₀ : ‖-v 0 + h‖ < b 0, hv : forall n > 0, ‖v n‖ < b n⟩ :=
    controlled_sum_of_mem_closure h_in b_pos
  /- The controlled surjectivity assumption on `f` allows to build preimages `u n` for all
    elements `v n` of the `v` sequence. -/
  have : forall n, exists m' : G, f m' = v n ∧ ‖m'‖ <= C * ‖v n‖ := fun n : Nat => hyp (v n) (v_in n)
  choose u hu hnorm_u using this
  /- The desired series `s` is then obtained by summing `u`. We then check our choice of
    `b` ensures `s` is Cauchy. -/
  set s : Nat -> G := fun n => ∑ k in range (n + 1), u k
  have : CauchySeq s := by
    apply NormedAddCommGroup.cauchy_series_of_le_geometric'' (by simp) one_half_lt_one
    · rintro n (hn : n >= 1)
      calc
        ‖u n‖ <= C * ‖v n‖ := hnorm_u n
        _ <= C * b n := by gcongr; exact (hv _ <| Nat.succ_le_iff.mp hn).le
        _ = (1 / 2) ^ n * (ε * ‖h‖ / 2) := by simp [b, mul_div_cancel₀ _ hC.ne.symm]
        _ = ε * ‖h‖ / 2 * (1 / 2) ^ n := mul_comm _ _
  -- We now show that the limit `g` of `s` is the desired preimage.
  obtain ⟨g : G, hg⟩ := cauchySeq_tendsto_of_complete this
  refine ⟨g, ?_, ?_⟩
  · -- We indeed get a preimage. First note:
    have : f ∘ s = fun n => ∑ k in range (n + 1), v k := by
      ext n
      simp [s, map_sum, hu]
    /- In the above equality, the left-hand-side converges to `f g` by continuity of `f` and
      definition of `g` while the right-hand-side converges to `h` by construction of `v` so
      `g` is indeed a preimage of `h`. -/
    rw [← this] at lim_v
    exact tendsto_nhds_unique ((f.continuous.tendsto g).comp hg) lim_v
  · -- Then we need to estimate the norm of `g`, using our careful choice of `b`.
    suffices forall n, ‖s n‖ <= (C + ε) * ‖h‖ from
      le_of_tendsto' (continuous_norm.continuousAt.tendsto.comp hg) this
    intro n
    have hnorm₀ : ‖u 0‖ <= C * b 0 + C * ‖h‖ := by
      have :=
        calc
          ‖v 0‖ <= ‖h‖ + ‖v 0 - h‖ := norm_le_insert' _ _
          _ <= ‖h‖ + b 0 := by rw [← norm_neg_add]; gcongr
      calc
        ‖u 0‖ <= C * ‖v 0‖ := hnorm_u 0
        _ <= C * (‖h‖ + b 0) := by gcongr
        _ = C * b 0 + C * ‖h‖ := by rw [add_comm, mul_add]
    have : (∑ k in range (n + 1), C * b k) <= ε * ‖h‖ :=
      calc (∑ k in range (n + 1), C * b k)
        _ = (∑ k in range (n + 1), (1 / 2 : Real) ^ k) * (ε * ‖h‖ / 2) := by
          simp only [b, mul_div_cancel₀ _ hC.ne.symm, ← sum_mul]
        _ <= 2 * (ε * ‖h‖ / 2) := by gcongr; apply sum_geometric_two_le
        _ = ε * ‖h‖ := mul_div_cancel₀ _ two_ne_zero
    calc
      ‖s n‖ <= ∑ k in range (n + 1), ‖u k‖ := norm_sum_le _ _
      _ = (∑ k in range n, ‖u (k + 1)‖) + ‖u 0‖ := sum_range_succ' _ _
      _ <= (∑ k in range n, C * ‖v (k + 1)‖) + ‖u 0‖ := by gcongr; apply hnorm_u
      _ <= (∑ k in range n, C * b (k + 1)) + (C * b 0 + C * ‖h‖) := by
        gcongr with k; exact (hv _ k.succ_pos).le
      _ = (∑ k in range (n + 1), C * b k) + C * ‖h‖ := by rw [← add_assoc, sum_range_succ']
      _ <= (C + ε) * ‖h‖ := by
        rw [add_comm]; rw [add_mul]
        gcongr

/--
theorem `controlled_closure_range_of_complete` / 定理 `controlled_closure_range_of_complete`

English:
theorem controlled_closure_range_of_complete
  statement: {f : NormedAddGroupHom G H} {K : Type*}
  proof: by
  replace hyp : forall h in j.range, exists g, f g = h ∧ ‖g‖ <= C * ‖h‖ := by
    intro h h_in
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp

中文:
定理 controlled_closure_range_of_complete
  结论: {f : NormedAddGroupHom G H} {K : 类型}
  证明: by
  replace hyp : forall h in j.range, exists g, f g = h ∧ ‖g‖ <= C * ‖h‖ := by
    intro h h_in
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp

Depends on / 依赖: controlled_closure_of_complete, h_in, j.mem_range, j.range, mem_range, replace
-/
theorem controlled_closure_range_of_complete {f : NormedAddGroupHom G H} {K : Type*}
    [SeminormedAddCommGroup K] {j : NormedAddGroupHom K H} (hj : forall x, ‖j x‖ = ‖x‖) {C ε : Real}
    (hC : 0 < C) (hε : 0 < ε) (hyp : forall k, exists g, f g = j k ∧ ‖g‖ <= C * ‖k‖) :
    f.SurjectiveOnWith j.range.topologicalClosure (C + ε) := by
  replace hyp : forall h in j.range, exists g, f g = h ∧ ‖g‖ <= C * ‖h‖ := by
    intro h h_in
    rcases (j.mem_range _).mp h_in with ⟨k, rfl⟩
    rw [hj]
    exact hyp k
  exact controlled_closure_of_complete hC hε hyp
