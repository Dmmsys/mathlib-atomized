/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.ZLattice.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
public import Mathlib.Analysis.PSeries

/-!
# Convergence of `p`-series on lattices

Let `E` be a finite dimensional normed `ℝ`-space, and `L` a discrete subgroup of `E` of rank `d`.
We show that `∑ z ∈ L, ‖z - x‖ʳ` is convergent for `r < -d`.

## Main results
- `ZLattice.summable_norm_rpow`: `∑ z ∈ L, ‖z‖ʳ` converges when `r < -d`.
- `ZLattice.summable_norm_sub_rpow`: `∑ z ∈ L, ‖z - x‖ʳ` converges when `r < -d`.
- `ZLattice.tsum_norm_rpow_le`:
  `∑ z ∈ L, ‖z‖ʳ ≤ Aʳ * ∑ k : ℕ, kᵈ⁺ʳ⁻¹` for some `A > 0` depending only on `L`.

-/

@[expose] public section

noncomputable section

open Module

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] {L : Submodule Int E} [DiscreteTopology L]
variable {ι : Type*} (b : Basis ι Int L)

namespace ZLattice

/--
lemma `exists_forall_abs_repr_le_norm` / 引理 `exists_forall_abs_repr_le_norm`

English:
lemma exists_forall_abs_repr_le_norm
  proof: by
  wlog H : IsZLattice Real L
  · let E' := Submodule.span Real (L : Set E)
    let L' : Submodule Int E' := ZLattice.comap Real L E'.subtype
    have inst : DiscreteTopology L' :=
      comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[Int] L := Submodule.comapSubty

中文:
引理 exists_forall_abs_repr_le_norm
  证明: by
  wlog H : IsZLattice Real L
  · let E' := Submodule.span Real (L : Set E)
    let L' : Submodule Int E' := ZLattice.comap Real L E'.subtype
    have inst : DiscreteTopology L' :=
      comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[Int] L := Submodule.comapSubty

Depends on / 依赖: DiscreteTopology, IsZLattice, Submodule, Submodule.comapSubtypeEquivOfLe, Submodule.map_injective_of_injective, Submodule.span, Submodule.subset_span, Subtype, Subtype.val_injective, ZLattice, ZLattice.comap, b.map, comapSubtypeEquivOfLe, comap_discreteTopology, fun_prop, map_injective_of_injective, restrictScalars, subset_span, subtype, subtype_injective
-/
lemma exists_forall_abs_repr_le_norm :
    exists (ε : Real), 0 < ε ∧ forall (x : L), forall i, ε * |b.repr x i| <= ‖x‖ := by
  wlog H : IsZLattice Real L
  · let E' := Submodule.span Real (L : Set E)
    let L' : Submodule Int E' := ZLattice.comap Real L E'.subtype
    have inst : DiscreteTopology L' :=
      comap_discreteTopology _ _ (by fun_prop) Subtype.val_injective
    let e : L' ≃ₗ[Int] L := Submodule.comapSubtypeEquivOfLe (p := L) (q := E'.restrictScalars Int)
      Submodule.subset_span
    have inst : IsZLattice Real L' :=
      ⟨Submodule.map_injective_of_injective E'.subtype_injective (by simp [E', L'])⟩
    obtain ⟨ε, hε, H⟩ := this (b.map e.symm) inst
    exact ⟨ε, hε, fun x i => by simpa using! H ⟨⟨x.1, Submodule.subset_span x.2⟩, x.2⟩ i⟩
  have : Finite ι := Module.Finite.finite_basis b
  let b' : Basis ι Real E := Basis.ofZLatticeBasis Real L b
  let e := ((b'.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).toContinuousLinearEquiv (𝕜 := Real))
  have := e.continuous.1 (Set.univ.pi fun _ => Set.Ioo (-1) 1)
    (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Ioo)
  obtain ⟨ε, hε, hε'⟩ := Metric.isOpen_iff.mp this 0 (by simp)
  refine ⟨ε / 2, by positivity, fun x i => ?_⟩
  by_cases hx : x = 0
  · simp [hx]
  have hx : ‖x.1‖ != 0 := by simpa
  have : |ε / 2 * (‖↑x‖⁻¹ * (b.repr x) i)| < 1 := by
    simpa [e, b', ← abs_lt] using! @hε' ((ε / 2) • ‖x‖⁻¹ • x)
      (by simpa [norm_smul, inv_mul_cancel₀ hx, abs_eq_self.mpr hε.le]) i trivial
  rw [abs_mul]; rw [abs_mul]; rw [abs_inv]; rw [mul_left_comm]; rw [abs_norm]; rw [inv_mul_lt_iff₀ (by positivity)]; rw [mul_one]; rw [abs_eq_self.mpr (by positivity)]; rw [← Int.cast_abs] at this
  exact this.le

/--
Definition of `normBound` / `normBound` 的定义

English:
definition normBound
  signature: {ι : Type*} (b : Basis ι Int L)
  body: (exists_forall_abs_repr_le_norm b).choose

中文:
定义 normBound
  签名: {ι : 类型} (b : Basis ι 整数 L)
  定义体: (exists_forall_abs_repr_le_norm b).choose

Depends on / 依赖: exists_forall_abs_repr_le_norm
-/
def normBound {ι : Type*} (b : Basis ι Int L) : Real :=
  (exists_forall_abs_repr_le_norm b).choose

/--
lemma `normBound_pos` / 引理 `normBound_pos`

English:
lemma normBound_pos
  given: {ι : Type*} (b : Basis ι Int L)
  statement: 0 < normBound b
  proof: (exists_forall_abs_repr_le_norm b).choose_spec.1

中文:
引理 normBound_pos
  条件: {ι : 类型} (b : Basis ι 整数 L)
  结论: 0 < normBound b
  证明: (exists_forall_abs_repr_le_norm b).choose_spec.1

Depends on / 依赖: choose_spec, exists_forall_abs_repr_le_norm
-/
lemma normBound_pos {ι : Type*} (b : Basis ι Int L) : 0 < normBound b :=
  (exists_forall_abs_repr_le_norm b).choose_spec.1

/--
lemma `normBound_spec` / 引理 `normBound_spec`

English:
lemma normBound_spec
  given: {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι)
  proof: (exists_forall_abs_repr_le_norm b).choose_spec.2 x i

中文:
引理 normBound_spec
  条件: {ι : 类型} (b : Basis ι 整数 L) (x : L) (i : ι)
  证明: (exists_forall_abs_repr_le_norm b).choose_spec.2 x i

Depends on / 依赖: choose_spec, exists_forall_abs_repr_le_norm
-/
lemma normBound_spec {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι) :
    normBound b * |b.repr x i| <= ‖x‖ :=
  (exists_forall_abs_repr_le_norm b).choose_spec.2 x i

/--
lemma `abs_repr_le` / 引理 `abs_repr_le`

English:
lemma abs_repr_le
  given: {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι)
  proof: by
  rw [le_inv_mul_iff₀ (normBound_pos b)]
  exact normBound_spec b x i

中文:
引理 abs_repr_le
  条件: {ι : 类型} (b : Basis ι 整数 L) (x : L) (i : ι)
  证明: by
  rw [le_inv_mul_iff₀ (normBound_pos b)]
  exact normBound_spec b x i

Depends on / 依赖: normBound_pos, normBound_spec
-/
lemma abs_repr_le {ι : Type*} (b : Basis ι Int L) (x : L) (i : ι) :
    |b.repr x i| <= (normBound b)⁻¹ * ‖x‖ := by
  rw [le_inv_mul_iff₀ (normBound_pos b)]
  exact normBound_spec b x i

/--
lemma `abs_repr_lt_of_norm_lt` / 引理 `abs_repr_lt_of_norm_lt`

English:
lemma abs_repr_lt_of_norm_lt
  statement: {ι : Type*} (b : Basis ι Int L) (x : L) (n : Nat)
  proof: by
  refine Int.cast_lt.mp ((abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (normBound_pos b)]

中文:
引理 abs_repr_lt_of_norm_lt
  结论: {ι : 类型} (b : Basis ι 整数 L) (x : L) (n : 自然数)
  证明: by
  refine Int.cast_lt.mp ((abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (normBound_pos b)]

Depends on / 依赖: Int.cast_lt.mp, abs_repr_le, cast_lt, normBound_pos, trans_lt
-/
lemma abs_repr_lt_of_norm_lt {ι : Type*} (b : Basis ι Int L) (x : L) (n : Nat)
    (hxn : ‖x‖ < normBound b * n) (i : ι) : |b.repr x i| < n := by
  refine Int.cast_lt.mp ((abs_repr_le b x i).trans_lt ?_)
  rwa [inv_mul_lt_iff₀ (normBound_pos b)]

/--
lemma `le_norm_of_le_abs_repr` / 引理 `le_norm_of_le_abs_repr`

English:
lemma le_norm_of_le_abs_repr
  statement: {ι : Type*} (b : Basis ι Int L) (x : L) (n : Nat) (i : ι)
  proof: by
  contrapose! hi
  exact abs_repr_lt_of_norm_lt b x n hi i

中文:
引理 le_norm_of_le_abs_repr
  结论: {ι : 类型} (b : Basis ι 整数 L) (x : L) (n : 自然数) (i : ι)
  证明: by
  contrapose! hi
  exact abs_repr_lt_of_norm_lt b x n hi i

Depends on / 依赖: abs_repr_lt_of_norm_lt, contrapose
-/
lemma le_norm_of_le_abs_repr {ι : Type*} (b : Basis ι Int L) (x : L) (n : Nat) (i : ι)
    (hi : n <= |b.repr x i|) : normBound b * n <= ‖x‖ := by
  contrapose! hi
  exact abs_repr_lt_of_norm_lt b x n hi i

open Finset in
/--
lemma `sum_piFinset_Icc_rpow_le` / 引理 `sum_piFinset_Icc_rpow_le`

English:
lemma sum_piFinset_Icc_rpow_le
  statement: {ι : Type*} [Fintype ι] [DecidableEq ι]
  proof: by
  let s (n : Nat) := Fintype.piFinset fun i : ι => Icc (-n : Int) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    simp [hd, hr'.ne]
  replace hd : 1 <= d := by rwa [Nat.one_le_i

中文:
引理 sum_piFinset_Icc_rpow_le
  结论: {ι : 类型} [Fintype ι] [DecidableEq ι]
  证明: by
  let s (n : Nat) := Fintype.piFinset fun i : ι => Icc (-n : Int) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    simp [hd, hr'.ne]
  replace hd : 1 <= d := by rwa [Nat.one_le_i

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_eq_zero_iff.mp, Fintype.piFinset, IsEmpty, Nat.one_le_iff_ne_zero, card_eq_zero_iff, funext_iff, hr.trans_le, one_le_iff_ne_zero, piFinset, replace, subseteq, trans_le
-/
lemma sum_piFinset_Icc_rpow_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Basis ι Int L) {d : Nat} (hd : d = Fintype.card ι)
    (n : Nat) (r : Real) (hr : r < -d) :
    ∑ p in Fintype.piFinset fun _ : ι => Icc (-n : Int) n, ‖∑ i, p i • b i‖ ^ r <=
      2 * d * 3 ^ (d - 1) * normBound b ^ r * ∑' k : Nat, (k : Real) ^ (d - 1 + r) := by
  let s (n : Nat) := Fintype.piFinset fun i : ι => Icc (-n : Int) n
  subst hd
  set d := Fintype.card ι
  have hr' : r < 0 := hr.trans_le (by linarith)
  by_cases hd : d = 0
  · have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hd
    simp [hd, hr'.ne]
  replace hd : 1 <= d := by rwa [Nat.one_le_iff_ne_zero]
  have hs0 : s 0 = {0} := by ext; simp [s, funext_iff]
  have hs {a b : Nat} (ha : a <= b) : s a subseteq s b := by grind
  have (k : Nat) : #(s (k + 1) \ s k) <= 2 * d * (2 * k + 3) ^ (d - 1) := by
    simp only [le_add_iff_nonneg_right, zero_le, hs, card_sdiff_of_subset, s, Fintype.card_piFinset,
      Int.card_Icc, prod_const]
    grind [abs_pow_sub_pow_le (α := Int) (2 * k + 3) (2 * k + 1) d]
  let ε := normBound b
  have hε : 0 < ε := normBound_pos b
  calc ∑ p in s n, ‖∑ i, p i • b i‖ ^ r
      = ∑ k in range n, ∑ p in (s (k + 1) \ s k), ‖∑ i, p i • b i‖ ^ r := by
        simp [Finset.sum_eq_sum_range_sdiff _ @hs, hs0, hr'.ne]
    _ <= ∑ k in range n, ∑ p in (s (k + 1) \ s k), ((k + 1) * ε) ^ r := by
        gcongr ∑ k in Finset.range n, ∑ p in (s (k + 1) \ s k), ?_ with k hk v hv
        rw [← Nat.cast_one]; rw [← Nat.cast_add]
        refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ hr'.le
        obtain ⟨j, hj⟩ : exists i, v i ∉ Icc (-k : Int) k := by simpa [s] using (mem_sdiff.mp hv).2
        refine mul_comm _ ε ▸ le_norm_of_le_abs_repr b _ _ j ?_
        suffices ↑k + 1 <= |v j| by simpa [Finsupp.single_apply] using this
        by_contra! H
        rw [Int.lt_add_one_iff]; rw [abs_le]; rw [← Finset.mem_Icc] at H
        exact hj H
    _ <= ∑ k in range n, ↑(2 * d * (3 * (k + 1)) ^ (d - 1)) * ((k + 1) * ε) ^ r := by
        simp only [sum_const, nsmul_eq_mul]
        gcongr with k hk
        refine (this _).trans ?_
        gcongr
        lia
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k in range n, (k + 1) ^ (d - 1) * (k + 1 : Real) ^ r := by
        simp_rw [Finset.mul_sum]
        congr with k
        push_cast
        rw [Real.mul_rpow (by positivity) (by positivity)]; rw [mul_pow]
        group
    _ = 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k in range n, (↑(k + 1) : Real) ^ (d - 1 + r) := by
        congr with k
        rw [← Real.rpow_natCast]; rw [← Real.rpow_add (by positivity)]; rw [Nat.cast_sub hd]
        norm_cast
    _ <= 2 * d * 3 ^ (d - 1) * ε ^ r * ∑ k in range (n + 1), (k : Real) ^ (d - 1 + r) := by
        grw [Finset.sum_range_succ', Nat.cast_zero, ← Real.rpow_nonneg le_rfl, add_zero]
    _ <= 2 * d * 3 ^ (d - 1) * ε ^ r * ∑' k : Nat, (k : Real) ^ (d - 1 + r) := by
        gcongr
        refine Summable.sum_le_tsum _ (fun _ _ => by positivity) (Real.summable_nat_rpow.mpr ?_)
        linarith

variable (L)

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exists_finsetSum_norm_rpow_le_tsum` / 引理 `exists_finsetSum_norm_rpow_le_tsum`

English:
lemma exists_finsetSum_norm_rpow_le_tsum
  proof: by
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s => ?_⟩
    have hr : r != 0 := by linarith
    simpa [Subsingleton.elim _ (0 : L), Real.zero_rpow hr] using tsum_nonneg fun _ => by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex Int L
  have : Fi

中文:
引理 exists_finsetSum_norm_rpow_le_tsum
  证明: by
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s => ?_⟩
    have hr : r != 0 := by linarith
    simpa [Subsingleton.elim _ (0 : L), Real.zero_rpow hr] using tsum_nonneg fun _ => by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex Int L
  have : Fi

Depends on / 依赖: ChooseBasisIndex, Fintype, Fintype.card, Module, Module.Free.ChooseBasisIndex, Module.Free.chooseBasis, Module.finrank_eq_card_basis, Real.zero_rpow, Subsingleton, Subsingleton.elim, chooseBasis, classical, finrank_eq_card_basis, normBound, simp_rw, subsingleton_or_nontrivial, tsum_nonneg, zero_lt_one, zero_rpow
-/
lemma exists_finsetSum_norm_rpow_le_tsum :
    exists A > (0 : Real), forall r < (-Module.finrank Int L : Real), forall s : Finset L,
      ∑ z in s, ‖z‖ ^ r <= A ^ r * ∑' k : Nat, (k : Real) ^ (Module.finrank Int L - 1 + r) := by
  cases subsingleton_or_nontrivial L
  · refine ⟨1, zero_lt_one, fun r hr s => ?_⟩
    have hr : r != 0 := by linarith
    simpa [Subsingleton.elim _ (0 : L), Real.zero_rpow hr] using tsum_nonneg fun _ => by positivity
  classical
  let I : Type _ := Module.Free.ChooseBasisIndex Int L
  have : Fintype I := inferInstance
  let b : Basis I Int L := Module.Free.chooseBasis Int L
  simp_rw [Module.finrank_eq_card_basis b]
  set d := Fintype.card I
  have hd : d != 0 := by simp [d]
  let ε := normBound b
  obtain ⟨A, hA, B, hB, H⟩ : exists A > (0 : Real), exists B > (0 : Real), forall r < (-d : Real), forall s : Finset L,
      ∑ z in s, ‖z‖ ^ r <= A * B ^ r * ∑' k : Nat, (k : Real) ^ (d - 1 + r) := by
    refine ⟨2 * d * 3 ^ (d - 1), by positivity, ε, normBound_pos b, fun r hr u => ?_⟩
    let e : (I -> Int) ≃ₗ[Int] L := (b.repr ≪≫ₗ Finsupp.linearEquivFunOnFinite _ _ _).symm
    obtain ⟨u, rfl⟩ : exists u' : Finset _, u = u'.image e.toEmbedding :=
      ⟨u.image e.symm.toEmbedding, Finset.coe_injective
        (by simpa using (e.image_symm_image _).symm)⟩
    dsimp
    simp only [EmbeddingLike.apply_eq_iff_eq, implies_true, Set.injOn_of_eq_iff_eq,
      Finset.sum_image, ge_iff_le]
    obtain ⟨n, hn⟩ : exists n : Nat, u subseteq Fintype.piFinset fun _ : I => Finset.Icc (-n : Int) n := by
      obtain ⟨r, hr, hr'⟩ := u.finite_toSet.isCompact.isBounded.subset_closedBall_lt 0 0
      refine ⟨⌊r⌋.toNat, fun x hx => ?_⟩
      have hr'' : ⌊r⌋ ⊔ 0 = ⌊r⌋ := by rw [sup_eq_left]; positivity
      have := hr' hx
      simp only [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hr.le,
        Int.norm_eq_abs, ← Int.cast_abs, ← Int.le_floor] at this
      simpa only [Int.ofNat_toNat, Fintype.mem_piFinset, Finset.mem_Icc, ← abs_le, hr'']
    refine (Finset.sum_le_sum_of_subset_of_nonneg hn (by intros; positivity)).trans ?_
    simp only [Submodule.norm_coe]
    convert! sum_piFinset_Icc_rpow_le b rfl n r hr with x
    simp [e, Finsupp.linearCombination]
  by_cases hA' : A <= 1
  · refine ⟨B, hB, fun r hr s => (H r hr s).trans ?_⟩
    rw [mul_assoc]
    exact mul_le_of_le_one_left (mul_nonneg (by positivity) (by positivity)) hA'
  · refine ⟨A⁻¹ * B, mul_pos (inv_pos.mpr hA) hB, fun r hr s => (H r hr s).trans ?_⟩
    rw [Real.mul_rpow (inv_pos.mpr hA).le hB.le]; rw [mul_assoc]; rw [mul_assoc]
    gcongr
    rw [← Real.rpow_neg_one]; rw [← Real.rpow_mul hA.le]
    refine Real.self_le_rpow_of_one_le (not_le.mp hA').le ?_
    simp only [neg_mul, one_mul, le_neg (b := r)]
    refine hr.le.trans ?_
    simpa [Nat.one_le_iff_ne_zero]

/--
Definition of `tsumNormRPowBound` / `tsumNormRPowBound` 的定义

English:
definition tsumNormRPowBound
  signature: : Real
  body: (exists_finsetSum_norm_rpow_le_tsum L).choose

中文:
定义 tsumNormRPowBound
  签名: : 实数
  定义体: (exists_finsetSum_norm_rpow_le_tsum L).choose

Depends on / 依赖: exists_finsetSum_norm_rpow_le_tsum
-/
def tsumNormRPowBound : Real :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose

/--
lemma `tsumNormRPowBound_pos` / 引理 `tsumNormRPowBound_pos`

English:
lemma tsumNormRPowBound_pos
  statement: 0 < tsumNormRPowBound L
  proof: (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.1

中文:
引理 tsumNormRPowBound_pos
  结论: 0 < tsumNormRPowBound L
  证明: (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.1

Depends on / 依赖: choose_spec, exists_finsetSum_norm_rpow_le_tsum
-/
lemma tsumNormRPowBound_pos : 0 < tsumNormRPowBound L :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.1

/--
lemma `tsumNormRPowBound_spec` / 引理 `tsumNormRPowBound_spec`

English:
lemma tsumNormRPowBound_spec
  given: (r : Real) (h : r < -Module.finrank Int L) (s : Finset L)
  proof: (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.2 r h s

中文:
引理 tsumNormRPowBound_spec
  条件: (r : 实数) (h : r < -Module.finrank 整数 L) (s : Finset L)
  证明: (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.2 r h s

Depends on / 依赖: choose_spec, exists_finsetSum_norm_rpow_le_tsum
-/
lemma tsumNormRPowBound_spec (r : Real) (h : r < -Module.finrank Int L) (s : Finset L) :
    ∑ z in s, ‖z‖ ^ r <=
      tsumNormRPowBound L ^ r * ∑' k : Nat, (k : Real) ^ (Module.finrank Int L - 1 + r) :=
  (exists_finsetSum_norm_rpow_le_tsum L).choose_spec.2 r h s

/--
lemma `summable_norm_rpow` / 引理 `summable_norm_rpow`

English:
lemma summable_norm_rpow
  given: (r : Real) (hr : r < -Module.finrank Int L)
  proof: summable_of_sum_le (fun _ => by positivity) (tsumNormRPowBound_spec L r hr)

中文:
引理 summable_norm_rpow
  条件: (r : 实数) (hr : r < -Module.finrank 整数 L)
  证明: summable_of_sum_le (fun _ => by positivity) (tsumNormRPowBound_spec L r hr)

Depends on / 依赖: summable_of_sum_le, tsumNormRPowBound_spec
-/
lemma summable_norm_rpow (r : Real) (hr : r < -Module.finrank Int L) :
    Summable fun z : L => ‖z‖ ^ r :=
  summable_of_sum_le (fun _ => by positivity) (tsumNormRPowBound_spec L r hr)

/--
lemma `tsum_norm_rpow_le` / 引理 `tsum_norm_rpow_le`

English:
lemma tsum_norm_rpow_le
  given: (r : Real) (hr : r < -Module.finrank Int L)
  proof: Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (tsumNormRPowBound_spec L r hr)

中文:
引理 tsum_norm_rpow_le
  条件: (r : 实数) (hr : r < -Module.finrank 整数 L)
  证明: Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (tsumNormRPowBound_spec L r hr)

Depends on / 依赖: Summable, Summable.tsum_le_of_sum_le, summable_norm_rpow, tsumNormRPowBound_spec, tsum_le_of_sum_le
-/
lemma tsum_norm_rpow_le (r : Real) (hr : r < -Module.finrank Int L) :
    ∑' z : L, ‖z‖ ^ r <=
      tsumNormRPowBound L ^ r * ∑' k : Nat, (k : Real) ^ (Module.finrank Int L - 1 + r) :=
  Summable.tsum_le_of_sum_le (summable_norm_rpow L r hr) (tsumNormRPowBound_spec L r hr)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `summable_norm_sub_rpow` / 引理 `summable_norm_sub_rpow`

English:
lemma summable_norm_sub_rpow
  given: (r : Real) (hr : r < -Module.finrank Int L) (x : E)
  proof: by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology 

中文:
引理 summable_norm_sub_rpow
  条件: (r : 实数) (hr : r < -Module.finrank 整数 L) (x : E)
  证明: by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology 

Depends on / 依赖: AddSubgroup, AddSubgroup.isClosed_of_discrete, DiscreteTopology, DiscreteTopology.isDiscrete, IsClosed, L.toAddSubgroup, Metric, Metric.finite_isBounded_inter_isClosed, Metric.isBounded_closedBall, Summable, Summable.of_norm_bounded_eventually, finite_isBounded_inter_isClosed, isBounded_closedBall, isClosed_of_discrete, isDiscrete, mul_left, of_finite, of_norm_bounded_eventually, preimage_embedding, subset
-/
lemma summable_norm_sub_rpow (r : Real) (hr : r < -Module.finrank Int L) (x : E) :
    Summable fun z : L => ‖z - x‖ ^ r := by
  cases subsingleton_or_nontrivial L
  · exact .of_finite
  refine Summable.of_norm_bounded_eventually
    (.mul_left ((1 / 2) ^ r) (summable_norm_rpow L r hr)) ?_
  have H : IsClosed (X := E) L := @AddSubgroup.isClosed_of_discrete _ _ _ _ _
    L.toAddSubgroup (inferInstanceAs (DiscreteTopology L))
  refine ((Metric.finite_isBounded_inter_isClosed DiscreteTopology.isDiscrete
    (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * ‖x‖)) H).preimage_embedding
    (.subtype _)).subset ?_
  intro t ht
  by_cases ht₁ : ‖t‖ = 0
  · simp [show t = 0 by simpa using ht₁]
  by_cases ht₂ : ‖t - x‖ = 0
  · simpa [show t = x by simpa [sub_eq_zero] using ht₂, two_mul] using t.2
  have : 0 < Module.finrank Int L := Module.finrank_pos
  have : ‖t - x‖ < 2⁻¹ * ‖t‖ := by
    rw [← Real.rpow_lt_rpow_iff_of_neg (by positivity) (by positivity) (hr.trans (by simpa))]
    simpa [Real.mul_rpow, abs_eq_self.mpr (show 0 <= ‖t - x‖ ^ r by positivity)] using ht
  have := (norm_sub_norm_le _ _).trans_lt this
  rw [sub_lt_iff_lt_add]; rw [← sub_lt_iff_lt_add']; rw [AddSubgroupClass.coe_norm] at this
  simpa using show ‖t.1‖ <= 2 * ‖x‖ by linarith

/--
lemma `summable_norm_sub_zpow` / 引理 `summable_norm_sub_zpow`

English:
lemma summable_norm_sub_zpow
  given: (n : Int) (hn : n < -Module.finrank Int L) (x : E)
  proof: mod_cast summable_norm_sub_rpow L n (mod_cast hn) x

中文:
引理 summable_norm_sub_zpow
  条件: (n : 整数) (hn : n < -Module.finrank 整数 L) (x : E)
  证明: mod_cast summable_norm_sub_rpow L n (mod_cast hn) x

Depends on / 依赖: mod_cast, summable_norm_sub_rpow
-/
lemma summable_norm_sub_zpow (n : Int) (hn : n < -Module.finrank Int L) (x : E) :
    Summable fun z : L => ‖z - x‖ ^ n :=
  mod_cast summable_norm_sub_rpow L n (mod_cast hn) x

/--
lemma `summable_norm_zpow` / 引理 `summable_norm_zpow`

English:
lemma summable_norm_zpow
  given: (n : Int) (hn : n < -Module.finrank Int L)
  proof: by
  simpa using summable_norm_sub_zpow L n hn 0

中文:
引理 summable_norm_zpow
  条件: (n : 整数) (hn : n < -Module.finrank 整数 L)
  证明: by
  simpa using summable_norm_sub_zpow L n hn 0

Depends on / 依赖: summable_norm_sub_zpow
-/
lemma summable_norm_zpow (n : Int) (hn : n < -Module.finrank Int L) :
    Summable fun z : L => ‖z‖ ^ n := by
  simpa using summable_norm_sub_zpow L n hn 0

/--
lemma `summable_norm_sub_inv_pow` / 引理 `summable_norm_sub_inv_pow`

English:
lemma summable_norm_sub_inv_pow
  given: (n : Nat) (hn : Module.finrank Int L < n) (x : E)
  proof: by
  simpa using summable_norm_sub_zpow L (-n) (by gcongr) x

中文:
引理 summable_norm_sub_inv_pow
  条件: (n : 自然数) (hn : Module.finrank 整数 L < n) (x : E)
  证明: by
  simpa using summable_norm_sub_zpow L (-n) (by gcongr) x

Depends on / 依赖: summable_norm_sub_zpow
-/
lemma summable_norm_sub_inv_pow (n : Nat) (hn : Module.finrank Int L < n) (x : E) :
    Summable fun z : L => ‖z - x‖⁻¹ ^ n := by
  simpa using summable_norm_sub_zpow L (-n) (by gcongr) x

/--
lemma `summable_norm_pow_inv` / 引理 `summable_norm_pow_inv`

English:
lemma summable_norm_pow_inv
  given: (n : Nat) (hn : Module.finrank Int L < n)
  proof: by
  simpa using summable_norm_sub_inv_pow L n hn 0

中文:
引理 summable_norm_pow_inv
  条件: (n : 自然数) (hn : Module.finrank 整数 L < n)
  证明: by
  simpa using summable_norm_sub_inv_pow L n hn 0

Depends on / 依赖: summable_norm_sub_inv_pow
-/
lemma summable_norm_pow_inv (n : Nat) (hn : Module.finrank Int L < n) :
    Summable fun z : L => ‖z‖⁻¹ ^ n := by
  simpa using summable_norm_sub_inv_pow L n hn 0

end ZLattice
