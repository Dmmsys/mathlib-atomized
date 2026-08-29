/-
Copyright (c) 2019 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp, Yury Kudryashov, Yaël Dillies, Joël Riou
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite
public import Mathlib.Topology.UnitInterval

/-!
# The standard simplex

In this file, given an ordered semiring `𝕜` and a finite type `ι`,
we define `stdSimplex : Set (ι → 𝕜)` as the set of vectors with non-negative
coordinates with total sum `1`.

When `f : X → Y` is a map between finite types, we define the map
`stdSimplex.map f : stdSimplex 𝕜 X → stdSimplex 𝕜 Y`.

-/

@[expose] public section

open Set Convex Bornology

section OrderedSemiring

variable (𝕜) (ι : Type*) [Semiring 𝕜] [PartialOrder 𝕜] [Fintype ι]

/--
Definition of `stdSimplex` / `stdSimplex` 的定义

English:
definition stdSimplex
  signature: : Set (ι -> 𝕜)
  body: { f | (forall x, 0 <= f x) ∧ ∑ x, f x = 1 }

中文:
定义 stdSimplex
  签名: : 集合 (ι -> 𝕜)
  定义体: { f | (forall x, 0 <= f x) ∧ ∑ x, f x = 1 }
-/
def stdSimplex : Set (ι -> 𝕜) :=
  { f | (forall x, 0 <= f x) ∧ ∑ x, f x = 1 }

/--
theorem `stdSimplex_eq_inter` / 定理 `stdSimplex_eq_inter`

English:
theorem stdSimplex_eq_inter
  statement: stdSimplex 𝕜 ι = (⋂ x, { f | 0 <= f x }) inter { f | ∑ x, f x = 1 }
  proof: by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

中文:
定理 stdSimplex_eq_inter
  结论: stdSimplex 𝕜 ι = (⋂ x, { f | 0 <= f x }) inter { f | ∑ x, f x = 1 }
  证明: by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

Depends on / 依赖: Set.mem_iInter, Set.mem_inter_iff, Set.mem_ofPred_eq, mem_iInter, mem_inter_iff, mem_ofPred_eq, stdSimplex
-/
theorem stdSimplex_eq_inter : stdSimplex 𝕜 ι = (⋂ x, { f | 0 <= f x }) inter { f | ∑ x, f x = 1 } := by
  ext f
  simp only [stdSimplex, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]

/--
theorem `convex_stdSimplex` / 定理 `convex_stdSimplex`

English:
theorem convex_stdSimplex
  given: [IsOrderedRing 𝕜]
  statement: Convex 𝕜 (stdSimplex 𝕜 ι)
  proof: by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

中文:
定理 convex_stdSimplex
  条件: [是Ordered环 𝕜]
  结论: 凸 𝕜 (stdSimplex 𝕜 ι)
  证明: by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

Depends on / 依赖: Finset, Finset.smul_sum, Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, add_apply, add_nonneg, apply_rules, mul_nonneg, mul_one, simp_rw, smul_apply, smul_eq_mul, smul_sum, sum_add_distrib
-/
theorem convex_stdSimplex [IsOrderedRing 𝕜] : Convex 𝕜 (stdSimplex 𝕜 ι) := by
  refine fun f hf g hg a b ha hb hab => ⟨fun x => ?_, ?_⟩
  · apply_rules [add_nonneg, mul_nonneg, hf.1, hg.1]
  · simp_rw [Pi.add_apply, Pi.smul_apply]
    rwa [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hf.2, hg.2, smul_eq_mul,
      smul_eq_mul, mul_one, mul_one]

/--
lemma `stdSimplex_of_subsingleton` / 引理 `stdSimplex_of_subsingleton`

English:
lemma stdSimplex_of_subsingleton
  given: [Subsingleton 𝕜]
  statement: stdSimplex 𝕜 ι = univ
  proof: eq_univ_of_forall fun _ => ⟨fun _ => (Subsingleton.elim _ _).le, Subsingleton.elim _ _⟩

中文:
引理 stdSimplex_of_subsingleton
  条件: [子单例 𝕜]
  结论: stdSimplex 𝕜 ι = univ
  证明: eq_univ_of_forall fun _ => ⟨fun _ => (Subsingleton.elim _ _).le, Subsingleton.elim _ _⟩
-/
@[nontriviality] lemma stdSimplex_of_subsingleton [Subsingleton 𝕜] : stdSimplex 𝕜 ι = univ :=
  eq_univ_of_forall fun _ => ⟨fun _ => (Subsingleton.elim _ _).le, Subsingleton.elim _ _⟩

/--
lemma `stdSimplex_of_isEmpty_index` / 引理 `stdSimplex_of_isEmpty_index`

English:
lemma stdSimplex_of_isEmpty_index
  given: [IsEmpty ι] [Nontrivial 𝕜]
  statement: stdSimplex 𝕜 ι = ∅
  proof: eq_empty_of_forall_notMem by rintro f ⟨-, hf⟩; simp at hf

中文:
引理 stdSimplex_of_isEmpty_index
  条件: [是空 ι] [非平凡 𝕜]
  结论: stdSimplex 𝕜 ι = ∅
  证明: eq_empty_of_forall_notMem by rintro f ⟨-, hf⟩; simp at hf

Depends on / 依赖: eq_empty_of_forall_notMem
-/
lemma stdSimplex_of_isEmpty_index [IsEmpty ι] [Nontrivial 𝕜] : stdSimplex 𝕜 ι = ∅ :=
eq_empty_of_forall_notMem by rintro f ⟨-, hf⟩; simp at hf

/--
lemma `stdSimplex_unique` / 引理 `stdSimplex_unique`

English:
lemma stdSimplex_unique
  given: [ZeroLEOneClass 𝕜] [Nonempty ι] [Subsingleton ι]
  proof: by
  cases nonempty_unique ι
  refine eq_singleton_iff_unique_mem.2 ⟨⟨fun _ => zero_le_one, Fintype.sum_unique _⟩, ?_⟩
  rintro f ⟨-, hf⟩
  rw [Fintype.sum_unique] at hf
  exact funext (Unique.forall_iff.2 hf)

中文:
引理 stdSimplex_unique
  条件: [ZeroLEOne类 𝕜] [非空 ι] [子单例 ι]
  证明: by
  cases nonempty_unique ι
  refine eq_singleton_iff_unique_mem.2 ⟨⟨fun _ => zero_le_one, Fintype.sum_unique _⟩, ?_⟩
  rintro f ⟨-, hf⟩
  rw [Fintype.sum_unique] at hf
  exact funext (Unique.forall_iff.2 hf)

Depends on / 依赖: Fintype, Fintype.sum_unique, Unique, Unique.forall_iff, eq_singleton_iff_unique_mem, forall_iff, nonempty_unique, sum_unique, zero_le_one
-/
lemma stdSimplex_unique [ZeroLEOneClass 𝕜] [Nonempty ι] [Subsingleton ι] :
    stdSimplex 𝕜 ι = {fun _ => 1} := by
  cases nonempty_unique ι
  refine eq_singleton_iff_unique_mem.2 ⟨⟨fun _ => zero_le_one, Fintype.sum_unique _⟩, ?_⟩
  rintro f ⟨-, hf⟩
  rw [Fintype.sum_unique] at hf
  exact funext (Unique.forall_iff.2 hf)

variable {ι}

variable {𝕜} in
/--
theorem `mem_Icc_of_mem_stdSimplex` / 定理 `mem_Icc_of_mem_stdSimplex`

English:
theorem mem_Icc_of_mem_stdSimplex
  statement: [IsOrderedAddMonoid 𝕜]
  proof: ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

中文:
定理 mem_Icc_of_mem_stdSimplex
  结论: [是OrderedAdd幺半群 𝕜]
  证明: ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

Depends on / 依赖: Finset, Finset.mem_univ, Finset.single_le_sum, mem_univ, single_le_sum
-/
theorem mem_Icc_of_mem_stdSimplex [IsOrderedAddMonoid 𝕜]
    {f : ι -> 𝕜} (hf : f in stdSimplex 𝕜 ι) (x) :
    f x in Icc (0 : 𝕜) 1 :=
  ⟨hf.1 x, hf.2 ▸ Finset.single_le_sum (fun y _ => hf.1 y) (Finset.mem_univ x)⟩

/--
theorem `stdSimplex_subset_Icc` / 定理 `stdSimplex_subset_Icc`

English:
theorem stdSimplex_subset_Icc
  given: [IsOrderedAddMonoid 𝕜]
  statement: stdSimplex 𝕜 ι subseteq Icc 0 1
  proof: by
  intro f h
  rw [← pi_univ_Icc]; rw [univ_pi_eq_iInter]; rw [mem_iInter]
  simpa using fun i => mem_Icc_of_mem_stdSimplex h i

中文:
定理 stdSimplex_subset_Icc
  条件: [是OrderedAdd幺半群 𝕜]
  结论: stdSimplex 𝕜 ι subseteq 闭区间 0 1
  证明: by
  intro f h
  rw [← pi_univ_Icc]; rw [univ_pi_eq_iInter]; rw [mem_iInter]
  simpa using fun i => mem_Icc_of_mem_stdSimplex h i

Depends on / 依赖: mem_Icc_of_mem_stdSimplex, mem_iInter, pi_univ_Icc, univ_pi_eq_iInter
-/
theorem stdSimplex_subset_Icc [IsOrderedAddMonoid 𝕜] : stdSimplex 𝕜 ι subseteq Icc 0 1 := by
  intro f h
  rw [← pi_univ_Icc]; rw [univ_pi_eq_iInter]; rw [mem_iInter]
  simpa using fun i => mem_Icc_of_mem_stdSimplex h i

variable [DecidableEq ι] [ZeroLEOneClass 𝕜]

/--
theorem `single_mem_stdSimplex` / 定理 `single_mem_stdSimplex`

English:
theorem single_mem_stdSimplex
  given: (i : ι)
  statement: Pi.single i 1 in stdSimplex 𝕜 ι
  proof: ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

中文:
定理 single_mem_stdSimplex
  条件: (i : ι)
  结论: 依赖函数类型.single i 1 in stdSimplex 𝕜 ι
  证明: ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

Depends on / 依赖: le_rfl, le_update_iff, zero_le_one
-/
theorem single_mem_stdSimplex (i : ι) : Pi.single i 1 in stdSimplex 𝕜 ι :=
  ⟨le_update_iff.2 ⟨zero_le_one, fun _ _ => le_rfl⟩, by simp⟩

/--
theorem `ite_eq_mem_stdSimplex` / 定理 `ite_eq_mem_stdSimplex`

English:
theorem ite_eq_mem_stdSimplex
  given: (i : ι)
  statement: (if i = · then (1 : 𝕜) else 0) in stdSimplex 𝕜 ι
  proof: by
  simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_stdSimplex 𝕜 i

中文:
定理 ite_eq_mem_stdSimplex
  条件: (i : ι)
  结论: (if i = · then (1 : 𝕜) else 0) in stdSimplex 𝕜 ι
  证明: by
  simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_stdSimplex 𝕜 i

Depends on / 依赖: Pi.single_apply, eq_comm, single_apply, single_mem_stdSimplex
-/
theorem ite_eq_mem_stdSimplex (i : ι) : (if i = · then (1 : 𝕜) else 0) in stdSimplex 𝕜 ι := by
  simpa only [@eq_comm _ i, ← Pi.single_apply] using single_mem_stdSimplex 𝕜 i

variable [IsOrderedRing 𝕜]

set_option linter.overlappingInstances false
/--
lemma `segment_single_subset_stdSimplex` / 引理 `segment_single_subset_stdSimplex`

English:
lemma segment_single_subset_stdSimplex
  given: (i j : ι)
  proof: (convex_stdSimplex 𝕜 ι).segment_subset (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

中文:
引理 segment_single_subset_stdSimplex
  条件: (i j : ι)
  证明: (convex_stdSimplex 𝕜 ι).segment_subset (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

Depends on / 依赖: convex_stdSimplex, segment_subset, single_mem_stdSimplex
-/
lemma segment_single_subset_stdSimplex (i j : ι) :
    [Pi.single i 1 -[𝕜] Pi.single j 1] subseteq stdSimplex 𝕜 ι :=
  (convex_stdSimplex 𝕜 ι).segment_subset (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

/--
lemma `stdSimplex_fin_two` / 引理 `stdSimplex_fin_two`

English:
lemma stdSimplex_fin_two
  proof: by
  refine Subset.antisymm ?_ (segment_single_subset_stdSimplex 𝕜 (0 : Fin 2) 1)
  rintro f ⟨hf₀, hf₁⟩
  rw [Fin.sum_univ_two] at hf₁
refine ⟨f 0, f 1, hf₀ 0, hf₀ 1, hf₁, funext Fin.forall_fin_two.2 ?_⟩
  simp

中文:
引理 stdSimplex_fin_two
  证明: by
  refine Subset.antisymm ?_ (segment_single_subset_stdSimplex 𝕜 (0 : Fin 2) 1)
  rintro f ⟨hf₀, hf₁⟩
  rw [Fin.sum_univ_two] at hf₁
refine ⟨f 0, f 1, hf₀ 0, hf₀ 1, hf₁, funext Fin.forall_fin_two.2 ?_⟩
  simp

Depends on / 依赖: Fin.forall_fin_two, Fin.sum_univ_two, Subset, Subset.antisymm, antisymm, forall_fin_two, segment_single_subset_stdSimplex, sum_univ_two
-/
lemma stdSimplex_fin_two :
    stdSimplex 𝕜 (Fin 2) = [Pi.single 0 1 -[𝕜] Pi.single 1 1] := by
  refine Subset.antisymm ?_ (segment_single_subset_stdSimplex 𝕜 (0 : Fin 2) 1)
  rintro f ⟨hf₀, hf₁⟩
  rw [Fin.sum_univ_two] at hf₁
refine ⟨f 0, f 1, hf₀ 0, hf₀ 1, hf₁, funext Fin.forall_fin_two.2 ?_⟩
  simp

end OrderedSemiring

section OrderedRing

variable (𝕜) [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]

/-- The standard one-dimensional simplex in `Fin 2 → 𝕜` is equivalent to the unit interval.
This bijection sends the zeroth vertex `Pi.single 0 1` to `0` and
the first vertex `Pi.single 1 1` to `1`. -/
@[simps -fullyApplied]
/--
Definition of `stdSimplexEquivIcc` / `stdSimplexEquivIcc` 的定义

English:
definition stdSimplexEquivIcc
  signature: : stdSimplex 𝕜 (Fin 2) ≃ Icc (0 : 𝕜) 1 where
  body: ⟨f.1 1, f.2.1 _, f.2.2 ▸
    Finset.single_le_sum (fun i _ => f.2.1 i) (Finset.mem_univ _)⟩
  invFun x := ⟨![1 - x, x], Fin.forall_fin_two.2 ⟨sub_nonneg.2 x.2.2, x.2.1⟩, by simp⟩
left_inv f := Subtype.ext funext Fin.forall_fin_two.2 by
    simp [← (show f.1 0 + f.1 1 = 1 by simpa using f.2.2)]

@[si

中文:
定义 stdSimplexEquivIcc
  签名: : stdSimplex 𝕜 (有限集 2) ≃ 闭区间 (0 : 𝕜) 1 where
  定义体: ⟨f.1 1, f.2.1 _, f.2.2 ▸
    Finset.single_le_sum (fun i _ => f.2.1 i) (Finset.mem_univ _)⟩
  invFun x := ⟨![1 - x, x], Fin.forall_fin_two.2 ⟨sub_nonneg.2 x.2.2, x.2.1⟩, by simp⟩
left_inv f := Subtype.ext funext Fin.forall_fin_two.2 by
    simp [← (show f.1 0 + f.1 1 = 1 by simpa using f.2.2)]

@[si
-/
def stdSimplexEquivIcc : stdSimplex 𝕜 (Fin 2) ≃ Icc (0 : 𝕜) 1 where
  toFun f := ⟨f.1 1, f.2.1 _, f.2.2 ▸
    Finset.single_le_sum (fun i _ => f.2.1 i) (Finset.mem_univ _)⟩
  invFun x := ⟨![1 - x, x], Fin.forall_fin_two.2 ⟨sub_nonneg.2 x.2.2, x.2.1⟩, by simp⟩
left_inv f := Subtype.ext funext Fin.forall_fin_two.2 by
    simp [← (show f.1 0 + f.1 1 = 1 by simpa using f.2.2)]

@[simp]
/--
lemma `stdSimplexEquivIcc_zero` / 引理 `stdSimplexEquivIcc_zero`

English:
lemma stdSimplexEquivIcc_zero
  proof: rfl

@[simp]

中文:
引理 stdSimplexEquivIcc_zero
  证明: rfl

@[simp]
-/
lemma stdSimplexEquivIcc_zero :
    stdSimplexEquivIcc 𝕜 ⟨_, single_mem_stdSimplex 𝕜 0⟩ = 0 := rfl

@[simp]
/--
lemma `stdSimplexEquivIcc_one` / 引理 `stdSimplexEquivIcc_one`

English:
lemma stdSimplexEquivIcc_one
  proof: rfl

中文:
引理 stdSimplexEquivIcc_one
  证明: rfl
-/
lemma stdSimplexEquivIcc_one :
    stdSimplexEquivIcc 𝕜 ⟨_, single_mem_stdSimplex 𝕜 1⟩ = 1 := rfl

end OrderedRing

section Field

variable (R : Type*) (ι : Type*) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [Fintype ι]

/--
theorem `convexHull_basis_eq_stdSimplex` / 定理 `convexHull_basis_eq_stdSimplex`

English:
theorem convexHull_basis_eq_stdSimplex
  given: [DecidableEq ι]
  proof: by
  refine Subset.antisymm (convexHull_min ?_ (convex_stdSimplex R ι)) ?_
  · rintro _ ⟨i, rfl⟩
    exact ite_eq_mem_stdSimplex R i
  · rintro w ⟨hw₀, hw₁⟩
    rw [pi_eq_sum_univ w]
    rw [← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i

中文:
定理 convexHull_basis_eq_stdSimplex
  条件: [DecidableEq ι]
  证明: by
  refine Subset.antisymm (convexHull_min ?_ (convex_stdSimplex R ι)) ?_
  · rintro _ ⟨i, rfl⟩
    exact ite_eq_mem_stdSimplex R i
  · rintro w ⟨hw₀, hw₁⟩
    rw [pi_eq_sum_univ w]
    rw [← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i

Depends on / 依赖: Finset, Finset.univ.centerMass_eq_of_sum_1, Finset.univ.centerMass_mem_convexHull, Subset, Subset.antisymm, antisymm, centerMass_eq_of_sum_1, centerMass_mem_convexHull, convexHull_min, convex_stdSimplex, ite_eq_mem_stdSimplex, mem_range_self, pi_eq_sum_univ, zero_lt_one
-/
theorem convexHull_basis_eq_stdSimplex [DecidableEq ι] :
    convexHull R (range fun i j : ι => if i = j then (1 : R) else 0) = stdSimplex R ι := by
  refine Subset.antisymm (convexHull_min ?_ (convex_stdSimplex R ι)) ?_
  · rintro _ ⟨i, rfl⟩
    exact ite_eq_mem_stdSimplex R i
  · rintro w ⟨hw₀, hw₁⟩
    rw [pi_eq_sum_univ w]
    rw [← Finset.univ.centerMass_eq_of_sum_1 _ hw₁]
    exact Finset.univ.centerMass_mem_convexHull (fun i _ => hw₀ i) (hw₁.symm ▸ zero_lt_one)
      fun i _ => mem_range_self i

/--
theorem `convexHull_rangle_single_eq_stdSimplex` / 定理 `convexHull_rangle_single_eq_stdSimplex`

English:
theorem convexHull_rangle_single_eq_stdSimplex
  given: [DecidableEq ι]
  proof: by
  convert! convexHull_basis_eq_stdSimplex R ι
  aesop

中文:
定理 convexHull_rangle_single_eq_stdSimplex
  条件: [DecidableEq ι]
  证明: by
  convert! convexHull_basis_eq_stdSimplex R ι
  aesop

Depends on / 依赖: convert, convexHull_basis_eq_stdSimplex
-/
theorem convexHull_rangle_single_eq_stdSimplex [DecidableEq ι] :
    convexHull R (range fun i : ι => Pi.single i 1) = stdSimplex R ι := by
  convert! convexHull_basis_eq_stdSimplex R ι
  aesop

variable {ι R}

/--
theorem `Set.Finite.convexHull_eq_image` / 定理 `Set.Finite.convexHull_eq_image`

English:
theorem Set.Finite.convexHull_eq_image
  statement: {E : Type*} [AddCommGroup E] [Module R E]
  proof: hs.fintype
    (⇑(∑ x : s, (LinearMap.proj (R := R) x).smulRight x.1)) '' stdSimplex R s := by
  classical
  let := hs.fintype
  rw [← convexHull_basis_eq_stdSimplex]; rw [LinearMap.image_convexHull]; rw [← Set.range_comp]
  apply congr_arg
  aesop

中文:
定理 集合.有限.convexHull_eq_image
  结论: {E : 类型} [加法交换群 E] [模 R E]
  证明: hs.fintype
    (⇑(∑ x : s, (LinearMap.proj (R := R) x).smulRight x.1)) '' stdSimplex R s := by
  classical
  let := hs.fintype
  rw [← convexHull_basis_eq_stdSimplex]; rw [LinearMap.image_convexHull]; rw [← Set.range_comp]
  apply congr_arg
  aesop

Depends on / 依赖: fintype, hs.fintype
-/
theorem Set.Finite.convexHull_eq_image {E : Type*} [AddCommGroup E] [Module R E]
    {s : Set E} (hs : s.Finite) : convexHull R s =
    haveI := hs.fintype
    (⇑(∑ x : s, (LinearMap.proj (R := R) x).smulRight x.1)) '' stdSimplex R s := by
  classical
  let := hs.fintype
  rw [← convexHull_basis_eq_stdSimplex]; rw [LinearMap.image_convexHull]; rw [← Set.range_comp]
  apply congr_arg
  aesop

end Field

section GeneralTopology
variable (𝕜 ι : Type*) [Fintype ι]
  [TopologicalSpace 𝕜] [Semiring 𝕜] [PartialOrder 𝕜] [OrderClosedTopology 𝕜] [ContinuousAdd 𝕜]

/--
theorem `isClosed_stdSimplex` / 定理 `isClosed_stdSimplex`

English:
theorem isClosed_stdSimplex
  statement: IsClosed (stdSimplex 𝕜 ι)
  proof: by
  rw [stdSimplex_eq_inter]
  apply IsClosed.inter
  · apply isClosed_iInter
    exact fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

中文:
定理 isClosed_stdSimplex
  结论: 是闭集 (stdSimplex 𝕜 ι)
  证明: by
  rw [stdSimplex_eq_inter]
  apply IsClosed.inter
  · apply isClosed_iInter
    exact fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

Depends on / 依赖: IsClosed, IsClosed.inter, continuous_apply, continuous_const, fun_prop, isClosed_eq, isClosed_iInter, isClosed_le, stdSimplex_eq_inter
-/
theorem isClosed_stdSimplex : IsClosed (stdSimplex 𝕜 ι) := by
  rw [stdSimplex_eq_inter]
  apply IsClosed.inter
  · apply isClosed_iInter
    exact fun i => isClosed_le continuous_const (continuous_apply i)
  · exact isClosed_eq (by fun_prop) continuous_const

/--
theorem `isCompact_stdSimplex` / 定理 `isCompact_stdSimplex`

English:
theorem isCompact_stdSimplex
  given: [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜]
  proof: IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)

中文:
定理 isCompact_stdSimplex
  条件: [余mpactIcc空间 𝕜] [是OrderedAdd幺半群 𝕜]
  证明: IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)

Depends on / 依赖: IsCompact, IsCompact.of_isClosed_subset, isClosed_stdSimplex, isCompact_Icc, of_isClosed_subset, stdSimplex_subset_Icc
-/
theorem isCompact_stdSimplex [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    IsCompact (stdSimplex 𝕜 ι) :=
  IsCompact.of_isClosed_subset isCompact_Icc (isClosed_stdSimplex 𝕜 ι) (stdSimplex_subset_Icc 𝕜)

/--
Instance `stdSimplex.instCompactSpace_coe` / 实例 `stdSimplex.instCompactSpace_coe`

English:
instance stdSimplex.instCompactSpace_coe
  signature: [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜]
  body: isCompact_iff_compactSpace.mp isCompact_stdSimplex 𝕜 _

中文:
实例 stdSimplex.instCompactSpace_coe
  签名: [余mpactIcc空间 𝕜] [是OrderedAdd幺半群 𝕜]
  定义体: isCompact_iff_compactSpace.mp isCompact_stdSimplex 𝕜 _

Depends on / 依赖: geometric_hahn_banach_point_point, hf.ne, hx.symm, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isCompact_stdSimplex, map_zero
-/
instance stdSimplex.instCompactSpace_coe [CompactIccSpace 𝕜] [IsOrderedAddMonoid 𝕜] :
    CompactSpace (stdSimplex 𝕜 ι) :=
isCompact_iff_compactSpace.mp isCompact_stdSimplex 𝕜 _

end GeneralTopology

section Topology

variable {ι : Type*} [Fintype ι]

/--
theorem `stdSimplex_subset_closedBall` / 定理 `stdSimplex_subset_closedBall`

English:
theorem stdSimplex_subset_closedBall
  statement: stdSimplex Real ι subseteq Metric.closedBall 0 1
  proof: fun f hf => by
  rw [Metric.mem_closedBall]; rw [dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply]; rw [Real.dist_0_eq_abs]; rw [abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2

中文:
定理 stdSimplex_subset_closedBall
  结论: stdSimplex 实数 ι subseteq Metric.closedBall 0 1
  证明: fun f hf => by
  rw [Metric.mem_closedBall]; rw [dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply]; rw [Real.dist_0_eq_abs]; rw [abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2

Depends on / 依赖: IsScalarTower, LocallyConvexSpace, Metric, Metric.mem_closedBall, Module, NormedSpace, NormedSpace.toLocallyConvexSpace, Pi.zero_apply, RCLike, RCLike.geometric_hahn_banach_point_point, Real.dist_0_eq_abs, abs_of_nonneg, dist_0_eq_abs, dist_pi_le_iff, geometric_hahn_banach_point_point, mem_Icc_of_mem_stdSimplex, mem_closedBall, restrictScalars, toLocallyConvexSpace, zero_apply
-/
theorem stdSimplex_subset_closedBall : stdSimplex Real ι subseteq Metric.closedBall 0 1 := fun f hf => by
  rw [Metric.mem_closedBall]; rw [dist_pi_le_iff zero_le_one]
  intro x
  rw [Pi.zero_apply]; rw [Real.dist_0_eq_abs]; rw [abs_of_nonneg <| hf.1 x]
  exact (mem_Icc_of_mem_stdSimplex hf x).2

variable (ι)

/--
theorem `bounded_stdSimplex` / 定理 `bounded_stdSimplex`

English:
theorem bounded_stdSimplex
  statement: IsBounded (stdSimplex Real ι)
  proof: (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, stdSimplex_subset_closedBall⟩

中文:
定理 bounded_stdSimplex
  结论: IsBounded (stdSimplex 实数 ι)
  证明: (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, stdSimplex_subset_closedBall⟩

Depends on / 依赖: Metric, Metric.isBounded_iff_subset_closedBall, isBounded_iff_subset_closedBall, stdSimplex_subset_closedBall
-/
theorem bounded_stdSimplex : IsBounded (stdSimplex Real ι) :=
  (Metric.isBounded_iff_subset_closedBall 0).2 ⟨1, stdSimplex_subset_closedBall⟩

/--
theorem `isPathConnected_stdSimplex` / 定理 `isPathConnected_stdSimplex`

English:
theorem isPathConnected_stdSimplex
  given: [Nonempty ι]
  proof: (convex_stdSimplex Real ι).isPathConnected (by
    classical
    exact ⟨_, single_mem_stdSimplex Real (Classical.arbitrary ι)⟩)

中文:
定理 isPathConnected_stdSimplex
  条件: [非空 ι]
  证明: (convex_stdSimplex Real ι).isPathConnected (by
    classical
    exact ⟨_, single_mem_stdSimplex Real (Classical.arbitrary ι)⟩)

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, classical, convex_stdSimplex, isPathConnected, single_mem_stdSimplex
-/
theorem isPathConnected_stdSimplex [Nonempty ι] :
    IsPathConnected (stdSimplex Real ι) :=
  (convex_stdSimplex Real ι).isPathConnected (by
    classical
    exact ⟨_, single_mem_stdSimplex Real (Classical.arbitrary ι)⟩)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: ι] : PathConnectedSpace (stdSimplex Real ι)
  body: isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_stdSimplex _)

中文:
实例 [非空
  签名: ι] : 道路连通空间 (stdSimplex 实数 ι)
  定义体: isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_stdSimplex _)

Depends on / 依赖: isPathConnected_iff_pathConnectedSpace, isPathConnected_stdSimplex
-/
instance [Nonempty ι] : PathConnectedSpace (stdSimplex Real ι) :=
  isPathConnected_iff_pathConnectedSpace.1 (isPathConnected_stdSimplex _)

/-- The standard one-dimensional simplex in `ℝ² = Fin 2 → ℝ`
is homeomorphic to the unit interval. -/
@[simps! -fullyApplied]
/--
Definition of `stdSimplexHomeomorphUnitInterval` / `stdSimplexHomeomorphUnitInterval` 的定义

English:
definition stdSimplexHomeomorphUnitInterval
  signature: : stdSimplex Real (Fin 2) ≃ₜ unitInterval where
  body: stdSimplexEquivIcc Real
  continuous_toFun := .subtype_mk ((continuous_apply 1).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_const.sub continuous_subtype_val, continuous_subtype_val⟩)

@[si

中文:
定义 stdSimplexHomeomorphUnit整数erval
  签名: : stdSimplex 实数 (有限集 2) ≃ₜ unit整数erval where
  定义体: stdSimplexEquivIcc Real
  continuous_toFun := .subtype_mk ((continuous_apply 1).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_const.sub continuous_subtype_val, continuous_subtype_val⟩)

@[si

Depends on / 依赖: stdSimplexEquivIcc
-/
def stdSimplexHomeomorphUnitInterval : stdSimplex Real (Fin 2) ≃ₜ unitInterval where
  toEquiv := stdSimplexEquivIcc Real
  continuous_toFun := .subtype_mk ((continuous_apply 1).comp continuous_subtype_val) _
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (continuous_pi <| Fin.forall_fin_two.2
      ⟨continuous_const.sub continuous_subtype_val, continuous_subtype_val⟩)

@[simp]
/--
lemma `stdSimplexHomeomorphUnitInterval_zero` / 引理 `stdSimplexHomeomorphUnitInterval_zero`

English:
lemma stdSimplexHomeomorphUnitInterval_zero
  proof: rfl

@[simp]

中文:
引理 stdSimplexHomeomorphUnit整数erval_zero
  证明: rfl

@[simp]
-/
lemma stdSimplexHomeomorphUnitInterval_zero :
    stdSimplexHomeomorphUnitInterval ⟨_, single_mem_stdSimplex _ 0⟩ = 0 := rfl

@[simp]
/--
lemma `stdSimplexHomeomorphUnitInterval_one` / 引理 `stdSimplexHomeomorphUnitInterval_one`

English:
lemma stdSimplexHomeomorphUnitInterval_one
  proof: rfl

中文:
引理 stdSimplexHomeomorphUnit整数erval_one
  证明: rfl
-/
lemma stdSimplexHomeomorphUnitInterval_one :
    stdSimplexHomeomorphUnitInterval ⟨_, single_mem_stdSimplex _ 1⟩ = 1 := rfl

/-! ### Diameter of a Standard Simplex (sup metric) -/

variable {ι}

/--
theorem `diam_stdSimplex_le` / 定理 `diam_stdSimplex_le`

English:
theorem diam_stdSimplex_le
  statement: Metric.diam (stdSimplex Real ι) <= 1
  proof: Metric.diam_le_of_forall_dist_le zero_le_one fun x hx y hy =>
    (dist_pi_le_iff zero_le_one).2 fun i => by
      have hx := mem_Icc_of_mem_stdSimplex hx i
      have hy := mem_Icc_of_mem_stdSimplex hy i
      grind [Real.dist_eq]

中文:
定理 diam_stdSimplex_le
  结论: Metric.diam (stdSimplex 实数 ι) <= 1
  证明: Metric.diam_le_of_forall_dist_le zero_le_one fun x hx y hy =>
    (dist_pi_le_iff zero_le_one).2 fun i => by
      have hx := mem_Icc_of_mem_stdSimplex hx i
      have hy := mem_Icc_of_mem_stdSimplex hy i
      grind [Real.dist_eq]

Depends on / 依赖: Metric, Metric.diam_le_of_forall_dist_le, Real.dist_eq, diam_le_of_forall_dist_le, dist_eq, dist_pi_le_iff, mem_Icc_of_mem_stdSimplex, zero_le_one
-/
theorem diam_stdSimplex_le : Metric.diam (stdSimplex Real ι) <= 1 :=
  Metric.diam_le_of_forall_dist_le zero_le_one fun x hx y hy =>
    (dist_pi_le_iff zero_le_one).2 fun i => by
      have hx := mem_Icc_of_mem_stdSimplex hx i
      have hy := mem_Icc_of_mem_stdSimplex hy i
      grind [Real.dist_eq]

/-- The (sup metric) diameter of a standard simplex indexed by a subsingleton is 0. -/
@[simp]
/--
theorem `diam_stdSimplex_of_subsingleton` / 定理 `diam_stdSimplex_of_subsingleton`

English:
theorem diam_stdSimplex_of_subsingleton
  given: [Subsingleton ι]
  statement: Metric.diam (stdSimplex Real ι) = 0
  proof: by
  cases isEmpty_or_nonempty ι with
  | inl h => rw [stdSimplex_of_isEmpty_index, Metric.diam_empty]
  | inr h => rw [stdSimplex_unique, Metric.diam_singleton]

中文:
定理 diam_stdSimplex_of_subsingleton
  条件: [子单例 ι]
  结论: Metric.diam (stdSimplex 实数 ι) = 0
  证明: by
  cases isEmpty_or_nonempty ι with
  | inl h => rw [stdSimplex_of_isEmpty_index, Metric.diam_empty]
  | inr h => rw [stdSimplex_unique, Metric.diam_singleton]

Depends on / 依赖: DFunLike, DFunLike.ne_iff.mpr, Metric, Metric.diam_empty, Metric.diam_singleton, diam_empty, diam_singleton, exists_ne, exists_ne_zero, isEmpty_or_nonempty, ne_iff, smulRight, stdSimplex_of_isEmpty_index, stdSimplex_unique
-/
theorem diam_stdSimplex_of_subsingleton [Subsingleton ι] : Metric.diam (stdSimplex Real ι) = 0 := by
  cases isEmpty_or_nonempty ι with
  | inl h => rw [stdSimplex_of_isEmpty_index, Metric.diam_empty]
  | inr h => rw [stdSimplex_unique, Metric.diam_singleton]

/-- The (sup metric) diameter of a standard simplex indexed by a nontrivial index is 1. -/
@[simp]
/--
theorem `diam_stdSimplex` / 定理 `diam_stdSimplex`

English:
theorem diam_stdSimplex
  given: [Nontrivial ι]
  statement: Metric.diam (stdSimplex Real ι) = 1
  proof: by
  refine le_antisymm diam_stdSimplex_le ?_
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  classical
  rw [show (1 : Real) = dist (Pi.single i 1 : ι -> Real) (Pi.single j 1) by
    simp [dist_single_single i j (1 : Real) 1 hij]; rw [Real.dist_eq]]
  exact Metric.dist_le_diam_of_mem (bounded_stdSimplex

中文:
定理 diam_stdSimplex
  条件: [非平凡 ι]
  结论: Metric.diam (stdSimplex 实数 ι) = 1
  证明: by
  refine le_antisymm diam_stdSimplex_le ?_
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  classical
  rw [show (1 : Real) = dist (Pi.single i 1 : ι -> Real) (Pi.single j 1) by
    simp [dist_single_single i j (1 : Real) 1 hij]; rw [Real.dist_eq]]
  exact Metric.dist_le_diam_of_mem (bounded_stdSimplex

Depends on / 依赖: Metric, Metric.dist_le_diam_of_mem, Pi.single, Real.dist_eq, bounded_stdSimplex, classical, diam_stdSimplex_le, dist_eq, dist_le_diam_of_mem, dist_single_single, exists_pair_ne, le_antisymm, single, single_mem_stdSimplex
-/
theorem diam_stdSimplex [Nontrivial ι] : Metric.diam (stdSimplex Real ι) = 1 := by
  refine le_antisymm diam_stdSimplex_le ?_
  obtain ⟨i, j, hij⟩ := exists_pair_ne ι
  classical
  rw [show (1 : Real) = dist (Pi.single i 1 : ι -> Real) (Pi.single j 1) by
    simp [dist_single_single i j (1 : Real) 1 hij]; rw [Real.dist_eq]]
  exact Metric.dist_le_diam_of_mem (bounded_stdSimplex _)
    (single_mem_stdSimplex _ _) (single_mem_stdSimplex _ _)

end Topology

namespace stdSimplex

variable {S : Type*} [Semiring S] [PartialOrder S]
  {X Y Z : Type*} [Fintype X] [Fintype Y] [Fintype Z]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (stdSimplex S X) X S
  body: s.val
  coe_injective := by aesop

@[ext high]

中文:
实例 :
  签名: 函数状 (stdSimplex S X) X S
  定义体: s.val
  coe_injective := by aesop

@[ext high]

Depends on / 依赖: s.val
-/
instance : FunLike (stdSimplex S X) X S where
  coe s := s.val
  coe_injective := by aesop

@[ext high]
/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  given: {s t : stdSimplex S X} (h : (s : X -> S) = t)
  statement: s = t
  proof: by
  ext : 1
  assumption

@[simp]

中文:
引理 ext
  条件: {s t : stdSimplex S X} (h : (s : X -> S) = t)
  结论: s = t
  证明: by
  ext : 1
  assumption

@[simp]
-/
lemma ext {s t : stdSimplex S X} (h : (s : X -> S) = t) : s = t := by
  ext : 1
  assumption

@[simp]
/--
lemma `zero_le` / 引理 `zero_le`

English:
lemma zero_le
  given: (s : stdSimplex S X) (x : X)
  statement: 0 <= s x
  proof: s.2.1 x

@[simp]

中文:
引理 zero_le
  条件: (s : stdSimplex S X) (x : X)
  结论: 0 <= s x
  证明: s.2.1 x

@[simp]
-/
lemma zero_le (s : stdSimplex S X) (x : X) : 0 <= s x := s.2.1 x

@[simp]
/--
lemma `sum_eq_one` / 引理 `sum_eq_one`

English:
lemma sum_eq_one
  given: (s : stdSimplex S X)
  statement: ∑ x, s x = 1
  proof: s.2.2

中文:
引理 sum_eq_one
  条件: (s : stdSimplex S X)
  结论: ∑ x, s x = 1
  证明: s.2.2
-/
lemma sum_eq_one (s : stdSimplex S X) : ∑ x, s x = 1 := s.2.2

/--
lemma `add_eq_one` / 引理 `add_eq_one`

English:
lemma add_eq_one
  given: (s : stdSimplex S (Fin 2))
  proof: by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

中文:
引理 add_eq_one
  条件: (s : stdSimplex S (有限集 2))
  证明: by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

Depends on / 依赖: Fin.sum_univ_two, sum_eq_one, sum_univ_two
-/
lemma add_eq_one (s : stdSimplex S (Fin 2)) :
    s 0 + s 1 = 1 := by
  simpa only [Fin.sum_univ_two] using sum_eq_one s

section

variable [IsOrderedRing S]

@[simp]
/--
lemma `le_one` / 引理 `le_one`

English:
lemma le_one
  given: (s : stdSimplex S X) (x : X)
  statement: s x <= 1
  proof: by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (by simp) (by simp)

中文:
引理 le_one
  条件: (s : stdSimplex S X) (x : X)
  结论: s x <= 1
  证明: by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (by simp) (by simp)

Depends on / 依赖: Finset, Finset.single_le_sum, single_le_sum, sum_eq_one
-/
lemma le_one (s : stdSimplex S X) (x : X) : s x <= 1 := by
  rw [← sum_eq_one s]
  exact Finset.single_le_sum (by simp) (by simp)

/--
lemma `image_linearMap` / 引理 `image_linearMap`

English:
lemma image_linearMap
  given: (f : X -> Y)
  proof: by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y => ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

中文:
引理 image_linearMap
  条件: (f : X -> Y)
  证明: by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y => ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

Depends on / 依赖: Finset, Finset.sum_fiberwise, Finset.sum_nonneg, Finset.univ, FunOnFinite, FunOnFinite.linearMap_apply_apply, classical, linearMap_apply_apply, sum_fiberwise, sum_nonneg
-/
lemma image_linearMap (f : X -> Y) :
    Set.image (FunOnFinite.linearMap S S f) (stdSimplex S X) subseteq stdSimplex S Y := by
  classical
  rintro _ ⟨s, ⟨hs₀, hs₁⟩, rfl⟩
  refine ⟨fun y => ?_, ?_⟩
  · rw [FunOnFinite.linearMap_apply_apply]
    exact Finset.sum_nonneg (by aesop)
  · simp only [FunOnFinite.linearMap_apply_apply, ← hs₁]
    exact Finset.sum_fiberwise Finset.univ f s

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : X -> Y) (s : stdSimplex S X)
  body: ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

@[simp]

中文:
定义 map
  签名: (f : X -> Y) (s : stdSimplex S X)
  定义体: ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

@[simp]

Depends on / 依赖: FunOnFinite, FunOnFinite.linearMap, image_linearMap, linearMap
-/
noncomputable def map (f : X -> Y) (s : stdSimplex S X) : stdSimplex S Y :=
  ⟨FunOnFinite.linearMap S S f s, image_linearMap f (by aesop)⟩

@[simp]
/--
lemma `map_coe` / 引理 `map_coe`

English:
lemma map_coe
  given: (f : X -> Y) (s : stdSimplex S X)
  proof: rfl

@[simp]

中文:
引理 map_coe
  条件: (f : X -> Y) (s : stdSimplex S X)
  证明: rfl

@[simp]
-/
lemma map_coe (f : X -> Y) (s : stdSimplex S X) :
    ⇑(map f s) = FunOnFinite.linearMap S S f s := rfl

@[simp]
/--
lemma `map_id_apply` / 引理 `map_id_apply`

English:
lemma map_id_apply
  given: (x : stdSimplex S X)
  statement: map id x = x
  proof: by
  aesop

中文:
引理 map_id_apply
  条件: (x : stdSimplex S X)
  结论: map id x = x
  证明: by
  aesop
-/
lemma map_id_apply (x : stdSimplex S X) : map id x = x := by
  aesop

/--
lemma `map_comp_apply` / 引理 `map_comp_apply`

English:
lemma map_comp_apply
  given: (f : X -> Y) (g : Y -> Z) (x : stdSimplex S X)
  proof: by
  ext
  simp [FunOnFinite.linearMap_comp]

中文:
引理 map_comp_apply
  条件: (f : X -> Y) (g : Y -> Z) (x : stdSimplex S X)
  证明: by
  ext
  simp [FunOnFinite.linearMap_comp]

Depends on / 依赖: FunOnFinite, FunOnFinite.linearMap_comp, linearMap_comp
-/
lemma map_comp_apply (f : X -> Y) (g : Y -> Z) (x : stdSimplex S X) :
    map g (map f x) = map (g.comp f) x := by
  ext
  simp [FunOnFinite.linearMap_comp]

/--
Definition of `vertex` / `vertex` 的定义

English:
abbreviation vertex
  signature: [DecidableEq X] (x : X)
  body: ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

@[simp]

中文:
缩写 vertex
  签名: [DecidableEq X] (x : X)
  定义体: ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

@[simp]

Depends on / 依赖: Pi.single, single, single_mem_stdSimplex
-/
abbrev vertex [DecidableEq X] (x : X) : stdSimplex S X :=
  ⟨Pi.single x 1, single_mem_stdSimplex S x⟩

@[simp]
/--
lemma `vertex_coe` / 引理 `vertex_coe`

English:
lemma vertex_coe
  given: [DecidableEq X] (x : X)
  proof: rfl

@[simp]

中文:
引理 vertex_coe
  条件: [DecidableEq X] (x : X)
  证明: rfl

@[simp]

Depends on / 依赖: Pi.single, single
-/
lemma vertex_coe [DecidableEq X] (x : X) :
    ⇑(vertex (S := S) x) = Pi.single x 1 := rfl

@[simp]
/--
lemma `map_vertex` / 引理 `map_vertex`

English:
lemma map_vertex
  given: [DecidableEq X] [DecidableEq Y] (f : X -> Y) (x : X)
  proof: by
  aesop

@[continuity]

中文:
引理 map_vertex
  条件: [DecidableEq X] [DecidableEq Y] (f : X -> Y) (x : X)
  证明: by
  aesop

@[continuity]

Depends on / 依赖: vertex
-/
lemma map_vertex [DecidableEq X] [DecidableEq Y] (f : X -> Y) (x : X) :
    map (S := S) f (vertex x) = vertex (f x) := by
  aesop

@[continuity]
/--
lemma `continuous_map` / 引理 `continuous_map`

English:
lemma continuous_map
  given: [TopologicalSpace S] [IsTopologicalSemiring S] (f : X -> Y)
  proof: Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _

中文:
引理 continuous_map
  条件: [拓扑空间 S] [是TopologicalSemiring S] (f : X -> Y)
  证明: Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _
-/
lemma continuous_map [TopologicalSpace S] [IsTopologicalSemiring S] (f : X -> Y) :
    Continuous (map (S := S) f) :=
  Continuous.subtype_mk ((FunOnFinite.continuous_linearMap S S f).comp continuous_induced_dom) _

/--
lemma `vertex_injective` / 引理 `vertex_injective`

English:
lemma vertex_injective
  given: [Nontrivial S] [DecidableEq X]
  proof: by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

中文:
引理 vertex_injective
  条件: [非平凡 S] [DecidableEq X]
  证明: by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

Depends on / 依赖: DFunLike, DFunLike.congr_fun, Pi.single_eq_of_ne, congr_fun, replace, single_eq_of_ne
-/
lemma vertex_injective [Nontrivial S] [DecidableEq X] :
    Function.Injective (vertex (S := S) (X := X)) := by
  intro x y h
  replace h := DFunLike.congr_fun h x
  by_contra!
  simp [Pi.single_eq_of_ne this] at h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nonempty
  signature: X] : Nonempty (stdSimplex S X)
  body: by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

中文:
实例 [非空
  签名: X] : 非空 (stdSimplex S X)
  定义体: by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

Depends on / 依赖: Classical, Classical.arbitrary, arbitrary, classical, vertex
-/
instance [Nonempty X] : Nonempty (stdSimplex S X) := by
  classical
  exact ⟨vertex (Classical.arbitrary _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: S] [Nontrivial X] : Nontrivial (stdSimplex S X) where
  body: by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h => hxy (vertex_injective h)⟩

中文:
实例 [非平凡
  签名: S] [非平凡 X] : 非平凡 (stdSimplex S X) where
  定义体: by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h => hxy (vertex_injective h)⟩

Depends on / 依赖: classical, exists_pair_ne, vertex, vertex_injective
-/
instance [Nontrivial S] [Nontrivial X] : Nontrivial (stdSimplex S X) where
  exists_pair_ne := by
    classical
    obtain ⟨x, y, hxy⟩ := exists_pair_ne X
    exact ⟨vertex x, vertex y, fun h => hxy (vertex_injective h)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: X] : Subsingleton (stdSimplex S X) where
  body: by
    ext i
    have (u : stdSimplex S X) : u i = 1 := by
      rw [← sum_eq_one u]; rw [Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

中文:
实例 [子单例
  签名: X] : 子单例 (stdSimplex S X) where
  定义体: by
    ext i
    have (u : stdSimplex S X) : u i = 1 := by
      rw [← sum_eq_one u]; rw [Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

Depends on / 依赖: Finset, Finset.sum_eq_single, Subsingleton, Subsingleton.elim, stdSimplex, sum_eq_one, sum_eq_single
-/
instance [Subsingleton X] : Subsingleton (stdSimplex S X) where
  allEq s t := by
    ext i
    have (u : stdSimplex S X) : u i = 1 := by
      rw [← sum_eq_one u]; rw [Finset.sum_eq_single i _ (by simp)]
      intro j _ hj
      exact (hj (Subsingleton.elim j i)).elim
    simp [this]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: X] : Unique (stdSimplex S X) where
  body: ⟨1, by simp, by simp⟩
  uniq := by subsingleton

@[simp]

中文:
实例 [唯一
  签名: X] : 唯一 (stdSimplex S X) where
  定义体: ⟨1, by simp, by simp⟩
  uniq := by subsingleton

@[simp]
-/
instance [Unique X] : Unique (stdSimplex S X) where
  default := ⟨1, by simp, by simp⟩
  uniq := by subsingleton

@[simp]
/--
lemma `eq_one_of_unique` / 引理 `eq_one_of_unique`

English:
lemma eq_one_of_unique
  given: [Unique X] (s : stdSimplex S X) (x : X)
  proof: by
  obtain rfl : s = default := by subsingleton
  rfl

中文:
引理 eq_one_of_unique
  条件: [唯一 X] (s : stdSimplex S X) (x : X)
  证明: by
  obtain rfl : s = default := by subsingleton
  rfl

Depends on / 依赖: subsingleton
-/
lemma eq_one_of_unique [Unique X] (s : stdSimplex S X) (x : X) :
    s x = 1 := by
  obtain rfl : s = default := by subsingleton
  rfl

end

/-! ### Barycenter of a Standard Simplex -/

section Barycenter

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Nonempty X]

/--
Definition of `barycenter` / `barycenter` 的定义

English:
definition barycenter
  signature: : stdSimplex 𝕜 X
  body: ⟨fun i => (Fintype.card X : 𝕜)⁻¹, by simp [stdSimplex]⟩

中文:
定义 barycenter
  签名: : stdSimplex 𝕜 X
  定义体: ⟨fun i => (Fintype.card X : 𝕜)⁻¹, by simp [stdSimplex]⟩

Depends on / 依赖: Fintype, Fintype.card, stdSimplex
-/
def barycenter : stdSimplex 𝕜 X :=
  ⟨fun i => (Fintype.card X : 𝕜)⁻¹, by simp [stdSimplex]⟩

/-- The barycenter of a standard simplex has coordinates `(Fintype.card X)⁻¹` at each index. -/
@[simp]
/--
theorem `barycenter_apply` / 定理 `barycenter_apply`

English:
theorem barycenter_apply
  given: (x : X)
  proof: rfl

中文:
定理 barycenter_apply
  条件: (x : X)
  证明: rfl
-/
theorem barycenter_apply (x : X) :
    (barycenter : stdSimplex 𝕜 X).val x = (Fintype.card X : 𝕜)⁻¹ := rfl

/--
theorem `barycenter_eq_centerMass` / 定理 `barycenter_eq_centerMass`

English:
theorem barycenter_eq_centerMass
  given: [DecidableEq X]
  proof: by
  simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ]
  ext x
  simp [barycenter, Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

中文:
定理 barycenter_eq_centerMass
  条件: [DecidableEq X]
  证明: by
  simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ]
  ext x
  simp [barycenter, Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

Depends on / 依赖: Finset, Finset.card_univ, Finset.centerMass, Finset.sum_apply, Finset.sum_const, Pi.single_apply, Pi.smul_apply, barycenter, card_univ, centerMass, single_apply, smul_apply, sum_apply, sum_const
-/
theorem barycenter_eq_centerMass [DecidableEq X] :
    (barycenter : stdSimplex 𝕜 X).val =
      Finset.centerMass Finset.univ (fun _ => (1 : 𝕜)) (fun i => Pi.single i 1) := by
  simp only [Finset.centerMass, Finset.sum_const, Finset.card_univ]
  ext x
  simp [barycenter, Pi.smul_apply, Finset.sum_apply, Pi.single_apply]

end Barycenter

end stdSimplex
