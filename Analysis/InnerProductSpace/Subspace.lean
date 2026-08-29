/-
Copyright (c) 2019 Zhouhang Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhouhang Zhou, Sébastien Gouëzel, Frédéric Dupuis
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthonormal

/-!
# Subspaces of inner product spaces

This file defines the inner-product structure on a subspace of an inner-product space, and proves
some theorems about orthogonal families of subspaces.
-/

@[expose] public section

noncomputable section

open RCLike Real Filter Topology ComplexConjugate Finsupp Module

open LinearMap (BilinForm)

variable {𝕜 E F : Type*} [RCLike 𝕜]

section Submodule

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-! ### Inner product space structure on subspaces -/

/--
Instance `Submodule.innerProductSpace` / 实例 `Submodule.innerProductSpace`

English:
instance Submodule.innerProductSpace
  signature: (W : Submodule 𝕜 E)
  body: fast_instance% .induced W.subtype

中文:
实例 子模.innerProductSpace
  签名: (W : 子模 𝕜 E)
  定义体: fast_instance% .induced W.subtype

Depends on / 依赖: W.subtype, fast_instance, induced, subtype
-/
instance Submodule.innerProductSpace (W : Submodule 𝕜 E) : InnerProductSpace 𝕜 W :=
  fast_instance% .induced W.subtype

/-- The inner product on submodules is the same as on the ambient space. -/
@[simp]
/--
theorem `Submodule.coe_inner` / 定理 `Submodule.coe_inner`

English:
theorem Submodule.coe_inner
  given: (W : Submodule 𝕜 E) (x y : W)
  statement: ⟪x, y⟫ = ⟪(x : E), ↑y⟫
  proof: rfl

中文:
定理 子模.coe_inner
  条件: (W : 子模 𝕜 E) (x y : W)
  结论: ⟪x, y⟫ = ⟪(x : E), ↑y⟫
  证明: rfl
-/
theorem Submodule.coe_inner (W : Submodule 𝕜 E) (x y : W) : ⟪x, y⟫ = ⟪(x : E), ↑y⟫ :=
  rfl

/--
theorem `Orthonormal.codRestrict` / 定理 `Orthonormal.codRestrict`

English:
theorem Orthonormal.codRestrict
  statement: {ι : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E)
  proof: s.subtypeₗᵢ.orthonormal_comp_iff.mp hv

中文:
定理 Orthonormal.codRestrict
  结论: {ι : 类型} {v : ι -> E} (hv : Orthonormal 𝕜 v) (s : 子模 𝕜 E)
  证明: s.subtypeₗᵢ.orthonormal_comp_iff.mp hv

Depends on / 依赖: orthonormal_comp_iff, orthonormal_comp_iff.mp, s.subtype
-/
theorem Orthonormal.codRestrict {ι : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) (s : Submodule 𝕜 E)
    (hvs : forall i, v i in s) : @Orthonormal 𝕜 s _ _ _ ι (Set.codRestrict v s hvs) :=
  s.subtypeₗᵢ.orthonormal_comp_iff.mp hv

/--
theorem `orthonormal_span` / 定理 `orthonormal_span`

English:
theorem orthonormal_span
  given: {ι : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)

中文:
定理 orthonormal_span
  条件: {ι : 类型} {v : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)

Depends on / 依赖: Set.mem_range_self, Set.range, Submodule, Submodule.span, Submodule.subset_span, codRestrict, hv.codRestrict, mem_range_self, subset_span
-/
theorem orthonormal_span {ι : Type*} {v : ι -> E} (hv : Orthonormal 𝕜 v) :
    @Orthonormal 𝕜 (Submodule.span 𝕜 (Set.range v)) _ _ _ ι fun i : ι =>
      ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩ :=
  hv.codRestrict (Submodule.span 𝕜 (Set.range v)) fun i =>
    Submodule.subset_span (Set.mem_range_self i)

end Submodule

/-! ### Families of mutually-orthogonal subspaces of an inner product space -/

section OrthogonalFamily_Seminormed

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} (𝕜)

open DirectSum

/--
Definition of `OrthogonalFamily` / `OrthogonalFamily` 的定义

English:
definition OrthogonalFamily
  signature: (G : ι -> Type*) [forall i, SeminormedAddCommGroup (G i)]
  body: Pairwise fun i j => forall v : G i, forall w : G j, ⟪V i v, V j w⟫ = 0

中文:
定义 OrthogonalFamily
  签名: (G : ι -> 类型) [对任意 i, SeminormedAddComm群 (G i)]
  定义体: Pairwise fun i j => forall v : G i, forall w : G j, ⟪V i v, V j w⟫ = 0

Depends on / 依赖: Pairwise
-/
def OrthogonalFamily (G : ι -> Type*) [forall i, SeminormedAddCommGroup (G i)]
    [forall i, InnerProductSpace 𝕜 (G i)] (V : forall i, G i ->ₗᵢ[𝕜] E) : Prop :=
  Pairwise fun i j => forall v : G i, forall w : G j, ⟪V i v, V j w⟫ = 0

variable {𝕜}
variable {G : ι -> Type*} [forall i, NormedAddCommGroup (G i)] [forall i, InnerProductSpace 𝕜 (G i)]
  {V : forall i, G i ->ₗᵢ[𝕜] E}

/--
theorem `Orthonormal.orthogonalFamily` / 定理 `Orthonormal.orthogonalFamily`

English:
theorem Orthonormal.orthogonalFamily
  given: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  proof: fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]

中文:
定理 Orthonormal.orthogonalFamily
  条件: {v : ι -> E} (hv : Orthonormal 𝕜 v)
  证明: fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]

Depends on / 依赖: inner_smul_left, inner_smul_right
-/
theorem Orthonormal.orthogonalFamily {v : ι -> E} (hv : Orthonormal 𝕜 v) :
    OrthogonalFamily 𝕜 (fun _i : ι => 𝕜) fun i => LinearIsometry.toSpanSingleton 𝕜 E (hv.1 i) :=
  fun i j hij a b => by simp [inner_smul_left, inner_smul_right, hv.2 hij]

section
variable (hV : OrthogonalFamily 𝕜 G V)
include hV

/--
theorem `OrthogonalFamily.eq_ite` / 定理 `OrthogonalFamily.eq_ite`

English:
theorem OrthogonalFamily.eq_ite
  given: [DecidableEq ι] {i j : ι} (v : G i) (w : G j)
  proof: by
  split_ifs with h
  · rfl
  · exact hV h v w

中文:
定理 OrthogonalFamily.eq_ite
  条件: [DecidableEq ι] {i j : ι} (v : G i) (w : G j)
  证明: by
  split_ifs with h
  · rfl
  · exact hV h v w

Depends on / 依赖: split_ifs
-/
theorem OrthogonalFamily.eq_ite [DecidableEq ι] {i j : ι} (v : G i) (w : G j) :
    ⟪V i v, V j w⟫ = ite (i = j) ⟪V i v, V j w⟫ 0 := by
  split_ifs with h
  · rfl
  · exact hV h v w

set_option backward.isDefEq.respectTransparency false in
/--
theorem `OrthogonalFamily.inner_right_dfinsupp` / 定理 `OrthogonalFamily.inner_right_dfinsupp`

English:
theorem OrthogonalFamily.inner_right_dfinsupp
  proof: calc
    ⟪V i v, l.sum fun j => V j⟫ = l.sum fun j w => ⟪V i v, V j w⟫ :=
      DFinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.sum fun j w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.sum <| funext fun _ => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ := by
      simp only [DFinsupp.sum, 

中文:
定理 OrthogonalFamily.inner_right_dfinsupp
  证明: calc
    ⟪V i v, l.sum fun j => V j⟫ = l.sum fun j w => ⟪V i v, V j w⟫ :=
      DFinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.sum fun j w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.sum <| funext fun _ => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ := by
      simp only [DFinsupp.sum, 

Depends on / 依赖: DFinsupp, DFinsupp.inner_sum, DFinsupp.mem_support_toFun, DFinsupp.sum, Finset, Finset.sum_ite_eq, LinearIsometry, LinearIsometry.inner_map_map, congr_arg, eq_ite, hV.eq_ite, inner_map_map, inner_sum, inner_zero_right, l.sum, mem_support_toFun, of_not_not, split_ifs, sum_ite_eq
-/
theorem OrthogonalFamily.inner_right_dfinsupp
    [forall (i) (x : G i), Decidable (x != 0)] [DecidableEq ι] (l : ⨁ i, G i) (i : ι) (v : G i) :
    ⟪V i v, l.sum fun j => V j⟫ = ⟪v, l i⟫ :=
  calc
    ⟪V i v, l.sum fun j => V j⟫ = l.sum fun j w => ⟪V i v, V j w⟫ :=
      DFinsupp.inner_sum (fun j => V j) l (V i v)
    _ = l.sum fun j w => ite (i = j) ⟪V i v, V j w⟫ 0 :=
      (congr_arg l.sum <| funext fun _ => funext <| hV.eq_ite v)
    _ = ⟪v, l i⟫ := by
      simp only [DFinsupp.sum, Finset.sum_ite_eq,
        DFinsupp.mem_support_toFun]
      split_ifs with h
      · simp only [LinearIsometry.inner_map_map]
      · simp only [of_not_not h, inner_zero_right]

/--
theorem `OrthogonalFamily.inner_right_fintype` / 定理 `OrthogonalFamily.inner_right_fintype`

English:
theorem OrthogonalFamily.inner_right_fintype
  given: [Fintype ι] (l : forall i, G i) (i : ι) (v : G i)
  proof: by
  classical
  calc
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
    _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
      (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
    _ = ⟪v, l i⟫ := by
      simp only [Finset.sum_ite_eq, Finset.

中文:
定理 OrthogonalFamily.inner_right_fintype
  条件: [有限类型 ι] (l : 对任意 i, G i) (i : ι) (v : G i)
  证明: by
  classical
  calc
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
    _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
      (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
    _ = ⟪v, l i⟫ := by
      simp only [Finset.sum_ite_eq, Finset.

Depends on / 依赖: Finset, Finset.mem_univ, Finset.sum, Finset.sum_ite_eq, Finset.univ, classical, congr_arg, eq_ite, hV.eq_ite, if_true, inner_map_map, inner_sum, mem_univ, sum_ite_eq
-/
theorem OrthogonalFamily.inner_right_fintype [Fintype ι] (l : forall i, G i) (i : ι) (v : G i) :
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ⟪v, l i⟫ := by
  classical
  calc
    ⟪V i v, ∑ j : ι, V j (l j)⟫ = ∑ j : ι, ⟪V i v, V j (l j)⟫ := by rw [inner_sum]
    _ = ∑ j, ite (i = j) ⟪V i v, V j (l j)⟫ 0 :=
      (congr_arg (Finset.sum Finset.univ) <| funext fun j => hV.eq_ite v (l j))
    _ = ⟪v, l i⟫ := by
      simp only [Finset.sum_ite_eq, Finset.mem_univ, (V i).inner_map_map, if_true]

nonrec theorem OrthogonalFamily.inner_sum (l₁ l₂ : forall i, G i) (s : Finset ι) :
    ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ i in s, ⟪l₁ i, l₂ i⟫ := by
  classical
  calc
    ⟪∑ i in s, V i (l₁ i), ∑ j in s, V j (l₂ j)⟫ = ∑ j in s, ∑ i in s, ⟪V i (l₁ i), V j (l₂ j)⟫ := by
      simp only [sum_inner, inner_sum]
    _ = ∑ j in s, ∑ i in s, ite (i = j) ⟪V i (l₁ i), V j (l₂ j)⟫ 0 := by
      congr with i
      congr with j
      apply hV.eq_ite
    _ = ∑ i in s, ⟪l₁ i, l₂ i⟫ := by
      simp only [Finset.sum_ite_of_true, Finset.sum_ite_eq', LinearIsometry.inner_map_map,
        imp_self, imp_true_iff]

/--
theorem `OrthogonalFamily.norm_sum` / 定理 `OrthogonalFamily.norm_sum`

English:
theorem OrthogonalFamily.norm_sum
  given: (l : forall i, G i) (s : Finset ι)
  proof: by
  have : ((‖∑ i in s, V i (l i)‖ : Real) : 𝕜) ^ 2 = ∑ i in s, ((‖l i‖ : Real) : 𝕜) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact mod_cast this

中文:
定理 OrthogonalFamily.norm_sum
  条件: (l : 对任意 i, G i) (s : 有限集 ι)
  证明: by
  have : ((‖∑ i in s, V i (l i)‖ : Real) : 𝕜) ^ 2 = ∑ i in s, ((‖l i‖ : Real) : 𝕜) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact mod_cast this

Depends on / 依赖: hV.inner_sum, inner_self_eq_norm_sq_to_K, inner_sum, mod_cast
-/
theorem OrthogonalFamily.norm_sum (l : forall i, G i) (s : Finset ι) :
    ‖∑ i in s, V i (l i)‖ ^ 2 = ∑ i in s, ‖l i‖ ^ 2 := by
  have : ((‖∑ i in s, V i (l i)‖ : Real) : 𝕜) ^ 2 = ∑ i in s, ((‖l i‖ : Real) : 𝕜) ^ 2 := by
    simp only [← inner_self_eq_norm_sq_to_K, hV.inner_sum]
  exact mod_cast this

/--
theorem `OrthogonalFamily.comp` / 定理 `OrthogonalFamily.comp`

English:
theorem OrthogonalFamily.comp
  given: {γ : Type*} {f : γ -> ι} (hf : Function.Injective f)
  proof: fun _i _j hij v w => hV (hf.ne hij) v w

中文:
定理 OrthogonalFamily.comp
  条件: {γ : 类型} {f : γ -> ι} (hf : 函数.单射 f)
  证明: fun _i _j hij v w => hV (hf.ne hij) v w

Depends on / 依赖: hf.ne
-/
theorem OrthogonalFamily.comp {γ : Type*} {f : γ -> ι} (hf : Function.Injective f) :
    OrthogonalFamily 𝕜 (fun g => G (f g)) fun g => V (f g) :=
  fun _i _j hij v w => hV (hf.ne hij) v w

/--
theorem `OrthogonalFamily.orthonormal_sigma_orthonormal` / 定理 `OrthogonalFamily.orthonormal_sigma_orthonormal`

English:
theorem OrthogonalFamily.orthonormal_sigma_orthonormal
  statement: {α : ι -> Type*} {v_family : forall i, α i -> G i}
  proof: by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v != w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).

中文:
定理 OrthogonalFamily.orthonormal_sigma_orthonormal
  结论: {α : ι -> 类型} {v_family : 对任意 i, α i -> G i}
  证明: by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v != w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).

Depends on / 依赖: LinearIsometry, LinearIsometry.inner_map_map, LinearIsometry.norm_map, hv_family, inner_map_map, norm_map, v_family
-/
theorem OrthogonalFamily.orthonormal_sigma_orthonormal {α : ι -> Type*} {v_family : forall i, α i -> G i}
    (hv_family : forall i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 fun a : Σ i, α i => V a.1 (v_family a.1 a.2) := by
  constructor
  · rintro ⟨i, v⟩
    simpa only [LinearIsometry.norm_map] using (hv_family i).left v
  rintro ⟨i, v⟩ ⟨j, w⟩ hvw
  by_cases hij : i = j
  · subst hij
    have : v != w := fun h => by
      subst h
      exact hvw rfl
    simpa only [LinearIsometry.inner_map_map] using (hv_family i).2 this
  · exact hV hij (v_family i v) (v_family j w)

/--
theorem `OrthogonalFamily.norm_sq_sdiff_sum` / 定理 `OrthogonalFamily.norm_sq_sdiff_sum`

English:
theorem OrthogonalFamily.norm_sq_sdiff_sum
  given: [DecidableEq ι] (f : forall i, G i) (s₁ s₂ : Finset ι)
  proof: by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]; rw [sub_eq_add_neg]; rw [← Finset.sum_neg_distrib]
  let F : forall i, G i := fun i => if i in s₁ then f i else -f i
  have hF₁ : forall i in s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset hi)
  have hF₂ : forall i in s₂ \ s₁, F i = -f i := 

中文:
定理 OrthogonalFamily.norm_sq_sdiff_sum
  条件: [DecidableEq ι] (f : 对任意 i, G i) (s₁ s₂ : 有限集 ι)
  证明: by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]; rw [sub_eq_add_neg]; rw [← Finset.sum_neg_distrib]
  let F : forall i, G i := fun i => if i in s₁ then f i else -f i
  have hF₁ : forall i in s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset hi)
  have hF₂ : forall i in s₂ \ s₁, F i = -f i := 

Depends on / 依赖: Finset, Finset.mem_sdiff.mp, Finset.sdiff_subset, Finset.sum_neg_distrib, Finset.sum_sdiff_sub_sum_sdiff, if_neg, if_pos, mem_sdiff, norm_neg, sdiff_subset, split_ifs, sub_eq_add_neg, sum_neg_distrib, sum_sdiff_sub_sum_sdiff
-/
theorem OrthogonalFamily.norm_sq_sdiff_sum [DecidableEq ι] (f : forall i, G i) (s₁ s₂ : Finset ι) :
    ‖(∑ i in s₁, V i (f i)) - ∑ i in s₂, V i (f i)‖ ^ 2 =
      (∑ i in s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2 := by
  rw [← Finset.sum_sdiff_sub_sum_sdiff]; rw [sub_eq_add_neg]; rw [← Finset.sum_neg_distrib]
  let F : forall i, G i := fun i => if i in s₁ then f i else -f i
  have hF₁ : forall i in s₁ \ s₂, F i = f i := fun i hi => if_pos (Finset.sdiff_subset hi)
  have hF₂ : forall i in s₂ \ s₁, F i = -f i := fun i hi => if_neg (Finset.mem_sdiff.mp hi).2
  have hF : forall i, ‖F i‖ = ‖f i‖ := by
    intro i
    dsimp only [F]
    split_ifs <;> simp only [norm_neg]
  have :
    ‖(∑ i in s₁ \ s₂, V i (F i)) + ∑ i in s₂ \ s₁, V i (F i)‖ ^ 2 =
      (∑ i in s₁ \ s₂, ‖F i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖F i‖ ^ 2 := by
    have hs : Disjoint (s₁ \ s₂) (s₂ \ s₁) := disjoint_sdiff_sdiff
    simpa only [Finset.sum_union hs] using hV.norm_sum F (s₁ \ s₂ union s₂ \ s₁)
  convert! this using 4
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₁ i hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    simp only [hF₂ i hi, LinearIsometry.map_neg]
  · simp only [hF]
  · simp only [hF]

@[deprecated (since := "2026-06-03")]
alias OrthogonalFamily.norm_sq_diff_sum := OrthogonalFamily.norm_sq_sdiff_sum

/--
theorem `OrthogonalFamily.summable_iff_norm_sq_summable` / 定理 `OrthogonalFamily.summable_iff_norm_sq_summable`

English:
theorem OrthogonalFamily.summable_iff_norm_sq_summable
  given: [CompleteSpace E] (f : forall i, G i)
  proof: by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, norm_neg_add,
      Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
   

中文:
定理 OrthogonalFamily.summable_iff_norm_sq_summable
  条件: [完备空间 E] (f : 对任意 i, G i)
  证明: by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, norm_neg_add,
      Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
   

Depends on / 依赖: Finset, Finset.abs_sum_of_nonneg, Finset.sum_sdiff_sub_sum_sdiff, NormedAddCommGroup, NormedAddCommGroup.cauchySeq_iff, Real.norm_eq_abs, abs_sub, abs_sum_of_nonneg, cauchySeq_iff, classical, hV.norm_sq_sdiff_sum, norm_eq_abs, norm_neg_add, norm_sq_sdiff_sum, sq_nonneg, sqrt_pos, sqrt_pos.mpr, sum_sdiff_sub_sum_sdiff, summable_iff_cauchySeq_finset, trans_lt
-/
theorem OrthogonalFamily.summable_iff_norm_sq_summable [CompleteSpace E] (f : forall i, G i) :
    (Summable fun i => V i (f i)) ↔ Summable fun i => ‖f i‖ ^ 2 := by
  classical
    simp only [summable_iff_cauchySeq_finset, NormedAddCommGroup.cauchySeq_iff, norm_neg_add,
      Real.norm_eq_abs]
    constructor
    · intro hf ε hε
      obtain ⟨a, H⟩ := hf _ (sqrt_pos.mpr hε)
      use a
      intro s₁ hs₁ s₂ hs₂
      rw [← Finset.sum_sdiff_sub_sum_sdiff]
      refine (abs_sub _ _).trans_lt ?_
      have : forall i, 0 <= ‖f i‖ ^ 2 := fun i : ι => sq_nonneg _
      simp only [Finset.abs_sum_of_nonneg' this]
      have : ((∑ i in s₁ \ s₂, ‖f i‖ ^ 2) + ∑ i in s₂ \ s₁, ‖f i‖ ^ 2) < √ε ^ 2 := by
        rw [← hV.norm_sq_sdiff_sum]; rw [sq_lt_sq]; rw [abs_of_nonneg (sqrt_nonneg _)]; rw [abs_of_nonneg (norm_nonneg _)]
        exact H s₁ hs₁ s₂ hs₂
      have hη := sq_sqrt (le_of_lt hε)
      linarith
    · intro hf ε hε
      have hε' : 0 < ε ^ 2 / 2 := half_pos (sq_pos_of_pos hε)
      obtain ⟨a, H⟩ := hf _ hε'
      use a
      intro s₁ hs₁ s₂ hs₂
      refine (abs_lt_of_sq_lt_sq' ?_ (le_of_lt hε)).2
      have has : a <= s₁ ⊓ s₂ := le_inf hs₁ hs₂
      rw [hV.norm_sq_sdiff_sum]
      have Hs₁ : ∑ x in s₁ \ s₂, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert! H _ hs₁ _ has
        have : s₁ ⊓ s₂ subseteq s₁ := Finset.inter_subset_left
        rw [← Finset.sum_sdiff this]; rw [add_tsub_cancel_right]; rw [Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      have Hs₂ : ∑ x in s₂ \ s₁, ‖f x‖ ^ 2 < ε ^ 2 / 2 := by
        convert! H _ hs₂ _ has
        have : s₁ ⊓ s₂ subseteq s₂ := Finset.inter_subset_right
        rw [← Finset.sum_sdiff this]; rw [add_tsub_cancel_right]; rw [Finset.abs_sum_of_nonneg']
        · simp
        · exact fun i => sq_nonneg _
      linarith

end

end OrthogonalFamily_Seminormed

section OrthogonalFamily

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

variable {ι : Type*} {G : ι -> Type*}

/--
theorem `OrthogonalFamily.independent` / 定理 `OrthogonalFamily.independent`

English:
theorem OrthogonalFamily.independent
  statement: {V : ι -> Submodule 𝕜 E}
  proof: by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  refine LinearMap.ker_eq_bot.mp ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using! this
  calc
    ⟪(v i : E), v i⟫ = ⟪(v i : E), DFi

中文:
定理 OrthogonalFamily.independent
  结论: {V : ι -> 子模 𝕜 E}
  证明: by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  refine LinearMap.ker_eq_bot.mp ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using! this
  calc
    ⟪(v i : E), v i⟫ = ⟪(v i : E), DFi

Depends on / 依赖: DFinsupp, DFinsupp.lsum, DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply, LinearMap, LinearMap.ker_eq_bot.mp, LinearMap.mem_ker, Submodule, Submodule.eq_bot_iff, classical, eq_bot_iff, hV.inner_right_dfinsupp, iSupIndep_of_dfinsupp_lsum_injective, inner_right_dfinsupp, inner_self_eq_zero, inner_zero_right, ker_eq_bot, lsum_apply_apply, mem_ker, subtype
-/
theorem OrthogonalFamily.independent {V : ι -> Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ) :
    iSupIndep V := by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  refine LinearMap.ker_eq_bot.mp ?_
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [LinearMap.mem_ker] at hv
  ext i
  suffices ⟪(v i : E), v i⟫ = 0 by simpa only [inner_self_eq_zero] using! this
  calc
    ⟪(v i : E), v i⟫ = ⟪(v i : E), DFinsupp.lsum Nat (fun i => (V i).subtype) v⟫ := by
      simpa only [DFinsupp.sumAddHom_apply, DFinsupp.lsum_apply_apply] using!
        (hV.inner_right_dfinsupp v i (v i)).symm
    _ = 0 := by simp only [hv, inner_zero_right]

/--
theorem `DirectSum.IsInternal.collectedBasis_orthonormal` / 定理 `DirectSum.IsInternal.collectedBasis_orthonormal`

English:
theorem DirectSum.IsInternal.collectedBasis_orthonormal
  statement: [DecidableEq ι] {V : ι -> Submodule 𝕜 E}
  proof: by
  simpa only [hV_sum.collectedBasis_coe] using! hV.orthonormal_sigma_orthonormal hv_family

中文:
定理 直和.Is整数ernal.collectedBasis_orthonormal
  结论: [DecidableEq ι] {V : ι -> 子模 𝕜 E}
  证明: by
  simpa only [hV_sum.collectedBasis_coe] using! hV.orthonormal_sigma_orthonormal hv_family

Depends on / 依赖: collectedBasis_coe, hV.orthonormal_sigma_orthonormal, hV_sum, hV_sum.collectedBasis_coe, hv_family, orthonormal_sigma_orthonormal
-/
theorem DirectSum.IsInternal.collectedBasis_orthonormal [DecidableEq ι] {V : ι -> Submodule 𝕜 E}
    (hV : OrthogonalFamily 𝕜 (fun i => V i) fun i => (V i).subtypeₗᵢ)
    (hV_sum : DirectSum.IsInternal fun i => V i) {α : ι -> Type*}
    {v_family : forall i, Basis (α i) 𝕜 (V i)} (hv_family : forall i, Orthonormal 𝕜 (v_family i)) :
    Orthonormal 𝕜 (hV_sum.collectedBasis v_family) := by
  simpa only [hV_sum.collectedBasis_coe] using! hV.orthonormal_sigma_orthonormal hv_family

end OrthogonalFamily
