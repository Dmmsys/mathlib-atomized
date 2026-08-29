/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Additive Haar measure constructed from a basis

Given a basis of a finite-dimensional real vector space, we define the corresponding Lebesgue
measure, which gives measure `1` to the parallelepiped spanned by the basis.

## Main definitions

* `parallelepiped v` is the parallelepiped spanned by a finite family of vectors.
* `Basis.parallelepiped` is the parallelepiped associated to a basis, seen as a compact set with
  nonempty interior.
* `Basis.addHaar` is the Lebesgue measure associated to a basis, giving measure `1` to the
  corresponding parallelepiped.

In particular, we declare a `MeasureSpace` instance on any finite-dimensional inner product space,
by using the Lebesgue measure associated to some orthonormal basis (which is in fact independent
of the basis).
-/

@[expose] public section


open Set TopologicalSpace MeasureTheory MeasureTheory.Measure Module

open scoped Pointwise

noncomputable section

variable {ι ι' E F : Type*}

section Fintype

variable [Fintype ι] [Fintype ι']

section AddCommGroup

variable [AddCommGroup E] [Module Real E] [AddCommGroup F] [Module Real F]

/--
Definition of `parallelepiped` / `parallelepiped` 的定义

English:
definition parallelepiped
  signature: (v : ι -> E)
  body: (fun t : ι -> Real => ∑ i, t i • v i) '' Icc 0 1

中文:
定义 parallelepiped
  签名: (v : ι -> E)
  定义体: (fun t : ι -> Real => ∑ i, t i • v i) '' Icc 0 1
-/
def parallelepiped (v : ι -> E) : Set E :=
  (fun t : ι -> Real => ∑ i, t i • v i) '' Icc 0 1

/--
theorem `mem_parallelepiped_iff` / 定理 `mem_parallelepiped_iff`

English:
theorem mem_parallelepiped_iff
  given: (v : ι -> E) (x : E)
  proof: by
  simp [parallelepiped, eq_comm]

中文:
定理 mem_parallelepiped_iff
  条件: (v : ι -> E) (x : E)
  证明: by
  simp [parallelepiped, eq_comm]

Depends on / 依赖: eq_comm, parallelepiped
-/
theorem mem_parallelepiped_iff (v : ι -> E) (x : E) :
    x in parallelepiped v ↔ exists t in Icc (0 : ι -> Real) 1, x = ∑ i, t i • v i := by
  simp [parallelepiped, eq_comm]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `parallelepiped_basis_eq` / 定理 `parallelepiped_basis_eq`

English:
theorem parallelepiped_basis_eq
  given: (b : Basis ι Real E)
  proof: by
  classical
  ext x
  simp_rw [mem_parallelepiped_iff, mem_ofPred_eq, b.ext_elem_iff, _root_.map_sum,
    map_smul, Finset.sum_apply', Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mem_Icc,
    Pi.le_def, Pi.ze

中文:
定理 parallelepiped_basis_eq
  条件: (b : 基 ι 实数 E)
  证明: by
  classical
  ext x
  simp_rw [mem_parallelepiped_iff, mem_ofPred_eq, b.ext_elem_iff, _root_.map_sum,
    map_smul, Finset.sum_apply', Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mem_Icc,
    Pi.le_def, Pi.ze

Depends on / 依赖: Basis.repr_self, Finset, Finset.mem_univ, Finset.sum_apply, Finset.sum_ite_eq, Finsupp, Finsupp.single_apply, Finsupp.smul_single, Pi.le_def, Pi.one_apply, Pi.zero_apply, _root_, _root_.map_sum, b.ext_elem_iff, classical, ext_elem_iff, forall_and, ite_true, le_def, map_smul
-/
theorem parallelepiped_basis_eq (b : Basis ι Real E) :
    parallelepiped b = {x | forall i, b.repr x i in Set.Icc 0 1} := by
  classical
  ext x
  simp_rw [mem_parallelepiped_iff, mem_ofPred_eq, b.ext_elem_iff, _root_.map_sum,
    map_smul, Finset.sum_apply', Basis.repr_self, Finsupp.smul_single, smul_eq_mul,
    mul_one, Finsupp.single_apply, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mem_Icc,
    Pi.le_def, Pi.zero_apply, Pi.one_apply, ← forall_and]
  aesop

/--
theorem `image_parallelepiped` / 定理 `image_parallelepiped`

English:
theorem image_parallelepiped
  given: (f : E ->ₗ[Real] F) (v : ι -> E)
  proof: by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, _root_.map_sum, map_smulₛₗ, RingHom.id_apply]

中文:
定理 image_parallelepiped
  条件: (f : E ->ₗ[实数] F) (v : ι -> E)
  证明: by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, _root_.map_sum, map_smulₛₗ, RingHom.id_apply]

Depends on / 依赖: Function, Function.comp_apply, RingHom, RingHom.id_apply, _root_, _root_.map_sum, comp_apply, id_apply, image_comp, map_sum, parallelepiped
-/
theorem image_parallelepiped (f : E ->ₗ[Real] F) (v : ι -> E) :
    f '' parallelepiped v = parallelepiped (f ∘ v) := by
  simp only [parallelepiped, ← image_comp]
  congr 1 with t
  simp only [Function.comp_apply, _root_.map_sum, map_smulₛₗ, RingHom.id_apply]

/-- Reindexing a family of vectors does not change their parallelepiped. -/
@[simp]
/--
theorem `parallelepiped_comp_equiv` / 定理 `parallelepiped_comp_equiv`

English:
theorem parallelepiped_comp_equiv
  given: (v : ι -> E) (e : ι' ≃ ι)
  proof: by
  simp only [parallelepiped]
  let K : (ι' -> Real) ≃ (ι -> Real) := Equiv.piCongrLeft' (fun _a : ι' => Real) e
  have : Icc (0 : ι -> Real) 1 = K '' Icc (0 : ι' -> Real) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [K, mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply,

中文:
定理 parallelepiped_comp_equiv
  条件: (v : ι -> E) (e : ι' ≃ ι)
  证明: by
  simp only [parallelepiped]
  let K : (ι' -> Real) ≃ (ι -> Real) := Equiv.piCongrLeft' (fun _a : ι' => Real) e
  have : Icc (0 : ι -> Real) 1 = K '' Icc (0 : ι' -> Real) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [K, mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply,

Depends on / 依赖: Equiv.piCongrLeft, Equiv.preimage_eq_iff_eq_image, Equiv.symm_apply_apply, Pi.le_def, Pi.one_apply, Pi.zero_apply, _apply, e.symm, le_def, mem_Icc, mem_preimage, one_apply, parallelepiped, piCongrLeft, preimage_eq_iff_eq_image, symm_apply_apply, zero_apply
-/
theorem parallelepiped_comp_equiv (v : ι -> E) (e : ι' ≃ ι) :
    parallelepiped (v ∘ e) = parallelepiped v := by
  simp only [parallelepiped]
  let K : (ι' -> Real) ≃ (ι -> Real) := Equiv.piCongrLeft' (fun _a : ι' => Real) e
  have : Icc (0 : ι -> Real) 1 = K '' Icc (0 : ι' -> Real) 1 := by
    rw [← Equiv.preimage_eq_iff_eq_image]
    ext x
    simp only [K, mem_preimage, mem_Icc, Pi.le_def, Pi.zero_apply, Equiv.piCongrLeft'_apply,
      Pi.one_apply]
    refine
      ⟨fun h => ⟨fun i => ?_, fun i => ?_⟩, fun h =>
        ⟨fun i => h.1 (e.symm i), fun i => h.2 (e.symm i)⟩⟩
    · simpa only [Equiv.symm_apply_apply] using h.1 (e i)
    · simpa only [Equiv.symm_apply_apply] using h.2 (e i)
  rw [this]; rw [← image_comp]
  ext x
  have := fun z : ι' -> Real => e.symm.sum_comp fun i => z i • v (e i)
  simp_rw [Equiv.apply_symm_apply] at this
  simp_rw [Function.comp_apply, mem_image, mem_Icc, K, Equiv.piCongrLeft'_apply, this]

-- The parallelepiped associated to an orthonormal basis of `ℝ` is either `[0, 1]` or `[-1, 0]`.
/--
theorem `parallelepiped_orthonormalBasis_one_dim` / 定理 `parallelepiped_orthonormalBasis_one_dim`

English:
theorem parallelepiped_orthonormalBasis_one_dim
  given: (b : OrthonormalBasis ι Real Real)
  proof: by
  have e : ι ≃ Fin 1 := by
    apply Fintype.equivFinOfCardEq
    simp only [← finrank_eq_card_basis b.toBasis, finrank_self]
  have B : parallelepiped (b.reindex e) = parallelepiped b := by
    convert! parallelepiped_comp_equiv b e.symm
    ext i
    simp only [OrthonormalBasis.coe_reindex]
  r

中文:
定理 parallelepiped_orthonormalBasis_one_dim
  条件: (b : 正交标准基 ι 实数 实数)
  证明: by
  have e : ι ≃ Fin 1 := by
    apply Fintype.equivFinOfCardEq
    simp only [← finrank_eq_card_basis b.toBasis, finrank_self]
  have B : parallelepiped (b.reindex e) = parallelepiped b := by
    convert! parallelepiped_comp_equiv b e.symm
    ext i
    simp only [OrthonormalBasis.coe_reindex]
  r

Depends on / 依赖: Fintype, Fintype.equivFinOfCardEq, OrthonormalBasis, OrthonormalBasis.coe_reindex, Subset, Subset.antisymm, Subsingleton, Subsingleton.eli, antisymm, b.reindex, b.toBasis, coe_reindex, convert, e.symm, equivFinOfCardEq, finrank_eq_card_basis, finrank_self, parallelepiped, parallelepiped_comp_equiv, reindex
-/
theorem parallelepiped_orthonormalBasis_one_dim (b : OrthonormalBasis ι Real Real) :
    parallelepiped b = Icc 0 1 ∨ parallelepiped b = Icc (-1) 0 := by
  have e : ι ≃ Fin 1 := by
    apply Fintype.equivFinOfCardEq
    simp only [← finrank_eq_card_basis b.toBasis, finrank_self]
  have B : parallelepiped (b.reindex e) = parallelepiped b := by
    convert! parallelepiped_comp_equiv b e.symm
    ext i
    simp only [OrthonormalBasis.coe_reindex]
  rw [← B]
  let F : Real -> Fin 1 -> Real := fun t _i => t
  have A : Icc (0 : Fin 1 -> Real) 1 = F '' Icc (0 : Real) 1 := by
    apply Subset.antisymm
    · intro x hx
      refine ⟨x 0, ⟨hx.1 0, hx.2 0⟩, ?_⟩
      ext j
      simp only [F, Subsingleton.elim j 0]
    · rintro x ⟨y, hy, rfl⟩
      exact ⟨fun _j => hy.1, fun _j => hy.2⟩
  rcases orthonormalBasis_one_dim (b.reindex e) with (H | H)
  · left
    simp_rw [parallelepiped, H, A, smul_eq_mul, mul_one]
    simp only [F, Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton,
      ← image_comp, Function.comp_apply, image_id']
  · right
    simp_rw [H, parallelepiped, smul_eq_mul, A]
    simp only [F, Finset.univ_unique, Fin.default_eq_zero, mul_neg, mul_one, Finset.sum_neg_distrib,
      Finset.sum_singleton, ← image_comp, Function.comp, image_neg_eq_neg, neg_Icc, neg_zero]

/--
theorem `parallelepiped_eq_sum_segment` / 定理 `parallelepiped_eq_sum_segment`

English:
theorem parallelepiped_eq_sum_segment
  given: (v : ι -> E)
  statement: parallelepiped v = ∑ i, segment Real 0 (v i)
  proof: by
  ext
  simp only [mem_parallelepiped_iff, Set.mem_finsetSum, Finset.mem_univ, forall_true_left,
    segment_eq_image, smul_zero, zero_add, ← Set.pi_univ_Icc, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • v, fun {i} => ⟨t i, ht _, by simp⟩, rfl⟩
  rintro ⟨g, hg, rfl⟩
  cho

中文:
定理 parallelepiped_eq_sum_segment
  条件: (v : ι -> E)
  结论: parallelepiped v = ∑ i, segment 实数 0 (v i)
  证明: by
  ext
  simp only [mem_parallelepiped_iff, Set.mem_finsetSum, Finset.mem_univ, forall_true_left,
    segment_eq_image, smul_zero, zero_add, ← Set.pi_univ_Icc, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • v, fun {i} => ⟨t i, ht _, by simp⟩, rfl⟩
  rintro ⟨g, hg, rfl⟩
  cho

Depends on / 依赖: Finset, Finset.mem_univ, Set.mem_finsetSum, Set.mem_univ_pi, Set.pi_univ_Icc, forall_true_left, mem_finsetSum, mem_parallelepiped_iff, mem_univ, mem_univ_pi, pi_univ_Icc, segment_eq_image, simp_rw, smul_zero, zero_add
-/
theorem parallelepiped_eq_sum_segment (v : ι -> E) : parallelepiped v = ∑ i, segment Real 0 (v i) := by
  ext
  simp only [mem_parallelepiped_iff, Set.mem_finsetSum, Finset.mem_univ, forall_true_left,
    segment_eq_image, smul_zero, zero_add, ← Set.pi_univ_Icc, Set.mem_univ_pi]
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t • v, fun {i} => ⟨t i, ht _, by simp⟩, rfl⟩
  rintro ⟨g, hg, rfl⟩
  choose t ht hg using @hg
  refine ⟨@t, @ht, ?_⟩
  simp_rw [hg]

/--
theorem `convex_parallelepiped` / 定理 `convex_parallelepiped`

English:
theorem convex_parallelepiped
  given: (v : ι -> E)
  statement: Convex Real (parallelepiped v)
  proof: by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _i _hi => convex_segment _ _

中文:
定理 convex_parallelepiped
  条件: (v : ι -> E)
  结论: 凸 实数 (parallelepiped v)
  证明: by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _i _hi => convex_segment _ _

Depends on / 依赖: convex_segment, convex_sum, parallelepiped_eq_sum_segment
-/
theorem convex_parallelepiped (v : ι -> E) : Convex Real (parallelepiped v) := by
  rw [parallelepiped_eq_sum_segment]
  exact convex_sum _ fun _i _hi => convex_segment _ _

/--
theorem `parallelepiped_eq_convexHull` / 定理 `parallelepiped_eq_convexHull`

English:
theorem parallelepiped_eq_convexHull
  given: (v : ι -> E)
  proof: by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

中文:
定理 parallelepiped_eq_convexHull
  条件: (v : ι -> E)
  证明: by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

Depends on / 依赖: convexHull_pair, convexHull_sum, parallelepiped_eq_sum_segment, simp_rw
-/
theorem parallelepiped_eq_convexHull (v : ι -> E) :
    parallelepiped v = convexHull Real (∑ i, {(0 : E), v i}) := by
  simp_rw [convexHull_sum, convexHull_pair, parallelepiped_eq_sum_segment]

/--
theorem `parallelepiped_single` / 定理 `parallelepiped_single`

English:
theorem parallelepiped_single
  given: [DecidableEq ι] (a : ι -> Real)
  proof: by
  ext x
  simp_rw [Set.uIcc, mem_parallelepiped_iff, Set.mem_Icc, Pi.le_def, ← forall_and, Pi.inf_apply,
    Pi.sup_apply, ← Pi.single_smul', Pi.one_apply, Pi.zero_apply, ← Pi.smul_apply',
    Finset.univ_sum_single (_ : ι -> Real)]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    specialize ht i
    

中文:
定理 parallelepiped_single
  条件: [DecidableEq ι] (a : ι -> 实数)
  证明: by
  ext x
  simp_rw [Set.uIcc, mem_parallelepiped_iff, Set.mem_Icc, Pi.le_def, ← forall_and, Pi.inf_apply,
    Pi.sup_apply, ← Pi.single_smul', Pi.one_apply, Pi.zero_apply, ← Pi.smul_apply',
    Finset.univ_sum_single (_ : ι -> Real)]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    specialize ht i
    

Depends on / 依赖: Finset, Finset.univ_sum_single, Pi.inf_apply, Pi.le_def, Pi.mul_apply, Pi.one_apply, Pi.single_smul, Pi.smul_apply, Pi.sup_apply, Pi.zero_apply, Set.mem_Icc, Set.uIcc, forall_and, inf_apply, inf_eq_right, inf_eq_right.mpr, le_def, le_mul_of_le_one_left, le_total, mem_Icc
-/
theorem parallelepiped_single [DecidableEq ι] (a : ι -> Real) :
    (parallelepiped fun i => Pi.single i (a i)) = Set.uIcc 0 a := by
  ext x
  simp_rw [Set.uIcc, mem_parallelepiped_iff, Set.mem_Icc, Pi.le_def, ← forall_and, Pi.inf_apply,
    Pi.sup_apply, ← Pi.single_smul', Pi.one_apply, Pi.zero_apply, ← Pi.smul_apply',
    Finset.univ_sum_single (_ : ι -> Real)]
  constructor
  · rintro ⟨t, ht, rfl⟩ i
    specialize ht i
    simp_rw [smul_eq_mul, Pi.mul_apply]
    rcases le_total (a i) 0 with hai | hai
    · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai]
      exact ⟨le_mul_of_le_one_left hai ht.2, mul_nonpos_of_nonneg_of_nonpos ht.1 hai⟩
    · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai]
      exact ⟨mul_nonneg ht.1 hai, mul_le_of_le_one_left hai ht.2⟩
  · intro h
    refine ⟨fun i => x i / a i, fun i => ?_, funext fun i => ?_⟩
    · specialize h i
      rcases le_total (a i) 0 with hai | hai
      · rw [sup_eq_left.mpr hai, inf_eq_right.mpr hai] at h
        exact ⟨div_nonneg_of_nonpos h.2 hai, div_le_one_of_ge h.1 hai⟩
      · rw [sup_eq_right.mpr hai, inf_eq_left.mpr hai] at h
        exact ⟨div_nonneg h.1 hai, div_le_one_of_le₀ h.2 hai⟩
    · specialize h i
      simp only [smul_eq_mul, Pi.mul_apply]
      rcases eq_or_ne (a i) 0 with hai | hai
      · rw [hai, inf_idem, sup_idem, ← le_antisymm_iff] at h
        rw [hai]; rw [← h]; rw [zero_div]; rw [zero_mul]
      · rw [div_mul_cancel₀ _ hai]

end AddCommGroup

section NormedSpace

variable [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedSpace Real E] [NormedSpace Real F]

namespace Module.Basis

/--
Definition of `parallelepiped` / `parallelepiped` 的定义

English:
definition parallelepiped
  signature: (b : Basis ι Real E)
  body: _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finsetSum Finset.univ
        fun (i : ι) (_H : i in Finset.univ) => by fun_prop)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1)) by
      dsimp only

中文:
定义 parallelepiped
  签名: (b : 基 ι 实数 E)
  定义体: _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finsetSum Finset.univ
        fun (i : ι) (_H : i in Finset.univ) => by fun_prop)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1)) by
      dsimp only

Depends on / 依赖: _root_, _root_.parallelepiped, parallelepiped
-/
def parallelepiped (b : Basis ι Real E) : PositiveCompacts E where
  carrier := _root_.parallelepiped b
  isCompact' := IsCompact.image isCompact_Icc
      (continuous_finsetSum Finset.univ
        fun (i : ι) (_H : i in Finset.univ) => by fun_prop)
  interior_nonempty' := by
    suffices H : Set.Nonempty (interior (b.equivFunL.symm.toHomeomorph '' Icc 0 1)) by
      dsimp only [_root_.parallelepiped]
      convert! H
      exact (b.equivFun_symm_apply _).symm
    have A : Set.Nonempty (interior (Icc (0 : ι -> Real) 1)) := by
      rw [← pi_univ_Icc]; rw [interior_pi_set (@finite_univ ι _)]
      simp only [univ_pi_nonempty_iff, Pi.zero_apply, Pi.one_apply, interior_Icc, nonempty_Ioo,
        zero_lt_one, imp_true_iff]
    rwa [← Homeomorph.image_interior, image_nonempty]

@[simp]
/--
theorem `coe_parallelepiped` / 定理 `coe_parallelepiped`

English:
theorem coe_parallelepiped
  given: (b : Basis ι Real E)
  proof: rfl

@[simp]

中文:
定理 coe_parallelepiped
  条件: (b : 基 ι 实数 E)
  证明: rfl

@[simp]
-/
theorem coe_parallelepiped (b : Basis ι Real E) :
    (b.parallelepiped : Set E) = _root_.parallelepiped b := rfl

@[simp]
/--
theorem `parallelepiped_reindex` / 定理 `parallelepiped_reindex`

English:
theorem parallelepiped_reindex
  given: (b : Basis ι Real E) (e : ι ≃ ι')
  proof: PositiveCompacts.ext
    (congr_arg _root_.parallelepiped (b.coe_reindex e)).trans (parallelepiped_comp_equiv b e.symm)

中文:
定理 parallelepiped_reindex
  条件: (b : 基 ι 实数 E) (e : ι ≃ ι')
  证明: PositiveCompacts.ext
    (congr_arg _root_.parallelepiped (b.coe_reindex e)).trans (parallelepiped_comp_equiv b e.symm)

Depends on / 依赖: PositiveCompacts, PositiveCompacts.ext, _root_, _root_.parallelepiped, b.coe_reindex, coe_reindex, congr_arg, e.symm, parallelepiped, parallelepiped_comp_equiv
-/
theorem parallelepiped_reindex (b : Basis ι Real E) (e : ι ≃ ι') :
    (b.reindex e).parallelepiped = b.parallelepiped :=
PositiveCompacts.ext
    (congr_arg _root_.parallelepiped (b.coe_reindex e)).trans (parallelepiped_comp_equiv b e.symm)

/--
theorem `parallelepiped_map` / 定理 `parallelepiped_map`

English:
theorem parallelepiped_map
  given: (b : Basis ι Real E) (e : E ≃ₗ[Real] F)
  proof: PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm

中文:
定理 parallelepiped_map
  条件: (b : 基 ι 实数 E) (e : E ≃ₗ[实数] F)
  证明: PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm

Depends on / 依赖: b.finiteDimensional_of_finite, finiteDimensional_of_finite
-/
theorem parallelepiped_map (b : Basis ι Real E) (e : E ≃ₗ[Real] F) :
    (b.map e).parallelepiped = b.parallelepiped.map e
    (haveI := b.finiteDimensional_of_finite
    LinearMap.continuous_of_finiteDimensional e.toLinearMap)
    (haveI := (b.map e).finiteDimensional_of_finite
    LinearMap.isOpenMap_of_finiteDimensional _ e.surjective) :=
  PositiveCompacts.ext (image_parallelepiped e.toLinearMap _).symm

/--
theorem `prod_parallelepiped` / 定理 `prod_parallelepiped`

English:
theorem prod_parallelepiped
  given: (v : Basis ι Real E) (w : Basis ι' Real F)
  proof: by
  ext x
  simp only [Basis.coe_parallelepiped, TopologicalSpace.PositiveCompacts.coe_prod, Set.mem_prod,
    mem_parallelepiped_iff]
  constructor
  · intro h
    rcases h with ⟨t, ht1, ht2⟩
    constructor
    · use t ∘ Sum.inl
      constructor
      · exact ⟨(ht1.1 <| Sum.inl ·), (ht1.2 <| Sum

中文:
定理 prod_parallelepiped
  条件: (v : 基 ι 实数 E) (w : 基 ι' 实数 F)
  证明: by
  ext x
  simp only [Basis.coe_parallelepiped, TopologicalSpace.PositiveCompacts.coe_prod, Set.mem_prod,
    mem_parallelepiped_iff]
  constructor
  · intro h
    rcases h with ⟨t, ht1, ht2⟩
    constructor
    · use t ∘ Sum.inl
      constructor
      · exact ⟨(ht1.1 <| Sum.inl ·), (ht1.2 <| Sum

Depends on / 依赖: Basis.coe_parallelepiped, PositiveCompacts, Prod.fst_sum, Prod.snd_sum, Set.mem_prod, Sum.elim, Sum.inl, Sum.inr, TopologicalSpace, TopologicalSpace.PositiveCompacts.coe_prod, coe_parallelepiped, coe_prod, constructo, fst_sum, mem_parallelepiped_iff, mem_prod, snd_sum
-/
theorem prod_parallelepiped (v : Basis ι Real E) (w : Basis ι' Real F) :
    (v.prod w).parallelepiped = v.parallelepiped ×ˢ w.parallelepiped := by
  ext x
  simp only [Basis.coe_parallelepiped, TopologicalSpace.PositiveCompacts.coe_prod, Set.mem_prod,
    mem_parallelepiped_iff]
  constructor
  · intro h
    rcases h with ⟨t, ht1, ht2⟩
    constructor
    · use t ∘ Sum.inl
      constructor
      · exact ⟨(ht1.1 <| Sum.inl ·), (ht1.2 <| Sum.inl ·)⟩
      simp [ht2, Prod.fst_sum]
    · use t ∘ Sum.inr
      constructor
      · exact ⟨(ht1.1 <| Sum.inr ·), (ht1.2 <| Sum.inr ·)⟩
      simp [ht2, Prod.snd_sum]
  intro h
  rcases h with ⟨⟨t, ht1, ht2⟩, ⟨s, hs1, hs2⟩⟩
  use Sum.elim t s
  constructor
  · constructor
    · change forall x : ι oplus ι', 0 <= Sum.elim t s x
      aesop
    · change forall x : ι oplus ι', Sum.elim t s x <= 1
      aesop
  ext
  · simp [ht2, Prod.fst_sum]
  · simp [hs2, Prod.snd_sum]

variable [MeasurableSpace E] [BorelSpace E]

/-- The Lebesgue measure associated to a basis, giving measure `1` to the parallelepiped spanned
by the basis. -/
irreducible_def addHaar (b : Basis ι Real E) : Measure E :=
  Measure.addHaarMeasure b.parallelepiped

/--
Instance `_root_.isAddHaarMeasure_basis_addHaar` / 实例 `_root_.isAddHaarMeasure_basis_addHaar`

English:
instance _root_.isAddHaarMeasure_basis_addHaar
  signature: (b : Basis ι Real E)
  body: by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _

中文:
实例 _root_.isAddHaarMeasure_basis_addHaar
  签名: (b : 基 ι 实数 E)
  定义体: by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _

Depends on / 依赖: Basis.addHaar, Measure, Measure.isAddHaarMeasure_addHaarMeasure, addHaar, isAddHaarMeasure_addHaarMeasure
-/
instance _root_.isAddHaarMeasure_basis_addHaar (b : Basis ι Real E) : IsAddHaarMeasure b.addHaar := by
  rw [Basis.addHaar]; exact Measure.isAddHaarMeasure_addHaarMeasure _

instance (b : Basis ι Real E) : SigmaFinite b.addHaar := by
  have : FiniteDimensional Real E := b.finiteDimensional_of_finite
  rw [Basis.addHaar_def]; exact sigmaFinite_addHaarMeasure

/--
theorem `addHaar_eq_iff` / 定理 `addHaar_eq_iff`

English:
theorem addHaar_eq_iff
  statement: [SecondCountableTopology E] (b : Basis ι Real E) (μ : Measure E)
  proof: by
  rw [Basis.addHaar_def]
  exact addHaarMeasure_eq_iff b.parallelepiped μ

@[simp]

中文:
定理 addHaar_eq_iff
  结论: [第二可数拓扑 E] (b : 基 ι 实数 E) (μ : 测度 E)
  证明: by
  rw [Basis.addHaar_def]
  exact addHaarMeasure_eq_iff b.parallelepiped μ

@[simp]

Depends on / 依赖: Basis.addHaar_def, addHaarMeasure_eq_iff, addHaar_def, b.parallelepiped, parallelepiped
-/
theorem addHaar_eq_iff [SecondCountableTopology E] (b : Basis ι Real E) (μ : Measure E)
    [SigmaFinite μ] [IsAddLeftInvariant μ] :
    b.addHaar = μ ↔ μ b.parallelepiped = 1 := by
  rw [Basis.addHaar_def]
  exact addHaarMeasure_eq_iff b.parallelepiped μ

@[simp]
/--
theorem `addHaar_reindex` / 定理 `addHaar_reindex`

English:
theorem addHaar_reindex
  given: (b : Basis ι Real E) (e : ι ≃ ι')
  proof: by
  rw [Basis.addHaar]; rw [b.parallelepiped_reindex e]; rw [← Basis.addHaar]

中文:
定理 addHaar_reindex
  条件: (b : 基 ι 实数 E) (e : ι ≃ ι')
  证明: by
  rw [Basis.addHaar]; rw [b.parallelepiped_reindex e]; rw [← Basis.addHaar]

Depends on / 依赖: Basis.addHaar, addHaar, b.parallelepiped_reindex, parallelepiped_reindex
-/
theorem addHaar_reindex (b : Basis ι Real E) (e : ι ≃ ι') :
    (b.reindex e).addHaar = b.addHaar := by
  rw [Basis.addHaar]; rw [b.parallelepiped_reindex e]; rw [← Basis.addHaar]

/--
theorem `addHaar_self` / 定理 `addHaar_self`

English:
theorem addHaar_self
  given: (b : Basis ι Real E)
  statement: b.addHaar (_root_.parallelepiped b) = 1
  proof: by
  rw [Basis.addHaar]; exact addHaarMeasure_self

中文:
定理 addHaar_self
  条件: (b : 基 ι 实数 E)
  结论: b.addHaar (_root_.parallelepiped b) = 1
  证明: by
  rw [Basis.addHaar]; exact addHaarMeasure_self

Depends on / 依赖: Basis.addHaar, addHaar, addHaarMeasure_self
-/
theorem addHaar_self (b : Basis ι Real E) : b.addHaar (_root_.parallelepiped b) = 1 := by
  rw [Basis.addHaar]; exact addHaarMeasure_self

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopologyEither E F]

/--
theorem `prod_addHaar` / 定理 `prod_addHaar`

English:
theorem prod_addHaar
  given: (v : Basis ι Real E) (w : Basis ι' Real F)
  proof: by
  have : FiniteDimensional Real E := v.finiteDimensional_of_finite
  have : FiniteDimensional Real F := w.finiteDimensional_of_finite
  simp [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped, Basis.addHaar_self]

中文:
定理 prod_addHaar
  条件: (v : 基 ι 实数 E) (w : 基 ι' 实数 F)
  证明: by
  have : FiniteDimensional Real E := v.finiteDimensional_of_finite
  have : FiniteDimensional Real F := w.finiteDimensional_of_finite
  simp [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped, Basis.addHaar_self]

Depends on / 依赖: Basis.addHaar_self, Basis.prod_parallelepiped, FiniteDimensional, addHaar_eq_iff, addHaar_self, finiteDimensional_of_finite, prod_parallelepiped, v.finiteDimensional_of_finite, v.prod, w.finiteDimensional_of_finite
-/
theorem prod_addHaar (v : Basis ι Real E) (w : Basis ι' Real F) :
    (v.prod w).addHaar = v.addHaar.prod w.addHaar := by
  have : FiniteDimensional Real E := v.finiteDimensional_of_finite
  have : FiniteDimensional Real F := w.finiteDimensional_of_finite
  simp [(v.prod w).addHaar_eq_iff, Basis.prod_parallelepiped, Basis.addHaar_self]

end Module.Basis

end NormedSpace

end Fintype

/-- A finite-dimensional inner product space has a canonical measure, the Lebesgue measure giving
volume `1` to the parallelepiped spanned by any orthonormal basis. We define the measure using
some arbitrary choice of orthonormal basis. The fact that it works with any orthonormal basis
is proved in `orthonormalBasis.volume_parallelepiped`.

This instance creates:

- a potential non-defeq diamond with the natural instance for `MeasureSpace (ULift E)`,
  which does not exist in Mathlib at the moment;

- a diamond with the existing instance `MeasureTheory.Measure.instMeasureSpacePUnit`.

However, we've decided not to refactor until one of these diamonds starts creating issues, see
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Hausdorff.20measure.20normalisation
-/
instance (priority := 100) measureSpaceOfInnerProductSpace [NormedAddCommGroup E]
    [InnerProductSpace Real E] [FiniteDimensional Real E] [MeasurableSpace E] [BorelSpace E] :
    MeasureSpace E where volume := (stdOrthonormalBasis Real E).toBasis.addHaar

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NormedAddCommGroup
  signature: E] [InnerProductSpace Real E] [FiniteDimensional Real E]
  body: isAddHaarMeasure_basis_addHaar _

中文:
实例 [赋范交换加群
  签名: E] [内积空间 实数 E] [有限维 实数 E]
  定义体: isAddHaarMeasure_basis_addHaar _

Depends on / 依赖: isAddHaarMeasure_basis_addHaar
-/
instance [NormedAddCommGroup E] [InnerProductSpace Real E] [FiniteDimensional Real E]
    [MeasurableSpace E] [BorelSpace E] : IsAddHaarMeasure (volume : Measure E) :=
  isAddHaarMeasure_basis_addHaar _

/--
Instance `Real.measureSpace` / 实例 `Real.measureSpace`

English:
instance Real.measureSpace
  signature: : MeasureSpace Real
  body: by infer_instance

中文:
实例 实数.measureSpace
  签名: : 测度空间 实数
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance Real.measureSpace : MeasureSpace Real := by infer_instance
