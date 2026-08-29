/-
Copyright (c) 2024 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.BigOperators.Sym
public import Mathlib.Data.Finsupp.Pointwise
public import Mathlib.Data.Sym.Sym2.Finsupp
public import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Constructing a bilinear map from a quadratic map, given a basis

This file provides an alternative to `QuadraticMap.associated`; unlike that definition, this one
does not require `Invertible (2 : R)`. Unlike that definition, this only works in the presence of
a basis.
-/

@[expose] public section

open LinearMap (BilinMap)
open Module

namespace QuadraticMap
variable {ι R M N : Type*}

section Finsupp
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Finsupp

/--
theorem `map_finsuppSum'` / 定理 `map_finsuppSum'`

English:
theorem map_finsuppSum'
  given: (Q : QuadraticMap R M N) (f : ι ->₀ R) (g : ι -> R -> M)
  proof: Q.map_sum' ..

中文:
定理 map_finsuppSum'
  条件: (Q : 二次映射 R M N) (f : ι ->₀ R) (g : ι -> R -> M)
  证明: Q.map_sum' ..

Depends on / 依赖: Q.map_sum, map_sum
-/
theorem map_finsuppSum' (Q : QuadraticMap R M N) (f : ι ->₀ R) (g : ι -> R -> M) :
    Q (f.sum g) =
      ∑ p in f.support.sym2, polarSym2 Q (p.map fun i => g i (f i)) - f.sum fun i a => Q (g i a) :=
  Q.map_sum' ..

/--
theorem `apply_linearCombination'` / 定理 `apply_linearCombination'`

English:
theorem apply_linearCombination'
  given: (Q : QuadraticMap R M N) {g : ι -> M} (l : ι ->₀ R)
  proof: by
  simp_rw [linearCombination_apply, map_finsuppSum', Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]; rw [l.sym2Mul.sum_of_support_subset support_sym2Mul_subset _ by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

中文:
定理 apply_linearCombination'
  条件: (Q : 二次映射 R M N) {g : ι -> M} (l : ι ->₀ R)
  证明: by
  simp_rw [linearCombination_apply, map_finsuppSum', Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]; rw [l.sym2Mul.sum_of_support_subset support_sym2Mul_subset _ by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

Depends on / 依赖: Finsupp, Finsupp.sum, Q.map_smul, l.sym2Mul.sum_of_support_subset, linearCombination_apply, map_finsuppSum, map_smul, mul_smul, polarSym2_map_smul, simp_rw, sum_of_support_subset, support_mul_subset_left, support_sym2Mul_subset, sym2Mul
-/
theorem apply_linearCombination' (Q : QuadraticMap R M N) {g : ι -> M} (l : ι ->₀ R) :
    Q (linearCombination R g l) =
      linearCombination R (polarSym2 Q ∘ Sym2.map g) l.sym2Mul -
        linearCombination R (Q ∘ g) (l * l) := by
  simp_rw [linearCombination_apply, map_finsuppSum', Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]; rw [l.sym2Mul.sum_of_support_subset support_sym2Mul_subset _ by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

/--
theorem `sum_polar_sub_repr_sq` / 定理 `sum_polar_sub_repr_sq`

English:
theorem sum_polar_sub_repr_sq
  given: (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M)
  proof: by
  rw [← apply_linearCombination']; rw [Basis.linearCombination_repr]

中文:
定理 sum_polar_sub_repr_sq
  条件: (Q : 二次映射 R M N) (bm : 基 ι R M) (x : M)
  证明: by
  rw [← apply_linearCombination']; rw [Basis.linearCombination_repr]

Depends on / 依赖: Basis.linearCombination_repr, apply_linearCombination, linearCombination_repr
-/
theorem sum_polar_sub_repr_sq (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (polarSym2 Q ∘ Sym2.map bm) (bm.repr x).sym2Mul -
      linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) = Q x := by
  rw [← apply_linearCombination']; rw [Basis.linearCombination_repr]

variable [DecidableEq ι]

/--
theorem `map_finsuppSum` / 定理 `map_finsuppSum`

English:
theorem map_finsuppSum
  given: (Q : QuadraticMap R M N) (f : ι ->₀ R) (g : ι -> R -> M)
  proof: Q.map_sum _ _

中文:
定理 map_finsuppSum
  条件: (Q : 二次映射 R M N) (f : ι ->₀ R) (g : ι -> R -> M)
  证明: Q.map_sum _ _

Depends on / 依赖: Q.map_sum, map_sum
-/
theorem map_finsuppSum (Q : QuadraticMap R M N) (f : ι ->₀ R) (g : ι -> R -> M) :
    Q (f.sum g) = f.sum (fun i r => Q (g i r)) +
      ∑ p in f.support.sym2 with ¬ p.IsDiag, polarSym2 Q (p.map fun i => g i (f i)) := Q.map_sum _ _

/--
theorem `apply_linearCombination` / 定理 `apply_linearCombination`

English:
theorem apply_linearCombination
  given: (Q : QuadraticMap R M N) {g : ι -> M} (l : ι ->₀ R)
  proof: by
  simp_rw [linearCombination_apply, map_finsuppSum, Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

中文:
定理 apply_linearCombination
  条件: (Q : 二次映射 R M N) {g : ι -> M} (l : ι ->₀ R)
  证明: by
  simp_rw [linearCombination_apply, map_finsuppSum, Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

Depends on / 依赖: Finsupp, Finsupp.sum, Q.map_smul, linearCombination_apply, map_finsuppSum, map_smul, mul_smul, polarSym2_map_smul, simp_rw, sum_of_support_subset, support_mul_subset_left
-/
theorem apply_linearCombination (Q : QuadraticMap R M N) {g : ι -> M} (l : ι ->₀ R) :
    Q (linearCombination R g l) = linearCombination R (Q ∘ g) (l * l) +
      ∑ p in l.support.sym2 with ¬ p.IsDiag, (p.map l).mul • polarSym2 Q (p.map g) := by
  simp_rw [linearCombination_apply, map_finsuppSum, Q.map_smul, mul_smul]
  rw [(l * l).sum_of_support_subset support_mul_subset_left _ <| by simp]
  simp [Finsupp.sum, ← polarSym2_map_smul, mul_smul]

/--
theorem `sum_repr_sq_add_sum_repr_mul_polar` / 定理 `sum_repr_sq_add_sum_repr_mul_polar`

English:
theorem sum_repr_sq_add_sum_repr_mul_polar
  given: (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M)
  proof: by
  rw [← apply_linearCombination]; rw [Basis.linearCombination_repr]

中文:
定理 sum_repr_sq_add_sum_repr_mul_polar
  条件: (Q : 二次映射 R M N) (bm : 基 ι R M) (x : M)
  证明: by
  rw [← apply_linearCombination]; rw [Basis.linearCombination_repr]

Depends on / 依赖: Basis.linearCombination_repr, apply_linearCombination, linearCombination_repr
-/
theorem sum_repr_sq_add_sum_repr_mul_polar (Q : QuadraticMap R M N) (bm : Basis ι R M) (x : M) :
    linearCombination R (Q ∘ bm) (bm.repr x * bm.repr x) +
      ∑ p in (bm.repr x).support.sym2 with ¬ p.IsDiag,
        Sym2.mul (p.map (bm.repr x)) • polarSym2 Q (p.map bm) = Q x := by
  rw [← apply_linearCombination]; rw [Basis.linearCombination_repr]

end Finsupp

variable [LinearOrder ι]
variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

/--
Definition of `toBilin` / `toBilin` 的定义

English:
definition toBilin
  signature: (Q : QuadraticMap R M N) (bm : Basis ι R M)
  body: bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

中文:
定义 toBilin
  签名: (Q : 二次映射 R M N) (bm : 基 ι R M)
  定义体: bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

Depends on / 依赖: bm.constr, constr
-/
noncomputable def toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) : LinearMap.BilinMap R M N :=
  bm.constr (S := R) fun i =>
    bm.constr (S := R) fun j =>
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0

/--
theorem `toBilin_apply` / 定理 `toBilin_apply`

English:
theorem toBilin_apply
  given: (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι)
  proof: by
  simp [toBilin]

中文:
定理 toBilin_apply
  条件: (Q : 二次映射 R M N) (bm : 基 ι R M) (i j : ι)
  证明: by
  simp [toBilin]

Depends on / 依赖: toBilin
-/
theorem toBilin_apply (Q : QuadraticMap R M N) (bm : Basis ι R M) (i j : ι) :
    Q.toBilin bm (bm i) (bm j) =
      if i = j then Q (bm i) else if i < j then polar Q (bm i) (bm j) else 0 := by
  simp [toBilin]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `toQuadraticMap_toBilin` / 定理 `toQuadraticMap_toBilin`

English:
theorem toQuadraticMap_toBilin
  given: (Q : QuadraticMap R M N) (bm : Basis ι R M)
  proof: by
  ext x
  rw [← bm.linearCombination_repr x]; rw [LinearMap.BilinMap.toQuadraticMap_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_un

中文:
定理 toQuadraticMap_toBilin
  条件: (Q : 二次映射 R M N) (bm : 基 ι R M)
  证明: by
  ext x
  rw [← bm.linearCombination_repr x]; rw [LinearMap.BilinMap.toQuadraticMap_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_un

Depends on / 依赖: BilinMap, Finset, Finset.diag_union_offDiag, Finset.disjoint_diag_offDiag, Finset.sum_diag, Finset.sum_filter, Finset.sum_ite_of_false, Finset.sum_product, Finset.sum_union, Finsupp, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap, LinearMap.BilinMap.toQuadraticMap_apply, LinearMap.map_smul, LinearMap.map_sum, QuadraticMap, QuadraticMap.map_sum, bm.linearCombination_repr, bm.re
-/
theorem toQuadraticMap_toBilin (Q : QuadraticMap R M N) (bm : Basis ι R M) :
    (Q.toBilin bm).toQuadraticMap = Q := by
  ext x
  rw [← bm.linearCombination_repr x]; rw [LinearMap.BilinMap.toQuadraticMap_apply]; rw [Finsupp.linearCombination_apply]; rw [Finsupp.sum]
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul, toBilin_apply,
    smul_ite, smul_zero, ← Finset.sum_product', ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _), Finset.sum_diag, if_true]
  rw [Finset.sum_ite_of_false]; rw [QuadraticMap.map_sum]; rw [← Finset.sum_filter]
  · simp_rw [← polar_smul_right _ (bm.repr x <| Prod.snd _),
      ← polar_smul_left _ (bm.repr x <| Prod.fst _)]
    simp_rw [QuadraticMap.map_smul, mul_smul, Finset.sum_sym2_filter_not_isDiag]
    rfl
  · intro x hx
    rw [Finset.mem_offDiag] at hx
    simpa using hx.2.2

/--
theorem `_root_.LinearMap.BilinMap.toQuadraticMap_surjective` / 定理 `_root_.LinearMap.BilinMap.toQuadraticMap_surjective`

English:
theorem _root_.LinearMap.BilinMap.toQuadraticMap_surjective
  given: [Module.Free R M]
  proof: by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]

中文:
定理 _root_.线性映射.BilinMap.toQuadraticMap_surjective
  条件: [模.自由 R M]
  证明: by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]

Depends on / 依赖: IsWellOrder, IsWellOrder.linearOrder, LinearOrder, Module, Module.Free.exists_basis, WellOrderingRel, exists_basis, linearOrder, toQuadraticMap_toBilin
-/
theorem _root_.LinearMap.BilinMap.toQuadraticMap_surjective [Module.Free R M] :
    Function.Surjective (LinearMap.BilinMap.toQuadraticMap : LinearMap.BilinMap R M N -> _) := by
  intro Q
  obtain ⟨ι, b⟩ := Module.Free.exists_basis (R := R) (M := M)
  let : LinearOrder ι := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, toQuadraticMap_toBilin _ b⟩

@[simp]
/--
lemma `add_toBilin` / 引理 `add_toBilin`

English:
lemma add_toBilin
  given: (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N)
  proof: by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

中文:
引理 add_toBilin
  条件: (bm : 基 ι R M) (Q₁ Q₂ : 二次映射 R M N)
  证明: by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

Depends on / 依赖: bm.ext, h.ne, h.not_gt, lt_trichotomy, not_gt, polar_add, toBilin_apply
-/
lemma add_toBilin (bm : Basis ι R M) (Q₁ Q₂ : QuadraticMap R M N) :
    (Q₁ + Q₂).toBilin bm = Q₁.toBilin bm + Q₂.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_add]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

variable (S) [CommSemiring S] [Algebra S R]
variable [Module S N] [IsScalarTower S R N]

@[simp]
/--
lemma `smul_toBilin` / 引理 `smul_toBilin`

English:
lemma smul_toBilin
  given: (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N)
  proof: by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

中文:
引理 smul_toBilin
  条件: (bm : 基 ι R M) (s : S) (Q : 二次映射 R M N)
  证明: by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

Depends on / 依赖: bm.ext, h.ne, h.not_gt, lt_trichotomy, not_gt, polar_smul, toBilin_apply
-/
lemma smul_toBilin (bm : Basis ι R M) (s : S) (Q : QuadraticMap R M N) :
    (s • Q).toBilin bm = s • Q.toBilin bm := by
  refine bm.ext fun i => bm.ext fun j => ?_
  obtain h | rfl | h := lt_trichotomy i j
  · simp [h.ne, h, toBilin_apply, polar_smul]
  · simp [toBilin_apply]
  · simp [h.ne', h.not_gt, toBilin_apply]

/-- `QuadraticMap.toBilin` as an S-linear map -/
@[simps]
/--
Definition of `toBilinHom` / `toBilinHom` 的定义

English:
definition toBilinHom
  signature: (bm : Basis ι R M)
  body: Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

中文:
定义 toBilinHom
  签名: (bm : 基 ι R M)
  定义体: Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

Depends on / 依赖: Q.toBilin, toBilin
-/
noncomputable def toBilinHom (bm : Basis ι R M) : QuadraticMap R M N ->ₗ[S] BilinMap R M N where
  toFun Q := Q.toBilin bm
  map_add' := add_toBilin bm
  map_smul' := smul_toBilin S bm

end QuadraticMap
