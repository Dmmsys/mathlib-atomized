/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Analysis.Normed.Group.Hom
public import Mathlib.Topology.Algebra.SeparationQuotient.Hom

/-!
# Lifts of maps to separation quotients of seminormed groups

For any `SeminormedAddCommGroup M`, a `NormedAddCommGroup` instance has been defined in
`Mathlib/Analysis/Normed/Group/Uniform.lean`.

## Main definitions

We use `M` and `N` to denote seminormed groups.
All the following definitions are in the `SeparationQuotient` namespace. Hence we can access
`SeparationQuotient.normedMk` as `normedMk`.

* `normedMk` : the normed group hom from `M` to `SeparationQuotient M`.

* `liftNormedAddGroupHom` : any bounded group hom `f : M → N` such that `∀ x, ‖x‖ = 0 → f x = 0`
  descends to a bounded group hom `SeparationQuotient M → N`.
  Here, `(f : NormedAddGroupHom M N)`, `(hf : ∀ x : M, ‖x‖ = 0 → f x = 0)`
  and `liftNormedAddGroupHom f hf : NormedAddGroupHom (SeparationQuotient M) N` such that
  `liftNormedAddGroupHom f hf (mk x) = f x`.

## Main results

* `norm_normedMk_eq_one` : the operator norm of the projection is `1` if the subspace is not `⊤`.

* `norm_liftNormedAddGroupHom_le` : `‖liftNormedAddGroupHom f hf‖ ≤ ‖f‖`.
-/

@[expose] public section

section

open SeparationQuotient NNReal

variable {M N : Type*} [SeminormedAddCommGroup M] [SeminormedAddCommGroup N]

namespace SeparationQuotient

open NormedAddGroupHom

/-- The morphism from a seminormed group to the quotient by the inseparable setoid. -/
@[simps]
/--
Definition of `normedMk` / `normedMk` 的定义

English:
definition normedMk
  signature: : NormedAddGroupHom M (SeparationQuotient M) where
  body: mkAddMonoidHom
  bound' := ⟨1, by simp⟩

中文:
定义 normedMk
  签名: : 赋范加群态射 M (SeparationQuotient M) where
  定义体: mkAddMonoidHom
  bound' := ⟨1, by simp⟩

Depends on / 依赖: mkAddMonoidHom
-/
noncomputable def normedMk : NormedAddGroupHom M (SeparationQuotient M) where
  __ := mkAddMonoidHom
  bound' := ⟨1, by simp⟩

/--
theorem `norm_normedMk_le` / 定理 `norm_normedMk_le`

English:
theorem norm_normedMk_le
  statement: ‖normedMk (M := M)‖ <= 1
  proof: NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp

中文:
定理 norm_normedMk_le
  结论: ‖normedMk (M := M)‖ <= 1
  证明: NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp
-/
theorem norm_normedMk_le : ‖normedMk (M := M)‖ <= 1 :=
  NormedAddGroupHom.opNorm_le_bound _ zero_le_one fun m => by simp

/--
lemma `apply_eq_apply_of_inseparable` / 引理 `apply_eq_apply_of_inseparable`

English:
lemma apply_eq_apply_of_inseparable
  statement: {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
  proof: fun x y h => eq_of_sub_eq_zero by
    rw [← map_sub]
    rw [Metric.inseparable_iff]; rw [dist_eq_norm] at h
    exact hf (x - y) h

中文:
引理 apply_eq_apply_of_inseparable
  结论: {F : 类型} [函数状 F M N] [加法幺半群态射类 F M N] (f : F)
  证明: fun x y h => eq_of_sub_eq_zero by
    rw [← map_sub]
    rw [Metric.inseparable_iff]; rw [dist_eq_norm] at h
    exact hf (x - y) h

Depends on / 依赖: Metric, Metric.inseparable_iff, dist_eq_norm, eq_of_sub_eq_zero, inseparable_iff, map_sub
-/
lemma apply_eq_apply_of_inseparable {F : Type*} [FunLike F M N] [AddMonoidHomClass F M N] (f : F)
    (hf : forall x, ‖x‖ = 0 -> f x = 0) : forall x y, Inseparable x y -> f x = f y :=
fun x y h => eq_of_sub_eq_zero by
    rw [← map_sub]
    rw [Metric.inseparable_iff]; rw [dist_eq_norm] at h
    exact hf (x - y) h

/-- The lift of a group hom to the separation quotient as a group hom. -/
@[simps]
/--
Definition of `liftNormedAddGroupHom` / `liftNormedAddGroupHom` 的定义

English:
definition liftNormedAddGroupHom
  signature: (f : NormedAddGroupHom M N)
  body: SeparationQuotient.liftContinuousAddMonoidHom f apply_eq_apply_of_inseparable f hf
  map_add' v₁ v₂ := map_add ..
  bound' := by
    refine ⟨‖f‖, fun v => ?_⟩
    obtain ⟨v, rfl⟩ := surjective_mk v
    exact le_opNorm f v

中文:
定义 liftNormedAddGroupHom
  签名: (f : 赋范加群态射 M N)
  定义体: SeparationQuotient.liftContinuousAddMonoidHom f apply_eq_apply_of_inseparable f hf
  map_add' v₁ v₂ := map_add ..
  bound' := by
    refine ⟨‖f‖, fun v => ?_⟩
    obtain ⟨v, rfl⟩ := surjective_mk v
    exact le_opNorm f v

Depends on / 依赖: SeparationQuotient, SeparationQuotient.liftContinuousAddMonoidHom, apply_eq_apply_of_inseparable, liftContinuousAddMonoidHom
-/
noncomputable def liftNormedAddGroupHom (f : NormedAddGroupHom M N)
    (hf : forall x, ‖x‖ = 0 -> f x = 0) : NormedAddGroupHom (SeparationQuotient M) N where
toFun := SeparationQuotient.liftContinuousAddMonoidHom f apply_eq_apply_of_inseparable f hf
  map_add' v₁ v₂ := map_add ..
  bound' := by
    refine ⟨‖f‖, fun v => ?_⟩
    obtain ⟨v, rfl⟩ := surjective_mk v
    exact le_opNorm f v

/--
theorem `norm_liftNormedAddGroupHom_apply_le` / 定理 `norm_liftNormedAddGroupHom_apply_le`

English:
theorem norm_liftNormedAddGroupHom_apply_le
  statement: (f : NormedAddGroupHom M N)
  proof: by
  obtain ⟨x, rfl⟩ := surjective_mk x
  exact le_opNorm f x

中文:
定理 norm_liftNormedAddGroupHom_apply_le
  结论: (f : 赋范加群态射 M N)
  证明: by
  obtain ⟨x, rfl⟩ := surjective_mk x
  exact le_opNorm f x

Depends on / 依赖: le_opNorm, surjective_mk
-/
theorem norm_liftNormedAddGroupHom_apply_le (f : NormedAddGroupHom M N)
    (hf : forall x, ‖x‖ = 0 -> f x = 0) (x : SeparationQuotient M) :
    ‖liftNormedAddGroupHom f hf x‖ <= ‖f‖ * ‖x‖ := by
  obtain ⟨x, rfl⟩ := surjective_mk x
  exact le_opNorm f x

/-- The equivalence between `NormedAddGroupHom M N` vanishing on the inseparable setoid and
`NormedAddGroupHom (SeparationQuotient M) N`. -/
@[simps]
/--
Definition of `liftNormedAddGroupHomEquiv` / `liftNormedAddGroupHomEquiv` 的定义

English:
definition liftNormedAddGroupHomEquiv
  signature: {N : Type*} [SeminormedAddCommGroup N]
  body: liftNormedAddGroupHom f f.prop
  invFun g := ⟨g.comp normedMk, by
    intro x hx
    rw [← norm_mk]; rw [norm_eq_zero] at hx
    simp [hx]⟩
  right_inv _ := by
    ext x
    obtain ⟨x, rfl⟩ := surjective_mk x
    rfl

中文:
定义 liftNormedAddGroupHomEquiv
  签名: {N : 类型} [SeminormedAddComm群 N]
  定义体: liftNormedAddGroupHom f f.prop
  invFun g := ⟨g.comp normedMk, by
    intro x hx
    rw [← norm_mk]; rw [norm_eq_zero] at hx
    simp [hx]⟩
  right_inv _ := by
    ext x
    obtain ⟨x, rfl⟩ := surjective_mk x
    rfl

Depends on / 依赖: f.prop, liftNormedAddGroupHom
-/
noncomputable def liftNormedAddGroupHomEquiv {N : Type*} [SeminormedAddCommGroup N] :
    {f : NormedAddGroupHom M N // forall x, ‖x‖ = 0 -> f x = 0} ≃
    NormedAddGroupHom (SeparationQuotient M) N where
  toFun f := liftNormedAddGroupHom f f.prop
  invFun g := ⟨g.comp normedMk, by
    intro x hx
    rw [← norm_mk]; rw [norm_eq_zero] at hx
    simp [hx]⟩
  right_inv _ := by
    ext x
    obtain ⟨x, rfl⟩ := surjective_mk x
    rfl

/--
theorem `norm_liftNormedAddGroupHom_le` / 定理 `norm_liftNormedAddGroupHom_le`

English:
theorem norm_liftNormedAddGroupHom_le
  statement: {N : Type*} [SeminormedAddCommGroup N]
  proof: NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)

中文:
定理 norm_liftNormedAddGroupHom_le
  结论: {N : 类型} [SeminormedAddComm群 N]
  证明: NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.opNorm_le_bound, norm_liftNormedAddGroupHom_apply_le, norm_nonneg, opNorm_le_bound
-/
theorem norm_liftNormedAddGroupHom_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : forall s, ‖s‖ = 0 -> f s = 0) :
    ‖liftNormedAddGroupHom f hf‖ <= ‖f‖ :=
  NormedAddGroupHom.opNorm_le_bound _ (norm_nonneg f) (norm_liftNormedAddGroupHom_apply_le f hf)

/--
theorem `liftNormedAddGroupHom_norm_le` / 定理 `liftNormedAddGroupHom_norm_le`

English:
theorem liftNormedAddGroupHom_norm_le
  statement: {N : Type*} [SeminormedAddCommGroup N]
  proof: (norm_liftNormedAddGroupHom_le f hf).trans fb

中文:
定理 liftNormedAddGroupHom_norm_le
  结论: {N : 类型} [SeminormedAddComm群 N]
  证明: (norm_liftNormedAddGroupHom_le f hf).trans fb

Depends on / 依赖: norm_liftNormedAddGroupHom_le
-/
theorem liftNormedAddGroupHom_norm_le {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : forall s, ‖s‖ = 0 -> f s = 0) {c : Real>=0} (fb : ‖f‖ <= c) :
    ‖liftNormedAddGroupHom f hf‖ <= c :=
  (norm_liftNormedAddGroupHom_le f hf).trans fb

/--
theorem `liftNormedAddGroupHom_normNoninc` / 定理 `liftNormedAddGroupHom_normNoninc`

English:
theorem liftNormedAddGroupHom_normNoninc
  statement: {N : Type*} [SeminormedAddCommGroup N]
  proof: fun x => by
  have fb' : ‖f‖ <= 1 := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  exact le_trans (norm_liftNormedAddGroupHom_apply_le f hf x)
    (mul_le_of_le_one_left (norm_nonneg x) fb')

中文:
定理 liftNormedAddGroupHom_normNoninc
  结论: {N : 类型} [SeminormedAddComm群 N]
  证明: fun x => by
  have fb' : ‖f‖ <= 1 := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  exact le_trans (norm_liftNormedAddGroupHom_apply_le f hf x)
    (mul_le_of_le_one_left (norm_nonneg x) fb')

Depends on / 依赖: NormNoninc, NormedAddGroupHom, NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp, le_trans, mul_le_of_le_one_left, normNoninc_iff_norm_le_one, norm_liftNormedAddGroupHom_apply_le, norm_nonneg
-/
theorem liftNormedAddGroupHom_normNoninc {N : Type*} [SeminormedAddCommGroup N]
    (f : NormedAddGroupHom M N) (hf : forall s, ‖s‖ = 0 -> f s = 0) (fb : f.NormNoninc) :
    (liftNormedAddGroupHom f hf).NormNoninc := fun x => by
  have fb' : ‖f‖ <= 1 := NormedAddGroupHom.NormNoninc.normNoninc_iff_norm_le_one.mp fb
  exact le_trans (norm_liftNormedAddGroupHom_apply_le f hf x)
    (mul_le_of_le_one_left (norm_nonneg x) fb')

/--
theorem `norm_normedMk_eq_one` / 定理 `norm_normedMk_eq_one`

English:
theorem norm_normedMk_eq_one
  given: [NontrivialTopology M]
  proof: by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simpa only [normedMk_apply, one_mul] using! fun _ => le_rfl
  · intro N _ hle
    obtain ⟨x, _⟩ := exists_norm_ne_zero M
    exact one_le_of_le_mul_right₀ (by positivity) (hle x)

中文:
定理 norm_normedMk_eq_one
  条件: [非平凡拓扑 M]
  证明: by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simpa only [normedMk_apply, one_mul] using! fun _ => le_rfl
  · intro N _ hle
    obtain ⟨x, _⟩ := exists_norm_ne_zero M
    exact one_le_of_le_mul_right₀ (by positivity) (hle x)

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.opNorm_eq_of_bounds, exists_norm_ne_zero, le_rfl, normedMk_apply, one_mul, opNorm_eq_of_bounds, zero_le_one
-/
theorem norm_normedMk_eq_one [NontrivialTopology M] :
    ‖normedMk (M := M)‖ = 1 := by
  apply NormedAddGroupHom.opNorm_eq_of_bounds _ zero_le_one
  · simpa only [normedMk_apply, one_mul] using! fun _ => le_rfl
  · intro N _ hle
    obtain ⟨x, _⟩ := exists_norm_ne_zero M
    exact one_le_of_le_mul_right₀ (by positivity) (hle x)

/--
theorem `normedMk_eq_zero_iff` / 定理 `normedMk_eq_zero_iff`

English:
theorem normedMk_eq_zero_iff
  statement: normedMk (M := M) = 0 ↔ forall (x : M), ‖x‖ = 0
  proof: by
  constructor
  · intro h x
    rw [SeparationQuotient.mk_eq_zero_iff.mp]
    have : normedMk x = 0 := by
      rw [h]
      simp only [NormedAddGroupHom.zero_apply]
    rw [← this]
    simp
  · intro h
    ext x
    simpa [← norm_eq_zero] using h x

中文:
定理 normedMk_eq_zero_iff
  结论: normedMk (M := M) = 0 ↔ 对任意 (x : M), ‖x‖ = 0
  证明: by
  constructor
  · intro h x
    rw [SeparationQuotient.mk_eq_zero_iff.mp]
    have : normedMk x = 0 := by
      rw [h]
      simp only [NormedAddGroupHom.zero_apply]
    rw [← this]
    simp
  · intro h
    ext x
    simpa [← norm_eq_zero] using h x

Depends on / 依赖: NormedAddGroupHom, NormedAddGroupHom.zero_apply, SeparationQuotient, SeparationQuotient.mk_eq_zero_iff.mp, mk_eq_zero_iff, norm_eq_zero, normedMk, zero_apply
-/
theorem normedMk_eq_zero_iff : normedMk (M := M) = 0 ↔ forall (x : M), ‖x‖ = 0 := by
  constructor
  · intro h x
    rw [SeparationQuotient.mk_eq_zero_iff.mp]
    have : normedMk x = 0 := by
      rw [h]
      simp only [NormedAddGroupHom.zero_apply]
    rw [← this]
    simp
  · intro h
    ext x
    simpa [← norm_eq_zero] using h x

end SeparationQuotient

end
