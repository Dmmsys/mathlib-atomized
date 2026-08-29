/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Fabian Glöckle, Kyle Miller
-/
module

public import Mathlib.Algebra.Module.LinearMap.DivisionRing
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.ErdosKaplansky
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.InvariantBasisNumber
public import Mathlib.LinearAlgebra.Projection
public import Mathlib.LinearAlgebra.SesquilinearForm.Basic
public import Mathlib.RingTheory.Finiteness.Projective
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# Dual vector spaces

The dual space of an $R$-module $M$ is the $R$-module of $R$-linear maps $M \to R$.
This file contains basic results on dual vector spaces.

## Main definitions

* Submodules:
  * `Submodule.dualRestrict_comap W'` is the dual annihilator of `W' : Submodule R (Dual R M)`,
    pulled back along `Module.Dual.eval R M`.
  * `Submodule.dualCopairing W` is the canonical pairing between `W.dualAnnihilator` and `M ⧸ W`.
    It is nondegenerate for vector spaces (`subspace.dualCopairing_nondegenerate`).
* Vector spaces:
  * `Subspace.dualLift W` is an arbitrary section (using choice) of `Submodule.dualRestrict W`.

## Main results

* Annihilators:
  * `LinearMap.ker_dual_map_eq_dualAnnihilator_range` says that
    `f.dual_map.ker = f.range.dualAnnihilator`
  * `LinearMap.range_dual_map_eq_dualAnnihilator_ker_of_subtype_range_surjective` says that
    `f.dual_map.range = f.ker.dualAnnihilator`; this is specialized to vector spaces in
    `LinearMap.range_dual_map_eq_dualAnnihilator_ker`.
  * `Submodule.dualQuotEquivDualAnnihilator` is the equivalence
    `Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator`
  * `Submodule.quotDualCoannihilatorToDual` is the nondegenerate pairing
    `M ⧸ W.dualCoannihilator →ₗ[R] Dual R W`.
    It is a perfect pairing when `R` is a field and `W` is finite-dimensional.
* Vector spaces:
  * `Subspace.dualAnnihilator_dualCoannihilator_eq` says that the double dual annihilator,
    pulled back ground `Module.Dual.eval`, is the original submodule.
  * `Subspace.dualAnnihilator_gci` says that `module.dualAnnihilator_gc R M` is an
    antitone Galois coinsertion.
  * `Subspace.quotAnnihilatorEquiv` is the equivalence
    `Dual K V ⧸ W.dualAnnihilator ≃ₗ[K] Dual K W`.
  * `LinearMap.id_nondegenerate` says that `LinearMap.id` is nondegenerate as a bilinear pairing.
  * `LinearMap.eval_nondegenerate` says that `Dual.eval` is nondegenerate.
  * `Subspace.is_compl_dualAnnihilator` says that the dual annihilator carries complementary
    subspaces to complementary subspaces.
* Finite-dimensional vector spaces:
  * `Subspace.orderIsoFiniteCodimDim` is the antitone order isomorphism between
    finite-codimensional subspaces of `V` and finite-dimensional subspaces of `Dual K V`.
  * `Subspace.orderIsoFiniteDimensional` is the antitone order isomorphism between
    subspaces of a finite-dimensional vector space `V` and subspaces of its dual.
  * `Subspace.quotDualEquivAnnihilator W` is the equivalence
    `(Dual K V ⧸ W.dualLift.range) ≃ₗ[K] W.dualAnnihilator`, where `W.dualLift.range` is a copy
    of `Dual K W` inside `Dual K V`.
  * `Subspace.quotEquivAnnihilator W` is the equivalence `(V ⧸ W) ≃ₗ[K] W.dualAnnihilator`
  * `Subspace.dualQuotDistrib W` is an equivalence
    `Dual K (V₁ ⧸ W) ≃ₗ[K] Dual K V₁ ⧸ W.dualLift.range` from an arbitrary choice of
    splitting of `V₁`.
-/

@[expose] public section

open Module Submodule

noncomputable section

namespace Module

variable (R A M : Type*)
variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Prod

variable (M' : Type*) [AddCommMonoid M'] [Module R M']

/-- Taking duals distributes over products. -/
@[simps!]
/--
Definition of `dualProdDualEquivDual` / `dualProdDualEquivDual` 的定义

English:
definition dualProdDualEquivDual
  signature: : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M')
  body: LinearMap.coprodEquiv R

@[simp]

中文:
定义 dualProdDualEquivDual
  签名: : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M')
  定义体: LinearMap.coprodEquiv R

@[simp]

Depends on / 依赖: LinearMap, LinearMap.coprodEquiv, coprodEquiv
-/
def dualProdDualEquivDual : (Module.Dual R M × Module.Dual R M') ≃ₗ[R] Module.Dual R (M × M') :=
  LinearMap.coprodEquiv R

@[simp]
/--
theorem `dualProdDualEquivDual_apply` / 定理 `dualProdDualEquivDual_apply`

English:
theorem dualProdDualEquivDual_apply
  given: (φ : Module.Dual R M) (ψ : Module.Dual R M')
  proof: rfl

中文:
定理 dualProdDualEquivDual_apply
  条件: (φ : Module.Dual R M) (ψ : Module.Dual R M')
  证明: rfl
-/
theorem dualProdDualEquivDual_apply (φ : Module.Dual R M) (ψ : Module.Dual R M') :
    dualProdDualEquivDual R M M' (φ, ψ) = φ.coprod ψ :=
  rfl

end Prod

end Module

section

open Module Module.Dual Submodule LinearMap Cardinal Function

universe uR uM uK uV uι
variable {R : Type uR} {M : Type uM} {K : Type uK} {V : Type uV} {ι : Type uι}

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

section Finite

variable [Finite ι]

-- Not sure whether this is true for free modules over a commutative ring
/--
theorem `Basis.linearEquiv_dual_iff_finiteDimensional` / 定理 `Basis.linearEquiv_dual_iff_finiteDimensional`

English:
theorem Basis.linearEquiv_dual_iff_finiteDimensional
  given: [Field K] [AddCommGroup V] [Module K V]
  proof: by
  refine ⟨fun ⟨e⟩ => ?_, fun h => ⟨(Module.Free.chooseBasis K V).toDualEquiv⟩⟩
  rw [FiniteDimensional]; rw [← Module.rank_lt_aleph0_iff]
  by_contra!
  apply (lift_rank_lt_rank_dual this).ne
  have := e.lift_rank_eq
  rwa [lift_umax, lift_id'.{uV}] at this

中文:
定理 Basis.linearEquiv_dual_iff_finiteDimensional
  条件: [Field K] [AddCommGroup V] [Module K V]
  证明: by
  refine ⟨fun ⟨e⟩ => ?_, fun h => ⟨(Module.Free.chooseBasis K V).toDualEquiv⟩⟩
  rw [FiniteDimensional]; rw [← Module.rank_lt_aleph0_iff]
  by_contra!
  apply (lift_rank_lt_rank_dual this).ne
  have := e.lift_rank_eq
  rwa [lift_umax, lift_id'.{uV}] at this

Depends on / 依赖: FiniteDimensional, Module, Module.Free.chooseBasis, Module.rank_lt_aleph0_iff, chooseBasis, e.lift_rank_eq, lift_id, lift_rank_eq, lift_rank_lt_rank_dual, lift_umax, rank_lt_aleph0_iff, toDualEquiv
-/
theorem Basis.linearEquiv_dual_iff_finiteDimensional [Field K] [AddCommGroup V] [Module K V] :
    Nonempty (V ≃ₗ[K] Dual K V) ↔ FiniteDimensional K V := by
  refine ⟨fun ⟨e⟩ => ?_, fun h => ⟨(Module.Free.chooseBasis K V).toDualEquiv⟩⟩
  rw [FiniteDimensional]; rw [← Module.rank_lt_aleph0_iff]
  by_contra!
  apply (lift_rank_lt_rank_dual this).ne
  have := e.lift_rank_eq
  rwa [lift_umax, lift_id'.{uV}] at this

/--
theorem `Module.Basis.dual_rank_eq` / 定理 `Module.Basis.dual_rank_eq`

English:
theorem Module.Basis.dual_rank_eq
  given: (b : Basis ι R M)
  proof: by
  classical rw [← lift_umax.{uM, uR}, b.toDualEquiv.lift_rank_eq, lift_id'.{uM, uR}]

中文:
定理 Module.Basis.dual_rank_eq
  条件: (b : Basis ι R M)
  证明: by
  classical rw [← lift_umax.{uM, uR}, b.toDualEquiv.lift_rank_eq, lift_id'.{uM, uR}]

Depends on / 依赖: b.toDualEquiv.lift_rank_eq, classical, lift_id, lift_rank_eq, lift_umax, toDualEquiv
-/
theorem Module.Basis.dual_rank_eq (b : Basis ι R M) :
    Module.rank R (Dual R M) = Cardinal.lift.{uR, uM} (Module.rank R M) := by
  classical rw [← lift_umax.{uM, uR}, b.toDualEquiv.lift_rank_eq, lift_id'.{uM, uR}]

end Finite

namespace Module

variable [Module.Finite R M]

/--
Instance `dual_free` / 实例 `dual_free`

English:
instance dual_free
  signature: [Free R M]
  body: Free.of_basis (Free.chooseBasis R M).dualBasis

中文:
实例 dual_free
  签名: [Free R M]
  定义体: Free.of_basis (Free.chooseBasis R M).dualBasis

Depends on / 依赖: ENNReal, ENNReal.coe_mul, ENNReal.coe_ne_top, ENNReal.coe_rpow_of_nonneg, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_le_rpow_iff, ENNReal.rpow_mul, ENNReal.rpow_one, ENNReal.smul_def, Free.chooseBasis, Free.of_basis, NNReal, NNReal.mul_rpow, _eq_lintegral_enorm, chooseBasis, coe_mul, coe_ne_top, coe_rpow_of_nonneg, dualBasis, eLpNorm
-/
instance dual_free [Free R M] : Free R (Dual R M) :=
  Free.of_basis (Free.chooseBasis R M).dualBasis

/--
Instance `dual_projective` / 实例 `dual_projective`

English:
instance dual_projective
  signature: [Projective R M]
  body: have ⟨_, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  .of_split f.dualMap g.dualMap (congr_arg dualMap hfg)

中文:
实例 dual_projective
  签名: [Projective R M]
  定义体: have ⟨_, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  .of_split f.dualMap g.dualMap (congr_arg dualMap hfg)

Depends on / 依赖: ENNReal, ENNReal.coe_ne_top, ENNReal.coe_r, ENNReal.coe_rpow_of_nonneg, ENNReal.mul_rpow_eq_ite, ENNReal.mul_rpow_of_nonneg, ENNReal.rpow_le_rpow_iff, ENNReal.rpow_mul, ENNReal.rpow_one, ENNReal.smul_def, Finite, Finite.exists_comp_eq_id_of_projective, _eq_lintegral_enorm, coe_ne_top, coe_r, coe_rpow_of_nonneg, congr_arg, dualMap, eLpNorm, exists_comp_eq_id_of_projective
-/
instance dual_projective [Projective R M] : Projective R (Dual R M) :=
  have ⟨_, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  .of_split f.dualMap g.dualMap (congr_arg dualMap hfg)

/--
Instance `dual_finite` / 实例 `dual_finite`

English:
instance dual_finite
  signature: [Projective R M]
  body: have ⟨n, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have := Finite.of_basis (Free.chooseBasis R <| Fin n -> R).dualBasis
  .of_surjective _ (surjective_of_comp_eq_id f.dualMap g.dualMap <| congr_arg dualMap hfg)

中文:
实例 dual_finite
  签名: [Projective R M]
  定义体: have ⟨n, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have := Finite.of_basis (Free.chooseBasis R <| Fin n -> R).dualBasis
  .of_surjective _ (surjective_of_comp_eq_id f.dualMap g.dualMap <| congr_arg dualMap hfg)

Depends on / 依赖: ENNReal, ENNReal.rpow_eq_zero_iff, Finite, Finite.exists_comp_eq_id_of_projective, Finite.of_basis, Free.chooseBasis, MeasureTheory, MeasureTheory.lintegral_eq_zero_iff, _eq_lintegral_enorm, and_false, and_true, chooseBasis, congr_arg, dualBasis, dualMap, eLpNorm, exists_comp_eq_id_of_projective, f.dualMap, fun_prop, g.dualMap
-/
instance dual_finite [Projective R M] : Module.Finite R (Dual R M) :=
  have ⟨n, f, g, _, _, hfg⟩ := Finite.exists_comp_eq_id_of_projective R M
  have := Finite.of_basis (Free.chooseBasis R <| Fin n -> R).dualBasis
  .of_surjective _ (surjective_of_comp_eq_id f.dualMap g.dualMap <| congr_arg dualMap hfg)

end Module

end CommSemiring

end

namespace Module

universe uK uV
variable {K : Type uK} {V : Type uV}
variable [CommSemiring K] [AddCommMonoid V] [Module K V] [Projective K V]

open Module Module.Dual Submodule LinearMap Cardinal Module

section

variable (K)

/--
theorem `eval_apply_injective` / 定理 `eval_apply_injective`

English:
theorem eval_apply_injective
  statement: Function.Injective (eval K V)
  proof: have ⟨s, hs⟩ := Module.projective_def'.mp ‹Projective K V›
  .of_comp (f := s.dualMap.dualMap)
    (Finsupp.basisSingleOne.eval_injective.comp <| injective_of_comp_eq_id s _ hs)

中文:
定理 eval_apply_injective
  结论: Function.Injective (eval K V)
  证明: have ⟨s, hs⟩ := Module.projective_def'.mp ‹Projective K V›
  .of_comp (f := s.dualMap.dualMap)
    (Finsupp.basisSingleOne.eval_injective.comp <| injective_of_comp_eq_id s _ hs)

Depends on / 依赖: Finsupp, Finsupp.basisSingleOne.eval_injective.comp, Module, Module.projective_def, Projective, basisSingleOne, dualMap, eval_injective, injective_of_comp_eq_id, of_comp, projective_def, s.dualMap.dualMap
-/
theorem eval_apply_injective : Function.Injective (eval K V) :=
  have ⟨s, hs⟩ := Module.projective_def'.mp ‹Projective K V›
  .of_comp (f := s.dualMap.dualMap)
    (Finsupp.basisSingleOne.eval_injective.comp <| injective_of_comp_eq_id s _ hs)

variable (V)

/--
theorem `eval_ker` / 定理 `eval_ker`

English:
theorem eval_ker
  statement: LinearMap.ker (eval K V) = ⊥
  proof: ker_eq_bot_of_injective (eval_apply_injective K)

中文:
定理 eval_ker
  结论: LinearMap.ker (eval K V) = ⊥
  证明: ker_eq_bot_of_injective (eval_apply_injective K)

Depends on / 依赖: eval_apply_injective, ker_eq_bot_of_injective
-/
theorem eval_ker : LinearMap.ker (eval K V) = ⊥ := ker_eq_bot_of_injective (eval_apply_injective K)

/--
theorem `map_eval_injective` / 定理 `map_eval_injective`

English:
theorem map_eval_injective
  statement: (Submodule.map (eval K V)).Injective
  proof: Submodule.map_injective_of_injective (eval_apply_injective K)

中文:
定理 map_eval_injective
  结论: (Submodule.map (eval K V)).Injective
  证明: Submodule.map_injective_of_injective (eval_apply_injective K)

Depends on / 依赖: Submodule, Submodule.map_injective_of_injective, eval_apply_injective, map_injective_of_injective
-/
theorem map_eval_injective : (Submodule.map (eval K V)).Injective :=
  Submodule.map_injective_of_injective (eval_apply_injective K)

/--
theorem `comap_eval_surjective` / 定理 `comap_eval_surjective`

English:
theorem comap_eval_surjective
  statement: (Submodule.comap (eval K V)).Surjective
  proof: Submodule.comap_surjective_of_injective (eval_apply_injective K)

中文:
定理 comap_eval_surjective
  结论: (Submodule.comap (eval K V)).Surjective
  证明: Submodule.comap_surjective_of_injective (eval_apply_injective K)

Depends on / 依赖: Submodule, Submodule.comap_surjective_of_injective, comap_surjective_of_injective, eval_apply_injective
-/
theorem comap_eval_surjective : (Submodule.comap (eval K V)).Surjective :=
  Submodule.comap_surjective_of_injective (eval_apply_injective K)

end

section

variable (K)

/--
theorem `eval_apply_eq_zero_iff` / 定理 `eval_apply_eq_zero_iff`

English:
theorem eval_apply_eq_zero_iff
  given: (v : V)
  statement: (eval K V) v = 0 ↔ v = 0
  proof: SetLike.ext_iff.mp (eval_ker K V) v

中文:
定理 eval_apply_eq_zero_iff
  条件: (v : V)
  结论: (eval K V) v = 0 ↔ v = 0
  证明: SetLike.ext_iff.mp (eval_ker K V) v

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, eval_ker, ext_iff
-/
theorem eval_apply_eq_zero_iff (v : V) : (eval K V) v = 0 ↔ v = 0 :=
  SetLike.ext_iff.mp (eval_ker K V) v

/--
theorem `Projective.exists_dual_ne_zero` / 定理 `Projective.exists_dual_ne_zero`

English:
theorem Projective.exists_dual_ne_zero
  statement: (R : Type*) [Semiring R] [Module R V]
  proof: have ⟨M, _, _, _, ⟨i, s, his⟩⟩ := Projective.iff_split.mp ‹Projective R V›
  let b := Free.chooseBasis R M
.not.mpr hx have : i x != 0 := i.map_eq_zero_iff (injective_of_comp_eq_id i s his)
have ⟨j, hj⟩ := not_forall.mp fun h => b.repr.map_ne_zero_iff.mpr this Finsupp.ext h
  ⟨b.coord j ∘ₗ i, hj⟩

中文:
定理 Projective.exists_dual_ne_zero
  结论: (R : 类型) [Semiring R] [Module R V]
  证明: have ⟨M, _, _, _, ⟨i, s, his⟩⟩ := Projective.iff_split.mp ‹Projective R V›
  let b := Free.chooseBasis R M
.not.mpr hx have : i x != 0 := i.map_eq_zero_iff (injective_of_comp_eq_id i s his)
have ⟨j, hj⟩ := not_forall.mp fun h => b.repr.map_ne_zero_iff.mpr this Finsupp.ext h
  ⟨b.coord j ∘ₗ i, hj⟩

Depends on / 依赖: Finsupp, Finsupp.ext, Free.chooseBasis, Projective, Projective.iff_split.mp, b.coord, b.repr.map_ne_zero_iff.mpr, chooseBasis, i.map_eq_zero_iff, iff_split, injective_of_comp_eq_id, map_eq_zero_iff, map_ne_zero_iff, not.mpr, not_forall, not_forall.mp
-/
theorem Projective.exists_dual_ne_zero (R : Type*) [Semiring R] [Module R V]
    [Projective R V] {x : V} (hx : x != 0) : exists f : Dual R V, f x != 0 :=
  have ⟨M, _, _, _, ⟨i, s, his⟩⟩ := Projective.iff_split.mp ‹Projective R V›
  let b := Free.chooseBasis R M
.not.mpr hx have : i x != 0 := i.map_eq_zero_iff (injective_of_comp_eq_id i s his)
have ⟨j, hj⟩ := not_forall.mp fun h => b.repr.map_ne_zero_iff.mpr this Finsupp.ext h
  ⟨b.coord j ∘ₗ i, hj⟩

/--
theorem `forall_dual_apply_eq_zero_iff` / 定理 `forall_dual_apply_eq_zero_iff`

English:
theorem forall_dual_apply_eq_zero_iff
  proof: by
  refine ⟨fun h => ?_, fun hv => by simp [hv]⟩
  contrapose! h
  exact Projective.exists_dual_ne_zero R h

中文:
定理 forall_dual_apply_eq_zero_iff
  证明: by
  refine ⟨fun h => ?_, fun hv => by simp [hv]⟩
  contrapose! h
  exact Projective.exists_dual_ne_zero R h

Depends on / 依赖: Projective, Projective.exists_dual_ne_zero, contrapose, exists_dual_ne_zero
-/
theorem forall_dual_apply_eq_zero_iff
    (R : Type*) [Semiring R] [Module R V] [Projective R V] (v : V) :
    (forall φ : Module.Dual R V, φ v = 0) ↔ v = 0 := by
  refine ⟨fun h => ?_, fun hv => by simp [hv]⟩
  contrapose! h
  exact Projective.exists_dual_ne_zero R h

/--
theorem `Projective.exists_dual_eq_one` / 定理 `Projective.exists_dual_eq_one`

English:
theorem Projective.exists_dual_eq_one
  statement: (K : Type*) [Semifield K] [Module K V] [Projective K V]
  proof: have ⟨f, hf⟩ := exists_dual_ne_zero K hx
  ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

@[simp]

中文:
定理 Projective.exists_dual_eq_one
  结论: (K : 类型) [Semifield K] [Module K V] [Projective K V]
  证明: have ⟨f, hf⟩ := exists_dual_ne_zero K hx
  ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

@[simp]

Depends on / 依赖: exists_dual_ne_zero
-/
theorem Projective.exists_dual_eq_one (K : Type*) [Semifield K] [Module K V] [Projective K V]
    {x : V} (hx : x != 0) : exists f : Dual K V, f x = 1 :=
  have ⟨f, hf⟩ := exists_dual_ne_zero K hx
  ⟨(f x)⁻¹ • f, inv_mul_cancel₀ hf⟩

@[simp]
/--
theorem `subsingleton_dual_iff` / 定理 `subsingleton_dual_iff`

English:
theorem subsingleton_dual_iff
  statement: Subsingleton (Dual K V) ↔ Subsingleton V
  proof: ⟨fun _ => ⟨fun _ _ => eval_apply_injective K (Subsingleton.elim ..)⟩, fun _ => inferInstance⟩

@[simp]

中文:
定理 subsingleton_dual_iff
  结论: Subsingleton (Dual K V) ↔ Subsingleton V
  证明: ⟨fun _ => ⟨fun _ _ => eval_apply_injective K (Subsingleton.elim ..)⟩, fun _ => inferInstance⟩

@[simp]

Depends on / 依赖: Subsingleton, Subsingleton.elim, eval_apply_injective
-/
theorem subsingleton_dual_iff : Subsingleton (Dual K V) ↔ Subsingleton V :=
  ⟨fun _ => ⟨fun _ _ => eval_apply_injective K (Subsingleton.elim ..)⟩, fun _ => inferInstance⟩

@[simp]
/--
theorem `nontrivial_dual_iff` / 定理 `nontrivial_dual_iff`

English:
theorem nontrivial_dual_iff
  statement: Nontrivial (Dual K V) ↔ Nontrivial V
  proof: by
  contrapose!; exact subsingleton_dual_iff K

中文:
定理 nontrivial_dual_iff
  结论: Nontrivial (Dual K V) ↔ Nontrivial V
  证明: by
  contrapose!; exact subsingleton_dual_iff K

Depends on / 依赖: contrapose, subsingleton_dual_iff
-/
theorem nontrivial_dual_iff : Nontrivial (Dual K V) ↔ Nontrivial V := by
  contrapose!; exact subsingleton_dual_iff K

/--
Instance `instNontrivialDual` / 实例 `instNontrivialDual`

English:
instance instNontrivialDual
  signature: [Nontrivial V]
  body: (nontrivial_dual_iff K).mpr inferInstance

omit [Projective K V] in

中文:
实例 instNontrivialDual
  签名: [Nontrivial V]
  定义体: (nontrivial_dual_iff K).mpr inferInstance

omit [Projective K V] in

Depends on / 依赖: nontrivial_dual_iff
-/
instance instNontrivialDual [Nontrivial V] : Nontrivial (Dual K V) :=
  (nontrivial_dual_iff K).mpr inferInstance

omit [Projective K V] in
/--
theorem `finite_dual_iff` / 定理 `finite_dual_iff`

English:
theorem finite_dual_iff
  given: [Free K V]
  statement: Module.Finite K (Dual K V) ↔ Module.Finite K V
  proof: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  have ⟨⟨ι, b⟩⟩ := Free.exists_basis (R := K) (M := V)
  cases finite_or_infinite ι
  · exact .of_basis b
  nontriviality K
  have ⟨n, hn⟩ := Module.Finite.exists_nat_not_surjective K (Dual K V)
  let g := Finsupp.llift K K K ι ≪≫ₗ b.repr.dualMap
  e

中文:
定理 finite_dual_iff
  条件: [Free K V]
  结论: Module.Finite K (Dual K V) ↔ Module.Finite K V
  证明: by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  have ⟨⟨ι, b⟩⟩ := Free.exists_basis (R := K) (M := V)
  cases finite_or_infinite ι
  · exact .of_basis b
  nontriviality K
  have ⟨n, hn⟩ := Module.Finite.exists_nat_not_surjective K (Dual K V)
  let g := Finsupp.llift K K K ι ≪≫ₗ b.repr.dualMap
  e

Depends on / 依赖: Embedding, Fin.valEmbedding.trans, Finite, Finsupp, Finsupp.llift, Free.exists_basis, Function, Function.Embedding.injective, Infinite, Infinite.natEmbedding, LinearMap, LinearMap.funLeft, Module, Module.Finite.exists_nat_not_surjective, b.repr.dualMap, dualMap, exists_basis, exists_nat_not_surjective, finite_or_infinite, funLeft
-/
theorem finite_dual_iff [Free K V] : Module.Finite K (Dual K V) ↔ Module.Finite K V := by
  refine ⟨fun h => ?_, fun _ => inferInstance⟩
  have ⟨⟨ι, b⟩⟩ := Free.exists_basis (R := K) (M := V)
  cases finite_or_infinite ι
  · exact .of_basis b
  nontriviality K
  have ⟨n, hn⟩ := Module.Finite.exists_nat_not_surjective K (Dual K V)
  let g := Finsupp.llift K K K ι ≪≫ₗ b.repr.dualMap
  exact hn (LinearMap.funLeft K K (Fin.valEmbedding.trans (Infinite.natEmbedding ι)) ∘ₗ _)
.elim ((Function.Embedding.injective _).surjective_comp_right.comp g.symm.surjective)

end

omit [Projective K V]

/--
theorem `dual_rank_eq` / 定理 `dual_rank_eq`

English:
theorem dual_rank_eq
  given: [Free K V] [Module.Finite K V]
  proof: (Free.chooseBasis K V).dual_rank_eq

中文:
定理 dual_rank_eq
  条件: [Free K V] [Module.Finite K V]
  证明: (Free.chooseBasis K V).dual_rank_eq

Depends on / 依赖: Free.chooseBasis, chooseBasis, dual_rank_eq
-/
theorem dual_rank_eq [Free K V] [Module.Finite K V] :
    Module.rank K (Dual K V) = Cardinal.lift.{uK, uV} (Module.rank K V) :=
  (Free.chooseBasis K V).dual_rank_eq

section IsReflexive

open Function

variable (R M N : Type*)
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- See also `Module.instFiniteDimensionalOfIsReflexive` for the converse over a field. -/
instance (priority := 900) IsReflexive.of_finite_of_free [Module.Finite R M] [Free R M] :
    IsReflexive R M where
  bijective_dual_eval'.left := (Free.chooseBasis R M).eval_injective
  bijective_dual_eval'.right := range_eq_top.mp (Free.chooseBasis R M).eval_range

variable [IsReflexive R M]

instance (priority := 900) [Module.Finite R N] [Projective R N] : IsReflexive R N :=
  have ⟨_, f, hf⟩ := Finite.exists_fin' R N
  have ⟨g, H⟩ := projective_lifting_property f .id hf
  .of_split g f H

/--
Instance `_root_.Prod.instModuleIsReflexive` / 实例 `_root_.Prod.instModuleIsReflexive`

English:
instance _root_.Prod.instModuleIsReflexive
  signature: [IsReflexive R N]
  body: by
    let e : Dual R (Dual R (M × N)) ≃ₗ[R] Dual R (Dual R M) × Dual R (Dual R N) :=
      (dualProdDualEquivDual R M N).dualMap.trans
        (dualProdDualEquivDual R (Dual R M) (Dual R N)).symm
    have : Dual.eval R (M × N) = e.symm.comp ((Dual.eval R M).prodMap (Dual.eval R N)) := by
      ext 

中文:
实例 _root_.Prod.instModuleIsReflexive
  签名: [IsReflexive R N]
  定义体: by
    let e : Dual R (Dual R (M × N)) ≃ₗ[R] Dual R (Dual R M) × Dual R (Dual R N) :=
      (dualProdDualEquivDual R M N).dualMap.trans
        (dualProdDualEquivDual R (Dual R M) (Dual R N)).symm
    have : Dual.eval R (M × N) = e.symm.comp ((Dual.eval R M).prodMap (Dual.eval R N)) := by
      ext 

Depends on / 依赖: Dual.eval, EquivLike, EquivLike.comp_bijective, LinearEquiv, LinearEquiv.coe_coe, bijective_dual_eval, coe_coe, coe_comp, comp_bijective, dualMap, dualMap.trans, dualProdDualEquivDual, e.symm.comp, prodMap
-/
instance _root_.Prod.instModuleIsReflexive [IsReflexive R N] :
    IsReflexive R (M × N) where
  bijective_dual_eval' := by
    let e : Dual R (Dual R (M × N)) ≃ₗ[R] Dual R (Dual R M) × Dual R (Dual R N) :=
      (dualProdDualEquivDual R M N).dualMap.trans
        (dualProdDualEquivDual R (Dual R M) (Dual R N)).symm
    have : Dual.eval R (M × N) = e.symm.comp ((Dual.eval R M).prodMap (Dual.eval R N)) := by
      ext m f <;> simp [e]
    simp only [this,
      coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective]
    exact (bijective_dual_eval R M).prodMap (bijective_dual_eval R N)

/--
Instance `_root_.ULift.instModuleIsReflexive.` / 实例 `_root_.ULift.instModuleIsReflexive.`

English:
instance _root_.ULift.instModuleIsReflexive.{w}
  signature: : IsReflexive R (ULift.{w} M)
  body: equiv ULift.moduleEquiv.symm

中文:
实例 _root_.ULift.instModuleIsReflexive.{w}
  签名: : IsReflexive R (ULift.{w} M)
  定义体: equiv ULift.moduleEquiv.symm

Depends on / 依赖: ULift.moduleEquiv.symm, moduleEquiv
-/
instance _root_.ULift.instModuleIsReflexive.{w} : IsReflexive R (ULift.{w} M) :=
  equiv ULift.moduleEquiv.symm

-- Very low priority because instance resolution will often end up using the instances above
-- to prove `IsReflexive`, which require proving `Finite` again.
instance (priority := 90) instFiniteDimensionalOfIsReflexive (K V : Type*)
    [Field K] [AddCommGroup V] [Module K V] [IsReflexive K V] :
    FiniteDimensional K V := by
  rw [FiniteDimensional]; rw [← rank_lt_aleph0_iff]
  by_contra! contra
  suffices lift (Module.rank K V) < Module.rank K (Dual K (Dual K V)) by
    have heq := lift_rank_eq_of_equiv_equiv (R := K) (R' := K) (M := V) (M' := Dual K (Dual K V))
      (ZeroHom.id K) (evalEquiv K V) bijective_id (fun r v => (evalEquiv K V).map_smul _ _)
    rw [← lift_umax]; rw [heq]; rw [lift_id'] at this
    exact lt_irrefl _ this
  have h₁ : lift (Module.rank K V) < Module.rank K (Dual K V) := lift_rank_lt_rank_dual contra
  have h₂ : Module.rank K (Dual K V) < Module.rank K (Dual K (Dual K V)) := by
convert! lift_rank_lt_rank_dual le_trans (by simpa) h₁.le
    rw [lift_id']
  exact lt_trans h₁ h₂

end IsReflexive

end Module

namespace Submodule

open Module

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {p : Submodule R M}

@[simp]
/--
theorem `dualCoannihilator_top` / 定理 `dualCoannihilator_top`

English:
theorem dualCoannihilator_top
  given: [Projective R M]
  proof: by
  rw [dualCoannihilator]; rw [dualAnnihilator_top]; rw [comap_bot]; rw [Module.eval_ker]

中文:
定理 dualCoannihilator_top
  条件: [Projective R M]
  证明: by
  rw [dualCoannihilator]; rw [dualAnnihilator_top]; rw [comap_bot]; rw [Module.eval_ker]

Depends on / 依赖: Module, Module.eval_ker, comap_bot, dualAnnihilator_top, dualCoannihilator, eval_ker
-/
theorem dualCoannihilator_top [Projective R M] :
    (⊤ : Submodule R (Module.Dual R M)).dualCoannihilator = ⊥ := by
  rw [dualCoannihilator]; rw [dualAnnihilator_top]; rw [comap_bot]; rw [Module.eval_ker]

/--
theorem `exists_dual_map_eq_bot_of_notMem` / 定理 `exists_dual_map_eq_bot_of_notMem`

English:
theorem exists_dual_map_eq_bot_of_notMem
  proof: by
  suffices exists f : Dual R (M ⧸ p), f (p.mkQ x) != 0 by
    obtain ⟨f, hf⟩ := this; exact ⟨f.comp p.mkQ, hf, by simp [Submodule.map_comp]⟩
  rw [← Submodule.Quotient.mk_eq_zero]; rw [← Submodule.mkQ_apply] at hx
  exact Projective.exists_dual_ne_zero R hx

中文:
定理 exists_dual_map_eq_bot_of_notMem
  证明: by
  suffices exists f : Dual R (M ⧸ p), f (p.mkQ x) != 0 by
    obtain ⟨f, hf⟩ := this; exact ⟨f.comp p.mkQ, hf, by simp [Submodule.map_comp]⟩
  rw [← Submodule.Quotient.mk_eq_zero]; rw [← Submodule.mkQ_apply] at hx
  exact Projective.exists_dual_ne_zero R hx

Depends on / 依赖: Projective, Projective.exists_dual_ne_zero, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.map_comp, Submodule.mkQ_apply, exists_dual_ne_zero, f.comp, map_comp, mkQ_apply, mk_eq_zero, p.mkQ
-/
theorem exists_dual_map_eq_bot_of_notMem
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    {x : M} (hx : x ∉ p) (hp' : Projective R (M ⧸ p)) :
    exists f : Dual R M, f x != 0 ∧ p.map f = ⊥ := by
  suffices exists f : Dual R (M ⧸ p), f (p.mkQ x) != 0 by
    obtain ⟨f, hf⟩ := this; exact ⟨f.comp p.mkQ, hf, by simp [Submodule.map_comp]⟩
  rw [← Submodule.Quotient.mk_eq_zero]; rw [← Submodule.mkQ_apply] at hx
  exact Projective.exists_dual_ne_zero R hx

/--
theorem `exists_dual_map_eq_bot_of_lt_top` / 定理 `exists_dual_map_eq_bot_of_lt_top`

English:
theorem exists_dual_map_eq_bot_of_lt_top
  proof: by
  obtain ⟨x, hx⟩ : exists x : M, x ∉ p := by rw [lt_top_iff_ne_top] at hp; contrapose! hp; ext; simp [hp]
  obtain ⟨f, hf, hf'⟩ := p.exists_dual_map_eq_bot_of_notMem hx hp'
  exact ⟨f, by aesop, hf'⟩

中文:
定理 exists_dual_map_eq_bot_of_lt_top
  证明: by
  obtain ⟨x, hx⟩ : exists x : M, x ∉ p := by rw [lt_top_iff_ne_top] at hp; contrapose! hp; ext; simp [hp]
  obtain ⟨f, hf, hf'⟩ := p.exists_dual_map_eq_bot_of_notMem hx hp'
  exact ⟨f, by aesop, hf'⟩

Depends on / 依赖: contrapose, exists_dual_map_eq_bot_of_notMem, lt_top_iff_ne_top, p.exists_dual_map_eq_bot_of_notMem
-/
theorem exists_dual_map_eq_bot_of_lt_top
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {p : Submodule R M}
    (hp : p < ⊤) (hp' : Projective R (M ⧸ p)) :
    exists f : Dual R M, f != 0 ∧ p.map f = ⊥ := by
  obtain ⟨x, hx⟩ : exists x : M, x ∉ p := by rw [lt_top_iff_ne_top] at hp; contrapose! hp; ext; simp [hp]
  obtain ⟨f, hf, hf'⟩ := p.exists_dual_map_eq_bot_of_notMem hx hp'
  exact ⟨f, by aesop, hf'⟩

/--
theorem `span_eq_top_of_ne_zero` / 定理 `span_eq_top_of_ne_zero`

English:
theorem span_eq_top_of_ne_zero
  statement: [IsReflexive R M]
  proof: by
  by_contra! hn
  obtain ⟨φ, φne, hφ⟩ := exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance
  let φs := (evalEquiv R M).symm φ
  have this f (hf : f in s) : f φs = 0 := by
    rw [← mem_bot R]; rw [← hφ]; rw [mem_map]
    exact ⟨f, subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩


中文:
定理 span_eq_top_of_ne_zero
  结论: [IsReflexive R M]
  证明: by
  by_contra! hn
  obtain ⟨φ, φne, hφ⟩ := exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance
  let φs := (evalEquiv R M).symm φ
  have this f (hf : f in s) : f φs = 0 := by
    rw [← mem_bot R]; rw [← hφ]; rw [mem_map]
    exact ⟨f, subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩


Depends on / 依赖: apply_evalEquiv_symm_apply, evalEquiv, exists_dual_map_eq_bot_of_lt_top, hn.lt_top, lt_top, mem_bot, mem_map, subset_span
-/
theorem span_eq_top_of_ne_zero [IsReflexive R M]
    {s : Set (M ->ₗ[R] R)} [Projective R ((M ->ₗ[R] R) ⧸ (span R s))]
    (h : forall z != 0, exists f in s, f z != 0) : span R s = ⊤ := by
  by_contra! hn
  obtain ⟨φ, φne, hφ⟩ := exists_dual_map_eq_bot_of_lt_top hn.lt_top inferInstance
  let φs := (evalEquiv R M).symm φ
  have this f (hf : f in s) : f φs = 0 := by
    rw [← mem_bot R]; rw [← hφ]; rw [mem_map]
    exact ⟨f, subset_span hf, (apply_evalEquiv_symm_apply R M f φ).symm⟩
  obtain ⟨x, xs, hx⟩ := h φs (by simp [φne, φs])
exact hx this x xs

variable {ι 𝕜 E : Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E]

open LinearMap Set FiniteDimensional

/--
theorem `_root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker` / 定理 `_root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker`

English:
theorem _root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker
  statement: [FiniteDimensional 𝕜 E]
  proof: by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_notMem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
refine h (Submodule.mem_iInf _).2 fun i => (mem_bot 𝕜).1 ?_
    rw [← hφ]; rw [Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i,

中文:
定理 _root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker
  结论: [FiniteDimensional 𝕜 E]
  证明: by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_notMem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
refine h (Submodule.mem_iInf _).2 fun i => (mem_bot 𝕜).1 ?_
    rw [← hφ]; rw [Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i,

Depends on / 依赖: Eventually, Eventually.of_forall, Module, Module.evalEquiv, Submodule, Submodule.mem_iInf, Submodule.mem_map, Submodule.subset_span, _le_nnreal_smul_eLpNorm, _of_ae_le_mul, apply_evalEquiv_symm_apply, eLpNorm, evalEquiv, exists_dual_map_eq_bot_of_notMem, mem_bot, mem_iInf, mem_map, nnnorm_smul_le, of_forall, subset_span
-/
theorem _root_.FiniteDimensional.mem_span_of_iInf_ker_le_ker [FiniteDimensional 𝕜 E]
    {L : ι -> E ->ₗ[𝕜] 𝕜} {K : E ->ₗ[𝕜] 𝕜}
    (h : ⨅ i, LinearMap.ker (L i) <= ker K) : K in span 𝕜 (range L) := by
  by_contra hK
  rcases exists_dual_map_eq_bot_of_notMem hK inferInstance with ⟨φ, φne, hφ⟩
  let φs := (Module.evalEquiv 𝕜 E).symm φ
  have : K φs = 0 := by
refine h (Submodule.mem_iInf _).2 fun i => (mem_bot 𝕜).1 ?_
    rw [← hφ]; rw [Submodule.mem_map]
    exact ⟨L i, Submodule.subset_span ⟨i, rfl⟩, (apply_evalEquiv_symm_apply 𝕜 E _ φ).symm⟩
  simp only [apply_evalEquiv_symm_apply, φs, φne] at this

/--
theorem `_root_.mem_span_of_iInf_ker_le_ker` / 定理 `_root_.mem_span_of_iInf_ker_le_ker`

English:
theorem _root_.mem_span_of_iInf_ker_le_ker
  statement: [Finite ι] {L : ι -> E ->ₗ[𝕜] 𝕜} {K : E ->ₗ[𝕜] 𝕜}
  proof: by
  have _ := Fintype.ofFinite ι
  let φ : E ->ₗ[𝕜] ι -> 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) ->ₗ[𝕜] ι -> 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))

中文:
定理 _root_.mem_span_of_iInf_ker_le_ker
  结论: [Finite ι] {L : ι -> E ->ₗ[𝕜] 𝕜} {K : E ->ₗ[𝕜] 𝕜}
  证明: by
  have _ := Fintype.ofFinite ι
  let φ : E ->ₗ[𝕜] ι -> 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) ->ₗ[𝕜] ι -> 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))

Depends on / 依赖: FiniteDimensional, Fintype, Fintype.ofFinite, LinearMap, LinearMap.pi, iInf_le, ker_eq_bot, ker_liftQ_eq_bot, ker_pi, ofFinite, of_injective, p.liftQ, p_eq, p_eq.le, pi_liftQ_eq_liftQ_pi, simp_rw, zetaDelta
-/
theorem _root_.mem_span_of_iInf_ker_le_ker [Finite ι] {L : ι -> E ->ₗ[𝕜] 𝕜} {K : E ->ₗ[𝕜] 𝕜}
    (h : ⨅ i, ker (L i) <= ker K) : K in span 𝕜 (range L) := by
  have _ := Fintype.ofFinite ι
  let φ : E ->ₗ[𝕜] ι -> 𝕜 := LinearMap.pi L
  let p := ⨅ i, ker (L i)
  have p_eq : p = ker φ := (ker_pi L).symm
  let ψ : (E ⧸ p) ->ₗ[𝕜] ι -> 𝕜 := p.liftQ φ p_eq.le
  have _ : FiniteDimensional 𝕜 (E ⧸ p) := of_injective ψ (ker_eq_bot.1 (ker_liftQ_eq_bot' p φ p_eq))
  let L' i : (E ⧸ p) ->ₗ[𝕜] 𝕜 := p.liftQ (L i) (iInf_le _ i)
  let K' : (E ⧸ p) ->ₗ[𝕜] 𝕜 := p.liftQ K h
  have : ⨅ i, ker (L' i) <= ker K' := by
    simp_rw +zetaDelta [← ker_pi, pi_liftQ_eq_liftQ_pi, ker_liftQ_eq_bot' p φ p_eq]
    exact bot_le
  obtain ⟨c, hK'⟩ :=
    (mem_span_range_iff_exists_fun 𝕜).1 (FiniteDimensional.mem_span_of_iInf_ker_le_ker this)
  refine (mem_span_range_iff_exists_fun 𝕜).2 ⟨c, ?_⟩
  conv_lhs => enter [2]; intro i; rw [← p.liftQ_mkQ (L i) (iInf_le _ i)]
  rw [← p.liftQ_mkQ K h]
  ext x
  convert! LinearMap.congr_fun hK' (p.mkQ x)
  simp only [L', LinearMap.coe_sum, Finset.sum_apply, smul_apply, coe_comp, Function.comp_apply,
    smul_eq_mul]

end Submodule

namespace Subspace

open Submodule LinearMap

-- We work in vector spaces because `exists_isCompl` only hold for vector spaces
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[simp]
/--
theorem `dualAnnihilator_dualCoannihilator_eq` / 定理 `dualAnnihilator_dualCoannihilator_eq`

English:
theorem dualAnnihilator_dualCoannihilator_eq
  given: {W : Subspace K V}
  proof: by
  refine le_antisymm (fun v => Function.mtr ?_) (le_dualAnnihilator_dualCoannihilator _)
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  rw [← Quotient.mk_eq_zero W]; rw [← Module.forall_dual_apply_eq_zero_iff K]
  push Not
  refine fun ⟨φ, hφ⟩ => ⟨φ.comp W.mkQ, fun w hw => ?_, hφ⟩
  r

中文:
定理 dualAnnihilator_dualCoannihilator_eq
  条件: {W : Subspace K V}
  证明: by
  refine le_antisymm (fun v => Function.mtr ?_) (le_dualAnnihilator_dualCoannihilator _)
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  rw [← Quotient.mk_eq_zero W]; rw [← Module.forall_dual_apply_eq_zero_iff K]
  push Not
  refine fun ⟨φ, hφ⟩ => ⟨φ.comp W.mkQ, fun w hw => ?_, hφ⟩
  r

Depends on / 依赖: Function, Function.mtr, Module, Module.forall_dual_apply_eq_zero_iff, Quotient, Quotient.mk_eq_zero, W.mkQ, comp_apply, forall_dual_apply_eq_zero_iff, le_antisymm, le_dualAnnihilator_dualCoannihilator, map_zero, mem_dualAnnihilator, mem_dualCoannihilator, mkQ_apply, mk_eq_zero
-/
theorem dualAnnihilator_dualCoannihilator_eq {W : Subspace K V} :
    W.dualAnnihilator.dualCoannihilator = W := by
  refine le_antisymm (fun v => Function.mtr ?_) (le_dualAnnihilator_dualCoannihilator _)
  simp only [mem_dualAnnihilator, mem_dualCoannihilator]
  rw [← Quotient.mk_eq_zero W]; rw [← Module.forall_dual_apply_eq_zero_iff K]
  push Not
  refine fun ⟨φ, hφ⟩ => ⟨φ.comp W.mkQ, fun w hw => ?_, hφ⟩
  rw [comp_apply]; rw [mkQ_apply]; rw [(Quotient.mk_eq_zero W).mpr hw]; rw [φ.map_zero]

-- exact elaborates slowly
/--
theorem `forall_mem_dualAnnihilator_apply_eq_zero_iff` / 定理 `forall_mem_dualAnnihilator_apply_eq_zero_iff`

English:
theorem forall_mem_dualAnnihilator_apply_eq_zero_iff
  given: (W : Subspace K V) (v : V)
  proof: by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v]; rw [mem_dualCoannihilator]

中文:
定理 forall_mem_dualAnnihilator_apply_eq_zero_iff
  条件: (W : Subspace K V) (v : V)
  证明: by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v]; rw [mem_dualCoannihilator]

Depends on / 依赖: SetLike, SetLike.ext_iff.mp, dualAnnihilator_dualCoannihilator_eq, ext_iff, mem_dualCoannihilator
-/
theorem forall_mem_dualAnnihilator_apply_eq_zero_iff (W : Subspace K V) (v : V) :
    (forall φ : Module.Dual K V, φ in W.dualAnnihilator -> φ v = 0) ↔ v in W := by
  rw [← SetLike.ext_iff.mp dualAnnihilator_dualCoannihilator_eq v]; rw [mem_dualCoannihilator]

/--
theorem `comap_dualAnnihilator_dualAnnihilator` / 定理 `comap_dualAnnihilator_dualAnnihilator`

English:
theorem comap_dualAnnihilator_dualAnnihilator
  given: (W : Subspace K V)
  proof: by
  ext; rw [Iff.comm, ← forall_mem_dualAnnihilator_apply_eq_zero_iff]; simp

中文:
定理 comap_dualAnnihilator_dualAnnihilator
  条件: (W : Subspace K V)
  证明: by
  ext; rw [Iff.comm, ← forall_mem_dualAnnihilator_apply_eq_zero_iff]; simp

Depends on / 依赖: Iff.comm, forall_mem_dualAnnihilator_apply_eq_zero_iff
-/
theorem comap_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator.comap (Module.Dual.eval K V) = W := by
  ext; rw [Iff.comm, ← forall_mem_dualAnnihilator_apply_eq_zero_iff]; simp

/--
theorem `map_le_dualAnnihilator_dualAnnihilator` / 定理 `map_le_dualAnnihilator_dualAnnihilator`

English:
theorem map_le_dualAnnihilator_dualAnnihilator
  given: (W : Subspace K V)
  proof: map_le_iff_le_comap.mpr (comap_dualAnnihilator_dualAnnihilator W).ge

中文:
定理 map_le_dualAnnihilator_dualAnnihilator
  条件: (W : Subspace K V)
  证明: map_le_iff_le_comap.mpr (comap_dualAnnihilator_dualAnnihilator W).ge

Depends on / 依赖: comap_dualAnnihilator_dualAnnihilator, map_le_iff_le_comap, map_le_iff_le_comap.mpr
-/
theorem map_le_dualAnnihilator_dualAnnihilator (W : Subspace K V) :
    W.map (Module.Dual.eval K V) <= W.dualAnnihilator.dualAnnihilator :=
  map_le_iff_le_comap.mpr (comap_dualAnnihilator_dualAnnihilator W).ge

/--
Definition of `dualAnnihilatorGci` / `dualAnnihilatorGci` 的定义

English:
definition dualAnnihilatorGci
  signature: (K V : Type*) [Field K] [AddCommGroup V] [Module K V]
  body: dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl

中文:
定义 dualAnnihilatorGci
  签名: (K V : 类型) [Field K] [AddCommGroup V] [Module K V]
  定义体: dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl

Depends on / 依赖: Eventually, Eventually.of_forall, _le_nnreal_smul_eLpNorm, _of_ae_le_mul, dualCoannihilator, eLpNorm, enorm_smul, le_of_eq, of_forall
-/
def dualAnnihilatorGci (K V : Type*) [Field K] [AddCommGroup V] [Module K V] :
    GaloisCoinsertion
      (OrderDual.toDual ∘ (dualAnnihilator : Subspace K V -> Subspace K (Module.Dual K V)))
      (dualCoannihilator ∘ OrderDual.ofDual) where
  choice W _ := dualCoannihilator W
  gc := dualAnnihilator_gc K V
  u_l_le _ := dualAnnihilator_dualCoannihilator_eq.le
  choice_eq _ _ := rfl

/--
theorem `dualAnnihilator_le_dualAnnihilator_iff` / 定理 `dualAnnihilator_le_dualAnnihilator_iff`

English:
theorem dualAnnihilator_le_dualAnnihilator_iff
  given: {W W' : Subspace K V}
  proof: (dualAnnihilatorGci K V).l_le_l_iff

中文:
定理 dualAnnihilator_le_dualAnnihilator_iff
  条件: {W W' : Subspace K V}
  证明: (dualAnnihilatorGci K V).l_le_l_iff

Depends on / 依赖: dualAnnihilatorGci, l_le_l_iff
-/
theorem dualAnnihilator_le_dualAnnihilator_iff {W W' : Subspace K V} :
    W.dualAnnihilator <= W'.dualAnnihilator ↔ W' <= W :=
  (dualAnnihilatorGci K V).l_le_l_iff

/--
theorem `dualAnnihilator_inj` / 定理 `dualAnnihilator_inj`

English:
theorem dualAnnihilator_inj
  given: {W W' : Subspace K V}
  proof: ⟨fun h => (dualAnnihilatorGci K V).l_injective h, congr_arg _⟩

中文:
定理 dualAnnihilator_inj
  条件: {W W' : Subspace K V}
  证明: ⟨fun h => (dualAnnihilatorGci K V).l_injective h, congr_arg _⟩

Depends on / 依赖: congr_arg, dualAnnihilatorGci, l_injective
-/
theorem dualAnnihilator_inj {W W' : Subspace K V} :
    W.dualAnnihilator = W'.dualAnnihilator ↔ W = W' :=
  ⟨fun h => (dualAnnihilatorGci K V).l_injective h, congr_arg _⟩

/--
Definition of `dualLift` / `dualLift` 的定义

English:
definition dualLift
  signature: (W : Subspace K V)
  body: W.subtype.leftInverse.dualMap

中文:
定义 dualLift
  签名: (W : Subspace K V)
  定义体: W.subtype.leftInverse.dualMap

Depends on / 依赖: W.subtype.leftInverse.dualMap, dualMap, leftInverse, subtype
-/
noncomputable def dualLift (W : Subspace K V) : Module.Dual K W ->ₗ[K] Module.Dual K V :=
  W.subtype.leftInverse.dualMap

variable {W : Subspace K V}

@[simp]
/--
theorem `dualLift_of_subtype` / 定理 `dualLift_of_subtype`

English:
theorem dualLift_of_subtype
  given: {φ : Module.Dual K W} (w : W)
  statement: W.dualLift φ (w : V) = φ w
  proof: congr_arg φ LinearMap.leftInverse_apply_of_inj W.ker_subtype _

中文:
定理 dualLift_of_subtype
  条件: {φ : Module.Dual K W} (w : W)
  结论: W.dualLift φ (w : V) = φ w
  证明: congr_arg φ LinearMap.leftInverse_apply_of_inj W.ker_subtype _

Depends on / 依赖: LinearMap, LinearMap.leftInverse_apply_of_inj, W.ker_subtype, congr_arg, ker_subtype, leftInverse_apply_of_inj
-/
theorem dualLift_of_subtype {φ : Module.Dual K W} (w : W) : W.dualLift φ (w : V) = φ w :=
congr_arg φ LinearMap.leftInverse_apply_of_inj W.ker_subtype _

/--
theorem `dualLift_of_mem` / 定理 `dualLift_of_mem`

English:
theorem dualLift_of_mem
  given: {φ : Module.Dual K W} {w : V} (hw : w in W)
  statement: W.dualLift φ w = φ ⟨w, hw⟩
  proof: dualLift_of_subtype ⟨w, hw⟩

@[simp]

中文:
定理 dualLift_of_mem
  条件: {φ : Module.Dual K W} {w : V} (hw : w in W)
  结论: W.dualLift φ w = φ ⟨w, hw⟩
  证明: dualLift_of_subtype ⟨w, hw⟩

@[simp]

Depends on / 依赖: ENNReal, ENNReal.div_eq_inv_mul, ENNReal.mul_le_of_le_div, _const_smul_le, _eq_lintegral_enorm, div_eq_inv_mul, dualLift_of_subtype, eLpNorm, enorm_inv, eq_or_ne, hq_pos, le_antisymm, mul_le_of_le_div
-/
theorem dualLift_of_mem {φ : Module.Dual K W} {w : V} (hw : w in W) : W.dualLift φ w = φ ⟨w, hw⟩ :=
  dualLift_of_subtype ⟨w, hw⟩

@[simp]
/--
theorem `dualRestrict_comp_dualLift` / 定理 `dualRestrict_comp_dualLift`

English:
theorem dualRestrict_comp_dualLift
  given: (W : Subspace K V)
  statement: W.dualRestrict.comp W.dualLift = 1
  proof: by
  ext φ x
  simp

中文:
定理 dualRestrict_comp_dualLift
  条件: (W : Subspace K V)
  结论: W.dualRestrict.comp W.dualLift = 1
  证明: by
  ext φ x
  simp
-/
theorem dualRestrict_comp_dualLift (W : Subspace K V) : W.dualRestrict.comp W.dualLift = 1 := by
  ext φ x
  simp

/--
theorem `dualRestrict_leftInverse` / 定理 `dualRestrict_leftInverse`

English:
theorem dualRestrict_leftInverse
  given: (W : Subspace K V)
  proof: fun x => by
  rw [← LinearMap.comp_apply]; rw [dualRestrict_comp_dualLift]; rw [End.one_apply]

中文:
定理 dualRestrict_leftInverse
  条件: (W : Subspace K V)
  证明: fun x => by
  rw [← LinearMap.comp_apply]; rw [dualRestrict_comp_dualLift]; rw [End.one_apply]

Depends on / 依赖: End.one_apply, LinearMap, LinearMap.comp_apply, comp_apply, dualRestrict_comp_dualLift, one_apply
-/
theorem dualRestrict_leftInverse (W : Subspace K V) :
    Function.LeftInverse W.dualRestrict W.dualLift := fun x => by
  rw [← LinearMap.comp_apply]; rw [dualRestrict_comp_dualLift]; rw [End.one_apply]

/--
theorem `dualLift_rightInverse` / 定理 `dualLift_rightInverse`

English:
theorem dualLift_rightInverse
  given: (W : Subspace K V)
  proof: W.dualRestrict_leftInverse

中文:
定理 dualLift_rightInverse
  条件: (W : Subspace K V)
  证明: W.dualRestrict_leftInverse

Depends on / 依赖: W.dualRestrict_leftInverse, dualRestrict_leftInverse
-/
theorem dualLift_rightInverse (W : Subspace K V) :
    Function.RightInverse W.dualLift W.dualRestrict :=
  W.dualRestrict_leftInverse

/--
theorem `dualRestrict_surjective` / 定理 `dualRestrict_surjective`

English:
theorem dualRestrict_surjective
  statement: Function.Surjective W.dualRestrict
  proof: W.dualLift_rightInverse.surjective

中文:
定理 dualRestrict_surjective
  结论: Function.Surjective W.dualRestrict
  证明: W.dualLift_rightInverse.surjective

Depends on / 依赖: ENNReal, ENNReal.lintegral_Lp_add_le, Pi.add_apply, W.dualLift_rightInverse.surjective, add_apply, dualLift_rightInverse, eLpNorm, enorm_add_le, hf.enorm, hg.enorm, lintegral_Lp_add_le, surjective
-/
theorem dualRestrict_surjective : Function.Surjective W.dualRestrict :=
  W.dualLift_rightInverse.surjective

/--
theorem `dualLift_injective` / 定理 `dualLift_injective`

English:
theorem dualLift_injective
  statement: Function.Injective W.dualLift
  proof: W.dualRestrict_leftInverse.injective

中文:
定理 dualLift_injective
  结论: Function.Injective W.dualLift
  证明: W.dualRestrict_leftInverse.injective

Depends on / 依赖: ENNReal, ENNReal.lintegral_Lp_add_le_of_le_one, Pi.add_apply, W.dualRestrict_leftInverse.injective, add_apply, dualRestrict_leftInverse, eLpNorm, enorm_add_le, hf.enorm, injective, lintegral_Lp_add_le_of_le_one
-/
theorem dualLift_injective : Function.Injective W.dualLift :=
  W.dualRestrict_leftInverse.injective

/--
Definition of `quotAnnihilatorEquiv` / `quotAnnihilatorEquiv` 的定义

English:
definition quotAnnihilatorEquiv
  signature: (W : Subspace K V)
  body: (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective

@[simp]

中文:
定义 quotAnnihilatorEquiv
  签名: (W : Subspace K V)
  定义体: (quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective

@[simp]

Depends on / 依赖: W.dualRestrict.quotKerEquivOfSurjective, W.dualRestrict_ker_eq_dualAnnihilator, dualRestrict, dualRestrict_ker_eq_dualAnnihilator, dualRestrict_surjective, quotEquivOfEq, quotKerEquivOfSurjective, symm.trans
-/
noncomputable def quotAnnihilatorEquiv (W : Subspace K V) :
    (Module.Dual K V ⧸ W.dualAnnihilator) ≃ₗ[K] Module.Dual K W :=
(quotEquivOfEq _ _ W.dualRestrict_ker_eq_dualAnnihilator).symm.trans
    W.dualRestrict.quotKerEquivOfSurjective dualRestrict_surjective

@[simp]
/--
theorem `quotAnnihilatorEquiv_apply` / 定理 `quotAnnihilatorEquiv_apply`

English:
theorem quotAnnihilatorEquiv_apply
  given: (W : Subspace K V) (φ : Module.Dual K V)
  proof: by
  ext
  rfl

中文:
定理 quotAnnihilatorEquiv_apply
  条件: (W : Subspace K V) (φ : Module.Dual K V)
  证明: by
  ext
  rfl
-/
theorem quotAnnihilatorEquiv_apply (W : Subspace K V) (φ : Module.Dual K V) :
    W.quotAnnihilatorEquiv (Submodule.Quotient.mk φ) = W.dualRestrict φ := by
  ext
  rfl

/--
Definition of `dualEquivDual` / `dualEquivDual` 的定义

English:
definition dualEquivDual
  signature: (W : Subspace K V)
  body: LinearEquiv.ofInjective _ dualLift_injective

中文:
定义 dualEquivDual
  签名: (W : Subspace K V)
  定义体: LinearEquiv.ofInjective _ dualLift_injective

Depends on / 依赖: LinearEquiv, LinearEquiv.ofInjective, dualLift_injective, ofInjective
-/
noncomputable def dualEquivDual (W : Subspace K V) :
    Module.Dual K W ≃ₗ[K] LinearMap.range W.dualLift :=
  LinearEquiv.ofInjective _ dualLift_injective

/--
theorem `dualEquivDual_def` / 定理 `dualEquivDual_def`

English:
theorem dualEquivDual_def
  given: (W : Subspace K V)
  proof: rfl

@[simp]

中文:
定理 dualEquivDual_def
  条件: (W : Subspace K V)
  证明: rfl

@[simp]
-/
theorem dualEquivDual_def (W : Subspace K V) :
    W.dualEquivDual.toLinearMap = W.dualLift.rangeRestrict :=
  rfl

@[simp]
/--
theorem `dualEquivDual_apply` / 定理 `dualEquivDual_apply`

English:
theorem dualEquivDual_apply
  given: (φ : Module.Dual K W)
  proof: rfl

中文:
定理 dualEquivDual_apply
  条件: (φ : Module.Dual K W)
  证明: rfl
-/
theorem dualEquivDual_apply (φ : Module.Dual K W) :
    W.dualEquivDual φ = ⟨W.dualLift φ, mem_range.2 ⟨φ, rfl⟩⟩ :=
  rfl

section

open FiniteDimensional Module

/--
Instance `instModuleDualFiniteDimensional` / 实例 `instModuleDualFiniteDimensional`

English:
instance instModuleDualFiniteDimensional
  signature: [FiniteDimensional K V]
  body: by
  infer_instance

@[simp]

中文:
实例 instModuleDualFiniteDimensional
  签名: [FiniteDimensional K V]
  定义体: by
  infer_instance

@[simp]

Depends on / 依赖: infer_instance
-/
instance instModuleDualFiniteDimensional [FiniteDimensional K V] :
    FiniteDimensional K (Module.Dual K V) := by
  infer_instance

@[simp]
/--
theorem `dual_finrank_eq` / 定理 `dual_finrank_eq`

English:
theorem dual_finrank_eq
  statement: finrank K (Module.Dual K V) = finrank K V
  proof: by
  by_cases h : FiniteDimensional K V
  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
  rw [finrank_eq_zero_of_basis_imp_false]; rw [finrank_eq_zero_of_basis_imp_false]
  · exact fun _ b => h (Module.Finite.of_basis b)
  · exact fun _ b => h ((Module.finite_du

中文:
定理 dual_finrank_eq
  结论: finrank K (Module.Dual K V) = finrank K V
  证明: by
  by_cases h : FiniteDimensional K V
  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
  rw [finrank_eq_zero_of_basis_imp_false]; rw [finrank_eq_zero_of_basis_imp_false]
  · exact fun _ b => h (Module.Finite.of_basis b)
  · exact fun _ b => h ((Module.finite_du

Depends on / 依赖: Basis.ofVectorSpace, Finite, FiniteDimensional, LinearEquiv, LinearEquiv.finrank_eq, Module, Module.Finite.of_basis, Module.finite_dual_iff, classical, finite_dual_iff, finrank_eq, finrank_eq_zero_of_basis_imp_false, ofVectorSpace, of_basis, toDualEquiv, toDualEquiv.symm
-/
theorem dual_finrank_eq : finrank K (Module.Dual K V) = finrank K V := by
  by_cases h : FiniteDimensional K V
  · classical exact LinearEquiv.finrank_eq (Basis.ofVectorSpace K V).toDualEquiv.symm
  rw [finrank_eq_zero_of_basis_imp_false]; rw [finrank_eq_zero_of_basis_imp_false]
  · exact fun _ b => h (Module.Finite.of_basis b)
  · exact fun _ b => h ((Module.finite_dual_iff K).mp <| Module.Finite.of_basis b)

variable [FiniteDimensional K V]

/--
theorem `dualAnnihilator_dualAnnihilator_eq` / 定理 `dualAnnihilator_dualAnnihilator_eq`

English:
theorem dualAnnihilator_dualAnnihilator_eq
  given: (W : Subspace K V)
  proof: by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator]; rw [← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]

中文:
定理 dualAnnihilator_dualAnnihilator_eq
  条件: (W : Subspace K V)
  证明: by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator]; rw [← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]

Depends on / 依赖: AEStronglyMeasurable, Finset, Finset.le_sum_of_subadditive_on_pred, Module, Module.mapEvalEquiv_symm_apply, OrderIso, OrderIso.symm_apply_eq, Subspace, Subspace.dualAnnihilator_dualCoannihilator_eq, _add_le, _zero, dualAnnihilator_dualCoannihilator_eq, dualCoannihilator, eLpNorm, hf.add, le_sum_of_subadditive_on_pred, mapEvalEquiv_symm_apply, symm_apply_eq, trans_le, zero_lt_one
-/
theorem dualAnnihilator_dualAnnihilator_eq (W : Subspace K V) :
    W.dualAnnihilator.dualAnnihilator = Module.mapEvalEquiv K V W := by
  have : _ = W := Subspace.dualAnnihilator_dualCoannihilator_eq
  rw [dualCoannihilator]; rw [← Module.mapEvalEquiv_symm_apply] at this
  rwa [← OrderIso.symm_apply_eq]

/--
Definition of `quotDualEquivAnnihilator` / `quotDualEquivAnnihilator` 的定义

English:
definition quotDualEquivAnnihilator
  signature: (W : Subspace K V)
  body: LinearEquiv.quotEquivOfQuotEquiv LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

中文:
定义 quotDualEquivAnnihilator
  签名: (W : Subspace K V)
  定义体: LinearEquiv.quotEquivOfQuotEquiv LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

Depends on / 依赖: LinearEquiv, LinearEquiv.quotEquivOfQuotEquiv, LinearEquiv.trans, W.dualEquivDual, W.quotAnnihilatorEquiv, dualEquivDual, quotAnnihilatorEquiv, quotEquivOfQuotEquiv
-/
noncomputable def quotDualEquivAnnihilator (W : Subspace K V) :
    (Module.Dual K V ⧸ LinearMap.range W.dualLift) ≃ₗ[K] W.dualAnnihilator :=
LinearEquiv.quotEquivOfQuotEquiv LinearEquiv.trans W.quotAnnihilatorEquiv W.dualEquivDual

open scoped Classical in
/--
Definition of `quotEquivAnnihilator` / `quotEquivAnnihilator` 的定义

English:
definition quotEquivAnnihilator
  signature: (W : Subspace K V)
  body: let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator

中文:
定义 quotEquivAnnihilator
  签名: (W : Subspace K V)
  定义体: let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator

Depends on / 依赖: Basis.ofVectorSpace, LinearEquiv, LinearEquiv.quotEquivOfEquiv, W.dualEquivDual, W.quotDualEquivAnnihilator, dualEquivDual, ofVectorSpace, quotDualEquivAnnihilator, quotEquivOfEquiv, toDualEquiv, toDualEquiv.trans
-/
noncomputable def quotEquivAnnihilator (W : Subspace K V) : (V ⧸ W) ≃ₗ[K] W.dualAnnihilator :=
  let φ := (Basis.ofVectorSpace K W).toDualEquiv.trans W.dualEquivDual
  let ψ := LinearEquiv.quotEquivOfEquiv φ (Basis.ofVectorSpace K V).toDualEquiv
  ψ ≪≫ₗ W.quotDualEquivAnnihilator

open Module

/--
theorem `finrank_add_finrank_dualAnnihilator_eq` / 定理 `finrank_add_finrank_dualAnnihilator_eq`

English:
theorem finrank_add_finrank_dualAnnihilator_eq
  given: (W : Subspace K V)
  proof: by
  rw [← W.quotEquivAnnihilator.finrank_eq]; rw [add_comm]; rw [Submodule.finrank_quotient_add_finrank]

@[simp]

中文:
定理 finrank_add_finrank_dualAnnihilator_eq
  条件: (W : Subspace K V)
  证明: by
  rw [← W.quotEquivAnnihilator.finrank_eq]; rw [add_comm]; rw [Submodule.finrank_quotient_add_finrank]

@[simp]

Depends on / 依赖: Submodule, Submodule.finrank_quotient_add_finrank, W.quotEquivAnnihilator.finrank_eq, add_comm, finrank_eq, finrank_quotient_add_finrank, quotEquivAnnihilator
-/
theorem finrank_add_finrank_dualAnnihilator_eq (W : Subspace K V) :
    finrank K W + finrank K W.dualAnnihilator = finrank K V := by
  rw [← W.quotEquivAnnihilator.finrank_eq]; rw [add_comm]; rw [Submodule.finrank_quotient_add_finrank]

@[simp]
/--
theorem `finrank_dualCoannihilator_eq` / 定理 `finrank_dualCoannihilator_eq`

English:
theorem finrank_dualCoannihilator_eq
  given: {Φ : Subspace K (Module.Dual K V)}
  proof: by
  rw [Submodule.dualCoannihilator]; rw [← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

中文:
定理 finrank_dualCoannihilator_eq
  条件: {Φ : Subspace K (Module.Dual K V)}
  证明: by
  rw [Submodule.dualCoannihilator]; rw [← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

Depends on / 依赖: LinearEquiv, LinearEquiv.finrank_eq, LinearEquiv.ofSubmodule, Module, Module.evalEquiv_toLinearMap, Submodule, Submodule.dualCoannihilator, dualCoannihilator, evalEquiv_toLinearMap, finrank_eq, ofSubmodule
-/
theorem finrank_dualCoannihilator_eq {Φ : Subspace K (Module.Dual K V)} :
    finrank K Φ.dualCoannihilator = finrank K Φ.dualAnnihilator := by
  rw [Submodule.dualCoannihilator]; rw [← Module.evalEquiv_toLinearMap]
  exact LinearEquiv.finrank_eq (LinearEquiv.ofSubmodule' _ _)

/--
theorem `finrank_add_finrank_dualCoannihilator_eq` / 定理 `finrank_add_finrank_dualCoannihilator_eq`

English:
theorem finrank_add_finrank_dualCoannihilator_eq
  given: (W : Subspace K (Module.Dual K V))
  proof: by
  rw [finrank_dualCoannihilator_eq]; rw [finrank_add_finrank_dualAnnihilator_eq]; rw [dual_finrank_eq]

中文:
定理 finrank_add_finrank_dualCoannihilator_eq
  条件: (W : Subspace K (Module.Dual K V))
  证明: by
  rw [finrank_dualCoannihilator_eq]; rw [finrank_add_finrank_dualAnnihilator_eq]; rw [dual_finrank_eq]

Depends on / 依赖: dual_finrank_eq, finrank_add_finrank_dualAnnihilator_eq, finrank_dualCoannihilator_eq
-/
theorem finrank_add_finrank_dualCoannihilator_eq (W : Subspace K (Module.Dual K V)) :
    finrank K W + finrank K W.dualCoannihilator = finrank K V := by
  rw [finrank_dualCoannihilator_eq]; rw [finrank_add_finrank_dualAnnihilator_eq]; rw [dual_finrank_eq]

end

end Subspace

open Module

section CommRing

variable {R M M' : Type*}
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

namespace Submodule

/--
Definition of `dualCopairing` / `dualCopairing` 的定义

English:
definition dualCopairing
  signature: (W : Submodule R M)
  body: LinearMap.flip W.liftQ W.dualAnnihilator.subtype.flip (by
    intro w hw
    ext ⟨φ, hφ⟩
    exact (mem_dualAnnihilator φ).mp hφ w hw)

中文:
定义 dualCopairing
  签名: (W : Submodule R M)
  定义体: LinearMap.flip W.liftQ W.dualAnnihilator.subtype.flip (by
    intro w hw
    ext ⟨φ, hφ⟩
    exact (mem_dualAnnihilator φ).mp hφ w hw)

Depends on / 依赖: LinearMap, LinearMap.flip, W.dualAnnihilator.subtype.flip, W.liftQ, dualAnnihilator, eLpNorm, fun_prop, lintegral_trim, mem_dualAnnihilator, simp_rw, subtype
-/
def dualCopairing (W : Submodule R M) : W.dualAnnihilator ->ₗ[R] M ⧸ W ->ₗ[R] R :=
LinearMap.flip W.liftQ W.dualAnnihilator.subtype.flip (by
    intro w hw
    ext ⟨φ, hφ⟩
    exact (mem_dualAnnihilator φ).mp hφ w hw)

instance (W : Submodule R M) : FunLike (W.dualAnnihilator) M R where
  coe φ := φ.val
  coe_injective φ ψ h := by
    ext
    simp only [funext_iff] at h
    exact h _

@[simp]
/--
theorem `dualCopairing_apply` / 定理 `dualCopairing_apply`

English:
theorem dualCopairing_apply
  given: {W : Submodule R M} (φ : W.dualAnnihilator) (x : M)
  proof: rfl

中文:
定理 dualCopairing_apply
  条件: {W : Submodule R M} (φ : W.dualAnnihilator) (x : M)
  证明: rfl
-/
theorem dualCopairing_apply {W : Submodule R M} (φ : W.dualAnnihilator) (x : M) :
    W.dualCopairing φ (Quotient.mk x) = φ x :=
  rfl

/--
Definition of `dualPairing` / `dualPairing` 的定义

English:
definition dualPairing
  signature: (W : Submodule R M)
  body: W.dualAnnihilator.liftQ W.dualRestrict le_rfl

@[simp]

中文:
定义 dualPairing
  签名: (W : Submodule R M)
  定义体: W.dualAnnihilator.liftQ W.dualRestrict le_rfl

@[simp]

Depends on / 依赖: W.dualAnnihilator.liftQ, W.dualRestrict, dualAnnihilator, dualRestrict, le_rfl
-/
def dualPairing (W : Submodule R M) : Module.Dual R M ⧸ W.dualAnnihilator ->ₗ[R] W ->ₗ[R] R :=
  W.dualAnnihilator.liftQ W.dualRestrict le_rfl

@[simp]
/--
theorem `dualPairing_apply` / 定理 `dualPairing_apply`

English:
theorem dualPairing_apply
  given: {W : Submodule R M} (φ : Module.Dual R M) (x : W)
  proof: rfl

中文:
定理 dualPairing_apply
  条件: {W : Submodule R M} (φ : Module.Dual R M) (x : W)
  证明: rfl
-/
theorem dualPairing_apply {W : Submodule R M} (φ : Module.Dual R M) (x : W) :
    W.dualPairing (Quotient.mk φ) x = φ x :=
  rfl

/--
theorem `range_dualMap_mkQ_eq` / 定理 `range_dualMap_mkQ_eq`

English:
theorem range_dualMap_mkQ_eq
  given: (W : Submodule R M)
  proof: by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using W.mkQ.range_dualMap_le_dualAnnihilator_ker this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩

中文:
定理 range_dualMap_mkQ_eq
  条件: (W : Submodule R M)
  证明: by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using W.mkQ.range_dualMap_le_dualAnnihilator_ker this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩

Depends on / 依赖: LinearMap, LinearMap.mem_range, LinearMap.mem_range_self, W.dualCopairing, W.mkQ.dualMap, W.mkQ.range_dualMap_le_dualAnnihilator_ker, dualCopairing, dualMap, ker_mkQ, mem_range, mem_range_self, range_dualMap_le_dualAnnihilator_ker
-/
theorem range_dualMap_mkQ_eq (W : Submodule R M) :
    LinearMap.range W.mkQ.dualMap = W.dualAnnihilator := by
  ext φ
  rw [LinearMap.mem_range]
  constructor
  · rintro ⟨ψ, rfl⟩
    have := LinearMap.mem_range_self W.mkQ.dualMap ψ
    simpa only [ker_mkQ] using W.mkQ.range_dualMap_le_dualAnnihilator_ker this
  · intro hφ
    exists W.dualCopairing ⟨φ, hφ⟩

/--
Definition of `dualQuotEquivDualAnnihilator` / `dualQuotEquivDualAnnihilator` 的定义

English:
definition dualQuotEquivDualAnnihilator
  signature: (W : Submodule R M)
  body: LinearEquiv.ofLinearMap
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing (by ext; rfl) (by ext; rfl)

@[simp]

中文:
定义 dualQuotEquivDualAnnihilator
  签名: (W : Submodule R M)
  定义体: LinearEquiv.ofLinearMap
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing (by ext; rfl) (by ext; rfl)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.mem_range_self, W.dualAnnihilator, W.dualCopairing, W.mkQ.dualMap, W.mkQ.dualMap.codRestrict, W.range_dualMap_mkQ_eq, codRestrict, dualAnnihilator, dualCopairing, dualMap, mem_range_self, ofLinearMap, range_dualMap_mkQ_eq
-/
def dualQuotEquivDualAnnihilator (W : Submodule R M) :
    Module.Dual R (M ⧸ W) ≃ₗ[R] W.dualAnnihilator :=
  LinearEquiv.ofLinearMap
    (W.mkQ.dualMap.codRestrict W.dualAnnihilator fun φ =>
      W.range_dualMap_mkQ_eq ▸ LinearMap.mem_range_self W.mkQ.dualMap φ)
    W.dualCopairing (by ext; rfl) (by ext; rfl)

@[simp]
/--
theorem `dualQuotEquivDualAnnihilator_apply` / 定理 `dualQuotEquivDualAnnihilator_apply`

English:
theorem dualQuotEquivDualAnnihilator_apply
  given: (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M)
  proof: rfl

中文:
定理 dualQuotEquivDualAnnihilator_apply
  条件: (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M)
  证明: rfl
-/
theorem dualQuotEquivDualAnnihilator_apply (W : Submodule R M) (φ : Module.Dual R (M ⧸ W)) (x : M) :
    dualQuotEquivDualAnnihilator W φ x = φ (Quotient.mk x) :=
  rfl

/--
theorem `dualCopairing_eq` / 定理 `dualCopairing_eq`

English:
theorem dualCopairing_eq
  given: (W : Submodule R M)
  proof: rfl

@[simp]

中文:
定理 dualCopairing_eq
  条件: (W : Submodule R M)
  证明: rfl

@[simp]
-/
theorem dualCopairing_eq (W : Submodule R M) :
    W.dualCopairing = (dualQuotEquivDualAnnihilator W).symm.toLinearMap :=
  rfl

@[simp]
/--
theorem `dualQuotEquivDualAnnihilator_symm_apply_mk` / 定理 `dualQuotEquivDualAnnihilator_symm_apply_mk`

English:
theorem dualQuotEquivDualAnnihilator_symm_apply_mk
  statement: (W : Submodule R M) (φ : W.dualAnnihilator)
  proof: rfl

中文:
定理 dualQuotEquivDualAnnihilator_symm_apply_mk
  结论: (W : Submodule R M) (φ : W.dualAnnihilator)
  证明: rfl
-/
theorem dualQuotEquivDualAnnihilator_symm_apply_mk (W : Submodule R M) (φ : W.dualAnnihilator)
    (x : M) : (dualQuotEquivDualAnnihilator W).symm φ (Quotient.mk x) = φ x :=
  rfl

/--
theorem `finite_dualAnnihilator_iff` / 定理 `finite_dualAnnihilator_iff`

English:
theorem finite_dualAnnihilator_iff
  given: {W : Submodule R M} [Free R (M ⧸ W)]
  proof: (Finite.equiv_iff W.dualQuotEquivDualAnnihilator.symm).trans (finite_dual_iff R)

中文:
定理 finite_dualAnnihilator_iff
  条件: {W : Submodule R M} [Free R (M ⧸ W)]
  证明: (Finite.equiv_iff W.dualQuotEquivDualAnnihilator.symm).trans (finite_dual_iff R)

Depends on / 依赖: Finite, Finite.equiv_iff, W.dualQuotEquivDualAnnihilator.symm, dualQuotEquivDualAnnihilator, equiv_iff, finite_dual_iff
-/
theorem finite_dualAnnihilator_iff {W : Submodule R M} [Free R (M ⧸ W)] :
    Module.Finite R W.dualAnnihilator ↔ Module.Finite R (M ⧸ W) :=
  (Finite.equiv_iff W.dualQuotEquivDualAnnihilator.symm).trans (finite_dual_iff R)

/--
lemma `dualAnnihilator_eq_bot_iff'` / 引理 `dualAnnihilator_eq_bot_iff'`

English:
lemma dualAnnihilator_eq_bot_iff'
  given: {W : Submodule R M}
  proof: by
  rw [W.dualQuotEquivDualAnnihilator.toEquiv.subsingleton_congr]; rw [subsingleton_iff_eq_bot]

中文:
引理 dualAnnihilator_eq_bot_iff'
  条件: {W : Submodule R M}
  证明: by
  rw [W.dualQuotEquivDualAnnihilator.toEquiv.subsingleton_congr]; rw [subsingleton_iff_eq_bot]

Depends on / 依赖: W.dualQuotEquivDualAnnihilator.toEquiv.subsingleton_congr, dualQuotEquivDualAnnihilator, subsingleton_congr, subsingleton_iff_eq_bot, toEquiv
-/
lemma dualAnnihilator_eq_bot_iff' {W : Submodule R M} :
    W.dualAnnihilator = ⊥ ↔ Subsingleton (Dual R (M ⧸ W)) := by
  rw [W.dualQuotEquivDualAnnihilator.toEquiv.subsingleton_congr]; rw [subsingleton_iff_eq_bot]

/--
lemma `dualAnnihilator_eq_bot_iff` / 引理 `dualAnnihilator_eq_bot_iff`

English:
lemma dualAnnihilator_eq_bot_iff
  given: {W : Submodule R M} [Projective R (M ⧸ W)]
  proof: by
  rw [dualAnnihilator_eq_bot_iff']; rw [subsingleton_dual_iff]; rw [Quotient.subsingleton_iff]

中文:
引理 dualAnnihilator_eq_bot_iff
  条件: {W : Submodule R M} [Projective R (M ⧸ W)]
  证明: by
  rw [dualAnnihilator_eq_bot_iff']; rw [subsingleton_dual_iff]; rw [Quotient.subsingleton_iff]
-/
@[simp] lemma dualAnnihilator_eq_bot_iff {W : Submodule R M} [Projective R (M ⧸ W)] :
    W.dualAnnihilator = ⊥ ↔ W = ⊤ := by
  rw [dualAnnihilator_eq_bot_iff']; rw [subsingleton_dual_iff]; rw [Quotient.subsingleton_iff]

/--
lemma `dualAnnihilator_eq_top_iff` / 引理 `dualAnnihilator_eq_top_iff`

English:
lemma dualAnnihilator_eq_top_iff
  given: {W : Submodule R M} [Projective R M]
  proof: by
  refine ⟨fun h => ?_, fun h => h ▸ dualAnnihilator_bot⟩
  refine W.eq_bot_iff.mpr fun v hv => (forall_dual_apply_eq_zero_iff R v).mp fun f => ?_
  refine (mem_dualAnnihilator f).mp ?_ v hv
  simp [h]

中文:
引理 dualAnnihilator_eq_top_iff
  条件: {W : Submodule R M} [Projective R M]
  证明: by
  refine ⟨fun h => ?_, fun h => h ▸ dualAnnihilator_bot⟩
  refine W.eq_bot_iff.mpr fun v hv => (forall_dual_apply_eq_zero_iff R v).mp fun f => ?_
  refine (mem_dualAnnihilator f).mp ?_ v hv
  simp [h]
-/
@[simp] lemma dualAnnihilator_eq_top_iff {W : Submodule R M} [Projective R M] :
    W.dualAnnihilator = ⊤ ↔ W = ⊥ := by
  refine ⟨fun h => ?_, fun h => h ▸ dualAnnihilator_bot⟩
  refine W.eq_bot_iff.mpr fun v hv => (forall_dual_apply_eq_zero_iff R v).mp fun f => ?_
  refine (mem_dualAnnihilator f).mp ?_ v hv
  simp [h]

open LinearMap in
/--
Definition of `quotDualCoannihilatorToDual` / `quotDualCoannihilatorToDual` 的定义

English:
definition quotDualCoannihilatorToDual
  signature: (W : Submodule R (Dual R M))
  body: liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]

中文:
定义 quotDualCoannihilatorToDual
  签名: (W : Submodule R (Dual R M))
  定义体: liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]

Depends on / 依赖: Submodule, Submodule.subtype, le_rfl, subtype
-/
def quotDualCoannihilatorToDual (W : Submodule R (Dual R M)) :
    M ⧸ W.dualCoannihilator ->ₗ[R] Dual R W :=
  liftQ _ (flip <| Submodule.subtype _) le_rfl

@[simp]
/--
theorem `quotDualCoannihilatorToDual_apply` / 定理 `quotDualCoannihilatorToDual_apply`

English:
theorem quotDualCoannihilatorToDual_apply
  given: (W : Submodule R (Dual R M)) (m : M) (w : W)
  proof: rfl

中文:
定理 quotDualCoannihilatorToDual_apply
  条件: (W : Submodule R (Dual R M)) (m : M) (w : W)
  证明: rfl
-/
theorem quotDualCoannihilatorToDual_apply (W : Submodule R (Dual R M)) (m : M) (w : W) :
    W.quotDualCoannihilatorToDual (Quotient.mk m) w = w.1 m := rfl

/--
theorem `quotDualCoannihilatorToDual_injective` / 定理 `quotDualCoannihilatorToDual_injective`

English:
theorem quotDualCoannihilatorToDual_injective
  given: (W : Submodule R (Dual R M))
  proof: LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)

中文:
定理 quotDualCoannihilatorToDual_injective
  条件: (W : Submodule R (Dual R M))
  证明: LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot.mp, ker_eq_bot, ker_liftQ_eq_bot, le_rfl
-/
theorem quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual :=
  LinearMap.ker_eq_bot.mp (ker_liftQ_eq_bot _ _ _ le_rfl)

/--
theorem `flip_quotDualCoannihilatorToDual_injective` / 定理 `flip_quotDualCoannihilatorToDual_injective`

English:
theorem flip_quotDualCoannihilatorToDual_injective
  given: (W : Submodule R (Dual R M))
  proof: fun _ _ he => Subtype.ext LinearMap.ext fun m => DFunLike.congr_fun he ⟦m⟧

中文:
定理 flip_quotDualCoannihilatorToDual_injective
  条件: (W : Submodule R (Dual R M))
  证明: fun _ _ he => Subtype.ext LinearMap.ext fun m => DFunLike.congr_fun he ⟦m⟧

Depends on / 依赖: DFunLike, DFunLike.congr_fun, LinearMap, LinearMap.ext, Subtype, Subtype.ext, congr_fun
-/
theorem flip_quotDualCoannihilatorToDual_injective (W : Submodule R (Dual R M)) :
    Function.Injective W.quotDualCoannihilatorToDual.flip :=
fun _ _ he => Subtype.ext LinearMap.ext fun m => DFunLike.congr_fun he ⟦m⟧

open LinearMap in
/--
theorem `quotDualCoannihilatorToDual_nondegenerate` / 定理 `quotDualCoannihilatorToDual_nondegenerate`

English:
theorem quotDualCoannihilatorToDual_nondegenerate
  given: (W : Submodule R (Dual R M))
  proof: by
  rw [Nondegenerate]; rw [separatingLeft_iff_ker_eq_bot]; rw [separatingRight_iff_flip_ker_eq_bot]
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

中文:
定理 quotDualCoannihilatorToDual_nondegenerate
  条件: (W : Submodule R (Dual R M))
  证明: by
  rw [Nondegenerate]; rw [separatingLeft_iff_ker_eq_bot]; rw [separatingRight_iff_flip_ker_eq_bot]
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

Depends on / 依赖: Nondegenerate, W.flip_quotDualCoannihilatorToDual_injective, W.quotDualCoannihilatorToDual_injective, flip_quotDualCoannihilatorToDual_injective, ker_eq_bot, quotDualCoannihilatorToDual_injective, separatingLeft_iff_ker_eq_bot, separatingRight_iff_flip_ker_eq_bot, simp_rw
-/
theorem quotDualCoannihilatorToDual_nondegenerate (W : Submodule R (Dual R M)) :
    W.quotDualCoannihilatorToDual.Nondegenerate := by
  rw [Nondegenerate]; rw [separatingLeft_iff_ker_eq_bot]; rw [separatingRight_iff_flip_ker_eq_bot]
  simp_rw [ker_eq_bot]
  exact ⟨W.quotDualCoannihilatorToDual_injective, W.flip_quotDualCoannihilatorToDual_injective⟩

end Submodule

namespace LinearMap

open Submodule

/--
theorem `range_dualMap_eq_dualAnnihilator_ker_of_surjective` / 定理 `range_dualMap_eq_dualAnnihilator_ker_of_surjective`

English:
theorem range_dualMap_eq_dualAnnihilator_ker_of_surjective
  statement: (f : M ->ₗ[R] M')
  proof: ((f.quotKerEquivOfSurjective hf).dualMap.range_comp _).trans
    (LinearMap.ker f).range_dualMap_mkQ_eq

中文:
定理 range_dualMap_eq_dualAnnihilator_ker_of_surjective
  结论: (f : M ->ₗ[R] M')
  证明: ((f.quotKerEquivOfSurjective hf).dualMap.range_comp _).trans
    (LinearMap.ker f).range_dualMap_mkQ_eq

Depends on / 依赖: LinearMap, LinearMap.ker, dualMap, dualMap.range_comp, f.quotKerEquivOfSurjective, quotKerEquivOfSurjective, range_comp, range_dualMap_mkQ_eq
-/
theorem range_dualMap_eq_dualAnnihilator_ker_of_surjective (f : M ->ₗ[R] M')
    (hf : Function.Surjective f) : LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
  ((f.quotKerEquivOfSurjective hf).dualMap.range_comp _).trans
    (LinearMap.ker f).range_dualMap_mkQ_eq

-- Note, this can be specialized to the case where `R` is an injective `R`-module, or when
-- `f.coker` is a projective `R`-module.
/--
theorem `range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective` / 定理 `range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective`

English:
theorem range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective
  statement: (f : M ->ₗ[R] M')
  proof: by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← range_eq_top]; rw [range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert! this using 1
  · calc
      _ = range ((range f).subtype.comp f.rangeRestrict).dualMap := by

中文:
定理 range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective
  结论: (f : M ->ₗ[R] M')
  证明: by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← range_eq_top]; rw [range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert! this using 1
  · calc
      _ = range ((range f).subtype.comp f.rangeRestrict).dualMap := by

Depends on / 依赖: Function, Function.Surjective, Surjective, congr_arg, convert, dualMap, dualMap_comp_dualMap, f.rangeRestrict, ker_rangeRestrict, rangeRestrict, range_comp_of_range_eq_top, range_dualMap_eq_dualAnnihilator_ker_of_surjective, range_eq_top, range_rangeRestrict, rr_surj, subtype, subtype.comp
-/
theorem range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective (f : M ->ₗ[R] M')
    (hf : Function.Surjective (range f).subtype.dualMap) :
    LinearMap.range f.dualMap = (ker f).dualAnnihilator := by
  have rr_surj : Function.Surjective f.rangeRestrict := by
    rw [← range_eq_top]; rw [range_rangeRestrict]
  have := range_dualMap_eq_dualAnnihilator_ker_of_surjective f.rangeRestrict rr_surj
  convert! this using 1
  · calc
      _ = range ((range f).subtype.comp f.rangeRestrict).dualMap := by simp
      _ = _ := ?_
    rw [← dualMap_comp_dualMap]; rw [range_comp_of_range_eq_top]
    rwa [range_eq_top]
  · apply congr_arg
    exact (ker_rangeRestrict f).symm

end LinearMap

end CommRing

section VectorSpace

section

variable {K V₁ V₂ : Type*} [DivisionRing K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace Module.Dual

variable {f : Module.Dual K V₁}

section
variable (hf : f != 0)

/--
lemma `range_eq_top_of_ne_zero` / 引理 `range_eq_top_of_ne_zero`

English:
lemma range_eq_top_of_ne_zero
  statement: {K V₁ : Type*} [DivisionSemiring K] [AddCommMonoid V₁] [Module K V₁]
  proof: LinearMap.range_eq_top.mpr (LinearMap.surjective hf)

中文:
引理 range_eq_top_of_ne_zero
  结论: {K V₁ : 类型} [DivisionSemiring K] [AddCommMonoid V₁] [Module K V₁]
  证明: LinearMap.range_eq_top.mpr (LinearMap.surjective hf)

Depends on / 依赖: LinearMap, LinearMap.range_eq_top.mpr, LinearMap.surjective, range_eq_top, surjective
-/
lemma range_eq_top_of_ne_zero {K V₁ : Type*} [DivisionSemiring K] [AddCommMonoid V₁] [Module K V₁]
    {f : Module.Dual K V₁} (hf : f != 0) : LinearMap.range f = ⊤ :=
  LinearMap.range_eq_top.mpr (LinearMap.surjective hf)

variable [FiniteDimensional K V₁]
include hf

/--
lemma `finrank_ker_add_one_of_ne_zero` / 引理 `finrank_ker_add_one_of_ne_zero`

English:
lemma finrank_ker_add_one_of_ne_zero
  proof: by
  suffices finrank K (LinearMap.range f) = 1 by
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank]; rw [add_comm]; rw [add_left_inj]; rw [f.quotKerEquivRange.finrank_eq]; rw [this]
  rw [range_eq_top_of_ne_zero hf]; rw [finrank_top]; rw [finrank_self]

中文:
引理 finrank_ker_add_one_of_ne_zero
  证明: by
  suffices finrank K (LinearMap.range f) = 1 by
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank]; rw [add_comm]; rw [add_left_inj]; rw [f.quotKerEquivRange.finrank_eq]; rw [this]
  rw [range_eq_top_of_ne_zero hf]; rw [finrank_top]; rw [finrank_self]

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.range, add_comm, add_left_inj, f.quotKerEquivRange.finrank_eq, finrank, finrank_eq, finrank_quotient_add_finrank, finrank_self, finrank_top, quotKerEquivRange, range_eq_top_of_ne_zero
-/
lemma finrank_ker_add_one_of_ne_zero :
    finrank K (LinearMap.ker f) + 1 = finrank K V₁ := by
  suffices finrank K (LinearMap.range f) = 1 by
    rw [← (LinearMap.ker f).finrank_quotient_add_finrank]; rw [add_comm]; rw [add_left_inj]; rw [f.quotKerEquivRange.finrank_eq]; rw [this]
  rw [range_eq_top_of_ne_zero hf]; rw [finrank_top]; rw [finrank_self]

/--
lemma `isCompl_ker_of_disjoint_of_ne_bot` / 引理 `isCompl_ker_of_disjoint_of_ne_bot`

English:
lemma isCompl_ker_of_disjoint_of_ne_bot
  statement: {p : Submodule K V₁}
  proof: by
refine ⟨hpf, codisjoint_iff.mpr eq_of_le_of_finrank_le le_top ?_⟩
  have : finrank K ↑(LinearMap.ker f ⊔ p) = finrank K (LinearMap.ker f) + finrank K p := by
    simp [← Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) p, hpf.eq_bot]
  rwa [finrank_top, this, ← finrank_ker_add_one_of_ne

中文:
引理 isCompl_ker_of_disjoint_of_ne_bot
  结论: {p : Submodule K V₁}
  证明: by
refine ⟨hpf, codisjoint_iff.mpr eq_of_le_of_finrank_le le_top ?_⟩
  have : finrank K ↑(LinearMap.ker f ⊔ p) = finrank K (LinearMap.ker f) + finrank K p := by
    simp [← Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) p, hpf.eq_bot]
  rwa [finrank_top, this, ← finrank_ker_add_one_of_ne

Depends on / 依赖: LinearMap, LinearMap.ker, Submodule, Submodule.finrank_sup_add_finrank_inf_eq, Submodule.one_le_finrank_iff, add_le_add_iff_left, codisjoint_iff, codisjoint_iff.mpr, eq_bot, eq_of_le_of_finrank_le, finrank, finrank_ker_add_one_of_ne_zero, finrank_sup_add_finrank_inf_eq, finrank_top, hpf.eq_bot, le_top, one_le_finrank_iff
-/
lemma isCompl_ker_of_disjoint_of_ne_bot {p : Submodule K V₁}
    (hpf : Disjoint (LinearMap.ker f) p) (hp : p != ⊥) :
    IsCompl (LinearMap.ker f) p := by
refine ⟨hpf, codisjoint_iff.mpr eq_of_le_of_finrank_le le_top ?_⟩
  have : finrank K ↑(LinearMap.ker f ⊔ p) = finrank K (LinearMap.ker f) + finrank K p := by
    simp [← Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker f) p, hpf.eq_bot]
  rwa [finrank_top, this, ← finrank_ker_add_one_of_ne_zero hf, add_le_add_iff_left,
    Submodule.one_le_finrank_iff]

end

/--
lemma `eq_of_ker_eq_of_apply_eq` / 引理 `eq_of_ker_eq_of_apply_eq`

English:
lemma eq_of_ker_eq_of_apply_eq
  statement: [FiniteDimensional K V₁] {f g : Module.Dual K V₁} (x : V₁)
  proof: by
  let p := K ∙ x
  have hp : p != ⊥ := by aesop
  have hpf : Disjoint (LinearMap.ker f) p := by
    rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
    rintro y ⟨hfy : f y = 0, hpy : y in p⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hpy
    have ht : t = 0 := by simpa [hx] using hfy
   

中文:
引理 eq_of_ker_eq_of_apply_eq
  结论: [FiniteDimensional K V₁] {f g : Module.Dual K V₁} (x : V₁)
  证明: by
  let p := K ∙ x
  have hp : p != ⊥ := by aesop
  have hpf : Disjoint (LinearMap.ker f) p := by
    rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
    rintro y ⟨hfy : f y = 0, hpy : y in p⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hpy
    have ht : t = 0 := by simpa [hx] using hfy
   

Depends on / 依赖: Disjoint, LinearMap, LinearMap.ker, Submodule, Submodule.eq_bot_iff, Submodule.mem_span_singleton.mp, Submodule.mem_top, disjoint_iff, eq_bot_iff, isCompl_ker_of_disjoint_of_ne_bo, mem_span_singleton, mem_top
-/
lemma eq_of_ker_eq_of_apply_eq [FiniteDimensional K V₁] {f g : Module.Dual K V₁} (x : V₁)
    (h : LinearMap.ker f = LinearMap.ker g) (h' : f x = g x) (hx : f x != 0) :
    f = g := by
  let p := K ∙ x
  have hp : p != ⊥ := by aesop
  have hpf : Disjoint (LinearMap.ker f) p := by
    rw [disjoint_iff]; rw [Submodule.eq_bot_iff]
    rintro y ⟨hfy : f y = 0, hpy : y in p⟩
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hpy
    have ht : t = 0 := by simpa [hx] using hfy
    simp [ht]
  have hf : f != 0 := by aesop
  ext v
  obtain ⟨y, hy, z, hz, rfl⟩ : existsᵉ (y in LinearMap.ker f) (z in p), y + z = v := by
    have : v in (⊤ : Submodule K V₁) := Submodule.mem_top
    rwa [← (isCompl_ker_of_disjoint_of_ne_bot hf hpf hp).sup_eq_top, Submodule.mem_sup] at this
  have hy' : g y = 0 := by rwa [← LinearMap.mem_ker, ← h]
  replace hy : f y = 0 := by rwa [LinearMap.mem_ker] at hy
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
  simp [h', hy, hy']

end Module.Dual

end

namespace LinearMap

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]

/--
theorem `id_separatingLeft` / 定理 `id_separatingLeft`

English:
theorem id_separatingLeft
  statement: SeparatingLeft (M₁ := V ->ₗ[K] K) .id
  proof: separatingLeft_iff_ker_eq_bot.mpr ker_id

中文:
定理 id_separatingLeft
  结论: SeparatingLeft (M₁ := V ->ₗ[K] K) .id
  证明: separatingLeft_iff_ker_eq_bot.mpr ker_id
-/
theorem id_separatingLeft : SeparatingLeft (M₁ := V ->ₗ[K] K) .id :=
  separatingLeft_iff_ker_eq_bot.mpr ker_id

/--
theorem `eval_separatingRight` / 定理 `eval_separatingRight`

English:
theorem eval_separatingRight
  statement: SeparatingRight (Dual.eval K V)
  proof: id_separatingLeft

中文:
定理 eval_separatingRight
  结论: SeparatingRight (Dual.eval K V)
  证明: id_separatingLeft

Depends on / 依赖: id_separatingLeft
-/
theorem eval_separatingRight : SeparatingRight (Dual.eval K V) := id_separatingLeft

variable [Module.Projective K V]

/--
theorem `id_separatingRight` / 定理 `id_separatingRight`

English:
theorem id_separatingRight
  statement: SeparatingRight (M₁ := V ->ₗ[K] K) .id
  proof: fun x => (forall_dual_apply_eq_zero_iff K x).mp

中文:
定理 id_separatingRight
  结论: SeparatingRight (M₁ := V ->ₗ[K] K) .id
  证明: fun x => (forall_dual_apply_eq_zero_iff K x).mp
-/
theorem id_separatingRight : SeparatingRight (M₁ := V ->ₗ[K] K) .id :=
  fun x => (forall_dual_apply_eq_zero_iff K x).mp

/--
theorem `eval_separatingLeft` / 定理 `eval_separatingLeft`

English:
theorem eval_separatingLeft
  statement: SeparatingLeft (Dual.eval K V)
  proof: id_separatingRight

中文:
定理 eval_separatingLeft
  结论: SeparatingLeft (Dual.eval K V)
  证明: id_separatingRight

Depends on / 依赖: id_separatingRight
-/
theorem eval_separatingLeft : SeparatingLeft (Dual.eval K V) := id_separatingRight

/--
theorem `id_nondegenerate` / 定理 `id_nondegenerate`

English:
theorem id_nondegenerate
  statement: Nondegenerate (M₁ := V ->ₗ[K] K) .id
  proof: ⟨id_separatingLeft, id_separatingRight⟩

@[deprecated (since := "2026-04-02")]
alias dualPairing_nondegenerate := id_nondegenerate

中文:
定理 id_nondegenerate
  结论: Nondegenerate (M₁ := V ->ₗ[K] K) .id
  证明: ⟨id_separatingLeft, id_separatingRight⟩

@[deprecated (since := "2026-04-02")]
alias dualPairing_nondegenerate := id_nondegenerate
-/
theorem id_nondegenerate : Nondegenerate (M₁ := V ->ₗ[K] K) .id :=
  ⟨id_separatingLeft, id_separatingRight⟩

@[deprecated (since := "2026-04-02")]
alias dualPairing_nondegenerate := id_nondegenerate

/--
theorem `eval_nondegenerate` / 定理 `eval_nondegenerate`

English:
theorem eval_nondegenerate
  statement: Nondegenerate (Dual.eval K V)
  proof: ⟨eval_separatingLeft, eval_separatingRight⟩

中文:
定理 eval_nondegenerate
  结论: Nondegenerate (Dual.eval K V)
  证明: ⟨eval_separatingLeft, eval_separatingRight⟩

Depends on / 依赖: eval_separatingLeft, eval_separatingRight
-/
theorem eval_nondegenerate : Nondegenerate (Dual.eval K V) :=
  ⟨eval_separatingLeft, eval_separatingRight⟩

variable {K V₁ V₂ : Type*} [Field K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

/--
theorem `dualMap_surjective_of_injective` / 定理 `dualMap_surjective_of_injective`

English:
theorem dualMap_surjective_of_injective
  given: {f : V₁ ->ₗ[K] V₂} (hf : Function.Injective f)
  proof: fun φ =>
  have ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (ker_eq_bot.mpr hf)
  ⟨φ.comp f', ext fun x => congr(φ <| $hf' x)⟩

中文:
定理 dualMap_surjective_of_injective
  条件: {f : V₁ ->ₗ[K] V₂} (hf : Function.Injective f)
  证明: fun φ =>
  have ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (ker_eq_bot.mpr hf)
  ⟨φ.comp f', ext fun x => congr(φ <| $hf' x)⟩
-/
theorem dualMap_surjective_of_injective {f : V₁ ->ₗ[K] V₂} (hf : Function.Injective f) :
    Function.Surjective f.dualMap := fun φ =>
  have ⟨f', hf'⟩ := f.exists_leftInverse_of_injective (ker_eq_bot.mpr hf)
  ⟨φ.comp f', ext fun x => congr(φ <| $hf' x)⟩

/--
theorem `range_dualMap_eq_dualAnnihilator_ker` / 定理 `range_dualMap_eq_dualAnnihilator_ker`

English:
theorem range_dualMap_eq_dualAnnihilator_ker
  given: (f : V₁ ->ₗ[K] V₂)
  proof: range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f
    dualMap_surjective_of_injective (range f).injective_subtype

中文:
定理 range_dualMap_eq_dualAnnihilator_ker
  条件: (f : V₁ ->ₗ[K] V₂)
  证明: range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f
    dualMap_surjective_of_injective (range f).injective_subtype

Depends on / 依赖: dualMap_surjective_of_injective, injective_subtype, range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective
-/
theorem range_dualMap_eq_dualAnnihilator_ker (f : V₁ ->ₗ[K] V₂) :
    LinearMap.range f.dualMap = (LinearMap.ker f).dualAnnihilator :=
range_dualMap_eq_dualAnnihilator_ker_of_subtype_range_surjective f
    dualMap_surjective_of_injective (range f).injective_subtype

/-- For vector spaces, `f.dualMap` is surjective if and only if `f` is injective -/
@[simp]
/--
theorem `dualMap_surjective_iff` / 定理 `dualMap_surjective_iff`

English:
theorem dualMap_surjective_iff
  given: {f : V₁ ->ₗ[K] V₂}
  proof: by
  rw [← LinearMap.range_eq_top]; rw [range_dualMap_eq_dualAnnihilator_ker]; rw [← Submodule.dualAnnihilator_bot]; rw [Subspace.dualAnnihilator_inj]; rw [LinearMap.ker_eq_bot]

中文:
定理 dualMap_surjective_iff
  条件: {f : V₁ ->ₗ[K] V₂}
  证明: by
  rw [← LinearMap.range_eq_top]; rw [range_dualMap_eq_dualAnnihilator_ker]; rw [← Submodule.dualAnnihilator_bot]; rw [Subspace.dualAnnihilator_inj]; rw [LinearMap.ker_eq_bot]

Depends on / 依赖: LinearMap, LinearMap.ker_eq_bot, LinearMap.range_eq_top, Submodule, Submodule.dualAnnihilator_bot, Subspace, Subspace.dualAnnihilator_inj, dualAnnihilator_bot, dualAnnihilator_inj, ker_eq_bot, range_dualMap_eq_dualAnnihilator_ker, range_eq_top
-/
theorem dualMap_surjective_iff {f : V₁ ->ₗ[K] V₂} :
    Function.Surjective f.dualMap ↔ Function.Injective f := by
  rw [← LinearMap.range_eq_top]; rw [range_dualMap_eq_dualAnnihilator_ker]; rw [← Submodule.dualAnnihilator_bot]; rw [Subspace.dualAnnihilator_inj]; rw [LinearMap.ker_eq_bot]

end LinearMap

variable {K V₁ V₂ : Type*} [Field K]
variable [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]

namespace Subspace

open Submodule

/--
theorem `dualPairing_eq` / 定理 `dualPairing_eq`

English:
theorem dualPairing_eq
  given: (W : Subspace K V₁)
  proof: by
  ext
  rfl

中文:
定理 dualPairing_eq
  条件: (W : Subspace K V₁)
  证明: by
  ext
  rfl
-/
theorem dualPairing_eq (W : Subspace K V₁) :
    W.dualPairing = W.quotAnnihilatorEquiv.toLinearMap := by
  ext
  rfl

/--
theorem `dualPairing_nondegenerate` / 定理 `dualPairing_nondegenerate`

English:
theorem dualPairing_nondegenerate
  given: (W : Subspace K V₁)
  statement: W.dualPairing.Nondegenerate
  proof: by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))

中文:
定理 dualPairing_nondegenerate
  条件: (W : Subspace K V₁)
  结论: W.dualPairing.Nondegenerate
  证明: by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))

Depends on / 依赖: LinearEquiv, LinearEquiv.ker, LinearMap, LinearMap.separatingLeft_iff_ker_eq_bot, Quotient, Submodule, Submodule.Quotient.mk, Submodule.dualPairing_apply, W.dualLift, dualLift, dualLift_of_subtype, dualPairing_apply, dualPairing_eq, forall_dual_apply_eq_zero_iff, separatingLeft_iff_ker_eq_bot
-/
theorem dualPairing_nondegenerate (W : Subspace K V₁) : W.dualPairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualPairing_eq]
    apply LinearEquiv.ker
  · intro x h
    rw [← forall_dual_apply_eq_zero_iff K x]
    intro φ
    simpa only [Submodule.dualPairing_apply, dualLift_of_subtype] using
      h (Submodule.Quotient.mk (W.dualLift φ))

/--
theorem `dualCopairing_nondegenerate` / 定理 `dualCopairing_nondegenerate`

English:
theorem dualCopairing_nondegenerate
  given: (W : Subspace K V₁)
  statement: W.dualCopairing.Nondegenerate
  proof: by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff]; rw [SetLike.forall]
    exact id

中文:
定理 dualCopairing_nondegenerate
  条件: (W : Subspace K V₁)
  结论: W.dualCopairing.Nondegenerate
  证明: by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff]; rw [SetLike.forall]
    exact id

Depends on / 依赖: LinearEquiv, LinearEquiv.ker, LinearMap, LinearMap.separatingLeft_iff_ker_eq_bot, Quotient, Quotient.mk_eq_zero, Quotient.quot_mk_eq_mk, SetLike, SetLike.forall, dualCopairing_apply, dualCopairing_eq, forall_mem_dualAnnihilator_apply_eq_zero_iff, mk_eq_zero, quot_mk_eq_mk, separatingLeft_iff_ker_eq_bot
-/
theorem dualCopairing_nondegenerate (W : Subspace K V₁) : W.dualCopairing.Nondegenerate := by
  constructor
  · rw [LinearMap.separatingLeft_iff_ker_eq_bot, dualCopairing_eq]
    apply LinearEquiv.ker
  · rintro ⟨x⟩
    simp only [Quotient.quot_mk_eq_mk, dualCopairing_apply, Quotient.mk_eq_zero]
    rw [← forall_mem_dualAnnihilator_apply_eq_zero_iff]; rw [SetLike.forall]
    exact id

-- Argument from https://math.stackexchange.com/a/2423263/172988
/--
theorem `dualAnnihilator_inf_eq` / 定理 `dualAnnihilator_inf_eq`

English:
theorem dualAnnihilator_inf_eq
  given: (W W' : Subspace K V₁)
  proof: by
  refine le_antisymm ?_ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ ->ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  have : LinearMap.ker F = W ⊓ W' := by simp only [F, LinearMap.ker_prod, ker_mkQ]
  rw [← this]; rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  i

中文:
定理 dualAnnihilator_inf_eq
  条件: (W W' : Subspace K V₁)
  证明: by
  refine le_antisymm ?_ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ ->ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  have : LinearMap.ker F = W ⊓ W' := by simp only [F, LinearMap.ker_prod, ker_mkQ]
  rw [← this]; rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  i

Depends on / 依赖: LinearMap, LinearMap.ker, LinearMap.ker_prod, LinearMap.mem_range, LinearMap.range_dualMap_eq_dualAnnihilator_ker, Submodule, Submodule.mem_sup, Submodule.mkQ, dualProdDualEquivDual, dualQuotEquivDualAnnihilator, ker_mkQ, ker_prod, le_antisymm, mem_range, mem_sup, range_dualMap_eq_dualAnnihilator_ker, sup_dualAnnihilator_le_inf, surjective
-/
theorem dualAnnihilator_inf_eq (W W' : Subspace K V₁) :
    (W ⊓ W').dualAnnihilator = W.dualAnnihilator ⊔ W'.dualAnnihilator := by
  refine le_antisymm ?_ (sup_dualAnnihilator_le_inf W W')
  let F : V₁ ->ₗ[K] (V₁ ⧸ W) × V₁ ⧸ W' := (Submodule.mkQ W).prod (Submodule.mkQ W')
  have : LinearMap.ker F = W ⊓ W' := by simp only [F, LinearMap.ker_prod, ker_mkQ]
  rw [← this]; rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker]
  intro φ
  rw [LinearMap.mem_range]
  rintro ⟨x, rfl⟩
  rw [Submodule.mem_sup]
  obtain ⟨⟨a, b⟩, rfl⟩ := (dualProdDualEquivDual K (V₁ ⧸ W) (V₁ ⧸ W')).surjective x
  obtain ⟨a', rfl⟩ := (dualQuotEquivDualAnnihilator W).symm.surjective a
  obtain ⟨b', rfl⟩ := (dualQuotEquivDualAnnihilator W').symm.surjective b
  use a', a'.property, b', b'.property
  rfl

-- This is also true if `V₁` is finite dimensional since one can restrict `ι` to some subtype
-- for which the infimum and supremum are the same.
-- The obstruction to the `dualAnnihilator_inf_eq` argument carrying through is that we need
-- for `Module.Dual R (Π (i : ι), V ⧸ W i) ≃ₗ[K] Π (i : ι), Module.Dual R (V ⧸ W i)`, which is not
-- true for infinite `ι`. One would need to add additional hypothesis on `W` (for example, it might
-- be true when the family is inf-closed).
-- TODO: generalize to `Sort`
/--
theorem `dualAnnihilator_iInf_eq` / 定理 `dualAnnihilator_iInf_eq`

English:
theorem dualAnnihilator_iInf_eq
  given: {ι : Type*} [Finite ι] (W : ι -> Subspace K V₁)
  proof: by
  revert ι
  apply Finite.induction_empty_option
  · intro α β h hyp W
    rw [← h.iInf_comp]; rw [hyp _]; rw [← h.iSup_comp]
  · intro W
    rw [iSup_of_empty']; rw [iInf_of_isEmpty]; rw [sInf_empty]; rw [sSup_empty]; rw [dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option]; rw [iSup_opti

中文:
定理 dualAnnihilator_iInf_eq
  条件: {ι : 类型} [Finite ι] (W : ι -> Subspace K V₁)
  证明: by
  revert ι
  apply Finite.induction_empty_option
  · intro α β h hyp W
    rw [← h.iInf_comp]; rw [hyp _]; rw [← h.iSup_comp]
  · intro W
    rw [iSup_of_empty']; rw [iInf_of_isEmpty]; rw [sInf_empty]; rw [sSup_empty]; rw [dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option]; rw [iSup_opti

Depends on / 依赖: Finite, Finite.induction_empty_option, dualAnnihilator_inf_eq, dualAnnihilator_top, h.iInf_comp, h.iSup_comp, iInf_comp, iInf_of_isEmpty, iInf_option, iSup_comp, iSup_of_empty, iSup_option, induction_empty_option, revert, sInf_empty, sSup_empty
-/
theorem dualAnnihilator_iInf_eq {ι : Type*} [Finite ι] (W : ι -> Subspace K V₁) :
    (⨅ i : ι, W i).dualAnnihilator = ⨆ i : ι, (W i).dualAnnihilator := by
  revert ι
  apply Finite.induction_empty_option
  · intro α β h hyp W
    rw [← h.iInf_comp]; rw [hyp _]; rw [← h.iSup_comp]
  · intro W
    rw [iSup_of_empty']; rw [iInf_of_isEmpty]; rw [sInf_empty]; rw [sSup_empty]; rw [dualAnnihilator_top]
  · intro α _ h W
    rw [iInf_option]; rw [iSup_option]; rw [dualAnnihilator_inf_eq]; rw [h]

/--
theorem `isCompl_dualAnnihilator` / 定理 `isCompl_dualAnnihilator`

English:
theorem isCompl_dualAnnihilator
  given: {W W' : Subspace K V₁} (h : IsCompl W W')
  proof: by
  rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff] at h ⊢
  rw [← dualAnnihilator_inf_eq]; rw [← dualAnnihilator_sup_eq]; rw [h.1]; rw [h.2]; rw [dualAnnihilator_top]; rw [dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩

中文:
定理 isCompl_dualAnnihilator
  条件: {W W' : Subspace K V₁} (h : IsCompl W W')
  证明: by
  rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff] at h ⊢
  rw [← dualAnnihilator_inf_eq]; rw [← dualAnnihilator_sup_eq]; rw [h.1]; rw [h.2]; rw [dualAnnihilator_top]; rw [dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩

Depends on / 依赖: codisjoint_iff, disjoint_iff, dualAnnihilator_bot, dualAnnihilator_inf_eq, dualAnnihilator_sup_eq, dualAnnihilator_top, isCompl_iff
-/
theorem isCompl_dualAnnihilator {W W' : Subspace K V₁} (h : IsCompl W W') :
    IsCompl W.dualAnnihilator W'.dualAnnihilator := by
  rw [isCompl_iff]; rw [disjoint_iff]; rw [codisjoint_iff] at h ⊢
  rw [← dualAnnihilator_inf_eq]; rw [← dualAnnihilator_sup_eq]; rw [h.1]; rw [h.2]; rw [dualAnnihilator_top]; rw [dualAnnihilator_bot]
  exact ⟨rfl, rfl⟩

/--
Definition of `dualQuotDistrib` / `dualQuotDistrib` 的定义

English:
definition dualQuotDistrib
  signature: [FiniteDimensional K V₁] (W : Subspace K V₁)
  body: W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm

中文:
定义 dualQuotDistrib
  签名: [FiniteDimensional K V₁] (W : Subspace K V₁)
  定义体: W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm

Depends on / 依赖: W.dualQuotEquivDualAnnihilator.trans, W.quotDualEquivAnnihilator.symm, dualQuotEquivDualAnnihilator, quotDualEquivAnnihilator
-/
def dualQuotDistrib [FiniteDimensional K V₁] (W : Subspace K V₁) :
    Module.Dual K (V₁ ⧸ W) ≃ₗ[K] Module.Dual K V₁ ⧸ LinearMap.range W.dualLift :=
  W.dualQuotEquivDualAnnihilator.trans W.quotDualEquivAnnihilator.symm

end Subspace

section FiniteDimensional

open Module LinearMap

namespace LinearMap

@[simp]
/--
theorem `finrank_range_dualMap_eq_finrank_range` / 定理 `finrank_range_dualMap_eq_finrank_range`

English:
theorem finrank_range_dualMap_eq_finrank_range
  given: (f : V₁ ->ₗ[K] V₂)
  proof: by
  rw [congr_arg dualMap (show f = (range f).subtype.comp f.rangeRestrict by rfl)]; rw [← dualMap_comp_dualMap]; rw [range_comp]; rw [range_eq_top.mpr (dualMap_surjective_of_injective (range f).injective_subtype)]; rw [Submodule.map_top]; rw [finrank_range_of_inj]; rw [Subspace.dual_finrank_eq]
  

中文:
定理 finrank_range_dualMap_eq_finrank_range
  条件: (f : V₁ ->ₗ[K] V₂)
  证明: by
  rw [congr_arg dualMap (show f = (range f).subtype.comp f.rangeRestrict by rfl)]; rw [← dualMap_comp_dualMap]; rw [range_comp]; rw [range_eq_top.mpr (dualMap_surjective_of_injective (range f).injective_subtype)]; rw [Submodule.map_top]; rw [finrank_range_of_inj]; rw [Subspace.dual_finrank_eq]
  

Depends on / 依赖: Submodule, Submodule.map_top, Subspace, Subspace.dual_finrank_eq, congr_arg, dualMap, dualMap_comp_dualMap, dualMap_injective_of_surjective, dualMap_surjective_of_injective, dual_finrank_eq, f.rangeRestrict, f.range_rangeRestrict, finrank_range_of_inj, injective_subtype, map_top, rangeRestrict, range_comp, range_eq_top, range_eq_top.mp, range_eq_top.mpr
-/
theorem finrank_range_dualMap_eq_finrank_range (f : V₁ ->ₗ[K] V₂) :
    finrank K (LinearMap.range f.dualMap) = finrank K (LinearMap.range f) := by
  rw [congr_arg dualMap (show f = (range f).subtype.comp f.rangeRestrict by rfl)]; rw [← dualMap_comp_dualMap]; rw [range_comp]; rw [range_eq_top.mpr (dualMap_surjective_of_injective (range f).injective_subtype)]; rw [Submodule.map_top]; rw [finrank_range_of_inj]; rw [Subspace.dual_finrank_eq]
  exact dualMap_injective_of_surjective (range_eq_top.mp f.range_rangeRestrict)

/-- `f.dualMap` is injective if and only if `f` is surjective -/
@[simp]
/--
theorem `dualMap_injective_iff` / 定理 `dualMap_injective_iff`

English:
theorem dualMap_injective_iff
  given: {f : V₁ ->ₗ[K] V₂}
  proof: by
  refine ⟨Function.mtr fun not_surj inj => ?_, dualMap_injective_of_surjective⟩
  rw [← range_eq_top]; rw [← Ne]; rw [← lt_top_iff_ne_top] at not_surj
  obtain ⟨φ, φ0, range_le_ker⟩ := (range f).exists_le_ker_of_lt_top not_surj
  exact φ0 (inj <| ext fun x => range_le_ker ⟨x, rfl⟩)

中文:
定理 dualMap_injective_iff
  条件: {f : V₁ ->ₗ[K] V₂}
  证明: by
  refine ⟨Function.mtr fun not_surj inj => ?_, dualMap_injective_of_surjective⟩
  rw [← range_eq_top]; rw [← Ne]; rw [← lt_top_iff_ne_top] at not_surj
  obtain ⟨φ, φ0, range_le_ker⟩ := (range f).exists_le_ker_of_lt_top not_surj
  exact φ0 (inj <| ext fun x => range_le_ker ⟨x, rfl⟩)

Depends on / 依赖: Function, Function.mtr, dualMap_injective_of_surjective, exists_le_ker_of_lt_top, lt_top_iff_ne_top, not_surj, range_eq_top, range_le_ker
-/
theorem dualMap_injective_iff {f : V₁ ->ₗ[K] V₂} :
    Function.Injective f.dualMap ↔ Function.Surjective f := by
  refine ⟨Function.mtr fun not_surj inj => ?_, dualMap_injective_of_surjective⟩
  rw [← range_eq_top]; rw [← Ne]; rw [← lt_top_iff_ne_top] at not_surj
  obtain ⟨φ, φ0, range_le_ker⟩ := (range f).exists_le_ker_of_lt_top not_surj
  exact φ0 (inj <| ext fun x => range_le_ker ⟨x, rfl⟩)

/-- `f.dualMap` is bijective if and only if `f` is -/
@[simp]
/--
theorem `dualMap_bijective_iff` / 定理 `dualMap_bijective_iff`

English:
theorem dualMap_bijective_iff
  given: {f : V₁ ->ₗ[K] V₂}
  proof: by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]

中文:
定理 dualMap_bijective_iff
  条件: {f : V₁ ->ₗ[K] V₂}
  证明: by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]

Depends on / 依赖: Bijective, Function, Function.Bijective, and_comm, dualMap_injective_iff, dualMap_surjective_iff, simp_rw
-/
theorem dualMap_bijective_iff {f : V₁ ->ₗ[K] V₂} :
    Function.Bijective f.dualMap ↔ Function.Bijective f := by
  simp_rw [Function.Bijective, dualMap_surjective_iff, dualMap_injective_iff, and_comm]

variable {B : V₁ ->ₗ[K] V₂ ->ₗ[K] K}

@[simp]
/--
lemma `dualAnnihilator_ker_eq_range_flip` / 引理 `dualAnnihilator_ker_eq_range_flip`

English:
lemma dualAnnihilator_ker_eq_range_flip
  given: [IsReflexive K V₂]
  proof: by
  change _ = range (B.dualMap.comp (Module.evalEquiv K V₂).toLinearMap)
  rw [← range_dualMap_eq_dualAnnihilator_ker]; rw [range_comp_of_range_eq_top _ (LinearEquiv.range _)]

中文:
引理 dualAnnihilator_ker_eq_range_flip
  条件: [IsReflexive K V₂]
  证明: by
  change _ = range (B.dualMap.comp (Module.evalEquiv K V₂).toLinearMap)
  rw [← range_dualMap_eq_dualAnnihilator_ker]; rw [range_comp_of_range_eq_top _ (LinearEquiv.range _)]

Depends on / 依赖: B.dualMap.comp, LinearEquiv, LinearEquiv.range, Module, Module.evalEquiv, dualMap, evalEquiv, range_comp_of_range_eq_top, range_dualMap_eq_dualAnnihilator_ker, toLinearMap
-/
lemma dualAnnihilator_ker_eq_range_flip [IsReflexive K V₂] :
    (ker B).dualAnnihilator = range B.flip := by
  change _ = range (B.dualMap.comp (Module.evalEquiv K V₂).toLinearMap)
  rw [← range_dualMap_eq_dualAnnihilator_ker]; rw [range_comp_of_range_eq_top _ (LinearEquiv.range _)]

open Function

/--
theorem `flip_injective_iff₁` / 定理 `flip_injective_iff₁`

English:
theorem flip_injective_iff₁
  given: [FiniteDimensional K V₁]
  statement: Injective B.flip ↔ Surjective B
  proof: by
  rw [← dualMap_surjective_iff]; rw [← (evalEquiv K V₁).toEquiv.surjective_comp]; rfl

中文:
定理 flip_injective_iff₁
  条件: [FiniteDimensional K V₁]
  结论: Injective B.flip ↔ Surjective B
  证明: by
  rw [← dualMap_surjective_iff]; rw [← (evalEquiv K V₁).toEquiv.surjective_comp]; rfl

Depends on / 依赖: dualMap_surjective_iff, evalEquiv, surjective_comp, toEquiv, toEquiv.surjective_comp
-/
theorem flip_injective_iff₁ [FiniteDimensional K V₁] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_surjective_iff]; rw [← (evalEquiv K V₁).toEquiv.surjective_comp]; rfl

/--
theorem `flip_injective_iff₂` / 定理 `flip_injective_iff₂`

English:
theorem flip_injective_iff₂
  given: [FiniteDimensional K V₂]
  statement: Injective B.flip ↔ Surjective B
  proof: by
  rw [← dualMap_injective_iff]; exact (evalEquiv K V₂).toEquiv.injective_comp B.dualMap

中文:
定理 flip_injective_iff₂
  条件: [FiniteDimensional K V₂]
  结论: Injective B.flip ↔ Surjective B
  证明: by
  rw [← dualMap_injective_iff]; exact (evalEquiv K V₂).toEquiv.injective_comp B.dualMap

Depends on / 依赖: B.dualMap, dualMap, dualMap_injective_iff, evalEquiv, injective_comp, toEquiv, toEquiv.injective_comp
-/
theorem flip_injective_iff₂ [FiniteDimensional K V₂] : Injective B.flip ↔ Surjective B := by
  rw [← dualMap_injective_iff]; exact (evalEquiv K V₂).toEquiv.injective_comp B.dualMap

/--
theorem `flip_surjective_iff₁` / 定理 `flip_surjective_iff₁`

English:
theorem flip_surjective_iff₁
  given: [FiniteDimensional K V₁]
  statement: Surjective B.flip ↔ Injective B
  proof: flip_injective_iff₂.symm

中文:
定理 flip_surjective_iff₁
  条件: [FiniteDimensional K V₁]
  结论: Surjective B.flip ↔ Injective B
  证明: flip_injective_iff₂.symm
-/
theorem flip_surjective_iff₁ [FiniteDimensional K V₁] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₂.symm

/--
theorem `flip_surjective_iff₂` / 定理 `flip_surjective_iff₂`

English:
theorem flip_surjective_iff₂
  given: [FiniteDimensional K V₂]
  statement: Surjective B.flip ↔ Injective B
  proof: flip_injective_iff₁.symm

中文:
定理 flip_surjective_iff₂
  条件: [FiniteDimensional K V₂]
  结论: Surjective B.flip ↔ Injective B
  证明: flip_injective_iff₁.symm
-/
theorem flip_surjective_iff₂ [FiniteDimensional K V₂] : Surjective B.flip ↔ Injective B :=
  flip_injective_iff₁.symm

/--
theorem `flip_bijective_iff₁` / 定理 `flip_bijective_iff₁`

English:
theorem flip_bijective_iff₁
  given: [FiniteDimensional K V₁]
  statement: Bijective B.flip ↔ Bijective B
  proof: by
  simp_rw [Bijective, flip_injective_iff₁, flip_surjective_iff₁, and_comm]

中文:
定理 flip_bijective_iff₁
  条件: [FiniteDimensional K V₁]
  结论: Bijective B.flip ↔ Bijective B
  证明: by
  simp_rw [Bijective, flip_injective_iff₁, flip_surjective_iff₁, and_comm]

Depends on / 依赖: Bijective, and_comm, simp_rw
-/
theorem flip_bijective_iff₁ [FiniteDimensional K V₁] : Bijective B.flip ↔ Bijective B := by
  simp_rw [Bijective, flip_injective_iff₁, flip_surjective_iff₁, and_comm]

/--
theorem `flip_bijective_iff₂` / 定理 `flip_bijective_iff₂`

English:
theorem flip_bijective_iff₂
  given: [FiniteDimensional K V₂]
  statement: Bijective B.flip ↔ Bijective B
  proof: flip_bijective_iff₁.symm

中文:
定理 flip_bijective_iff₂
  条件: [FiniteDimensional K V₂]
  结论: Bijective B.flip ↔ Bijective B
  证明: flip_bijective_iff₁.symm
-/
theorem flip_bijective_iff₂ [FiniteDimensional K V₂] : Bijective B.flip ↔ Bijective B :=
  flip_bijective_iff₁.symm

end LinearMap

namespace Subspace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/--
theorem `quotDualCoannihilatorToDual_bijective` / 定理 `quotDualCoannihilatorToDual_bijective`

English:
theorem quotDualCoannihilatorToDual_bijective
  given: (W : Subspace K (Dual K V)) [FiniteDimensional K W]
  proof: ⟨W.quotDualCoannihilatorToDual_injective, letI : AddCommGroup W := inferInstance
    flip_injective_iff₂.mp W.flip_quotDualCoannihilatorToDual_injective⟩

中文:
定理 quotDualCoannihilatorToDual_bijective
  条件: (W : Subspace K (Dual K V)) [FiniteDimensional K W]
  证明: ⟨W.quotDualCoannihilatorToDual_injective, letI : AddCommGroup W := inferInstance
    flip_injective_iff₂.mp W.flip_quotDualCoannihilatorToDual_injective⟩

Depends on / 依赖: AddCommGroup, W.flip_quotDualCoannihilatorToDual_injective, W.quotDualCoannihilatorToDual_injective, flip_quotDualCoannihilatorToDual_injective, quotDualCoannihilatorToDual_injective
-/
theorem quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V)) [FiniteDimensional K W] :
    Function.Bijective W.quotDualCoannihilatorToDual :=
  ⟨W.quotDualCoannihilatorToDual_injective, letI : AddCommGroup W := inferInstance
    flip_injective_iff₂.mp W.flip_quotDualCoannihilatorToDual_injective⟩

/--
theorem `flip_quotDualCoannihilatorToDual_bijective` / 定理 `flip_quotDualCoannihilatorToDual_bijective`

English:
theorem flip_quotDualCoannihilatorToDual_bijective
  statement: (W : Subspace K (Dual K V))
  proof: letI : AddCommGroup W := inferInstance
  flip_bijective_iff₂.mpr W.quotDualCoannihilatorToDual_bijective

中文:
定理 flip_quotDualCoannihilatorToDual_bijective
  结论: (W : Subspace K (Dual K V))
  证明: letI : AddCommGroup W := inferInstance
  flip_bijective_iff₂.mpr W.quotDualCoannihilatorToDual_bijective

Depends on / 依赖: AddCommGroup, W.quotDualCoannihilatorToDual_bijective, quotDualCoannihilatorToDual_bijective
-/
theorem flip_quotDualCoannihilatorToDual_bijective (W : Subspace K (Dual K V))
    [FiniteDimensional K W] : Function.Bijective W.quotDualCoannihilatorToDual.flip :=
  letI : AddCommGroup W := inferInstance
  flip_bijective_iff₂.mpr W.quotDualCoannihilatorToDual_bijective

/--
theorem `dualCoannihilator_dualAnnihilator_eq` / 定理 `dualCoannihilator_dualAnnihilator_eq`

English:
theorem dualCoannihilator_dualAnnihilator_eq
  given: {W : Subspace K (Dual K V)} [FiniteDimensional K W]
  proof: let e := (LinearEquiv.ofBijective _ W.flip_quotDualCoannihilatorToDual_bijective).trans
    (Submodule.dualQuotEquivDualAnnihilator _)
  letI : AddCommGroup W := inferInstance
  haveI : FiniteDimensional K W.dualCoannihilator.dualAnnihilator := LinearEquiv.finiteDimensional e
  (eq_of_le_of_finrank_

中文:
定理 dualCoannihilator_dualAnnihilator_eq
  条件: {W : Subspace K (Dual K V)} [FiniteDimensional K W]
  证明: let e := (LinearEquiv.ofBijective _ W.flip_quotDualCoannihilatorToDual_bijective).trans
    (Submodule.dualQuotEquivDualAnnihilator _)
  letI : AddCommGroup W := inferInstance
  haveI : FiniteDimensional K W.dualCoannihilator.dualAnnihilator := LinearEquiv.finiteDimensional e
  (eq_of_le_of_finrank_

Depends on / 依赖: AddCommGroup, FiniteDimensional, LinearEquiv, LinearEquiv.finiteDimensional, LinearEquiv.ofBijective, Submodule, Submodule.dualQuotEquivDualAnnihilator, W.dualCoannihilator.dualAnnihilator, W.flip_quotDualCoannihilatorToDual_bijective, W.le_dualCoannihilator_dualAnnihilator, dualAnnihilator, dualCoannihilator, dualQuotEquivDualAnnihilator, e.finrank_eq, eq_of_le_of_finrank_eq, finiteDimensional, finrank_eq, flip_quotDualCoannihilatorToDual_bijective, le_dualCoannihilator_dualAnnihilator, ofBijective
-/
theorem dualCoannihilator_dualAnnihilator_eq {W : Subspace K (Dual K V)} [FiniteDimensional K W] :
    W.dualCoannihilator.dualAnnihilator = W :=
  let e := (LinearEquiv.ofBijective _ W.flip_quotDualCoannihilatorToDual_bijective).trans
    (Submodule.dualQuotEquivDualAnnihilator _)
  letI : AddCommGroup W := inferInstance
  haveI : FiniteDimensional K W.dualCoannihilator.dualAnnihilator := LinearEquiv.finiteDimensional e
  (eq_of_le_of_finrank_eq W.le_dualCoannihilator_dualAnnihilator e.finrank_eq).symm

/--
theorem `finiteDimensional_quot_dualCoannihilator_iff` / 定理 `finiteDimensional_quot_dualCoannihilator_iff`

English:
theorem finiteDimensional_quot_dualCoannihilator_iff
  given: {W : Submodule K (Dual K V)}
  proof: ⟨fun _ => FiniteDimensional.of_injective _ W.flip_quotDualCoannihilatorToDual_injective,
    fun _ => FiniteDimensional.of_injective _ W.quotDualCoannihilatorToDual_injective⟩

中文:
定理 finiteDimensional_quot_dualCoannihilator_iff
  条件: {W : Submodule K (Dual K V)}
  证明: ⟨fun _ => FiniteDimensional.of_injective _ W.flip_quotDualCoannihilatorToDual_injective,
    fun _ => FiniteDimensional.of_injective _ W.quotDualCoannihilatorToDual_injective⟩

Depends on / 依赖: FiniteDimensional, FiniteDimensional.of_injective, W.flip_quotDualCoannihilatorToDual_injective, W.quotDualCoannihilatorToDual_injective, flip_quotDualCoannihilatorToDual_injective, of_injective, quotDualCoannihilatorToDual_injective
-/
theorem finiteDimensional_quot_dualCoannihilator_iff {W : Submodule K (Dual K V)} :
    FiniteDimensional K (V ⧸ W.dualCoannihilator) ↔ FiniteDimensional K W :=
  ⟨fun _ => FiniteDimensional.of_injective _ W.flip_quotDualCoannihilatorToDual_injective,
    fun _ => FiniteDimensional.of_injective _ W.quotDualCoannihilatorToDual_injective⟩

open OrderDual in
/--
Definition of `orderIsoFiniteCodimDim` / `orderIsoFiniteCodimDim` 的定义

English:
definition orderIsoFiniteCodimDim
  signature: :
  body: toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype

中文:
定义 orderIsoFiniteCodimDim
  签名: :
  定义体: toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype

Depends on / 依赖: Submodule, Submodule.finite_dualAnnihilator_iff.mpr, dualAnnihilator, finite_dualAnnihilator_iff, toDual
-/
def orderIsoFiniteCodimDim :
    {W : Subspace K V // FiniteDimensional K (V ⧸ W)} ≃o
    {W : Subspace K (Dual K V) // FiniteDimensional K W}ᵒᵈ where
  toFun W := toDual ⟨W.1.dualAnnihilator, Submodule.finite_dualAnnihilator_iff.mpr W.2⟩
  invFun W := ⟨(ofDual W).1.dualCoannihilator,
    finiteDimensional_quot_dualCoannihilator_iff.mpr (ofDual W).2⟩
  left_inv _ := Subtype.ext dualAnnihilator_dualCoannihilator_eq
  right_inv W := have := (ofDual W).2; Subtype.ext dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open OrderDual in
/--
Definition of `orderIsoFiniteDimensional` / `orderIsoFiniteDimensional` 的定义

English:
definition orderIsoFiniteDimensional
  signature: [FiniteDimensional K V]
  body: toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

中文:
定义 orderIsoFiniteDimensional
  签名: [FiniteDimensional K V]
  定义体: toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

Depends on / 依赖: W.dualAnnihilator, dualAnnihilator, toDual
-/
def orderIsoFiniteDimensional [FiniteDimensional K V] :
    Subspace K V ≃o (Subspace K (Dual K V))ᵒᵈ where
  toFun W := toDual W.dualAnnihilator
  invFun W := (ofDual W).dualCoannihilator
  left_inv _ := dualAnnihilator_dualCoannihilator_eq
  right_inv _ := dualCoannihilator_dualAnnihilator_eq
  map_rel_iff' := dualAnnihilator_le_dualAnnihilator_iff

open Submodule in
/--
theorem `dualAnnihilator_dualAnnihilator_eq_map` / 定理 `dualAnnihilator_dualAnnihilator_eq_map`

English:
theorem dualAnnihilator_dualAnnihilator_eq_map
  given: (W : Subspace K V) [FiniteDimensional K W]
  proof: by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  have := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  have := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw

中文:
定理 dualAnnihilator_dualAnnihilator_eq_map
  条件: (W : Subspace K V) [FiniteDimensional K W]
  证明: by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  have := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  have := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw

Depends on / 依赖: Free.chooseBasis, LinearEquiv, LinearEquiv.finiteDimensional, W.dualAnnihilator.dualAnnihilator, W.dualAnnihilator.dualQuotEquivDualAnnihilator, W.quotAnnihilatorEquiv.symm, chooseBasis, dualAnnihilator, dualQuotEquivDualAnnihilator, e1.finiteDimensional, e1.finrank_eq, e2.finrank_eq, eq_of_le_of_finrank_eq, equivMapOfInjective, eval_apply_injective, finiteDimensional, finrank_eq, map_le_dualAnnihilator_dualAnnihilator, quotAnnihilatorEquiv, toDualEquiv
-/
theorem dualAnnihilator_dualAnnihilator_eq_map (W : Subspace K V) [FiniteDimensional K W] :
    W.dualAnnihilator.dualAnnihilator = W.map (Dual.eval K V) := by
  let e1 := (Free.chooseBasis K W).toDualEquiv ≪≫ₗ W.quotAnnihilatorEquiv.symm
  have := e1.finiteDimensional
  let e2 := (Free.chooseBasis K _).toDualEquiv ≪≫ₗ W.dualAnnihilator.dualQuotEquivDualAnnihilator
  have := LinearEquiv.finiteDimensional (V₂ := W.dualAnnihilator.dualAnnihilator) e2
  rw [eq_of_le_of_finrank_eq (map_le_dualAnnihilator_dualAnnihilator W)]
  rw [← (equivMapOfInjective _ (eval_apply_injective K (V := V)) W).finrank_eq]; rw [e1.finrank_eq]
  exact e2.finrank_eq

/--
theorem `map_dualCoannihilator` / 定理 `map_dualCoannihilator`

English:
theorem map_dualCoannihilator
  given: (W : Subspace K (Dual K V)) [FiniteDimensional K V]
  proof: by
  rw [← dualAnnihilator_dualAnnihilator_eq_map]; rw [dualCoannihilator_dualAnnihilator_eq]

中文:
定理 map_dualCoannihilator
  条件: (W : Subspace K (Dual K V)) [FiniteDimensional K V]
  证明: by
  rw [← dualAnnihilator_dualAnnihilator_eq_map]; rw [dualCoannihilator_dualAnnihilator_eq]

Depends on / 依赖: dualAnnihilator_dualAnnihilator_eq_map, dualCoannihilator_dualAnnihilator_eq
-/
theorem map_dualCoannihilator (W : Subspace K (Dual K V)) [FiniteDimensional K V] :
    W.dualCoannihilator.map (Dual.eval K V) = W.dualAnnihilator := by
  rw [← dualAnnihilator_dualAnnihilator_eq_map]; rw [dualCoannihilator_dualAnnihilator_eq]

end Subspace

end FiniteDimensional

end VectorSpace

/--
theorem `span_flip_eq_top_iff_linearIndependent` / 定理 `span_flip_eq_top_iff_linearIndependent`

English:
theorem span_flip_eq_top_iff_linearIndependent
  given: {ι α F} [Finite ι] [Field F] {f : ι -> α -> F}
  proof: by
  rw [linearIndependent_iff_ker]; rw [← Submodule.map_eq_top_iff (e := Finsupp.llift F F F ι)]; rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := map ..)]; rw [dualAnnihilator_eq_top_iff]
  congr!
  rw [SetLike.ext'_iff]; rw [map_span]; rw [Submodule.coe_dualCoannihilator_span]; rw [← Set

中文:
定理 span_flip_eq_top_iff_linearIndependent
  条件: {ι α F} [Finite ι] [Field F] {f : ι -> α -> F}
  证明: by
  rw [linearIndependent_iff_ker]; rw [← Submodule.map_eq_top_iff (e := Finsupp.llift F F F ι)]; rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := map ..)]; rw [dualAnnihilator_eq_top_iff]
  congr!
  rw [SetLike.ext'_iff]; rw [map_span]; rw [Submodule.coe_dualCoannihilator_span]; rw [← Set

Depends on / 依赖: Finset, Finset.sum_apply, Finsupp, Finsupp.linearCombination, Finsupp.llift, Finsupp.sum, Set.range_comp, SetLike, SetLike.ext, Submodule, Submodule.coe_dualCoannihilator_span, Submodule.map_eq_top_iff, Subspace, Subspace.dualCoannihilator_dualAnnihilator_eq, _iff, coe_dualCoannihilator_span, dualAnnihilator_eq_top_iff, dualCoannihilator_dualAnnihilator_eq, funext_iff, linearCombination
-/
theorem span_flip_eq_top_iff_linearIndependent {ι α F} [Finite ι] [Field F] {f : ι -> α -> F} :
    span F (Set.range <| flip f) = ⊤ ↔ LinearIndependent F f := by
  rw [linearIndependent_iff_ker]; rw [← Submodule.map_eq_top_iff (e := Finsupp.llift F F F ι)]; rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := map ..)]; rw [dualAnnihilator_eq_top_iff]
  congr!
  rw [SetLike.ext'_iff]; rw [map_span]; rw [Submodule.coe_dualCoannihilator_span]; rw [← Set.range_comp]
  ext
  simp [funext_iff, Finsupp.linearCombination, Finsupp.sum, Finset.sum_apply, flip]

/--
lemma `Module.exists_dual_forall_apply_eq_one` / 引理 `Module.exists_dual_forall_apply_eq_one`

English:
lemma Module.exists_dual_forall_apply_eq_one
  statement: {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  proof: by
  replace hli : LinearIndepOn K id (v '' s) := LinearIndepOn.id_image hli
let b : Basis _ K V := .mk (hli.linearIndepOn_extend (Set.subset_univ _)) by
simpa using hli.span_extend_eq_span Set.subset_univ _
  refine ⟨b.constr K 1, fun i hi => ?_⟩
  replace hi : v i in hli.extend (Set.subset_univ _)

中文:
引理 Module.exists_dual_forall_apply_eq_one
  结论: {ι K V : 类型} [Field K] [AddCommGroup V] [Module K V]
  证明: by
  replace hli : LinearIndepOn K id (v '' s) := LinearIndepOn.id_image hli
let b : Basis _ K V := .mk (hli.linearIndepOn_extend (Set.subset_univ _)) by
simpa using hli.span_extend_eq_span Set.subset_univ _
  refine ⟨b.constr K 1, fun i hi => ?_⟩
  replace hi : v i in hli.extend (Set.subset_univ _)

Depends on / 依赖: LinearIndepOn, LinearIndepOn.id_image, Set.mem_image_of_mem, Set.subset_univ, b.constr, constr, extend, hli.extend, hli.linearIndepOn_extend, hli.span_extend_eq_span, hli.subset_extend, id_image, linearIndepOn_extend, mem_image_of_mem, replace, span_extend_eq_span, subset_extend, subset_univ
-/
lemma Module.exists_dual_forall_apply_eq_one {ι K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {s : Set ι} {v : ι -> V} (hli : LinearIndepOn K v s) :
    exists f : Dual K V, forall i in s, f (v i) = 1 := by
  replace hli : LinearIndepOn K id (v '' s) := LinearIndepOn.id_image hli
let b : Basis _ K V := .mk (hli.linearIndepOn_extend (Set.subset_univ _)) by
simpa using hli.span_extend_eq_span Set.subset_univ _
  refine ⟨b.constr K 1, fun i hi => ?_⟩
  replace hi : v i in hli.extend (Set.subset_univ _) :=
hli.subset_extend _ Set.mem_image_of_mem v hi
  let ri : hli.extend (Set.subset_univ _) := ⟨v i, hi⟩
  have : b ri = v i := by simp [b, ri]
  simp [← this]

namespace TensorProduct

variable (R A : Type*) (M : Type*) (N : Type*)
variable {ι κ : Type*}
variable [DecidableEq ι] [DecidableEq κ]
variable [Fintype ι] [Fintype κ]

open TensorProduct

attribute [local ext] TensorProduct.ext

open TensorProduct

open LinearMap

section

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module R N]

/--
Definition of `dualDistrib` / `dualDistrib` 的定义

English:
definition dualDistrib
  signature: : Dual R M otimes[R] Dual R N ->ₗ[R] Dual R (M otimes[R] N)
  body: compRight _ (TensorProduct.lid R R) ∘ₗ homTensorHomMap (.id R) M N R R

中文:
定义 dualDistrib
  签名: : Dual R M otimes[R] Dual R N ->ₗ[R] Dual R (M otimes[R] N)
  定义体: compRight _ (TensorProduct.lid R R) ∘ₗ homTensorHomMap (.id R) M N R R

Depends on / 依赖: TensorProduct, TensorProduct.lid, compRight, homTensorHomMap
-/
def dualDistrib : Dual R M otimes[R] Dual R N ->ₗ[R] Dual R (M otimes[R] N) :=
  compRight _ (TensorProduct.lid R R) ∘ₗ homTensorHomMap (.id R) M N R R

variable {R M N}

@[simp]
/--
theorem `dualDistrib_apply` / 定理 `dualDistrib_apply`

English:
theorem dualDistrib_apply
  given: (f : Dual R M) (g : Dual R N) (m : M) (n : N)
  proof: rfl

中文:
定理 dualDistrib_apply
  条件: (f : Dual R M) (g : Dual R N) (m : M) (n : N)
  证明: rfl
-/
theorem dualDistrib_apply (f : Dual R M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R M N (f otimesₜ g) (m otimesₜ n) = f m * g n :=
  rfl

/--
lemma `dualDistrib_apply_comm` / 引理 `dualDistrib_apply_comm`

English:
lemma dualDistrib_apply_comm
  given: (w : Dual R N otimes[R] Dual R M) (z : M otimes[R] N)
  proof: by
  induction w <;> induction z <;> simp_all [mul_comm]

中文:
引理 dualDistrib_apply_comm
  条件: (w : Dual R N otimes[R] Dual R M) (z : M otimes[R] N)
  证明: by
  induction w <;> induction z <;> simp_all [mul_comm]

Depends on / 依赖: mul_comm
-/
lemma dualDistrib_apply_comm (w : Dual R N otimes[R] Dual R M) (z : M otimes[R] N) :
    dualDistrib R N M w (TensorProduct.comm R M N z) =
      dualDistrib R M N (TensorProduct.comm R _ _ w) z := by
  induction w <;> induction z <;> simp_all [mul_comm]

end

namespace AlgebraTensorModule
variable [CommSemiring R] [CommSemiring A] [Algebra R A] [AddCommMonoid M] [AddCommMonoid N]
variable [Module R M] [Module A M] [Module R N] [IsScalarTower R A M]

/--
Definition of `dualDistrib` / `dualDistrib` 的定义

English:
definition dualDistrib
  signature: : Dual A M otimes[R] Dual R N ->ₗ[A] Dual A (M otimes[R] N)
  body: compRight _ (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

中文:
定义 dualDistrib
  签名: : Dual A M otimes[R] Dual R N ->ₗ[A] Dual A (M otimes[R] N)
  定义体: compRight _ (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

Depends on / 依赖: Algebra, Algebra.TensorProduct.rid, TensorProduct, compRight, homTensorHomMap, toLinearMap
-/
def dualDistrib : Dual A M otimes[R] Dual R N ->ₗ[A] Dual A (M otimes[R] N) :=
  compRight _ (Algebra.TensorProduct.rid R A A).toLinearMap ∘ₗ homTensorHomMap R A A M N A R

variable {R M N}

@[simp]
/--
theorem `dualDistrib_apply` / 定理 `dualDistrib_apply`

English:
theorem dualDistrib_apply
  given: (f : Dual A M) (g : Dual R N) (m : M) (n : N)
  proof: rfl

中文:
定理 dualDistrib_apply
  条件: (f : Dual A M) (g : Dual R N) (m : M) (n : N)
  证明: rfl
-/
theorem dualDistrib_apply (f : Dual A M) (g : Dual R N) (m : M) (n : N) :
    dualDistrib R A M N (f otimesₜ g) (m otimesₜ n) = g n • f m :=
  rfl

end AlgebraTensorModule

end TensorProduct
