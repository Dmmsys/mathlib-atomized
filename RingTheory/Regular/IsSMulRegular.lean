/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.QuotSMulTop

/-!
# Lemmas about the `IsSMulRegular` Predicate

For modules over a ring the proposition `IsSMulRegular r M` is equivalent to
`r` being a *non-zero-divisor*, i.e. `r • x = 0` only if `x = 0` for `x ∈ M`.
This specific result is `isSMulRegular_iff_smul_eq_zero_imp_eq_zero`.
Lots of results starting from this, especially ones about quotients (which
don't make sense without some algebraic assumptions), are in this file.
We don't pollute the `Mathlib/Algebra/Regular/SMul.lean` file with these because
it's supposed to import a minimal amount of the algebraic hierarchy.

## Tags

module, regular element, commutative algebra
-/

public section

section Congr

variable {R S M N} [Semiring R] [Semiring S] {σ : R ->+* S} {σ' : S ->+* R}
    [RingHomInvPair σ σ'] [RingHomInvPair σ' σ] [AddCommMonoid M] [Module R M]

/--
lemma `LinearEquiv.isSMulRegular_congr'` / 引理 `LinearEquiv.isSMulRegular_congr'`

English:
lemma LinearEquiv.isSMulRegular_congr'
  statement: [AddCommMonoid N] [Module S N]
  proof: e.toEquiv.isSMulRegular_congr (e.map_smul' r)

中文:
引理 LinearEquiv.isSMulRegular_congr'
  结论: [AddCommMonoid N] [Module S N]
  证明: e.toEquiv.isSMulRegular_congr (e.map_smul' r)

Depends on / 依赖: e.map_smul, e.toEquiv.isSMulRegular_congr, isSMulRegular_congr, map_smul, toEquiv
-/
lemma LinearEquiv.isSMulRegular_congr' [AddCommMonoid N] [Module S N]
    (e : M ≃ₛₗ[σ] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N (σ r) :=
  e.toEquiv.isSMulRegular_congr (e.map_smul' r)

/--
lemma `LinearEquiv.isSMulRegular_congr` / 引理 `LinearEquiv.isSMulRegular_congr`

English:
lemma LinearEquiv.isSMulRegular_congr
  statement: [AddCommMonoid N] [Module R N]
  proof: e.isSMulRegular_congr' r

中文:
引理 LinearEquiv.isSMulRegular_congr
  结论: [AddCommMonoid N] [Module R N]
  证明: e.isSMulRegular_congr' r

Depends on / 依赖: e.isSMulRegular_congr, isSMulRegular_congr
-/
lemma LinearEquiv.isSMulRegular_congr [AddCommMonoid N] [Module R N]
    (e : M ≃ₗ[R] N) (r : R) : IsSMulRegular M r ↔ IsSMulRegular N r :=
  e.isSMulRegular_congr' r

end Congr

variable {R S M M' M'' : Type*}

/--
lemma `IsSMulRegular.submodule` / 引理 `IsSMulRegular.submodule`

English:
lemma IsSMulRegular.submodule
  statement: [Semiring R] [AddCommMonoid M] [Module R M]
  proof: h.of_injective N.subtype N.injective_subtype

中文:
引理 IsSMulRegular.submodule
  结论: [Semiring R] [AddCommMonoid M] [Module R M]
  证明: h.of_injective N.subtype N.injective_subtype

Depends on / 依赖: N.injective_subtype, N.subtype, h.of_injective, injective_subtype, of_injective, subtype
-/
lemma IsSMulRegular.submodule [Semiring R] [AddCommMonoid M] [Module R M]
    (N : Submodule R M) (r : R) (h : IsSMulRegular M r) : IsSMulRegular N r :=
  h.of_injective N.subtype N.injective_subtype

section TensorProduct

open scoped TensorProduct

variable (M) [CommRing R] [AddCommGroup M] [AddCommGroup M']
    [Module R M] [Module R M'] [Module.Flat R M] {r : R}
    (h : IsSMulRegular M' r)
include h

/--
lemma `IsSMulRegular.lTensor` / 引理 `IsSMulRegular.lTensor`

English:
lemma IsSMulRegular.lTensor
  statement: IsSMulRegular (M otimes[R] M') r
  proof: have h1 := congrArg DFunLike.coe (LinearMap.lTensor_smul_action M M' r)
  h1.subst (Module.Flat.lTensor_preserves_injective_linearMap _ h)

中文:
引理 IsSMulRegular.lTensor
  结论: IsSMulRegular (M otimes[R] M') r
  证明: have h1 := congrArg DFunLike.coe (LinearMap.lTensor_smul_action M M' r)
  h1.subst (Module.Flat.lTensor_preserves_injective_linearMap _ h)

Depends on / 依赖: DFunLike, DFunLike.coe, LinearMap, LinearMap.lTensor_smul_action, Module, Module.Flat.lTensor_preserves_injective_linearMap, h1.subst, lTensor_preserves_injective_linearMap, lTensor_smul_action
-/
lemma IsSMulRegular.lTensor : IsSMulRegular (M otimes[R] M') r :=
  have h1 := congrArg DFunLike.coe (LinearMap.lTensor_smul_action M M' r)
  h1.subst (Module.Flat.lTensor_preserves_injective_linearMap _ h)

/--
lemma `IsSMulRegular.rTensor` / 引理 `IsSMulRegular.rTensor`

English:
lemma IsSMulRegular.rTensor
  statement: IsSMulRegular (M' otimes[R] M) r
  proof: have h1 := congrArg DFunLike.coe (LinearMap.rTensor_smul_action M M' r)
  h1.subst (Module.Flat.rTensor_preserves_injective_linearMap _ h)

中文:
引理 IsSMulRegular.rTensor
  结论: IsSMulRegular (M' otimes[R] M) r
  证明: have h1 := congrArg DFunLike.coe (LinearMap.rTensor_smul_action M M' r)
  h1.subst (Module.Flat.rTensor_preserves_injective_linearMap _ h)

Depends on / 依赖: DFunLike, DFunLike.coe, LinearMap, LinearMap.rTensor_smul_action, Module, Module.Flat.rTensor_preserves_injective_linearMap, h1.subst, rTensor_preserves_injective_linearMap, rTensor_smul_action
-/
lemma IsSMulRegular.rTensor : IsSMulRegular (M' otimes[R] M) r :=
  have h1 := congrArg DFunLike.coe (LinearMap.rTensor_smul_action M M' r)
  h1.subst (Module.Flat.rTensor_preserves_injective_linearMap _ h)

end TensorProduct

section Ring

variable [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (N : Submodule R M) (r : R)

/--
lemma `isSMulRegular_submodule_iff_right_eq_zero_of_smul` / 引理 `isSMulRegular_submodule_iff_right_eq_zero_of_smul`

English:
lemma isSMulRegular_submodule_iff_right_eq_zero_of_smul
  proof: isSMulRegular_iff_right_eq_zero_of_smul.trans
Subtype.forall.trans by
      simp only [SetLike.mk_smul_mk, Submodule.mk_eq_zero]

中文:
引理 isSMulRegular_submodule_iff_right_eq_zero_of_smul
  证明: isSMulRegular_iff_right_eq_zero_of_smul.trans
Subtype.forall.trans by
      simp only [SetLike.mk_smul_mk, Submodule.mk_eq_zero]

Depends on / 依赖: SetLike, SetLike.mk_smul_mk, Submodule, Submodule.mk_eq_zero, Subtype, Subtype.forall.trans, isSMulRegular_iff_right_eq_zero_of_smul, isSMulRegular_iff_right_eq_zero_of_smul.trans, mk_eq_zero, mk_smul_mk
-/
lemma isSMulRegular_submodule_iff_right_eq_zero_of_smul :
    IsSMulRegular N r ↔ forall x in N, r • x = 0 -> x = 0 :=
isSMulRegular_iff_right_eq_zero_of_smul.trans
Subtype.forall.trans by
      simp only [SetLike.mk_smul_mk, Submodule.mk_eq_zero]

/--
lemma `isSMulRegular_quotient_iff_mem_of_smul_mem` / 引理 `isSMulRegular_quotient_iff_mem_of_smul_mem`

English:
lemma isSMulRegular_quotient_iff_mem_of_smul_mem
  proof: isSMulRegular_iff_right_eq_zero_of_smul.trans
N.mkQ_surjective.forall.trans by
      simp_rw [← map_smul, N.mkQ_apply, Submodule.Quotient.mk_eq_zero]

中文:
引理 isSMulRegular_quotient_iff_mem_of_smul_mem
  证明: isSMulRegular_iff_right_eq_zero_of_smul.trans
N.mkQ_surjective.forall.trans by
      simp_rw [← map_smul, N.mkQ_apply, Submodule.Quotient.mk_eq_zero]

Depends on / 依赖: N.mkQ_apply, N.mkQ_surjective.forall.trans, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, isSMulRegular_iff_right_eq_zero_of_smul, isSMulRegular_iff_right_eq_zero_of_smul.trans, map_smul, mkQ_apply, mkQ_surjective, mk_eq_zero, simp_rw
-/
lemma isSMulRegular_quotient_iff_mem_of_smul_mem :
    IsSMulRegular (M ⧸ N) r ↔ forall x : M, r • x in N -> x in N :=
isSMulRegular_iff_right_eq_zero_of_smul.trans
N.mkQ_surjective.forall.trans by
      simp_rw [← map_smul, N.mkQ_apply, Submodule.Quotient.mk_eq_zero]

variable {N r}

/--
lemma `mem_of_isSMulRegular_quotient_of_smul_mem` / 引理 `mem_of_isSMulRegular_quotient_of_smul_mem`

English:
lemma mem_of_isSMulRegular_quotient_of_smul_mem
  statement: (h1 : IsSMulRegular (M ⧸ N) r)
  proof: (isSMulRegular_quotient_iff_mem_of_smul_mem N r).mp h1 x h2

中文:
引理 mem_of_isSMulRegular_quotient_of_smul_mem
  结论: (h1 : IsSMulRegular (M ⧸ N) r)
  证明: (isSMulRegular_quotient_iff_mem_of_smul_mem N r).mp h1 x h2

Depends on / 依赖: isSMulRegular_quotient_iff_mem_of_smul_mem
-/
lemma mem_of_isSMulRegular_quotient_of_smul_mem (h1 : IsSMulRegular (M ⧸ N) r)
    {x : M} (h2 : r • x in N) : x in N :=
  (isSMulRegular_quotient_iff_mem_of_smul_mem N r).mp h1 x h2

/--
lemma `isSMulRegular_of_range_eq_ker` / 引理 `isSMulRegular_of_range_eq_ker`

English:
lemma isSMulRegular_of_range_eq_ker
  statement: {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''}
  proof: by
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
obtain ⟨y, ⟨⟩⟩ := (congrArg (x in ·) hfg).mpr h2.right_eq_zero_of_smul
(g.map_smul r x).symm.trans (congrArg _ hx).trans g.map_zero
  refine (congrArg f (h1.right_eq_zero_of_smul ?_)).trans f.map_zero
exact hf (f.map_smul r y).trans 

中文:
引理 isSMulRegular_of_range_eq_ker
  结论: {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''}
  证明: by
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
obtain ⟨y, ⟨⟩⟩ := (congrArg (x in ·) hfg).mpr h2.right_eq_zero_of_smul
(g.map_smul r x).symm.trans (congrArg _ hx).trans g.map_zero
  refine (congrArg f (h1.right_eq_zero_of_smul ?_)).trans f.map_zero
exact hf (f.map_smul r y).trans 

Depends on / 依赖: IsSMulRegular, IsSMulRegular.of_right_eq_zero_of_smul, f.map_smul, f.map_zero, f.map_zero.symm, g.map_smul, g.map_zero, h1.right_eq_zero_of_smul, h2.right_eq_zero_of_smul, hx.trans, map_smul, map_zero, of_right_eq_zero_of_smul, right_eq_zero_of_smul, symm.trans
-/
lemma isSMulRegular_of_range_eq_ker {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''}
    (hf : Function.Injective f) (hfg : LinearMap.range f = LinearMap.ker g)
    (h1 : IsSMulRegular M r) (h2 : IsSMulRegular M'' r) :
    IsSMulRegular M' r := by
  refine IsSMulRegular.of_right_eq_zero_of_smul ?_
  intro x hx
obtain ⟨y, ⟨⟩⟩ := (congrArg (x in ·) hfg).mpr h2.right_eq_zero_of_smul
(g.map_smul r x).symm.trans (congrArg _ hx).trans g.map_zero
  refine (congrArg f (h1.right_eq_zero_of_smul ?_)).trans f.map_zero
exact hf (f.map_smul r y).trans hx.trans f.map_zero.symm

/--
lemma `isSMulRegular_of_isSMulRegular_on_submodule_on_quotient` / 引理 `isSMulRegular_of_isSMulRegular_on_submodule_on_quotient`

English:
lemma isSMulRegular_of_isSMulRegular_on_submodule_on_quotient
  proof: isSMulRegular_of_range_eq_ker N.injective_subtype
    (N.range_subtype.trans N.ker_mkQ.symm) h1 h2

中文:
引理 isSMulRegular_of_isSMulRegular_on_submodule_on_quotient
  证明: isSMulRegular_of_range_eq_ker N.injective_subtype
    (N.range_subtype.trans N.ker_mkQ.symm) h1 h2

Depends on / 依赖: N.injective_subtype, N.ker_mkQ.symm, N.range_subtype.trans, injective_subtype, isSMulRegular_of_range_eq_ker, ker_mkQ, range_subtype
-/
lemma isSMulRegular_of_isSMulRegular_on_submodule_on_quotient
    (h1 : IsSMulRegular N r) (h2 : IsSMulRegular (M ⧸ N) r) : IsSMulRegular M r :=
  isSMulRegular_of_range_eq_ker N.injective_subtype
    (N.range_subtype.trans N.ker_mkQ.symm) h1 h2

end Ring

section CommRing

open Submodule Pointwise

variable (M) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup M''] [Module R M'']
    (N : Submodule R M) (r : R)

variable (R) in
/--
lemma `biUnion_associatedPrimes_eq_compl_regular` / 引理 `biUnion_associatedPrimes_eq_compl_regular`

English:
lemma biUnion_associatedPrimes_eq_compl_regular
  given: [IsNoetherianRing R]
  proof: Eq.trans (biUnion_associatedPrimes_eq_zero_divisors R M) by
    simp_rw [Set.compl_ofPred, isSMulRegular_iff_right_eq_zero_of_smul,
      not_forall, exists_prop, and_comm]

中文:
引理 biUnion_associatedPrimes_eq_compl_regular
  条件: [IsNoetherianRing R]
  证明: Eq.trans (biUnion_associatedPrimes_eq_zero_divisors R M) by
    simp_rw [Set.compl_ofPred, isSMulRegular_iff_right_eq_zero_of_smul,
      not_forall, exists_prop, and_comm]

Depends on / 依赖: Eq.trans, Set.compl_ofPred, and_comm, biUnion_associatedPrimes_eq_zero_divisors, compl_ofPred, exists_prop, isSMulRegular_iff_right_eq_zero_of_smul, not_forall, simp_rw
-/
lemma biUnion_associatedPrimes_eq_compl_regular [IsNoetherianRing R] :
    ⋃ p in associatedPrimes R M, p = { r : R | IsSMulRegular M r }ᶜ :=
Eq.trans (biUnion_associatedPrimes_eq_zero_divisors R M) by
    simp_rw [Set.compl_ofPred, isSMulRegular_iff_right_eq_zero_of_smul,
      not_forall, exists_prop, and_comm]

/--
lemma `isSMulRegular_iff_ker_lsmul_eq_bot` / 引理 `isSMulRegular_iff_ker_lsmul_eq_bot`

English:
lemma isSMulRegular_iff_ker_lsmul_eq_bot
  proof: isSMulRegular_iff_torsionBy_eq_bot M r

中文:
引理 isSMulRegular_iff_ker_lsmul_eq_bot
  证明: isSMulRegular_iff_torsionBy_eq_bot M r

Depends on / 依赖: isSMulRegular_iff_torsionBy_eq_bot
-/
lemma isSMulRegular_iff_ker_lsmul_eq_bot :
    IsSMulRegular M r ↔ LinearMap.ker (LinearMap.lsmul R M r) = ⊥ :=
  isSMulRegular_iff_torsionBy_eq_bot M r

variable {M}

/--
lemma `isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule` / 引理 `isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule`

English:
lemma isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule
  proof: Iff.trans (isSMulRegular_submodule_iff_right_eq_zero_of_smul N r)
Iff.symm Iff.trans disjoint_comm disjoint_def

中文:
引理 isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule
  证明: Iff.trans (isSMulRegular_submodule_iff_right_eq_zero_of_smul N r)
Iff.symm Iff.trans disjoint_comm disjoint_def

Depends on / 依赖: Iff.symm, Iff.trans, disjoint_comm, disjoint_def, isSMulRegular_submodule_iff_right_eq_zero_of_smul
-/
lemma isSMulRegular_on_submodule_iff_disjoint_ker_lsmul_submodule :
    IsSMulRegular N r ↔ Disjoint (LinearMap.ker (LinearMap.lsmul R M r)) N :=
Iff.trans (isSMulRegular_submodule_iff_right_eq_zero_of_smul N r)
Iff.symm Iff.trans disjoint_comm disjoint_def

/--
lemma `isSMulRegular_on_quot_iff_lsmul_comap_le` / 引理 `isSMulRegular_on_quot_iff_lsmul_comap_le`

English:
lemma isSMulRegular_on_quot_iff_lsmul_comap_le
  proof: isSMulRegular_quotient_iff_mem_of_smul_mem N r

中文:
引理 isSMulRegular_on_quot_iff_lsmul_comap_le
  证明: isSMulRegular_quotient_iff_mem_of_smul_mem N r

Depends on / 依赖: isSMulRegular_quotient_iff_mem_of_smul_mem
-/
lemma isSMulRegular_on_quot_iff_lsmul_comap_le :
    IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) <= N :=
  isSMulRegular_quotient_iff_mem_of_smul_mem N r

/--
lemma `isSMulRegular_on_quot_iff_lsmul_comap_eq` / 引理 `isSMulRegular_on_quot_iff_lsmul_comap_eq`

English:
lemma isSMulRegular_on_quot_iff_lsmul_comap_eq
  proof: Iff.trans (isSMulRegular_on_quot_iff_lsmul_comap_le N r)
    LE.le.ge_iff_eq' (fun _ => N.smul_mem r)

中文:
引理 isSMulRegular_on_quot_iff_lsmul_comap_eq
  证明: Iff.trans (isSMulRegular_on_quot_iff_lsmul_comap_le N r)
    LE.le.ge_iff_eq' (fun _ => N.smul_mem r)

Depends on / 依赖: Iff.trans, LE.le.ge_iff_eq, N.smul_mem, ge_iff_eq, isSMulRegular_on_quot_iff_lsmul_comap_le, smul_mem
-/
lemma isSMulRegular_on_quot_iff_lsmul_comap_eq :
    IsSMulRegular (M ⧸ N) r ↔ N.comap (LinearMap.lsmul R M r) = N :=
Iff.trans (isSMulRegular_on_quot_iff_lsmul_comap_le N r)
    LE.le.ge_iff_eq' (fun _ => N.smul_mem r)

variable {r}

/--
lemma `IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul` / 引理 `IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul`

English:
lemma IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul
  proof: by
  intro (h : Function.Injective (DistribSMul.toLinearMap R M r))
  rw [isSMulRegular_on_quot_iff_lsmul_comap_le]; rw [← map_le_map_iff_of_injective h]; rw [← LinearMap.lsmul_eq_distribSMultoLinearMap]; rw [map_comap_eq]; rw [LinearMap.range_eq_map]; rfl

中文:
引理 IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul
  证明: by
  intro (h : Function.Injective (DistribSMul.toLinearMap R M r))
  rw [isSMulRegular_on_quot_iff_lsmul_comap_le]; rw [← map_le_map_iff_of_injective h]; rw [← LinearMap.lsmul_eq_distribSMultoLinearMap]; rw [map_comap_eq]; rw [LinearMap.range_eq_map]; rfl

Depends on / 依赖: DistribSMul, DistribSMul.toLinearMap, Function, Function.Injective, Injective, LinearMap, LinearMap.lsmul_eq_distribSMultoLinearMap, LinearMap.range_eq_map, isSMulRegular_on_quot_iff_lsmul_comap_le, lsmul_eq_distribSMultoLinearMap, map_comap_eq, map_le_map_iff_of_injective, range_eq_map, toLinearMap
-/
lemma IsSMulRegular.isSMulRegular_on_quot_iff_smul_top_inf_eq_smul :
    IsSMulRegular M r -> (IsSMulRegular (M ⧸ N) r ↔ r • ⊤ ⊓ N <= r • N) := by
  intro (h : Function.Injective (DistribSMul.toLinearMap R M r))
  rw [isSMulRegular_on_quot_iff_lsmul_comap_le]; rw [← map_le_map_iff_of_injective h]; rw [← LinearMap.lsmul_eq_distribSMultoLinearMap]; rw [map_comap_eq]; rw [LinearMap.range_eq_map]; rfl

/--
lemma `isSMulRegular_of_ker_lsmul_eq_bot` / 引理 `isSMulRegular_of_ker_lsmul_eq_bot`

English:
lemma isSMulRegular_of_ker_lsmul_eq_bot
  proof: (isSMulRegular_iff_ker_lsmul_eq_bot M r).mpr h

中文:
引理 isSMulRegular_of_ker_lsmul_eq_bot
  证明: (isSMulRegular_iff_ker_lsmul_eq_bot M r).mpr h

Depends on / 依赖: isSMulRegular_iff_ker_lsmul_eq_bot
-/
lemma isSMulRegular_of_ker_lsmul_eq_bot
    (h : LinearMap.ker (LinearMap.lsmul R M r) = ⊥) :
    IsSMulRegular M r :=
  (isSMulRegular_iff_ker_lsmul_eq_bot M r).mpr h

variable {N} in
/--
lemma `smul_top_inf_eq_smul_of_isSMulRegular_on_quot` / 引理 `smul_top_inf_eq_smul_of_isSMulRegular_on_quot`

English:
lemma smul_top_inf_eq_smul_of_isSMulRegular_on_quot
  proof: by
  convert! map_mono ∘ (isSMulRegular_on_quot_iff_lsmul_comap_le N r).mp using 2
  exact Eq.trans (congrArg (· ⊓ N) (map_top _)) (map_comap_eq _ _).symm

中文:
引理 smul_top_inf_eq_smul_of_isSMulRegular_on_quot
  证明: by
  convert! map_mono ∘ (isSMulRegular_on_quot_iff_lsmul_comap_le N r).mp using 2
  exact Eq.trans (congrArg (· ⊓ N) (map_top _)) (map_comap_eq _ _).symm

Depends on / 依赖: Eq.trans, convert, isSMulRegular_on_quot_iff_lsmul_comap_le, map_comap_eq, map_mono, map_top
-/
lemma smul_top_inf_eq_smul_of_isSMulRegular_on_quot :
    IsSMulRegular (M ⧸ N) r -> r • ⊤ ⊓ N <= r • N := by
  convert! map_mono ∘ (isSMulRegular_on_quot_iff_lsmul_comap_le N r).mp using 2
  exact Eq.trans (congrArg (· ⊓ N) (map_top _)) (map_comap_eq _ _).symm

-- Who knew this didn't rely on exactness at the right!?
set_option backward.isDefEq.respectTransparency.types false in
open Function in
/--
lemma `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last` / 引理 `QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last`

English:
lemma QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
  proof: suffices IsSMulRegular (M'' ⧸ LinearMap.range f₂) r by
    dsimp [map, mapQLinear]
    rw [Exact.exact_mapQ_iff h₁₂]; rw [map_pointwise_smul]; rw [Submodule.map_top]; rw [inf_comm]
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot this
h.of_injective _ LinearMap.ker_eq_bot.mp
    ker_liftQ_eq_

中文:
引理 QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
  证明: suffices IsSMulRegular (M'' ⧸ LinearMap.range f₂) r by
    dsimp [map, mapQLinear]
    rw [Exact.exact_mapQ_iff h₁₂]; rw [map_pointwise_smul]; rw [Submodule.map_top]; rw [inf_comm]
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot this
h.of_injective _ LinearMap.ker_eq_bot.mp
    ker_liftQ_eq_

Depends on / 依赖: Exact.exact_mapQ_iff, IsSMulRegular, LinearMap, LinearMap.ker_eq_bot.mp, LinearMap.range, Submodule, Submodule.map_top, exact_mapQ_iff, h.of_injective, inf_comm, ker_eq_bot, ker_liftQ_eq_bot, linearMap_ker_eq, linearMap_ker_eq.symm, mapQLinear, map_pointwise_smul, map_top, of_injective, smul_top_inf_eq_smul_of_isSMulRegular_on_quot
-/
lemma QuotSMulTop.map_first_exact_on_four_term_exact_of_isSMulRegular_last
    {M'''} [AddCommGroup M'''] [Module R M''']
    {r : R} {f₁ : M ->ₗ[R] M'} {f₂ : M' ->ₗ[R] M''} {f₃ : M'' ->ₗ[R] M'''}
    (h₁₂ : Exact f₁ f₂) (h₂₃ : Exact f₂ f₃) (h : IsSMulRegular M''' r) :
    Exact (map r f₁) (map r f₂) :=
  suffices IsSMulRegular (M'' ⧸ LinearMap.range f₂) r by
    dsimp [map, mapQLinear]
    rw [Exact.exact_mapQ_iff h₁₂]; rw [map_pointwise_smul]; rw [Submodule.map_top]; rw [inf_comm]
    exact smul_top_inf_eq_smul_of_isSMulRegular_on_quot this
h.of_injective _ LinearMap.ker_eq_bot.mp
    ker_liftQ_eq_bot' _ _ h₂₃.linearMap_ker_eq.symm

end CommRing
