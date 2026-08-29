/-
Copyright (c) 2024 Brendan Murphy. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brendan Murphy
-/
module

public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness

/-!
# Reducing a module modulo an element of the ring

Given a commutative ring `R` and an element `r : R`, the association
`M ↦ M ⧸ rM` extends to a functor on the category of `R`-modules. This functor
is isomorphic to the functor of tensoring by `R ⧸ (r)` on either side, but can
be more convenient to work with since we can work with quotient types instead
of fiddling with simple tensors.

## Tags

module, commutative algebra
-/

@[expose] public section

open scoped Pointwise

variable {R} [CommRing R] (r : R) (M : Type*) {M' M''}
    [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M'']

/--
Definition of `QuotSMulTop` / `QuotSMulTop` 的定义

English:
abbreviation QuotSMulTop
  body: M ⧸ r • (⊤ : Submodule R M)

中文:
缩写 QuotSMulTop
  定义体: M ⧸ r • (⊤ : Submodule R M)

Depends on / 依赖: Submodule
-/
abbrev QuotSMulTop := M ⧸ r • (⊤ : Submodule R M)

namespace QuotSMulTop

open Submodule Function TensorProduct

/--
Definition of `congr` / `congr` 的定义

English:
definition congr
  signature: (e : M' ≃ₗ[R] M'')
  body: Submodule.Quotient.equiv (r • ⊤) (r • ⊤) e
    (Submodule.map_pointwise_smul r _ e.toLinearMap).trans (by simp)

中文:
定义 congr
  签名: (e : M' ≃ₗ[R] M'')
  定义体: Submodule.Quotient.equiv (r • ⊤) (r • ⊤) e
    (Submodule.map_pointwise_smul r _ e.toLinearMap).trans (by simp)
-/
protected def congr (e : M' ≃ₗ[R] M'') : QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r M'' :=
Submodule.Quotient.equiv (r • ⊤) (r • ⊤) e
    (Submodule.map_pointwise_smul r _ e.toLinearMap).trans (by simp)

/--
Definition of `equivQuotTensor` / `equivQuotTensor` 的定义

English:
definition equivQuotTensor
  signature: :
  body: quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (quotTensorEquivQuotSMul M _).symm

中文:
定义 equivQuotTensor
  签名: :
  定义体: quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (quotTensorEquivQuotSMul M _).symm

Depends on / 依赖: ideal_span_singleton_smul, quotEquivOfEq, quotTensorEquivQuotSMul
-/
noncomputable def equivQuotTensor :
    QuotSMulTop r M ≃ₗ[R] (R ⧸ Ideal.span {r}) otimes[R] M :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (quotTensorEquivQuotSMul M _).symm

/--
Definition of `equivTensorQuot` / `equivTensorQuot` 的定义

English:
definition equivTensorQuot
  signature: :
  body: quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (tensorQuotEquivQuotSMul M _).symm

中文:
定义 equivTensorQuot
  签名: :
  定义体: quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (tensorQuotEquivQuotSMul M _).symm

Depends on / 依赖: ideal_span_singleton_smul, quotEquivOfEq, tensorQuotEquivQuotSMul
-/
noncomputable def equivTensorQuot :
    QuotSMulTop r M ≃ₗ[R] M otimes[R] (R ⧸ Ideal.span {r}) :=
  quotEquivOfEq _ _ (ideal_span_singleton_smul _ _).symm ≪≫ₗ
    (tensorQuotEquivQuotSMul M _).symm

variable {M}

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: : (M ->ₗ[R] M') ->ₗ[R] QuotSMulTop r M ->ₗ[R] QuotSMulTop r M'
  body: Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
map_le_iff_le_comap.mp le_of_eq_of_le (map_pointwise_smul _ _ _)
      smul_mono_right r le_top

@[simp]

中文:
定义 map
  签名: : (M ->ₗ[R] M') ->ₗ[R] QuotSMulTop r M ->ₗ[R] QuotSMulTop r M'
  定义体: Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
map_le_iff_le_comap.mp le_of_eq_of_le (map_pointwise_smul _ _ _)
      smul_mono_right r le_top

@[simp]

Depends on / 依赖: LinearMap, LinearMap.id.codRestrict, Submodule, Submodule.mapQLinear, codRestrict, le_of_eq_of_le, le_top, mapQLinear, map_le_iff_le_comap, map_le_iff_le_comap.mp, map_pointwise_smul, smul_mono_right
-/
def map : (M ->ₗ[R] M') ->ₗ[R] QuotSMulTop r M ->ₗ[R] QuotSMulTop r M' :=
  Submodule.mapQLinear _ _ ∘ₗ LinearMap.id.codRestrict _ fun _ =>
map_le_iff_le_comap.mp le_of_eq_of_le (map_pointwise_smul _ _ _)
      smul_mono_right r le_top

@[simp]
/--
lemma `map_apply_mk` / 引理 `map_apply_mk`

English:
lemma map_apply_mk
  given: (f : M ->ₗ[R] M') (x : M)
  proof: rfl

中文:
引理 map_apply_mk
  条件: (f : M ->ₗ[R] M') (x : M)
  证明: rfl
-/
lemma map_apply_mk (f : M ->ₗ[R] M') (x : M) :
    map r f (Submodule.Quotient.mk x) =
      (Submodule.Quotient.mk (f x) : QuotSMulTop r M') := rfl

-- weirdly expensive to typecheck the type here?
/--
lemma `map_comp_mkQ` / 引理 `map_comp_mkQ`

English:
lemma map_comp_mkQ
  given: (f : M ->ₗ[R] M')
  proof: by
  ext; rfl

中文:
引理 map_comp_mkQ
  条件: (f : M ->ₗ[R] M')
  证明: by
  ext; rfl
-/
lemma map_comp_mkQ (f : M ->ₗ[R] M') :
    map r f ∘ₗ mkQ (r • ⊤) = mkQ (r • ⊤) ∘ₗ f := by
  ext; rfl

variable (M)

@[simp]
/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: map r (LinearMap.id : M ->ₗ[R] M) = .id
  proof: DFunLike.ext _ _ (mkQ_surjective _).forall.mpr fun _ => rfl

中文:
引理 map_id
  结论: map r (LinearMap.id : M ->ₗ[R] M) = .id
  证明: DFunLike.ext _ _ (mkQ_surjective _).forall.mpr fun _ => rfl

Depends on / 依赖: DFunLike, DFunLike.ext, forall.mpr, mkQ_surjective
-/
lemma map_id : map r (LinearMap.id : M ->ₗ[R] M) = .id :=
DFunLike.ext _ _ (mkQ_surjective _).forall.mpr fun _ => rfl

variable {M}

@[simp]
/--
lemma `map_comp` / 引理 `map_comp`

English:
lemma map_comp
  given: (g : M' ->ₗ[R] M'') (f : M ->ₗ[R] M')
  proof: DFunLike.ext _ _ (mkQ_surjective _).forall.mpr fun _ => rfl

中文:
引理 map_comp
  条件: (g : M' ->ₗ[R] M'') (f : M ->ₗ[R] M')
  证明: DFunLike.ext _ _ (mkQ_surjective _).forall.mpr fun _ => rfl

Depends on / 依赖: CompHaus, CompHaus.epi_iff_surjective, CompHaus.of, CompHausLike, CompHausLike.ofHom, CompactT2, CompactT2.Projective.extremallyDisconnected, DFunLike, DFunLike.ext, Projective, Projective.factors, apply_fun, epi_iff_surjective, extremallyDisconnected, factors, forall.mpr, h.hom.hom, mkQ_surjective
-/
lemma map_comp (g : M' ->ₗ[R] M'') (f : M ->ₗ[R] M') :
    map r (g ∘ₗ f) = map r g ∘ₗ map r f :=
DFunLike.ext _ _ (mkQ_surjective _).forall.mpr fun _ => rfl

/--
lemma `equivQuotTensor_naturality_mk` / 引理 `equivQuotTensor_naturality_mk`

English:
lemma equivQuotTensor_naturality_mk
  given: (f : M ->ₗ[R] M') (x : M)
  proof: (LinearMap.lTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

中文:
引理 equivQuotTensor_naturality_mk
  条件: (f : M ->ₗ[R] M') (x : M)
  证明: (LinearMap.lTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

Depends on / 依赖: Ideal.span, LinearMap, LinearMap.lTensor_tmul, lTensor_tmul
-/
lemma equivQuotTensor_naturality_mk (f : M ->ₗ[R] M') (x : M) :
    equivQuotTensor r M' (map r f (Submodule.Quotient.mk x)) =
      f.lTensor (R ⧸ Ideal.span {r})
        (equivQuotTensor r M (Submodule.Quotient.mk x)) :=
  (LinearMap.lTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

/--
lemma `equivQuotTensor_naturality` / 引理 `equivQuotTensor_naturality`

English:
lemma equivQuotTensor_naturality
  given: (f : M ->ₗ[R] M')
  proof: quot_hom_ext _ _ _ (equivQuotTensor_naturality_mk r f)

中文:
引理 equivQuotTensor_naturality
  条件: (f : M ->ₗ[R] M')
  证明: quot_hom_ext _ _ _ (equivQuotTensor_naturality_mk r f)

Depends on / 依赖: equivQuotTensor_naturality_mk, quot_hom_ext
-/
lemma equivQuotTensor_naturality (f : M ->ₗ[R] M') :
    equivQuotTensor r M' ∘ₗ map r f =
      f.lTensor (R ⧸ Ideal.span {r}) ∘ₗ equivQuotTensor r M :=
  quot_hom_ext _ _ _ (equivQuotTensor_naturality_mk r f)

/--
lemma `equivTensorQuot_naturality_mk` / 引理 `equivTensorQuot_naturality_mk`

English:
lemma equivTensorQuot_naturality_mk
  given: (f : M ->ₗ[R] M') (x : M)
  proof: (LinearMap.rTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

中文:
引理 equivTensorQuot_naturality_mk
  条件: (f : M ->ₗ[R] M') (x : M)
  证明: (LinearMap.rTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

Depends on / 依赖: Ideal.span, LinearMap, LinearMap.rTensor_tmul, rTensor_tmul
-/
lemma equivTensorQuot_naturality_mk (f : M ->ₗ[R] M') (x : M) :
    equivTensorQuot r M' (map r f (Submodule.Quotient.mk x)) =
      f.rTensor (R ⧸ Ideal.span {r})
        (equivTensorQuot r M (Submodule.Quotient.mk x)) :=
  (LinearMap.rTensor_tmul (R ⧸ Ideal.span {r}) f 1 x).symm

/--
lemma `equivTensorQuot_naturality` / 引理 `equivTensorQuot_naturality`

English:
lemma equivTensorQuot_naturality
  given: (f : M ->ₗ[R] M')
  proof: quot_hom_ext _ _ _ (equivTensorQuot_naturality_mk r f)

中文:
引理 equivTensorQuot_naturality
  条件: (f : M ->ₗ[R] M')
  证明: quot_hom_ext _ _ _ (equivTensorQuot_naturality_mk r f)

Depends on / 依赖: ExtremallyDisconnected, equivTensorQuot_naturality_mk, quot_hom_ext
-/
lemma equivTensorQuot_naturality (f : M ->ₗ[R] M') :
    equivTensorQuot r M' ∘ₗ map r f =
      f.rTensor (R ⧸ Ideal.span {r}) ∘ₗ equivTensorQuot r M :=
  quot_hom_ext _ _ _ (equivTensorQuot_naturality_mk r f)

/--
lemma `map_surjective` / 引理 `map_surjective`

English:
lemma map_surjective
  given: {f : M ->ₗ[R] M'} (hf : Surjective f)
  statement: Surjective (map r f)
  proof: have H₁ := (mkQ_surjective (r • ⊤ : Submodule R M')).comp hf
@Surjective.of_comp _ _ _ _ (mkQ (r • ⊤ : Submodule R M)) by
    rwa [← LinearMap.coe_comp, map_comp_mkQ, LinearMap.coe_comp]

中文:
引理 map_surjective
  条件: {f : M ->ₗ[R] M'} (hf : Surjective f)
  结论: Surjective (map r f)
  证明: have H₁ := (mkQ_surjective (r • ⊤ : Submodule R M')).comp hf
@Surjective.of_comp _ _ _ _ (mkQ (r • ⊤ : Submodule R M)) by
    rwa [← LinearMap.coe_comp, map_comp_mkQ, LinearMap.coe_comp]

Depends on / 依赖: LinearMap, LinearMap.coe_comp, Submodule, Surjective, Surjective.of_comp, coe_comp, map_comp_mkQ, mkQ_surjective, of_comp
-/
lemma map_surjective {f : M ->ₗ[R] M'} (hf : Surjective f) : Surjective (map r f) :=
  have H₁ := (mkQ_surjective (r • ⊤ : Submodule R M')).comp hf
@Surjective.of_comp _ _ _ _ (mkQ (r • ⊤ : Submodule R M)) by
    rwa [← LinearMap.coe_comp, map_comp_mkQ, LinearMap.coe_comp]

/--
lemma `map_exact` / 引理 `map_exact`

English:
lemma map_exact
  statement: {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''}
  proof: (Exact.iff_of_ladder_linearEquiv (equivQuotTensor_naturality r f).symm
                             (equivQuotTensor_naturality r g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r}) hfg hg)

中文:
引理 map_exact
  结论: {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''}
  证明: (Exact.iff_of_ladder_linearEquiv (equivQuotTensor_naturality r f).symm
                             (equivQuotTensor_naturality r g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r}) hfg hg)

Depends on / 依赖: Exact.iff_of_ladder_linearEquiv, Ideal.span, X.prop, equivQuotTensor_naturality, iff_of_ladder_linearEquiv, lTensor_exact
-/
lemma map_exact {f : M ->ₗ[R] M'} {g : M' ->ₗ[R] M''}
    (hfg : Exact f g) (hg : Surjective g) : Exact (map r f) (map r g) :=
  (Exact.iff_of_ladder_linearEquiv (equivQuotTensor_naturality r f).symm
                             (equivQuotTensor_naturality r g).symm).mp
    (lTensor_exact (R ⧸ Ideal.span {r}) hfg hg)

variable (M M')

/--
Definition of `tensorQuotSMulTopEquivQuotSMulTop` / `tensorQuotSMulTopEquivQuotSMulTop` 的定义

English:
definition tensorQuotSMulTopEquivQuotSMulTop
  signature: :
  body: (equivTensorQuot r M').lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R ⧸ Ideal.span {r})).symm ≪≫ₗ
      (equivTensorQuot r (M otimes[R] M')).symm

中文:
定义 tensorQuotSMulTopEquivQuotSMulTop
  签名: :
  定义体: (equivTensorQuot r M').lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R ⧸ Ideal.span {r})).symm ≪≫ₗ
      (equivTensorQuot r (M otimes[R] M')).symm

Depends on / 依赖: Ideal.span, TensorProduct, TensorProduct.assoc, equivTensorQuot, lTensor, otimes
-/
noncomputable def tensorQuotSMulTopEquivQuotSMulTop :
    M otimes[R] QuotSMulTop r M' ≃ₗ[R] QuotSMulTop r (M otimes[R] M') :=
  (equivTensorQuot r M').lTensor M ≪≫ₗ
    (TensorProduct.assoc R M M' (R ⧸ Ideal.span {r})).symm ≪≫ₗ
      (equivTensorQuot r (M otimes[R] M')).symm

/--
Definition of `quotSMulTopTensorEquivQuotSMulTop` / `quotSMulTopTensorEquivQuotSMulTop` 的定义

English:
definition quotSMulTopTensorEquivQuotSMulTop
  signature: :
  body: (equivQuotTensor r M').rTensor M ≪≫ₗ
    TensorProduct.assoc R (R ⧸ Ideal.span {r}) M' M ≪≫ₗ
      (equivQuotTensor r (M' otimes[R] M)).symm

中文:
定义 quotSMulTopTensorEquivQuotSMulTop
  签名: :
  定义体: (equivQuotTensor r M').rTensor M ≪≫ₗ
    TensorProduct.assoc R (R ⧸ Ideal.span {r}) M' M ≪≫ₗ
      (equivQuotTensor r (M' otimes[R] M)).symm

Depends on / 依赖: Ideal.span, TensorProduct, TensorProduct.assoc, equivQuotTensor, otimes, rTensor
-/
noncomputable def quotSMulTopTensorEquivQuotSMulTop :
    QuotSMulTop r M' otimes[R] M ≃ₗ[R] QuotSMulTop r (M' otimes[R] M) :=
  (equivQuotTensor r M').rTensor M ≪≫ₗ
    TensorProduct.assoc R (R ⧸ Ideal.span {r}) M' M ≪≫ₗ
      (equivQuotTensor r (M' otimes[R] M)).symm

/--
Definition of `algebraMapTensorEquivTensorQuotSMulTop` / `algebraMapTensorEquivTensorQuotSMulTop` 的定义

English:
definition algebraMapTensorEquivTensorQuotSMulTop
  signature: (S : Type*) [CommRing S] [Algebra R S]
  body: Submodule.quotEquivOfEq _ _ (by simp [Ideal.map_span, ideal_span_singleton_smul]) ≪≫ₗ
    tensorQuotMapSMulEquivTensorQuot M S (Ideal.span {r}) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ (ideal_span_singleton_smul r _)).baseChange R S _ _

中文:
定义 algebraMapTensorEquivTensorQuotSMulTop
  签名: (S : 类型) [CommRing S] [Algebra R S]
  定义体: Submodule.quotEquivOfEq _ _ (by simp [Ideal.map_span, ideal_span_singleton_smul]) ≪≫ₗ
    tensorQuotMapSMulEquivTensorQuot M S (Ideal.span {r}) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ (ideal_span_singleton_smul r _)).baseChange R S _ _

Depends on / 依赖: Ideal.map_span, Ideal.span, Submodule, Submodule.quotEquivOfEq, baseChange, ideal_span_singleton_smul, map_span, quotEquivOfEq, tensorQuotMapSMulEquivTensorQuot
-/
noncomputable def algebraMapTensorEquivTensorQuotSMulTop (S : Type*) [CommRing S] [Algebra R S] :
    QuotSMulTop ((algebraMap R S) r) (S otimes[R] M) ≃ₗ[S] S otimes[R] QuotSMulTop r M :=
  Submodule.quotEquivOfEq _ _ (by simp [Ideal.map_span, ideal_span_singleton_smul]) ≪≫ₗ
    tensorQuotMapSMulEquivTensorQuot M S (Ideal.span {r}) ≪≫ₗ
      (Submodule.quotEquivOfEq _ _ (ideal_span_singleton_smul r _)).baseChange R S _ _

/--
lemma `mem_annihilator` / 引理 `mem_annihilator`

English:
lemma mem_annihilator
  given: (x : R)
  statement: x in Module.annihilator R (QuotSMulTop x M)
  proof: by
  refine Module.mem_annihilator.mpr (fun m => ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

中文:
引理 mem_annihilator
  条件: (x : R)
  结论: x in Module.annihilator R (QuotSMulTop x M)
  证明: by
  refine Module.mem_annihilator.mpr (fun m => ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

Depends on / 依赖: Module, Module.mem_annihilator.mpr, Quotient, Submodule, Submodule.Quotient.mk_smul, Submodule.Quotient.mk_surjective, Submodule.smul_mem_pointwise_smul, mem_annihilator, mk_smul, mk_surjective, smul_mem_pointwise_smul
-/
lemma mem_annihilator (x : R) : x in Module.annihilator R (QuotSMulTop x M) := by
  refine Module.mem_annihilator.mpr (fun m => ?_)
  rcases Submodule.Quotient.mk_surjective _ m with ⟨m', hm'⟩
  simpa [← hm', ← Submodule.Quotient.mk_smul] using Submodule.smul_mem_pointwise_smul m' x ⊤ trivial

end QuotSMulTop
