/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.DirectSum.LinearMap
public import Mathlib.Algebra.Lie.InvariantForm
public import Mathlib.Algebra.Lie.Weights.Cartan
public import Mathlib.Algebra.Lie.Weights.Linear
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.PID

/-!
# The trace and Killing forms of a Lie algebra.

Let `L` be a Lie algebra with coefficients in a commutative ring `R`. Suppose `M` is a finite, free
`R`-module and we have a representation `φ : L → End M`. This data induces a natural bilinear form
`B` on `L`, called the trace form associated to `M`; it is defined as `B(x, y) = Tr (φ x) (φ y)`.

In the special case that `M` is `L` itself and `φ` is the adjoint representation, the trace form
is known as the Killing form.

We define the trace / Killing form in this file and prove some basic properties.

## Main definitions

* `LieModule.traceForm`: a finite, free representation of a Lie algebra `L` induces a bilinear form
  on `L` called the trace form.
* `LieModule.traceForm_eq_zero_of_isNilpotent`: the trace form induced by a nilpotent
  representation of a Lie algebra vanishes.
* `killingForm`: the adjoint representation of a (finite, free) Lie algebra `L` induces a bilinear
  form on `L` via the trace form construction.
-/

@[expose] public section

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "φ" => LieModule.toEnd R L M

open LinearMap (trace)
open Set Module

namespace LieModule

attribute [local instance 100] LieRing.ofAssociativeRing

/--
Definition of `traceForm` / `traceForm` 的定义

English:
definition traceForm
  signature: : LinearMap.BilinForm R L
  body: ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

中文:
定义 traceForm
  签名: : 线性映射.BilinForm R L
  定义体: ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

Depends on / 依赖: LinearMap, LinearMap.mul, _mul_mk, _of_map_mul, f.toLinearMap, map_mul, toLinearMap
-/
noncomputable def traceForm : LinearMap.BilinForm R L :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

/--
lemma `traceForm_apply_apply` / 引理 `traceForm_apply_apply`

English:
lemma traceForm_apply_apply
  given: (x y : L)
  proof: rfl

中文:
引理 traceForm_apply_apply
  条件: (x y : L)
  证明: rfl

Depends on / 依赖: Submonoid, Submonoid.smul_def, _cancel, _smul, smul_def, smul_inj
-/
lemma traceForm_apply_apply (x y : L) :
    traceForm R L M x y = trace R _ (φ x ∘ₗ φ y) :=
  rfl

/--
lemma `traceForm_comm` / 引理 `traceForm_comm`

English:
lemma traceForm_comm
  given: (x y : L)
  statement: traceForm R L M x y = traceForm R L M y x
  proof: LinearMap.trace_mul_comm R (φ x) (φ y)

中文:
引理 traceForm_comm
  条件: (x y : L)
  结论: traceForm R L M x y = traceForm R L M y x
  证明: LinearMap.trace_mul_comm R (φ x) (φ y)

Depends on / 依赖: LinearMap, LinearMap.trace_mul_comm, _eq_iff, smul_zero, trace_mul_comm
-/
lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)

/--
lemma `traceForm_isSymm` / 引理 `traceForm_isSymm`

English:
lemma traceForm_isSymm
  statement: LinearMap.IsSymm (traceForm R L M)
  proof: ⟨LieModule.traceForm_comm R L M⟩

中文:
引理 traceForm_isSymm
  结论: 线性映射.是Symm (traceForm R L M)
  证明: ⟨LieModule.traceForm_comm R L M⟩

Depends on / 依赖: LieModule, LieModule.traceForm_comm, _eq_mk, _iff, _zero, eq_comm, one_smul, simp_rw, smul_zero, traceForm_comm
-/
lemma traceForm_isSymm : LinearMap.IsSymm (traceForm R L M) := ⟨LieModule.traceForm_comm R L M⟩

/--
lemma `traceForm_flip` / 引理 `traceForm_flip`

English:
lemma traceForm_flip
  statement: LinearMap.flip (traceForm R L M) = traceForm R L M
  proof: Eq.symm LinearMap.ext₂ traceForm_comm R L M

中文:
引理 traceForm_flip
  结论: 线性映射.flip (traceForm R L M) = traceForm R L M
  证明: Eq.symm LinearMap.ext₂ traceForm_comm R L M
-/
@[simp] lemma traceForm_flip : LinearMap.flip (traceForm R L M) = traceForm R L M :=
Eq.symm LinearMap.ext₂ traceForm_comm R L M

/--
lemma `traceForm_apply_lie_apply` / 引理 `traceForm_apply_lie_apply`

English:
lemma traceForm_apply_lie_apply
  given: (x y z : L)
  proof: by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← Module.End.mul_eq_comp]
  · simp only [sub_mul, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← Module.End.mul_eq_comp]

中文:
引理 traceForm_apply_lie_apply
  条件: (x y z : L)
  证明: by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← Module.End.mul_eq_comp]
  · simp only [sub_mul, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← Module.End.mul_eq_comp]

Depends on / 依赖: IsLocalization, IsLocalization.smul_mk, LieHom, LieHom.map_lie, LinearMap, LinearMap.trace_mul_cycle, Module, Module.End.mul_eq_comp, Ring.lie_def, Submonoid, Submonoid.smul_def, _cancel, _self, algebraMap_smul, conv_lhs, lie_def, map_lie, map_smul, map_sub, mul_assoc
-/
lemma traceForm_apply_lie_apply (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = traceForm R L M x ⁅y, z⁆ := by
  calc traceForm R L M ⁅x, y⁆ z
      = trace R _ (φ ⁅x, y⁆ ∘ₗ φ z) := by simp only [traceForm_apply_apply]
    _ = trace R _ ((φ x * φ y - φ y * φ x) * φ z) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ y * (φ x * φ z)) := ?_
    _ = trace R _ (φ x * (φ y * φ z)) - trace R _ (φ x * (φ z * φ y)) := ?_
    _ = traceForm R L M x ⁅y, z⁆ := ?_
  · simp only [LieHom.map_lie, Ring.lie_def, ← Module.End.mul_eq_comp]
  · simp only [sub_mul, map_sub, mul_assoc]
  · simp only [LinearMap.trace_mul_cycle' R (φ x) (φ z) (φ y)]
  · simp only [traceForm_apply_apply, LieHom.map_lie, Ring.lie_def, mul_sub, map_sub,
      ← Module.End.mul_eq_comp]

/--
lemma `traceForm_apply_lie_apply'` / 引理 `traceForm_apply_lie_apply'`

English:
lemma traceForm_apply_lie_apply'
  given: (x y z : L)
  proof: calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]

中文:
引理 traceForm_apply_lie_apply'
  条件: (x y z : L)
  证明: calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]

Depends on / 依赖: LinearMap, LinearMap.neg_apply, lie_skew, map_neg, neg_apply, traceForm, traceForm_apply_lie_apply
-/
lemma traceForm_apply_lie_apply' (x y z : L) :
    traceForm R L M ⁅x, y⁆ z = - traceForm R L M y ⁅x, z⁆ :=
  calc traceForm R L M ⁅x, y⁆ z
      = - traceForm R L M ⁅y, x⁆ z := by rw [← lie_skew x y, map_neg, LinearMap.neg_apply]
    _ = - traceForm R L M y ⁅x, z⁆ := by rw [traceForm_apply_lie_apply]

/--
lemma `traceForm_lieInvariant` / 引理 `traceForm_lieInvariant`

English:
lemma traceForm_lieInvariant
  statement: (traceForm R L M).lieInvariant L
  proof: by
  intro x y z
  rw [← lie_skew]; rw [map_neg]; rw [LinearMap.neg_apply]; rw [LieModule.traceForm_apply_lie_apply R L M]

中文:
引理 traceForm_lieInvariant
  结论: (traceForm R L M).lieInvariant L
  证明: by
  intro x y z
  rw [← lie_skew]; rw [map_neg]; rw [LinearMap.neg_apply]; rw [LieModule.traceForm_apply_lie_apply R L M]

Depends on / 依赖: IsLocalizedModule, IsLocalizedModule.surj, LieModule, LieModule.traceForm_apply_lie_apply, LinearMap, LinearMap.neg_apply, _eq_iff, _eq_iff.mpr, e.symm, lie_skew, map_neg, neg_apply, traceForm_apply_lie_apply
-/
lemma traceForm_lieInvariant : (traceForm R L M).lieInvariant L := by
  intro x y z
  rw [← lie_skew]; rw [map_neg]; rw [LinearMap.neg_apply]; rw [LieModule.traceForm_apply_lie_apply R L M]

/--
lemma `lie_traceForm_eq_zero` / 引理 `lie_traceForm_eq_zero`

English:
lemma lie_traceForm_eq_zero
  given: (x : L)
  statement: ⁅x, traceForm R L M⁆ = 0
  proof: by
  ext y z
  rw [LieHom.lie_apply]; rw [LinearMap.sub_apply]; rw [Module.Dual.lie_apply]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [traceForm_apply_lie_apply']; rw [sub_self]

中文:
引理 lie_traceForm_eq_zero
  条件: (x : L)
  结论: ⁅x, traceForm R L M⁆ = 0
  证明: by
  ext y z
  rw [LieHom.lie_apply]; rw [LinearMap.sub_apply]; rw [Module.Dual.lie_apply]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [traceForm_apply_lie_apply']; rw [sub_self]
-/
@[simp] lemma lie_traceForm_eq_zero (x : L) : ⁅x, traceForm R L M⁆ = 0 := by
  ext y z
  rw [LieHom.lie_apply]; rw [LinearMap.sub_apply]; rw [Module.Dual.lie_apply]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]; rw [traceForm_apply_lie_apply']; rw [sub_self]

/--
lemma `traceForm_eq_zero_of_isNilpotent` / 引理 `traceForm_eq_zero_of_isNilpotent`

English:
lemma traceForm_eq_zero_of_isNilpotent
  given: [IsReduced R] [IsNilpotent L M]
  proof: by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEnd_of_isNilpotent₂ R L M x y

中文:
引理 traceForm_eq_zero_of_isNilpotent
  条件: [是既约 R] [是幂零 L M]
  证明: by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEnd_of_isNilpotent₂ R L M x y
-/
@[simp] lemma traceForm_eq_zero_of_isNilpotent [IsReduced R] [IsNilpotent L M] :
    traceForm R L M = 0 := by
  ext x y
  simp only [traceForm_apply_apply, LinearMap.zero_apply, ← isNilpotent_iff_eq_zero]
  apply LinearMap.isNilpotent_trace_of_isNilpotent
  exact isNilpotent_toEnd_of_isNilpotent₂ R L M x y

open scoped TensorProduct in
/--
lemma `traceForm_baseChange` / 引理 `traceForm_baseChange`

English:
lemma traceForm_baseChange
  statement: [Module.Free R M] [Module.Finite R M]
  proof: by
  ext; simp [traceForm_apply_apply, ← LinearMap.baseChange_comp, Algebra.algebraMap_eq_smul_one]

中文:
引理 traceForm_baseChange
  结论: [模.自由 R M] [模.有限 R M]
  证明: by
  ext; simp [traceForm_apply_apply, ← LinearMap.baseChange_comp, Algebra.algebraMap_eq_smul_one]
-/
@[simp] lemma traceForm_baseChange [Module.Free R M] [Module.Finite R M]
    (A : Type*) [CommRing A] [Algebra R A] :
    traceForm A (A otimes[R] L) (A otimes[R] M) = (traceForm R L M).baseChange A := by
  ext; simp [traceForm_apply_apply, ← LinearMap.baseChange_comp, Algebra.algebraMap_eq_smul_one]

variable {R L M} in
/--
lemma `trace_toEnd_mul_eq_zero_of_traceForm_eq_zero` / 引理 `trace_toEnd_mul_eq_zero_of_traceForm_eq_zero`

English:
lemma trace_toEnd_mul_eq_zero_of_traceForm_eq_zero
  statement: (h : traceForm R L M = 0)
  proof: by
  replace hx : x in Submodule.span R {⁅u, v⁆ | (u : L) (v : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]; exact hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c : L, hbc : φ c = ⁅y, φ b⁆⟩ := hy (φ b) (LieHom.mem_range_self φ b)
    replace hbc : ⁅φ b, y⁆ = -φ c := by rw [hbc, Module.End.instLieRingModule_eq, lie_skew]
    rw [LieHom.map_lie]; rw [LinearMap.trace_lie_mul_eq]; rw [Ring.lie_def]; rw [← LieRing.of_associative_ring_bracket]; rw [hbc]; rw [mul_neg]; rw [map_neg]; rw [neg_eq_zero]; rw [Module.End.mul_eq_comp]; rw [← traceForm_apply_apply]; rw [h]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]
  | zero => simp
  | add u v _ _ hu hv => simp [add_mul, hu, hv]
  | smul t u _ hu => simp [hu]

@[simp]

中文:
引理 trace_toEnd_mul_eq_zero_of_traceForm_eq_zero
  结论: (h : traceForm R L M = 0)
  证明: by
  replace hx : x in Submodule.span R {⁅u, v⁆ | (u : L) (v : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]; exact hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c : L, hbc : φ c = ⁅y, φ b⁆⟩ := hy (φ b) (LieHom.mem_range_self φ b)
    replace hbc : ⁅φ b, y⁆ = -φ c := by rw [hbc, Module.End.instLieRingModule_eq, lie_skew]
    rw [LieHom.map_lie]; rw [LinearMap.trace_lie_mul_eq]; rw [Ring.lie_def]; rw [← LieRing.of_associative_ring_bracket]; rw [hbc]; rw [mul_neg]; rw [map_neg]; rw [neg_eq_zero]; rw [Module.End.mul_eq_comp]; rw [← traceForm_apply_apply]; rw [h]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]
  | zero => simp
  | add u v _ _ hu hv => simp [add_mul, hu, hv]
  | smul t u _ hu => simp [hu]

@[simp]

Depends on / 依赖: LieAlgebra, LieAlgebra.coe_derivedSeries_one_eq, LieHom, LieHom.map_lie, LieHom.mem_range_self, LieRing, LieRing.of_associative_ring_bracket, LinearMap, LinearMap.trace_lie_mul_eq, Module, Module.End.instLieRingModule_eq, Ring.lie_def, Submodule, Submodule.span, Submodule.span_induction, coe_derivedSeries_one_eq, instLieRingModule_eq, lie_def, lie_skew, map_lie
-/
lemma trace_toEnd_mul_eq_zero_of_traceForm_eq_zero (h : traceForm R L M = 0)
    (y : End R M) (hy : forall z in LieHom.range φ, ⁅y, z⁆ in LieHom.range φ)
    (x : L) (hx : x in LieAlgebra.derivedSeries R L 1) :
    trace R M (φ x * y) = 0 := by
  replace hx : x in Submodule.span R {⁅u, v⁆ | (u : L) (v : L)} := by
    rw [← LieAlgebra.coe_derivedSeries_one_eq]; exact hx
  induction hx using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨a, b, rfl⟩ := hu
    obtain ⟨c : L, hbc : φ c = ⁅y, φ b⁆⟩ := hy (φ b) (LieHom.mem_range_self φ b)
    replace hbc : ⁅φ b, y⁆ = -φ c := by rw [hbc, Module.End.instLieRingModule_eq, lie_skew]
    rw [LieHom.map_lie]; rw [LinearMap.trace_lie_mul_eq]; rw [Ring.lie_def]; rw [← LieRing.of_associative_ring_bracket]; rw [hbc]; rw [mul_neg]; rw [map_neg]; rw [neg_eq_zero]; rw [Module.End.mul_eq_comp]; rw [← traceForm_apply_apply]; rw [h]; rw [LinearMap.zero_apply]; rw [LinearMap.zero_apply]
  | zero => simp
  | add u v _ _ hu hv => simp [add_mul, hu, hv]
  | smul t u _ hu => simp [hu]

@[simp]
/--
lemma `traceForm_genWeightSpace_eq` / 引理 `traceForm_genWeightSpace_eq`

English:
lemma traceForm_genWeightSpace_eq
  statement: [Module.Free R M]
  proof: by
  set d := finrank R (genWeightSpace M χ)
  have h₁ : χ y • d • χ x - χ y • χ x • (d : R) = 0 := by simp [mul_comm (χ x)]
  have h₂ : χ x • d • χ y = d • (χ x * χ y) := by
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_left_comm (χ x) d (χ y)
  have := traceForm_eq_zero_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)
  replace this := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  rwa [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply,
    shiftedGenWeightSpace.toEnd_eq, shiftedGenWeightSpace.toEnd_eq,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj', LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, map_sub, map_sub, map_sub, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_id, LinearMap.id_comp, map_smul, map_smul,
    trace_toEnd_genWeightSpace, trace_toEnd_genWeightSpace,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, map_smul, map_smul,
    LinearMap.trace_id, ← traceForm_apply_apply, h₁, h₂, sub_zero, sub_eq_zero] at this

中文:
引理 traceForm_genWeightSpace_eq
  结论: [模.自由 R M]
  证明: by
  set d := finrank R (genWeightSpace M χ)
  have h₁ : χ y • d • χ x - χ y • χ x • (d : R) = 0 := by simp [mul_comm (χ x)]
  have h₂ : χ x • d • χ y = d • (χ x * χ y) := by
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_left_comm (χ x) d (χ y)
  have := traceForm_eq_zero_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)
  replace this := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  rwa [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply,
    shiftedGenWeightSpace.toEnd_eq, shiftedGenWeightSpace.toEnd_eq,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj', LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, map_sub, map_sub, map_sub, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_id, LinearMap.id_comp, map_smul, map_smul,
    trace_toEnd_genWeightSpace, trace_toEnd_genWeightSpace,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, map_smul, map_smul,
    LinearMap.trace_id, ← traceForm_apply_apply, h₁, h₂, sub_zero, sub_eq_zero] at this

Depends on / 依赖: LinearMap, LinearMap.congr_fun, LinearMap.zero_apply, congr_fun, finrank, genWeightSpace, mul_comm, mul_left_comm, nsmul_eq_mul, replace, shiftedGenWeigh, shiftedGenWeightSpace, shiftedGenWeightSpace.toEnd_eq, smul_eq_mul, toEnd_eq, traceForm_apply_apply, traceForm_eq_zero_of_isNilpotent, zero_apply
-/
lemma traceForm_genWeightSpace_eq [Module.Free R M]
    [IsDomain R] [IsPrincipalIdealRing R]
    [LieRing.IsNilpotent L] [IsNoetherian R M] [LinearWeights R L M] (χ : L -> R) (x y : L) :
    traceForm R L (genWeightSpace M χ) x y = finrank R (genWeightSpace M χ) • (χ x * χ y) := by
  set d := finrank R (genWeightSpace M χ)
  have h₁ : χ y • d • χ x - χ y • χ x • (d : R) = 0 := by simp [mul_comm (χ x)]
  have h₂ : χ x • d • χ y = d • (χ x * χ y) := by
    simpa [nsmul_eq_mul, smul_eq_mul] using mul_left_comm (χ x) d (χ y)
  have := traceForm_eq_zero_of_isNilpotent R L (shiftedGenWeightSpace R L M χ)
  replace this := LinearMap.congr_fun (LinearMap.congr_fun this x) y
  rwa [LinearMap.zero_apply, LinearMap.zero_apply, traceForm_apply_apply,
    shiftedGenWeightSpace.toEnd_eq, shiftedGenWeightSpace.toEnd_eq,
    ← LinearEquiv.conj_comp, LinearMap.trace_conj', LinearMap.comp_sub, LinearMap.sub_comp,
    LinearMap.sub_comp, map_sub, map_sub, map_sub, LinearMap.comp_smul, LinearMap.smul_comp,
    LinearMap.comp_id, LinearMap.id_comp, map_smul, map_smul,
    trace_toEnd_genWeightSpace, trace_toEnd_genWeightSpace,
    LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.id_comp, map_smul, map_smul,
    LinearMap.trace_id, ← traceForm_apply_apply, h₁, h₂, sub_zero, sub_eq_zero] at this

/--
lemma `traceForm_eq_zero_if_mem_lcs_of_mem_ucs` / 引理 `traceForm_eq_zero_if_mem_lcs_of_mem_ucs`

English:
lemma traceForm_eq_zero_if_mem_lcs_of_mem_ucs
  statement: {x y : L} (k : Nat)
  proof: by
  induction k generalizing x y with
  | zero =>
    replace hy : y = 0 := by simpa using hy
    simp [hy]
  | succ k ih =>
    rw [LieSubmodule.ucs_succ]; rw [LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction ?_ ?_ (fun z w _ _ hz hw => ?_) (fun t z _ hz => ?_) hx
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew]; rw [map_neg]; rw [LinearMap.neg_apply]; rw [neg_eq_zero]; rw [traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]

中文:
引理 traceForm_eq_zero_if_mem_lcs_of_mem_ucs
  结论: {x y : L} (k : 自然数)
  证明: by
  induction k generalizing x y with
  | zero =>
    replace hy : y = 0 := by simpa using hy
    simp [hy]
  | succ k ih =>
    rw [LieSubmodule.ucs_succ]; rw [LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction ?_ ?_ (fun z w _ _ hz hw => ?_) (fun t z _ hz => ?_) hx
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew]; rw [map_neg]; rw [LinearMap.neg_apply]; rw [neg_eq_zero]; rw [traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]

Depends on / 依赖: LieIdeal, LieIdeal.lcs_succ, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_normalizer, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top, LieSubmodule.ucs_succ, LinearMap, LinearMap.neg_apply, Submodule, Submodule.span_induction, generalizing, lcs_succ, lieIdeal_oper_eq_linear_span, lie_skew, map_neg, mem_normalizer, mem_toSubmodule, mem_top
-/
lemma traceForm_eq_zero_if_mem_lcs_of_mem_ucs {x y : L} (k : Nat)
    (hx : x in (⊤ : LieIdeal R L).lcs L k) (hy : y in (⊥ : LieIdeal R L).ucs k) :
    traceForm R L M x y = 0 := by
  induction k generalizing x y with
  | zero =>
    replace hy : y = 0 := by simpa using hy
    simp [hy]
  | succ k ih =>
    rw [LieSubmodule.ucs_succ]; rw [LieSubmodule.mem_normalizer] at hy
    simp_rw [LieIdeal.lcs_succ, ← LieSubmodule.mem_toSubmodule,
      LieSubmodule.lieIdeal_oper_eq_linear_span', LieSubmodule.mem_top, true_and] at hx
    refine Submodule.span_induction ?_ ?_ (fun z w _ _ hz hw => ?_) (fun t z _ hz => ?_) hx
    · rintro - ⟨z, w, hw, rfl⟩
      rw [← lie_skew]; rw [map_neg]; rw [LinearMap.neg_apply]; rw [neg_eq_zero]; rw [traceForm_apply_lie_apply]
      exact ih hw (hy _)
    · simp
    · simp [hz, hw]
    · simp [hz]

/--
lemma `traceForm_apply_eq_zero_of_mem_lcs_of_mem_center` / 引理 `traceForm_apply_eq_zero_of_mem_lcs_of_mem_center`

English:
lemma traceForm_apply_eq_zero_of_mem_lcs_of_mem_center
  statement: {x y : L}
  proof: by
  apply traceForm_eq_zero_if_mem_lcs_of_mem_ucs R L M 1
  · simpa using hx
  · simpa using hy

中文:
引理 traceForm_apply_eq_zero_of_mem_lcs_of_mem_center
  结论: {x y : L}
  证明: by
  apply traceForm_eq_zero_if_mem_lcs_of_mem_ucs R L M 1
  · simpa using hx
  · simpa using hy

Depends on / 依赖: traceForm_eq_zero_if_mem_lcs_of_mem_ucs
-/
lemma traceForm_apply_eq_zero_of_mem_lcs_of_mem_center {x y : L}
    (hx : x in lowerCentralSeries R L L 1) (hy : y in LieAlgebra.center R L) :
    traceForm R L M x y = 0 := by
  apply traceForm_eq_zero_if_mem_lcs_of_mem_ucs R L M 1
  · simpa using hx
  · simpa using hy

-- This is barely worth having: it usually follows from `LieModule.traceForm_eq_zero_of_isNilpotent`
/--
lemma `traceForm_eq_zero_of_isTrivial` / 引理 `traceForm_eq_zero_of_isTrivial`

English:
lemma traceForm_eq_zero_of_isTrivial
  given: [IsTrivial L M]
  proof: by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [traceForm_apply_apply, this]
  ext m
  simp [trivial_lie_zero]

中文:
引理 traceForm_eq_zero_of_isTrivial
  条件: [是平凡 L M]
  证明: by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [traceForm_apply_apply, this]
  ext m
  simp [trivial_lie_zero]

Depends on / 依赖: traceForm_apply_apply, trivial_lie_zero
-/
lemma traceForm_eq_zero_of_isTrivial [IsTrivial L M] :
    traceForm R L M = 0 := by
  ext x y
  suffices φ x ∘ₗ φ y = 0 by simp [traceForm_apply_apply, this]
  ext m
  simp [trivial_lie_zero]

/--
lemma `eq_zero_of_mem_genWeightSpace_mem_posFitting` / 引理 `eq_zero_of_mem_genWeightSpace_mem_posFitting`

English:
lemma eq_zero_of_mem_genWeightSpace_mem_posFitting
  statement: [LieRing.IsNilpotent L]
  proof: by
  replace hB : forall x (k : Nat) m n, B m ((φ x ^ k) n) = (-1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : forall m, B m (φ x n) = (-1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← Module.End.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices forall (x : L) m, m in posFittingCompOf R M x -> B m₀ m = 0 by
    refine LieSubmodule.iSup_induction (motive := fun m => (B m₀) m = 0) _ hm₁ this (map_zero _) ?_
    simp_all
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

中文:
引理 eq_zero_of_mem_genWeightSpace_mem_posFitting
  结论: [Lie环.是幂零 L]
  证明: by
  replace hB : forall x (k : Nat) m n, B m ((φ x ^ k) n) = (-1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : forall m, B m (φ x n) = (-1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← Module.End.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices forall (x : L) m, m in posFittingCompOf R M x -> B m₀ m = 0 by
    refine LieSubmodule.iSup_induction (motive := fun m => (B m₀) m = 0) _ hm₁ this (map_zero _) ?_
    simp_all
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

Depends on / 依赖: LinearMap, LinearMap.comp_apply, Module, Module.End.mul_eq_comp, comp_apply, conv_lhs, mul_eq_comp, pow_succ, replace, smul_assoc, smul_eq_mul
-/
lemma eq_zero_of_mem_genWeightSpace_mem_posFitting [LieRing.IsNilpotent L]
    {B : LinearMap.BilinForm R M} (hB : forall (x : L) (m n : M), B ⁅x, m⁆ n = -B m ⁅x, n⁆)
    {m₀ m₁ : M} (hm₀ : m₀ in genWeightSpace M (0 : L -> R)) (hm₁ : m₁ in posFittingComp R L M) :
    B m₀ m₁ = 0 := by
  replace hB : forall x (k : Nat) m n, B m ((φ x ^ k) n) = (-1 : R) ^ k • B ((φ x ^ k) m) n := by
    intro x k
    induction k with
    | zero => simp
    | succ k ih =>
    intro m n
    replace hB : forall m, B m (φ x n) = (-1 : R) • B (φ x m) n := by simp [hB]
    have : (-1 : R) ^ k • (-1 : R) = (-1 : R) ^ (k + 1) := by rw [pow_succ (-1 : R), smul_eq_mul]
    conv_lhs => rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply, ih, hB,
      ← (φ x).comp_apply, ← Module.End.mul_eq_comp, ← pow_succ', ← smul_assoc, this]
  suffices forall (x : L) m, m in posFittingCompOf R M x -> B m₀ m = 0 by
    refine LieSubmodule.iSup_induction (motive := fun m => (B m₀) m = 0) _ hm₁ this (map_zero _) ?_
    simp_all
  clear hm₁ m₁; intro x m₁ hm₁
  simp only [mem_genWeightSpace, Pi.zero_apply, zero_smul, sub_zero] at hm₀
  obtain ⟨k, hk⟩ := hm₀ x
  obtain ⟨m, rfl⟩ := (mem_posFittingCompOf R x m₁).mp hm₁ k
  simp [hB, hk]

/--
lemma `trace_toEnd_eq_zero_of_mem_lcs` / 引理 `trace_toEnd_eq_zero_of_mem_lcs`

English:
lemma trace_toEnd_eq_zero_of_mem_lcs
  proof: by
  replace hx : x in lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x in Submodule.span R {m | exists u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ]; rw [← LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x _ => trace R _ (toEnd R L M x) = 0)
    ?_ ?_ (fun u v _ _ hu hv => ?_) (fun t u _ hu => ?_) hx
  · intro y ⟨u, v, huv⟩
    simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

@[simp]

中文:
引理 trace_toEnd_eq_zero_of_mem_lcs
  证明: by
  replace hx : x in lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x in Submodule.span R {m | exists u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ]; rw [← LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x _ => trace R _ (toEnd R L M x) = 0)
    ?_ ?_ (fun u v _ _ hu hv => ?_) (fun t u _ hu => ?_) hx
  · intro y ⟨u, v, huv⟩
    simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, Submodule, Submodule.span, Submodule.span_induction, antitone_lowerCentralSeries, lieIdeal_oper_eq_linear_span, lowerCentralSeries, lowerCentralSeries_succ, mem_toSubmodule, replace, span_induction
-/
lemma trace_toEnd_eq_zero_of_mem_lcs
    {k : Nat} {x : L} (hk : 1 <= k) (hx : x in lowerCentralSeries R L L k) :
    trace R _ (toEnd R L M x) = 0 := by
  replace hx : x in lowerCentralSeries R L L 1 := antitone_lowerCentralSeries _ _ _ hk hx
  replace hx : x in Submodule.span R {m | exists u v : L, ⁅u, v⁆ = m} := by
    rw [lowerCentralSeries_succ]; rw [← LieSubmodule.mem_toSubmodule]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span'] at hx
    simpa using hx
  refine Submodule.span_induction (p := fun x _ => trace R _ (toEnd R L M x) = 0)
    ?_ ?_ (fun u v _ _ hu hv => ?_) (fun t u _ hu => ?_) hx
  · intro y ⟨u, v, huv⟩
    simp [← huv]
  · simp
  · simp [hu, hv]
  · simp [hu]

@[simp]
/--
lemma `traceForm_lieSubalgebra_mk_left` / 引理 `traceForm_lieSubalgebra_mk_left`

English:
lemma traceForm_lieSubalgebra_mk_left
  given: (L' : LieSubalgebra R L) {x : L} (hx : x in L') (y : L')
  proof: rfl

@[simp]

中文:
引理 traceForm_lieSubalgebra_mk_left
  条件: (L' : Lie子代数 R L) {x : L} (hx : x in L') (y : L')
  证明: rfl

@[simp]
-/
lemma traceForm_lieSubalgebra_mk_left (L' : LieSubalgebra R L) {x : L} (hx : x in L') (y : L') :
    traceForm R L' M ⟨x, hx⟩ y = traceForm R L M x y :=
  rfl

@[simp]
/--
lemma `traceForm_lieSubalgebra_mk_right` / 引理 `traceForm_lieSubalgebra_mk_right`

English:
lemma traceForm_lieSubalgebra_mk_right
  given: (L' : LieSubalgebra R L) {x : L'} {y : L} (hy : y in L')
  proof: rfl

中文:
引理 traceForm_lieSubalgebra_mk_right
  条件: (L' : Lie子代数 R L) {x : L'} {y : L} (hy : y in L')
  证明: rfl
-/
lemma traceForm_lieSubalgebra_mk_right (L' : LieSubalgebra R L) {x : L'} {y : L} (hy : y in L') :
    traceForm R L' M x ⟨y, hy⟩ = traceForm R L M x y :=
  rfl

open TensorProduct

variable [LieRing.IsNilpotent L] [IsDomain R]

/--
lemma `traceForm_eq_sum_genWeightSpaceOf` / 引理 `traceForm_eq_sum_genWeightSpaceOf`

English:
lemma traceForm_eq_sum_genWeightSpaceOf
  statement: [IsPrincipalIdealRing R]
  proof: by
  ext x y
  have hxy : forall χ : R, MapsTo ((toEnd R L M x).comp (toEnd R L M y))
      (genWeightSpaceOf M χ z) (genWeightSpaceOf M χ z) :=
fun χ m hm => LieSubmodule.lie_mem _ LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (genWeightSpaceOf M χ z : Submodule R M) != ⊥}.Finite := by
    simp_rw [ne_eq, LieSubmodule.toSubmodule_eq_bot (genWeightSpaceOf M _ _)]
    exact finite_genWeightSpaceOf_ne_bot R L M z
  classical
have h := LieSubmodule.iSupIndep_toSubmodule.mpr iSupIndep_genWeightSpaceOf R L M z
have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h by
    simp [← LieSubmodule.iSup_toSubmodule]
  simp only [LinearMap.coe_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ => rfl)

中文:
引理 traceForm_eq_sum_genWeightSpaceOf
  结论: [是主理想环 R]
  证明: by
  ext x y
  have hxy : forall χ : R, MapsTo ((toEnd R L M x).comp (toEnd R L M y))
      (genWeightSpaceOf M χ z) (genWeightSpaceOf M χ z) :=
fun χ m hm => LieSubmodule.lie_mem _ LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (genWeightSpaceOf M χ z : Submodule R M) != ⊥}.Finite := by
    simp_rw [ne_eq, LieSubmodule.toSubmodule_eq_bot (genWeightSpaceOf M _ _)]
    exact finite_genWeightSpaceOf_ne_bot R L M z
  classical
have h := LieSubmodule.iSupIndep_toSubmodule.mpr iSupIndep_genWeightSpaceOf R L M z
have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h by
    simp [← LieSubmodule.iSup_toSubmodule]
  simp only [LinearMap.coe_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ => rfl)

Depends on / 依赖: Finite, LieSubmodule, LieSubmodule.iSupIndep_toSubmodule.mpr, LieSubmodule.lie_mem, LieSubmodule.toSubmodule_eq_bot, MapsTo, Submodule, classical, finite_genWeightSpaceOf_ne_bot, genWeightSpaceOf, iSupIndep_genWeightSpaceOf, iSupIndep_toSubmodule, lie_mem, ne_eq, simp_rw, toSubmodule_eq_bot
-/
lemma traceForm_eq_sum_genWeightSpaceOf [IsPrincipalIdealRing R]
    [Module.IsTorsionFree R M] [IsNoetherian R M] [IsTriangularizable R L M] (z : L) :
    traceForm R L M =
    ∑ χ in (finite_genWeightSpaceOf_ne_bot R L M z).toFinset,
      traceForm R L (genWeightSpaceOf M χ z) := by
  ext x y
  have hxy : forall χ : R, MapsTo ((toEnd R L M x).comp (toEnd R L M y))
      (genWeightSpaceOf M χ z) (genWeightSpaceOf M χ z) :=
fun χ m hm => LieSubmodule.lie_mem _ LieSubmodule.lie_mem _ hm
  have hfin : {χ : R | (genWeightSpaceOf M χ z : Submodule R M) != ⊥}.Finite := by
    simp_rw [ne_eq, LieSubmodule.toSubmodule_eq_bot (genWeightSpaceOf M _ _)]
    exact finite_genWeightSpaceOf_ne_bot R L M z
  classical
have h := LieSubmodule.iSupIndep_toSubmodule.mpr iSupIndep_genWeightSpaceOf R L M z
have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top h by
    simp [← LieSubmodule.iSup_toSubmodule]
  simp only [LinearMap.coe_sum, Finset.sum_apply, traceForm_apply_apply,
    LinearMap.trace_eq_sum_trace_restrict' hds hfin hxy]
  exact Finset.sum_congr (by simp) (fun χ _ => rfl)

-- In characteristic zero (or even just `LinearWeights R L M`) a stronger result holds (no
-- `⊓ LieAlgebra.center R L`) TODO prove this using `LieModule.traceForm_eq_sum_finrank_nsmul_mul`.
/--
lemma `lowerCentralSeries_one_inf_center_le_ker_traceForm` / 引理 `lowerCentralSeries_one_inf_center_le_ker_traceForm`

English:
lemma lowerCentralSeries_one_inf_center_le_ker_traceForm
  given: [Module.Free R M] [Module.Finite R M]
  proof: by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEnd_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z in lowerCentralSeries R L L 1, hzc : z in LieAlgebra.center R L⟩
  ext x
  rw [traceForm_apply_apply]; rw [LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have that : Module.IsTorsionFree R A := .trans_faithfulSMul R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact FaithfulSMul.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange]; rw [LinearMap.baseChange_comp]; rw [← toEnd_baseChange]; rw [← toEnd_baseChange]
  replace hz : 1 otimesₜ z in lowerCentralSeries A (A otimes[R] L) (A otimes[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top]; rw [← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 otimesₜ[R] z in LieAlgebra.center A (A otimes[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u => by simp [hzc u])
      (fun u v hu hv => by simp [A, hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.maxGenEigenspace_eq_top (1 otimesₜ[R] x)
  · exact fun μ => trace_toEnd_eq_zero_of_mem_lcs A (A otimes[R] L)
      (genWeightSpaceOf (A otimes[R] M) μ ((1 : A) otimesₜ[R] x)) (le_refl 1) hz
  · exact commute_toEnd_of_mem_center_right (A otimes[R] M) hzc (1 otimesₜ x)

中文:
引理 lowerCentralSeries_one_inf_center_le_ker_traceForm
  条件: [模.自由 R M] [模.有限 R M]
  证明: by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEnd_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z in lowerCentralSeries R L L 1, hzc : z in LieAlgebra.center R L⟩
  ext x
  rw [traceForm_apply_apply]; rw [LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have that : Module.IsTorsionFree R A := .trans_faithfulSMul R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact FaithfulSMul.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange]; rw [LinearMap.baseChange_comp]; rw [← toEnd_baseChange]; rw [← toEnd_baseChange]
  replace hz : 1 otimesₜ z in lowerCentralSeries A (A otimes[R] L) (A otimes[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top]; rw [← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 otimesₜ[R] z in LieAlgebra.center A (A otimes[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u => by simp [hzc u])
      (fun u v hu hv => by simp [A, hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.maxGenEigenspace_eq_top (1 otimesₜ[R] x)
  · exact fun μ => trace_toEnd_eq_zero_of_mem_lcs A (A otimes[R] L)
      (genWeightSpaceOf (A otimes[R] M) μ ((1 : A) otimesₜ[R] x)) (le_refl 1) hz
  · exact commute_toEnd_of_mem_center_right (A otimes[R] M) hzc (1 otimesₜ x)
-/
lemma lowerCentralSeries_one_inf_center_le_ker_traceForm [Module.Free R M] [Module.Finite R M] :
    lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L <= LinearMap.ker (traceForm R L M) := by
  /- Sketch of proof (due to Zassenhaus):

  Let `z ∈ lowerCentralSeries R L L 1 ⊓ LieAlgebra.center R L` and `x : L`. We must show that
  `trace (φ x ∘ φ z) = 0` where `φ z : End R M` indicates the action of `z` on `M` (and likewise
  for `φ x`).

  Because `z` belongs to the indicated intersection, it has two key properties:
  (a) the trace of the action of `z` vanishes on any Lie module of `L`
      (see `LieModule.trace_toEnd_eq_zero_of_mem_lcs`),
  (b) `z` commutes with all elements of `L`.

  If `φ x` were triangularizable, we could write `M` as a direct sum of generalized eigenspaces of
  `φ x`. Because `L` is nilpotent these are all Lie submodules, thus Lie modules in their own right,
  and thus by (a) above we learn that `trace (φ z) = 0` restricted to each generalized eigenspace.
  Because `z` commutes with `x`, this forces `trace (φ x ∘ φ z) = 0` on each generalized eigenspace,
  and so by summing the traces on each generalized eigenspace we learn the total trace is zero, as
  required (see `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero`).

  To cater for the fact that `φ x` may not be triangularizable, we first extend the scalars from `R`
  to `AlgebraicClosure (FractionRing R)` and argue using the action of `A ⊗ L` on `A ⊗ M`. -/
  rintro z ⟨hz : z in lowerCentralSeries R L L 1, hzc : z in LieAlgebra.center R L⟩
  ext x
  rw [traceForm_apply_apply]; rw [LinearMap.zero_apply]
  let A := AlgebraicClosure (FractionRing R)
  suffices algebraMap R A (trace R _ ((φ z).comp (φ x))) = 0 by
    have that : Module.IsTorsionFree R A := .trans_faithfulSMul R (FractionRing R) A
    rw [← map_zero (algebraMap R A)] at this
    exact FaithfulSMul.algebraMap_injective R A this
  rw [← LinearMap.trace_baseChange]; rw [LinearMap.baseChange_comp]; rw [← toEnd_baseChange]; rw [← toEnd_baseChange]
  replace hz : 1 otimesₜ z in lowerCentralSeries A (A otimes[R] L) (A otimes[R] L) 1 := by
    simp only [lowerCentralSeries_succ, lowerCentralSeries_zero] at hz ⊢
    rw [← LieSubmodule.baseChange_top]; rw [← LieSubmodule.lie_baseChange]
    exact Submodule.tmul_mem_baseChange_of_mem 1 hz
  replace hzc : 1 otimesₜ[R] z in LieAlgebra.center A (A otimes[R] L) := by
    simp only [mem_maxTrivSubmodule] at hzc ⊢
    intro y
    exact y.induction_on rfl (fun a u => by simp [hzc u])
      (fun u v hu hv => by simp [A, hu, hv])
  apply LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero
  · exact IsTriangularizable.maxGenEigenspace_eq_top (1 otimesₜ[R] x)
  · exact fun μ => trace_toEnd_eq_zero_of_mem_lcs A (A otimes[R] L)
      (genWeightSpaceOf (A otimes[R] M) μ ((1 : A) otimesₜ[R] x)) (le_refl 1) hz
  · exact commute_toEnd_of_mem_center_right (A otimes[R] M) hzc (1 otimesₜ x)

/--
lemma `isLieAbelian_of_ker_traceForm_eq_bot` / 引理 `isLieAbelian_of_ker_traceForm_eq_bot`

English:
lemma isLieAbelian_of_ker_traceForm_eq_bot
  statement: [Module.Free R M] [Module.Finite R M]
  proof: by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.toSubmodule_eq_bot, h]
    using! lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

中文:
引理 isLieAbelian_of_ker_traceForm_eq_bot
  结论: [模.自由 R M] [模.有限 R M]
  证明: by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.toSubmodule_eq_bot, h]
    using! lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

Depends on / 依赖: LieIdeal, LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule, LieSubmodule.toSubmodule_eq_bot, disjoint_iff_inf_le, disjoint_lowerCentralSeries_maxTrivSubmodule_iff, lowerCentralSeries_one_inf_center_le_ker_traceForm, toLieSubalgebra_toSubmodule, toSubmodule_eq_bot
-/
lemma isLieAbelian_of_ker_traceForm_eq_bot [Module.Free R M] [Module.Finite R M]
    (h : LinearMap.ker (traceForm R L M) = ⊥) : IsLieAbelian L := by
  simpa only [← disjoint_lowerCentralSeries_maxTrivSubmodule_iff R L L, disjoint_iff_inf_le,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.toSubmodule_eq_bot, h]
    using! lowerCentralSeries_one_inf_center_le_ker_traceForm R L M

end LieModule

namespace LieSubmodule

open LieModule (traceForm)

variable {R L M}
variable [Module.Free R M] [Module.Finite R M]
variable [IsDomain R] [IsPrincipalIdealRing R]
  (N : LieSubmodule R L M) (I : LieIdeal R L) (h : I <= N.idealizer) (x : L) {y : L} (hy : y in I)

/--
lemma `trace_eq_trace_restrict_of_le_idealizer` / 引理 `trace_eq_trace_restrict_of_le_idealizer`

English:
lemma trace_eq_trace_restrict_of_le_idealizer
  proof: by
  suffices forall m, ⁅x, ⁅y, m⁆⁆ in N by
    have : (trace R { x // x in N }) ((φ x ∘ₗ φ y).restrict _) = (trace R M) (φ x ∘ₗ φ y) :=
      (φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this
    simp [this]
  exact fun m => N.lie_mem (h hy m)

include h in

中文:
引理 trace_eq_trace_restrict_of_le_idealizer
  证明: by
  suffices forall m, ⁅x, ⁅y, m⁆⁆ in N by
    have : (trace R { x // x in N }) ((φ x ∘ₗ φ y).restrict _) = (trace R M) (φ x ∘ₗ φ y) :=
      (φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this
    simp [this]
  exact fun m => N.lie_mem (h hy m)

include h in

Depends on / 依赖: N.lie_mem, N.mem_idealizer.mp, lie_mem, mem_idealizer
-/
lemma trace_eq_trace_restrict_of_le_idealizer
    (hy' : forall m in N, (φ x ∘ₗ φ y) m in N := fun m _ => N.lie_mem (N.mem_idealizer.mp (h hy) m)) :
    trace R M (φ x ∘ₗ φ y) = trace R N ((φ x ∘ₗ φ y).restrict hy') := by
  suffices forall m, ⁅x, ⁅y, m⁆⁆ in N by
    have : (trace R { x // x in N }) ((φ x ∘ₗ φ y).restrict _) = (trace R M) (φ x ∘ₗ φ y) :=
      (φ x ∘ₗ φ y).trace_restrict_eq_of_forall_mem _ this
    simp [this]
  exact fun m => N.lie_mem (h hy m)

include h in
/--
lemma `traceForm_eq_of_le_idealizer` / 引理 `traceForm_eq_of_le_idealizer`

English:
lemma traceForm_eq_of_le_idealizer
  proof: by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

include h hy in

中文:
引理 traceForm_eq_of_le_idealizer
  证明: by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

include h hy in

Depends on / 依赖: N.trace_eq_trace_restrict_of_le_idealizer, trace_eq_trace_restrict_of_le_idealizer
-/
lemma traceForm_eq_of_le_idealizer :
    traceForm R I N = (traceForm R L M).restrict I := by
  ext ⟨x, hx⟩ ⟨y, hy⟩
  change _ = trace R M (φ x ∘ₗ φ y)
  rw [N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  rfl

include h hy in
/--
lemma `traceForm_eq_zero_of_isTrivial` / 引理 `traceForm_eq_zero_of_isTrivial`

English:
lemma traceForm_eq_zero_of_isTrivial
  given: [LieModule.IsTrivial I N]
  proof: by
  let hy' : forall m in N, (φ x ∘ₗ φ y) m in N := fun m _ => N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext (n : N)
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

中文:
引理 traceForm_eq_zero_of_isTrivial
  条件: [Lie模.是平凡 I N]
  证明: by
  let hy' : forall m in N, (φ x ∘ₗ φ y) m in N := fun m _ => N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext (n : N)
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

Depends on / 依赖: IsTrivial, LieModule, LieModule.IsTrivial.trivial, N.lie_mem, N.mem_idealizer.mp, N.trace_eq_trace_restrict_of_le_idealizer, Submodule, Submodule.coe_eq_zero.mpr, coe_eq_zero, lie_mem, mem_idealizer, restrict, trace_eq_trace_restrict_of_le_idealizer
-/
lemma traceForm_eq_zero_of_isTrivial [LieModule.IsTrivial I N] :
    trace R M (φ x ∘ₗ φ y) = 0 := by
  let hy' : forall m in N, (φ x ∘ₗ φ y) m in N := fun m _ => N.lie_mem (N.mem_idealizer.mp (h hy) m)
  suffices (φ x ∘ₗ φ y).restrict hy' = 0 by
    simp [this, N.trace_eq_trace_restrict_of_le_idealizer I h x hy]
  ext (n : N)
  suffices ⁅y, (n : M)⁆ = 0 by simp [this]
  exact Submodule.coe_eq_zero.mpr (LieModule.IsTrivial.trivial (⟨y, hy⟩ : I) n)

end LieSubmodule

section LieAlgebra

/--
Definition of `killingForm` / `killingForm` 的定义

English:
abbreviation killingForm
  signature: : LinearMap.BilinForm R L
  body: LieModule.traceForm R L L

中文:
缩写 killingForm
  签名: : 线性映射.BilinForm R L
  定义体: LieModule.traceForm R L L

Depends on / 依赖: LieModule, LieModule.traceForm, traceForm
-/
noncomputable abbrev killingForm : LinearMap.BilinForm R L := LieModule.traceForm R L L

open LieAlgebra in
/--
lemma `killingForm_apply_apply` / 引理 `killingForm_apply_apply`

English:
lemma killingForm_apply_apply
  given: (x y : L)
  statement: killingForm R L x y = trace R L (ad R L x ∘ₗ ad R L y)
  proof: LieModule.traceForm_apply_apply R L L x y

中文:
引理 killingForm_apply_apply
  条件: (x y : L)
  结论: killingForm R L x y = trace R L (ad R L x ∘ₗ ad R L y)
  证明: LieModule.traceForm_apply_apply R L L x y

Depends on / 依赖: LieModule, LieModule.traceForm_apply_apply, traceForm_apply_apply
-/
lemma killingForm_apply_apply (x y : L) : killingForm R L x y = trace R L (ad R L x ∘ₗ ad R L y) :=
  LieModule.traceForm_apply_apply R L L x y

/--
lemma `killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting` / 引理 `killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting`

English:
lemma killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
  proof: LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting R H L
    (fun x y z => LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

中文:
引理 killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
  证明: LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting R H L
    (fun x y z => LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

Depends on / 依赖: LieModule, LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting, LieModule.traceForm_apply_lie_apply, eq_zero_of_mem_genWeightSpace_mem_posFitting, traceForm_apply_lie_apply
-/
lemma killingForm_eq_zero_of_mem_zeroRoot_mem_posFitting
    (H : LieSubalgebra R L) [LieRing.IsNilpotent H]
    {x₀ x₁ : L}
    (hx₀ : x₀ in LieAlgebra.zeroRootSubalgebra R L H)
    (hx₁ : x₁ in LieModule.posFittingComp R H L) :
    killingForm R L x₀ x₁ = 0 :=
  LieModule.eq_zero_of_mem_genWeightSpace_mem_posFitting R H L
    (fun x y z => LieModule.traceForm_apply_lie_apply' R L L x y z) hx₀ hx₁

namespace LieIdeal

variable (I : LieIdeal R L)

/--
Definition of `killingCompl` / `killingCompl` 的定义

English:
definition killingCompl
  signature: : LieIdeal R L
  body: LieAlgebra.InvariantForm.orthogonal (killingForm R L) (LieModule.traceForm_lieInvariant R L L) I

中文:
定义 killingCompl
  签名: : LieIdeal R L
  定义体: LieAlgebra.InvariantForm.orthogonal (killingForm R L) (LieModule.traceForm_lieInvariant R L L) I

Depends on / 依赖: InvariantForm, LieAlgebra, LieAlgebra.InvariantForm.orthogonal, LieModule, LieModule.traceForm_lieInvariant, killingForm, orthogonal, traceForm_lieInvariant
-/
noncomputable def killingCompl : LieIdeal R L :=
  LieAlgebra.InvariantForm.orthogonal (killingForm R L) (LieModule.traceForm_lieInvariant R L L) I

/--
lemma `toSubmodule_killingCompl` / 引理 `toSubmodule_killingCompl`

English:
lemma toSubmodule_killingCompl
  proof: rfl

中文:
引理 toSubmodule_killingCompl
  证明: rfl
-/
@[simp] lemma toSubmodule_killingCompl :
    LieSubmodule.toSubmodule I.killingCompl = (killingForm R L).orthogonal I.toSubmodule :=
  rfl

/--
lemma `mem_killingCompl` / 引理 `mem_killingCompl`

English:
lemma mem_killingCompl
  given: {x : L}
  proof: by
  rfl

中文:
引理 mem_killingCompl
  条件: {x : L}
  证明: by
  rfl
-/
@[simp] lemma mem_killingCompl {x : L} :
    x in I.killingCompl ↔ forall y in I, killingForm R L y x = 0 := by
  rfl

/--
lemma `coe_killingCompl_top` / 引理 `coe_killingCompl_top`

English:
lemma coe_killingCompl_top
  proof: by
  ext x
  simp [LinearMap.ext_iff, LieModule.traceForm_comm R L L x]

中文:
引理 coe_killingCompl_top
  证明: by
  ext x
  simp [LinearMap.ext_iff, LieModule.traceForm_comm R L L x]

Depends on / 依赖: LieModule, LieModule.traceForm_comm, LinearMap, LinearMap.ext_iff, ext_iff, traceForm_comm
-/
lemma coe_killingCompl_top :
    killingCompl R L ⊤ = LinearMap.ker (killingForm R L) := by
  ext x
  simp [LinearMap.ext_iff, LieModule.traceForm_comm R L L x]

/--
lemma `restrict_killingForm` / 引理 `restrict_killingForm`

English:
lemma restrict_killingForm
  proof: rfl

中文:
引理 restrict_killingForm
  证明: rfl
-/
lemma restrict_killingForm :
    (killingForm R L).restrict I = LieModule.traceForm R I L :=
  rfl

variable [Module.Free R L] [Module.Finite R L] [IsDomain R] [IsPrincipalIdealRing R]

/--
lemma `killingForm_eq` / 引理 `killingForm_eq`

English:
lemma killingForm_eq
  proof: LieSubmodule.traceForm_eq_of_le_idealizer I I by simp

中文:
引理 killingForm_eq
  证明: LieSubmodule.traceForm_eq_of_le_idealizer I I by simp

Depends on / 依赖: LieSubmodule, LieSubmodule.traceForm_eq_of_le_idealizer, traceForm_eq_of_le_idealizer
-/
lemma killingForm_eq :
    killingForm R I = (killingForm R L).restrict I :=
LieSubmodule.traceForm_eq_of_le_idealizer I I by simp

/--
lemma `le_killingCompl_top_of_isLieAbelian` / 引理 `le_killingCompl_top_of_isLieAbelian`

English:
lemma le_killingCompl_top_of_isLieAbelian
  given: [IsLieAbelian I]
  proof: by
  intro x (hx : x in I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

中文:
引理 le_killingCompl_top_of_isLieAbelian
  条件: [IsLieAbelian I]
  证明: by
  intro x (hx : x in I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx
-/
@[simp] lemma le_killingCompl_top_of_isLieAbelian [IsLieAbelian I] :
    I <= LieIdeal.killingCompl R L ⊤ := by
  intro x (hx : x in I)
  simp only [mem_killingCompl, LieSubmodule.mem_top, forall_true_left]
  intro y
  rw [LieModule.traceForm_apply_apply]
  exact LieSubmodule.traceForm_eq_zero_of_isTrivial I I (by simp) _ hx

end LieIdeal

open LieModule Module
open Submodule (span subset_span)

namespace LieModule

variable [Field K] [LieAlgebra K L] [Module K M] [LieModule K L M] [FiniteDimensional K M]
variable [LieRing.IsNilpotent L] [LinearWeights K L M] [IsTriangularizable K L M]

/--
lemma `traceForm_eq_sum_finrank_nsmul_mul` / 引理 `traceForm_eq_sum_finrank_nsmul_mul`

English:
lemma traceForm_eq_sum_finrank_nsmul_mul
  given: (x y : L)
  proof: by
  have hxy : forall χ : Weight K L M, MapsTo (toEnd K L M x ∘ₗ toEnd K L M y)
      (genWeightSpace M χ) (genWeightSpace M χ) :=
fun χ m hm => LieSubmodule.lie_mem _ LieSubmodule.lie_mem _ hm
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K L M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K L M)
  simp_rw [traceForm_apply_apply, LinearMap.trace_eq_sum_trace_restrict hds hxy,
    ← traceForm_genWeightSpace_eq K L M _ x y]
  rfl

中文:
引理 traceForm_eq_sum_finrank_nsmul_mul
  条件: (x y : L)
  证明: by
  have hxy : forall χ : Weight K L M, MapsTo (toEnd K L M x ∘ₗ toEnd K L M y)
      (genWeightSpace M χ) (genWeightSpace M χ) :=
fun χ m hm => LieSubmodule.lie_mem _ LieSubmodule.lie_mem _ hm
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K L M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K L M)
  simp_rw [traceForm_apply_apply, LinearMap.trace_eq_sum_trace_restrict hds hxy,
    ← traceForm_genWeightSpace_eq K L M _ x y]
  rfl

Depends on / 依赖: DirectSum, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top, LieSubmodule, LieSubmodule.iSupIndep_toSubmodule.mpr, LieSubmodule.iSup_toSubmodule_eq_top.mpr, LieSubmodule.lie_mem, LinearMap, LinearMap.trace_eq_sum_trace_restrict, MapsTo, Weight, classical, genWeightSpace, iSupIndep_genWeightSpace, iSupIndep_toSubmodule, iSup_genWeightSpace_eq_top, iSup_toSubmodule_eq_top, isInternal_submodule_of_iSupIndep_of_iSup_eq_top, lie_mem, simp_rw, traceForm_apply_apply
-/
lemma traceForm_eq_sum_finrank_nsmul_mul (x y : L) :
    traceForm K L M x y = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) • (χ x * χ y) := by
  have hxy : forall χ : Weight K L M, MapsTo (toEnd K L M x ∘ₗ toEnd K L M y)
      (genWeightSpace M χ) (genWeightSpace M χ) :=
fun χ m hm => LieSubmodule.lie_mem _ LieSubmodule.lie_mem _ hm
  classical
  have hds := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    (LieSubmodule.iSupIndep_toSubmodule.mpr <| iSupIndep_genWeightSpace' K L M)
    (LieSubmodule.iSup_toSubmodule_eq_top.mpr <| iSup_genWeightSpace_eq_top' K L M)
  simp_rw [traceForm_apply_apply, LinearMap.trace_eq_sum_trace_restrict hds hxy,
    ← traceForm_genWeightSpace_eq K L M _ x y]
  rfl

/--
lemma `traceForm_eq_sum_finrank_nsmul` / 引理 `traceForm_eq_sum_finrank_nsmul`

English:
lemma traceForm_eq_sum_finrank_nsmul
  proof: by
  ext
  rw [traceForm_eq_sum_finrank_nsmul_mul]; rw [← Finset.sum_attach]
  simp [-LinearMap.coe_smul]

中文:
引理 traceForm_eq_sum_finrank_nsmul
  证明: by
  ext
  rw [traceForm_eq_sum_finrank_nsmul_mul]; rw [← Finset.sum_attach]
  simp [-LinearMap.coe_smul]

Depends on / 依赖: Finset, Finset.sum_attach, LinearMap, LinearMap.coe_smul, coe_smul, sum_attach, traceForm_eq_sum_finrank_nsmul_mul
-/
lemma traceForm_eq_sum_finrank_nsmul :
    traceForm K L M = ∑ χ : Weight K L M, finrank K (genWeightSpace M χ) •
      (χ : L ->ₗ[K] K).smulRight (χ : L ->ₗ[K] K) := by
  ext
  rw [traceForm_eq_sum_finrank_nsmul_mul]; rw [← Finset.sum_attach]
  simp [-LinearMap.coe_smul]

/--
lemma `traceForm_eq_sum_finrank_nsmul'` / 引理 `traceForm_eq_sum_finrank_nsmul'`

English:
lemma traceForm_eq_sum_finrank_nsmul'
  proof: by
  classical
  suffices ∑ χ in {χ : Weight K L M | χ.IsZero}, finrank K (genWeightSpace M χ) •
      (χ : L ->ₗ[K] K).smulRight (χ : L ->ₗ[K] K) = 0 by
    rw [traceForm_eq_sum_finrank_nsmul]; rw [← Finset.sum_filter_add_sum_filter_not (p := fun χ : Weight K L M => χ.IsNonZero)]
    simp [this]
  refine Finset.sum_eq_zero fun χ hχ => ?_
  replace hχ : (χ : L ->ₗ[K] K) = 0 := by simpa [← Weight.coe_toLinear_eq_zero_iff] using hχ
  simp [hχ]

中文:
引理 traceForm_eq_sum_finrank_nsmul'
  证明: by
  classical
  suffices ∑ χ in {χ : Weight K L M | χ.IsZero}, finrank K (genWeightSpace M χ) •
      (χ : L ->ₗ[K] K).smulRight (χ : L ->ₗ[K] K) = 0 by
    rw [traceForm_eq_sum_finrank_nsmul]; rw [← Finset.sum_filter_add_sum_filter_not (p := fun χ : Weight K L M => χ.IsNonZero)]
    simp [this]
  refine Finset.sum_eq_zero fun χ hχ => ?_
  replace hχ : (χ : L ->ₗ[K] K) = 0 := by simpa [← Weight.coe_toLinear_eq_zero_iff] using hχ
  simp [hχ]

Depends on / 依赖: Finset, Finset.sum_eq_zero, Finset.sum_filter_add_sum_filter_not, IsNonZero, IsZero, Weight, Weight.coe_toLinear_eq_zero_iff, classical, coe_toLinear_eq_zero_iff, finrank, genWeightSpace, replace, smulRight, sum_eq_zero, sum_filter_add_sum_filter_not, traceForm_eq_sum_finrank_nsmul
-/
lemma traceForm_eq_sum_finrank_nsmul' :
    traceForm K L M = ∑ χ in {χ : Weight K L M | χ.IsNonZero}, finrank K (genWeightSpace M χ) •
      (χ : L ->ₗ[K] K).smulRight (χ : L ->ₗ[K] K) := by
  classical
  suffices ∑ χ in {χ : Weight K L M | χ.IsZero}, finrank K (genWeightSpace M χ) •
      (χ : L ->ₗ[K] K).smulRight (χ : L ->ₗ[K] K) = 0 by
    rw [traceForm_eq_sum_finrank_nsmul]; rw [← Finset.sum_filter_add_sum_filter_not (p := fun χ : Weight K L M => χ.IsNonZero)]
    simp [this]
  refine Finset.sum_eq_zero fun χ hχ => ?_
  replace hχ : (χ : L ->ₗ[K] K) = 0 := by simpa [← Weight.coe_toLinear_eq_zero_iff] using hχ
  simp [hχ]

-- The reverse inclusion should also hold: TODO prove this!
/--
lemma `range_traceForm_le_span_weight` / 引理 `range_traceForm_le_span_weight`

English:
lemma range_traceForm_le_span_weight
  proof: by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul]; rw [LinearMap.coe_sum]; rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ => ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, Weight.toLinear_apply,
    ← Nat.cast_smul_eq_nsmul K]
exact Submodule.smul_mem _ _ Submodule.smul_mem _ _ subset_span mem_range_self χ

中文:
引理 range_traceForm_le_span_weight
  证明: by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul]; rw [LinearMap.coe_sum]; rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ => ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, Weight.toLinear_apply,
    ← Nat.cast_smul_eq_nsmul K]
exact Submodule.smul_mem _ _ Submodule.smul_mem _ _ subset_span mem_range_self χ

Depends on / 依赖: Finset, Finset.sum_apply, LieModule, LieModule.traceForm_eq_sum_finrank_nsmul, LinearMap, LinearMap.coe_smulRight, LinearMap.coe_sum, LinearMap.smul_apply, Nat.cast_smul_eq_nsmul, Submodule, Submodule.smul_mem, Submodule.sum_mem, Weight, Weight.toLinear_apply, cast_smul_eq_nsmul, coe_smulRight, coe_sum, mem_range_self, simp_rw, smul_apply
-/
lemma range_traceForm_le_span_weight :
    LinearMap.range (traceForm K L M) <= span K (range (Weight.toLinear K L M)) := by
  rintro - ⟨x, rfl⟩
  rw [LieModule.traceForm_eq_sum_finrank_nsmul]; rw [LinearMap.coe_sum]; rw [Finset.sum_apply]
  refine Submodule.sum_mem _ fun χ _ => ?_
  simp_rw [LinearMap.smul_apply, LinearMap.coe_smulRight, Weight.toLinear_apply,
    ← Nat.cast_smul_eq_nsmul K]
exact Submodule.smul_mem _ _ Submodule.smul_mem _ _ subset_span mem_range_self χ

end LieModule

end LieAlgebra
