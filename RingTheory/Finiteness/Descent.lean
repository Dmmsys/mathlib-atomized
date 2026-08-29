/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.FiniteStability
public import Mathlib.RingTheory.RingHom.FinitePresentation
public import Mathlib.RingTheory.RingHom.FaithfullyFlat

/-!
# Descent of finiteness conditions under faithfully flat maps

In this file we show that

- `Algebra.FiniteType`:
- `Algebra.FinitePresentation`:
- `Module.Finite`:

descend along faithfully flat base change.
-/

public section

universe u v w

open TensorProduct

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (T : Type*) [CommRing T] [Algebra R T]

/--
lemma `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat` / 引理 `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`

English:
lemma Module.Finite.of_finite_tensorProduct_of_faithfullyFlat
  statement: {M : Type*} [AddCommGroup M]
  proof: by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T otimes[R] M)
  choose k t m h using fun i : Fin n => TensorProduct.exists_sum_tmul_eq (s i)
  let f₀ : ((Σ i, Fin (k i)) -> R) ->ₗ[R] M := (Pi.basisFun R _).constr R fun ⟨i, j⟩ => m i j
  apply of_surjective f₀
  have : Function.Sur

中文:
引理 模.有限.of_finite_tensorProduct_of_faithfullyFlat
  结论: {M : 类型} [加法交换群 M]
  证明: by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T otimes[R] M)
  choose k t m h using fun i : Fin n => TensorProduct.exists_sum_tmul_eq (s i)
  let f₀ : ((Σ i, Fin (k i)) -> R) ->ₗ[R] M := (Pi.basisFun R _).constr R fun ⟨i, j⟩ => m i j
  apply of_surjective f₀
  have : Function.Sur

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.lTensor, Finite, Function, Function.Surjective, LinearMap, LinearMap.range_eq_top, Module, Module.Finite.exists_fin, Pi.ba, Pi.basisFun, Set.range_subset_iff, Submodule, Submodule.span_le, Surjective, TensorProduct, TensorProduct.exists_sum_tmul_eq, basisFun, constr, eq_top_iff
-/
lemma Module.Finite.of_finite_tensorProduct_of_faithfullyFlat {M : Type*} [AddCommGroup M]
    [Module R M] [Module.FaithfullyFlat R T] [Module.Finite T (T otimes[R] M)] :
    Module.Finite R M := by
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := T) (M := T otimes[R] M)
  choose k t m h using fun i : Fin n => TensorProduct.exists_sum_tmul_eq (s i)
  let f₀ : ((Σ i, Fin (k i)) -> R) ->ₗ[R] M := (Pi.basisFun R _).constr R fun ⟨i, j⟩ => m i j
  apply of_surjective f₀
  have : Function.Surjective (AlgebraTensorModule.lTensor T T f₀) := by
    rw [← LinearMap.range_eq_top]; rw [eq_top_iff]; rw [← hs]; rw [Submodule.span_le]; rw [Set.range_subset_iff]
    intro i
    use ∑ (j : Fin (k i)), t i j otimesₜ Pi.basisFun R _ ⟨i, j⟩
    simp [f₀, -Pi.basisFun_equivFun, -Pi.basisFun_apply, h i]
  rwa [← Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T]

/--
lemma `Ideal.FG.of_FG_map_of_faithfullyFlat` / 引理 `Ideal.FG.of_FG_map_of_faithfullyFlat`

English:
lemma Ideal.FG.of_FG_map_of_faithfullyFlat
  statement: [Module.FaithfullyFlat R S] {I : Ideal R}
  proof: by
  change Submodule.FG I
  rw [← Module.Finite.iff_fg]
  let f : S otimes[R] I ->ₗ[S] S :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S I.subtype
  have hf : Function.Injective f := by simp [f]
  have : I.map (algebraMap R S) = LinearMap.range f := by
    refi

中文:
引理 理想.FG.of_FG_map_of_faithfullyFlat
  结论: [模.忠实平坦 R S] {I : 理想 R}
  证明: by
  change Submodule.FG I
  rw [← Module.Finite.iff_fg]
  let f : S otimes[R] I ->ₗ[S] S :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S I.subtype
  have hf : Function.Injective f := by simp [f]
  have : I.map (algebraMap R S) = LinearMap.range f := by
    refi

Depends on / 依赖: Algebra, Algebra.smul_def, AlgebraTensorModule, AlgebraTensorModule.lTensor, AlgebraTensorModule.rid, Finite, Function, Function.Injective, I.map, I.subtype, Ideal.add_mem, Ideal.map_le_iff_le_comap, Injective, LinearMap, LinearMap.range, Module, Module.Finite.iff_fg, Submodule, Submodule.FG, add_mem
-/
lemma Ideal.FG.of_FG_map_of_faithfullyFlat [Module.FaithfullyFlat R S] {I : Ideal R}
    (hI : (I.map (algebraMap R S)).FG) : I.FG := by
  change Submodule.FG I
  rw [← Module.Finite.iff_fg]
  let f : S otimes[R] I ->ₗ[S] S :=
    (AlgebraTensorModule.rid _ _ _).toLinearMap ∘ₗ AlgebraTensorModule.lTensor S S I.subtype
  have hf : Function.Injective f := by simp [f]
  have : I.map (algebraMap R S) = LinearMap.range f := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      use 1 otimesₜ ⟨x, hx⟩
      simp [f, Algebra.smul_def]
    · rintro - ⟨x, rfl⟩
      induction x with
      | zero => simp
      | add _ _ _ _ => simp_all [Ideal.add_mem]
      | tmul s x =>
        have : f (s otimesₜ[R] x) = s • f (1 otimesₜ x) := by simp [f]
        rw [this]
        apply Ideal.mul_mem_left
        simpa [f, Algebra.smul_def] using Ideal.mem_map_of_mem _ x.2
  let e : S otimes[R] I ≃ₗ[S] I.map (algebraMap R S) := .ofInjective _ hf ≪≫ₗ .ofEq _ _ this.symm
  have : Module.Finite S (S otimes[R] ↥I) := by
    rwa [Module.Finite.equiv_iff e, Module.Finite.iff_fg]
  apply Module.Finite.of_finite_tensorProduct_of_faithfullyFlat S

namespace Algebra

/--
lemma `FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat` / 引理 `FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat`

English:
lemma FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
  proof: by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := T) (A := T otimes[R] S)
  have (x : s) := TensorProduct.exists_sum_tmul_eq x.1
  choose k t m h using this
  let f : MvPolynomial (Σ x : s, Fin (k x)) R ->ₐ[R] S := MvPolynomial.aeval (fun ⟨x, i⟩ => m x i)
  apply Algebra.FiniteType.of_surjective f

中文:
引理 有限型.of_finiteType_tensorProduct_of_faithfullyFlat
  证明: by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := T) (A := T otimes[R] S)
  have (x : s) := TensorProduct.exists_sum_tmul_eq x.1
  choose k t m h using this
  let f : MvPolynomial (Σ x : s, Fin (k x)) R ->ₐ[R] S := MvPolynomial.aeval (fun ⟨x, i⟩ => m x i)
  apply Algebra.FiniteType.of_surjective f

Depends on / 依赖: AlgHom, AlgHom.range_eq_top, Algebra, Algebra.FiniteType.of_surjective, Algebra.FiniteType.out, Algebra.TensorProduct.map, FiniteType, Function, Function.Surjective, MvPolynomial, MvPolynomial.aeval, Surjective, TensorProduct, TensorProduct.exists_sum_tmul_eq, _root_, _root_.eq_top_iff, adjoin_le_iff, eq_top_iff, exists_sum_tmul_eq, of_surjective
-/
lemma FiniteType.of_finiteType_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.FiniteType T (T otimes[R] S)] :
    Algebra.FiniteType R S := by
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := T) (A := T otimes[R] S)
  have (x : s) := TensorProduct.exists_sum_tmul_eq x.1
  choose k t m h using this
  let f : MvPolynomial (Σ x : s, Fin (k x)) R ->ₐ[R] S := MvPolynomial.aeval (fun ⟨x, i⟩ => m x i)
  apply Algebra.FiniteType.of_surjective f
  have hf : Function.Surjective (Algebra.TensorProduct.map (.id T T) f) := by
    rw [← AlgHom.range_eq_top]; rw [_root_.eq_top_iff]; rw [← hs]; rw [adjoin_le_iff]
    intro x hx
    let i : s := ⟨x, hx⟩
    use ∑ (j : Fin (k i)), t i j otimesₜ MvPolynomial.X ⟨i, j⟩
    simp [f, ← h, i]
  exact (Module.FaithfullyFlat.lTensor_surjective_iff_surjective _ T _).mp hf

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/--
lemma `FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat` / 引理 `FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat`

English:
lemma FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
  proof: by
  have : Algebra.FiniteType R S := .of_finiteType_tensorProduct_of_faithfullyFlat T
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at this
  obtain ⟨n, f, hf⟩ := this
  have : Module.FaithfullyFlat (MvPolynomial (Fin n) R) (T otimes[R] MvPolynomial (Fin n) R) :=
    .of_linearEquiv _ _ (Al

中文:
引理 有限呈现.of_finitePresentation_tensorProduct_of_faithfullyFlat
  证明: by
  have : Algebra.FiniteType R S := .of_finiteType_tensorProduct_of_faithfullyFlat T
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at this
  obtain ⟨n, f, hf⟩ := this
  have : Module.FaithfullyFlat (MvPolynomial (Fin n) R) (T otimes[R] MvPolynomial (Fin n) R) :=
    .of_linearEquiv _ _ (Al

Depends on / 依赖: Algebra, Algebra.FiniteType, Algebra.FiniteType.iff_quotient_mvPolynomial, Algebra.TensorProduct.commRight, Algebra.TensorProduct.map, FaithfullyFlat, FiniteType, Module, Module.FaithfullyFlat, MvPolynomial, TensorProduct, commRight, iff_quotient_mvPolynomial, of_FG_map_of_faithfullyFlat, of_finiteType_tensorProduct_of_faithfullyFlat, of_linearEquiv, of_surjective, otimes, symm.toLinearEquiv, toLinearEquiv
-/
lemma FinitePresentation.of_finitePresentation_tensorProduct_of_faithfullyFlat
    [Module.FaithfullyFlat R T] [Algebra.FinitePresentation T (T otimes[R] S)] :
    Algebra.FinitePresentation R S := by
  have : Algebra.FiniteType R S := .of_finiteType_tensorProduct_of_faithfullyFlat T
  rw [Algebra.FiniteType.iff_quotient_mvPolynomial''] at this
  obtain ⟨n, f, hf⟩ := this
  have : Module.FaithfullyFlat (MvPolynomial (Fin n) R) (T otimes[R] MvPolynomial (Fin n) R) :=
    .of_linearEquiv _ _ (Algebra.TensorProduct.commRight _ _ _).symm.toLinearEquiv
  let fT := Algebra.TensorProduct.map (.id T T) f
  refine .of_surjective hf (.of_FG_map_of_faithfullyFlat (S := T otimes[R] MvPolynomial (Fin n) R) ?_)
  have : (RingHom.ker f.toRingHom).map
      (algebraMap (MvPolynomial (Fin n) R) (T otimes[R] MvPolynomial (Fin n) R)) = RingHom.ker fT :=
    (Algebra.TensorProduct.lTensor_ker f hf).symm
  rw [this]
  apply ker_fG_of_surjective
  exact FiniteType.baseChangeAux_surj T hf

end Algebra

namespace RingHom

/--
lemma `FiniteType.codescendsAlong_faithfullyFlat` / 引理 `FiniteType.codescendsAlong_faithfullyFlat`

English:
lemma FiniteType.codescendsAlong_faithfullyFlat
  proof: by
  refine .mk _ finiteType_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finiteType_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finiteType_tensorProduct_of_faithfullyFlat S

中文:
引理 有限型.codescendsAlong_faithfullyFlat
  证明: by
  refine .mk _ finiteType_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finiteType_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finiteType_tensorProduct_of_faithfullyFlat S

Depends on / 依赖: faithfullyFlat_algebraMap_iff, finiteType_algebraMap, finiteType_respectsIso, of_finiteType_tensorProduct_of_faithfullyFlat
-/
lemma FiniteType.codescendsAlong_faithfullyFlat :
    CodescendsAlong FiniteType FaithfullyFlat := by
  refine .mk _ finiteType_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finiteType_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finiteType_tensorProduct_of_faithfullyFlat S

/--
lemma `FinitePresentation.codescendsAlong_faithfullyFlat` / 引理 `FinitePresentation.codescendsAlong_faithfullyFlat`

English:
lemma FinitePresentation.codescendsAlong_faithfullyFlat
  proof: by
  refine .mk _ finitePresentation_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finitePresentation_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat S

中文:
引理 有限呈现.codescendsAlong_faithfullyFlat
  证明: by
  refine .mk _ finitePresentation_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finitePresentation_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat S

Depends on / 依赖: faithfullyFlat_algebraMap_iff, finitePresentation_algebraMap, finitePresentation_respectsIso, of_finitePresentation_tensorProduct_of_faithfullyFlat
-/
lemma FinitePresentation.codescendsAlong_faithfullyFlat :
    CodescendsAlong FinitePresentation FaithfullyFlat := by
  refine .mk _ finitePresentation_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finitePresentation_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finitePresentation_tensorProduct_of_faithfullyFlat S

/--
lemma `Finite.codescendsAlong_faithfullyFlat` / 引理 `Finite.codescendsAlong_faithfullyFlat`

English:
lemma Finite.codescendsAlong_faithfullyFlat
  proof: by
  refine .mk _ finite_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finite_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finite_tensorProduct_of_faithfullyFlat S

中文:
引理 有限.codescendsAlong_faithfullyFlat
  证明: by
  refine .mk _ finite_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finite_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finite_tensorProduct_of_faithfullyFlat S

Depends on / 依赖: faithfullyFlat_algebraMap_iff, finite_algebraMap, finite_respectsIso, of_finite_tensorProduct_of_faithfullyFlat
-/
lemma Finite.codescendsAlong_faithfullyFlat :
    CodescendsAlong Finite FaithfullyFlat := by
  refine .mk _ finite_respectsIso fun R S T _ _ _ _ _ h h' => ?_
  rw [finite_algebraMap] at h' ⊢
  rw [faithfullyFlat_algebraMap_iff] at h
  exact .of_finite_tensorProduct_of_faithfullyFlat S

end RingHom
