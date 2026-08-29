/-
Copyright (c) 2024 Judith Ludwig, Florent Schaffhauser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Florent Schaffhauser, Yunzhou Xie, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Flat.Stability

/-!
# Faithfully flat modules

A module `M` over a commutative ring `R` is *faithfully flat* if it is flat and `IM ≠ M` whenever
`I` is a maximal ideal of `R`.

## Main declaration

- `Module.FaithfullyFlat`: the predicate asserting that an `R`-module `M` is faithfully flat.

## Main theorems

- `Module.FaithfullyFlat.iff_flat_and_proper_ideal`: an `R`-module `M` is faithfully flat iff it is
  flat and for all proper ideals `I` of `R`, `I • M ≠ M`.
- `Module.FaithfullyFlat.iff_flat_and_rTensor_faithful`: an `R`-module `M` is faithfully flat iff it
  is flat and tensoring with `M` is faithful, i.e. `N ≠ 0` implies `N ⊗ M ≠ 0`.
- `Module.FaithfullyFlat.iff_flat_and_lTensor_faithful`: an `R`-module `M` is faithfully flat iff it
  is flat and tensoring with `M` is faithful, i.e. `N ≠ 0` implies `M ⊗ N ≠ 0`.
- `Module.FaithfullyFlat.iff_exact_iff_rTensor_exact`: an `R`-module `M` is faithfully flat iff
  tensoring with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is
  exact *iff* the sequence `N₁ ⊗ M → N₂ ⊗ M → N₃ ⊗ M` is exact.
- `Module.FaithfullyFlat.iff_exact_iff_lTensor_exact`: an `R`-module `M` is faithfully flat iff
  tensoring with `M` preserves and reflects exact sequences, i.e. the sequence `N₁ → N₂ → N₃` is
  exact *iff* the sequence `M ⊗ N₁ → M ⊗ N₂ → M ⊗ N₃` is exact.
- `Module.FaithfullyFlat.iff_zero_iff_lTensor_zero`: an `R`-module `M` is faithfully flat iff for
  all linear maps `f : N → N'`, `f = 0` iff `M ⊗ f = 0`.
- `Module.FaithfullyFlat.iff_zero_iff_rTensor_zero`: an `R`-module `M` is faithfully flat iff for
  all linear maps `f : N → N'`, `f = 0` iff `f ⊗ M = 0`.

- `Module.FaithfullyFlat.of_linearEquiv`: modules linearly equivalent to a flat modules are flat
- `Module.FaithfullyFlat.trans`: if `S` is `R`-faithfully flat and `M` is `S`-faithfully flat, then
  `M` is `R`-faithfully flat.

- `Module.FaithfullyFlat.self`: the `R`-module `R` is faithfully flat.

-/

@[expose] public section

universe u v

open TensorProduct DirectSum

namespace Module

variable (R : Type u) (M : Type v) [CommRing R] [AddCommGroup M] [Module R M]

/--
Definition of `FaithfullyFlat` / `FaithfullyFlat` 的定义

English:
class FaithfullyFlat
  parameters: : Prop extends Module.Flat R M where
  extends: Module.Flat R M
  axioms and operations (1):
    - submodule_ne_top : forall ⦃m : Ideal R⦄ (_ : Ideal.IsMaximal m), m • (⊤ : Submodule R M) != ⊤

中文:
类 忠实平坦
  参数: : 命题 extends 模.平坦 R M where
  继承: 模.平坦 R M
  公理与运算 (1 个):
    - submodule_ne_top : 对任意 ⦃m : 理想 R⦄ (_ : 理想.是极大 m), m • (⊤ : 子模 R M) != ⊤
-/
@[mk_iff] class FaithfullyFlat : Prop extends Module.Flat R M where
  submodule_ne_top : forall ⦃m : Ideal R⦄ (_ : Ideal.IsMaximal m), m • (⊤ : Submodule R M) != ⊤

namespace FaithfullyFlat
/--
Instance `self` / 实例 `self`

English:
instance self
  signature: : FaithfullyFlat R R where
  body: Ideal.eq_top_iff_one _
    simpa using show 1 in (m • ⊤ : Ideal R) from r.symm ▸ ⟨⟩

中文:
实例 self
  签名: : 忠实平坦 R R where
  定义体: Ideal.eq_top_iff_one _
    simpa using show 1 in (m • ⊤ : Ideal R) from r.symm ▸ ⟨⟩

Depends on / 依赖: Ideal.eq_top_iff_one, eq_top_iff_one
-/
instance self : FaithfullyFlat R R where
.not.1 h.ne_top by submodule_ne_top m h r := Ideal.eq_top_iff_one _
    simpa using show 1 in (m • ⊤ : Ideal R) from r.symm ▸ ⟨⟩

section proper_ideal

/--
lemma `iff_flat_and_proper_ideal` / 引理 `iff_flat_and_proper_ideal`

English:
lemma iff_flat_and_proper_ideal
  proof: by
  rw [faithfullyFlat_iff]
  refine ⟨fun ⟨flat, h⟩ => ⟨flat, fun I hI r => ?_⟩, fun h => ⟨h.1, fun m hm => h.2 _ hm.ne_top⟩⟩
  obtain ⟨m, hm, le⟩ := I.exists_le_maximal hI
exact h hm eq_top_iff.2 show ⊤ <= m • ⊤ from r ▸ Submodule.smul_mono le (by simp [r])

中文:
引理 iff_flat_and_proper_ideal
  证明: by
  rw [faithfullyFlat_iff]
  refine ⟨fun ⟨flat, h⟩ => ⟨flat, fun I hI r => ?_⟩, fun h => ⟨h.1, fun m hm => h.2 _ hm.ne_top⟩⟩
  obtain ⟨m, hm, le⟩ := I.exists_le_maximal hI
exact h hm eq_top_iff.2 show ⊤ <= m • ⊤ from r ▸ Submodule.smul_mono le (by simp [r])

Depends on / 依赖: I.exists_le_maximal, Submodule, Submodule.smul_mono, eq_top_iff, exists_le_maximal, faithfullyFlat_iff, hm.ne_top, ne_top, smul_mono
-/
lemma iff_flat_and_proper_ideal :
    FaithfullyFlat R M ↔
    (Flat R M ∧ forall (I : Ideal R), I != ⊤ -> I • (⊤ : Submodule R M) != ⊤) := by
  rw [faithfullyFlat_iff]
  refine ⟨fun ⟨flat, h⟩ => ⟨flat, fun I hI r => ?_⟩, fun h => ⟨h.1, fun m hm => h.2 _ hm.ne_top⟩⟩
  obtain ⟨m, hm, le⟩ := I.exists_le_maximal hI
exact h hm eq_top_iff.2 show ⊤ <= m • ⊤ from r ▸ Submodule.smul_mono le (by simp [r])

/--
lemma `iff_flat_and_ideal_smul_eq_top` / 引理 `iff_flat_and_ideal_smul_eq_top`

English:
lemma iff_flat_and_ideal_smul_eq_top
  proof: .trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_proper_ideal R M
forall_congr fun I => eq_iff_iff.2 by tauto

中文:
引理 iff_flat_and_ideal_smul_eq_top
  证明: .trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_proper_ideal R M
forall_congr fun I => eq_iff_iff.2 by tauto

Depends on / 依赖: and_congr_right_iff, eq_iff_iff, forall_congr, iff_flat_and_proper_ideal, iff_of_eq
-/
lemma iff_flat_and_ideal_smul_eq_top :
    FaithfullyFlat R M ↔
    (Flat R M ∧ forall (I : Ideal R), I • (⊤ : Submodule R M) = ⊤ -> I = ⊤) :=
.trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_proper_ideal R M
forall_congr fun I => eq_iff_iff.2 by tauto

end proper_ideal

section faithful

/--
Instance `rTensor_nontrivial` / 实例 `rTensor_nontrivial`

English:
instance rTensor_nontrivial
  body: by
.1 inferInstance obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N)
  let I := (Submodule.span R {n}).annihilator
  by_cases I_ne_top : I = ⊤
  · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
    contradiction
let inc : R ⧸ I ->ₗ[R] N := Submodule.liftQ

中文:
实例 rTensor_nontrivial
  定义体: by
.1 inferInstance obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N)
  let I := (Submodule.span R {n}).annihilator
  by_cases I_ne_top : I = ⊤
  · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
    contradiction
let inc : R ⧸ I ->ₗ[R] N := Submodule.liftQ

Depends on / 依赖: Function, Function.I, I_ne_top, Ideal.eq_top_iff_one, LinearMap, LinearMap.flip_apply, LinearMap.lsmul, LinearMap.lsmul_apply, LinearMap.mem_ker, Submodule, Submodule.liftQ, Submodule.mem_annihilator_span_singleton, Submodule.span, annihilator, eq_top_iff_one, flip_apply, injective_inc, lsmul_apply, mem_annihilator_span_singleton, mem_ker
-/
instance rTensor_nontrivial
    [fl : FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (N otimes[R] M) := by
.1 inferInstance obtain ⟨n, hn⟩ := nontrivial_iff_exists_ne (0 : N)
  let I := (Submodule.span R {n}).annihilator
  by_cases I_ne_top : I = ⊤
  · rw [Ideal.eq_top_iff_one, Submodule.mem_annihilator_span_singleton, one_smul] at I_ne_top
    contradiction
let inc : R ⧸ I ->ₗ[R] N := Submodule.liftQ _ ((LinearMap.lsmul R N).flip n) fun r hr => by
    simpa only [LinearMap.mem_ker, LinearMap.flip_apply, LinearMap.lsmul_apply,
      Submodule.mem_annihilator_span_singleton, I] using hr
have injective_inc : Function.Injective inc := LinearMap.ker_eq_bot.1 eq_bot_iff.2 by
    intro r hr
    induction r using Quotient.inductionOn' with | h r =>
    simpa only [Submodule.Quotient.mk''_eq_mk, Submodule.mem_bot, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_annihilator_span_singleton, LinearMap.mem_ker, Submodule.liftQ_apply,
      LinearMap.flip_apply, LinearMap.lsmul_apply, I, inc] using hr
.2 I I_ne_top .1 fl have ne_top := iff_flat_and_proper_ideal R M
.resolve_left fun rid => ne_top ?_ refine subsingleton_or_nontrivial _
  rw [← Submodule.Quotient.subsingleton_iff]
  exact (fl.toFlat.rTensor_preserves_injective_linearMap inc injective_inc).comp
.subsingleton (quotTensorEquivQuotSMul M I).symm.injective

/--
Instance `lTensor_nontrivial` / 实例 `lTensor_nontrivial`

English:
instance lTensor_nontrivial
  body: .toEquiv.nontrivial TensorProduct.comm R M N

中文:
实例 lTensor_nontrivial
  定义体: .toEquiv.nontrivial TensorProduct.comm R M N

Depends on / 依赖: TensorProduct, TensorProduct.comm, nontrivial, toEquiv, toEquiv.nontrivial
-/
instance lTensor_nontrivial
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N] [Nontrivial N] :
    Nontrivial (M otimes[R] N) :=
.toEquiv.nontrivial TensorProduct.comm R M N

/--
lemma `rTensor_reflects_triviality` / 引理 `rTensor_reflects_triviality`

English:
lemma rTensor_reflects_triviality
  proof: by
  revert h; change _ -> _; contrapose!
  intro h
  infer_instance

中文:
引理 rTensor_reflects_triviality
  证明: by
  revert h; change _ -> _; contrapose!
  intro h
  infer_instance

Depends on / 依赖: contrapose, infer_instance, revert
-/
lemma rTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [h : Subsingleton (N otimes[R] M)] : Subsingleton N := by
  revert h; change _ -> _; contrapose!
  intro h
  infer_instance

/--
lemma `lTensor_reflects_triviality` / 引理 `lTensor_reflects_triviality`

English:
lemma lTensor_reflects_triviality
  proof: by
  have : Subsingleton (N otimes[R] M) := (TensorProduct.comm R N M).toEquiv.injective.subsingleton
  apply rTensor_reflects_triviality R M

中文:
引理 lTensor_reflects_triviality
  证明: by
  have : Subsingleton (N otimes[R] M) := (TensorProduct.comm R N M).toEquiv.injective.subsingleton
  apply rTensor_reflects_triviality R M

Depends on / 依赖: Subsingleton, TensorProduct, TensorProduct.comm, injective, otimes, rTensor_reflects_triviality, subsingleton, toEquiv, toEquiv.injective.subsingleton
-/
lemma lTensor_reflects_triviality
    [FaithfullyFlat R M] (N : Type*) [AddCommGroup N] [Module R N]
    [Subsingleton (M otimes[R] N)] :
    Subsingleton N := by
  have : Subsingleton (N otimes[R] M) := (TensorProduct.comm R N M).toEquiv.injective.subsingleton
  apply rTensor_reflects_triviality R M

attribute [-simp] Ideal.Quotient.mk_eq_mk in
/--
lemma `iff_flat_and_rTensor_faithful` / 引理 `iff_flat_and_rTensor_faithful`

English:
lemma iff_flat_and_rTensor_faithful
  proof: by
  refine ⟨fun fl => ⟨inferInstance, rTensor_nontrivial R M⟩, fun ⟨flat, faithful⟩ => ⟨?_⟩⟩
  intro m hm rid
  specialize faithful (ULift (R ⧸ m)) inferInstance
  have : Nontrivial ((R ⧸ m) otimes[R] M) :=
    (congr (ULift.moduleEquiv : ULift (R ⧸ m) ≃ₗ[R] R ⧸ m)
      (LinearEquiv.refl R M)).sym

中文:
引理 iff_flat_and_rTensor_faithful
  证明: by
  refine ⟨fun fl => ⟨inferInstance, rTensor_nontrivial R M⟩, fun ⟨flat, faithful⟩ => ⟨?_⟩⟩
  intro m hm rid
  specialize faithful (ULift (R ⧸ m)) inferInstance
  have : Nontrivial ((R ⧸ m) otimes[R] M) :=
    (congr (ULift.moduleEquiv : ULift (R ⧸ m) ≃ₗ[R] R ⧸ m)
      (LinearEquiv.refl R M)).sym

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, Nontrivial, Quotient, Submodule, Submodule.Quotient.subsingleton_iff, ULift.moduleEquiv, faithful, moduleEquiv, nontrivial, not_subsingleton, otimes, quotTensorEquivQuotSMul, rTensor_nontrivial, specialize, subsingleton_iff, symm.toEquiv.nontrivial, toEquiv, toEquiv.symm.nontrivial
-/
lemma iff_flat_and_rTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      forall (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N -> Nontrivial (N otimes[R] M)) := by
  refine ⟨fun fl => ⟨inferInstance, rTensor_nontrivial R M⟩, fun ⟨flat, faithful⟩ => ⟨?_⟩⟩
  intro m hm rid
  specialize faithful (ULift (R ⧸ m)) inferInstance
  have : Nontrivial ((R ⧸ m) otimes[R] M) :=
    (congr (ULift.moduleEquiv : ULift (R ⧸ m) ≃ₗ[R] R ⧸ m)
      (LinearEquiv.refl R M)).symm.toEquiv.nontrivial
  have := (quotTensorEquivQuotSMul M m).toEquiv.symm.nontrivial
  refine not_subsingleton (M ⧸ m • (⊤ : Submodule R M)) ?_
  rwa [Submodule.Quotient.subsingleton_iff]

/--
lemma `iff_flat_and_rTensor_reflects_triviality` / 引理 `iff_flat_and_rTensor_reflects_triviality`

English:
lemma iff_flat_and_rTensor_reflects_triviality
  proof: .trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_rTensor_faithful R M
forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

中文:
引理 iff_flat_and_rTensor_reflects_triviality
  证明: .trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_rTensor_faithful R M
forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

Depends on / 依赖: and_congr_right_iff, forall_congr, iff_flat_and_rTensor_faithful, iff_iff_eq, iff_of_eq, not_subsingleton_iff_nontrivial
-/
lemma iff_flat_and_rTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      forall (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (N otimes[R] M) -> Subsingleton N) :=
.trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_rTensor_faithful R M
forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

/--
lemma `iff_flat_and_lTensor_faithful` / 引理 `iff_flat_and_lTensor_faithful`

English:
lemma iff_flat_and_lTensor_faithful
  proof: .trans iff_flat_and_rTensor_faithful R M
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.

中文:
引理 iff_flat_and_lTensor_faithful
  证明: .trans iff_flat_and_rTensor_faithful R M
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.

Depends on / 依赖: TensorProduct, TensorProduct.comm, faithful, iff_flat_and_rTensor_faithful, nontrivial, symm.toEquiv.nontrivial, toEquiv, toEquiv.nontrivial
-/
lemma iff_flat_and_lTensor_faithful :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      forall (N : Type max u v) [AddCommGroup N] [Module R N],
        Nontrivial N -> Nontrivial (M otimes[R] N)) :=
.trans iff_flat_and_rTensor_faithful R M
  ⟨fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).toEquiv.nontrivial⟩,
    fun ⟨flat, faithful⟩ => ⟨flat, fun N _ _ _ =>
      letI := faithful N inferInstance; (TensorProduct.comm R M N).symm.toEquiv.nontrivial⟩⟩

/--
lemma `iff_flat_and_lTensor_reflects_triviality` / 引理 `iff_flat_and_lTensor_reflects_triviality`

English:
lemma iff_flat_and_lTensor_reflects_triviality
  proof: .trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_lTensor_faithful R M
forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

中文:
引理 iff_flat_and_lTensor_reflects_triviality
  证明: .trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_lTensor_faithful R M
forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

Depends on / 依赖: and_congr_right_iff, forall_congr, iff_flat_and_lTensor_faithful, iff_iff_eq, iff_of_eq, not_subsingleton_iff_nontrivial
-/
lemma iff_flat_and_lTensor_reflects_triviality :
    FaithfullyFlat R M ↔
    (Flat R M ∧
      forall (N : Type max u v) [AddCommGroup N] [Module R N],
        Subsingleton (M otimes[R] N) -> Subsingleton N) :=
.trans and_congr_right_iff.2 fun _ => iff_of_eq iff_flat_and_lTensor_faithful R M
forall_congr fun N => forall_congr fun _ => forall_congr fun _ => iff_iff_eq.1 by
      simp only [← not_subsingleton_iff_nontrivial]; tauto

end faithful

/--
lemma `of_linearEquiv` / 引理 `of_linearEquiv`

English:
lemma of_linearEquiv
  statement: {N : Type*} [AddCommGroup N] [Module R N] [FaithfullyFlat R M]
  proof: by
  rw [iff_flat_and_lTensor_faithful]
  exact ⟨Flat.of_linearEquiv e,
    fun P _ _ hP => (TensorProduct.congr e (LinearEquiv.refl R P)).toEquiv.nontrivial⟩

中文:
引理 of_linearEquiv
  结论: {N : 类型} [加法交换群 N] [模 R N] [忠实平坦 R M]
  证明: by
  rw [iff_flat_and_lTensor_faithful]
  exact ⟨Flat.of_linearEquiv e,
    fun P _ _ hP => (TensorProduct.congr e (LinearEquiv.refl R P)).toEquiv.nontrivial⟩

Depends on / 依赖: Flat.of_linearEquiv, LinearEquiv, LinearEquiv.refl, TensorProduct, TensorProduct.congr, iff_flat_and_lTensor_faithful, nontrivial, of_linearEquiv, toEquiv, toEquiv.nontrivial
-/
lemma of_linearEquiv {N : Type*} [AddCommGroup N] [Module R N] [FaithfullyFlat R M]
    (e : N ≃ₗ[R] M) : FaithfullyFlat R N := by
  rw [iff_flat_and_lTensor_faithful]
  exact ⟨Flat.of_linearEquiv e,
    fun P _ _ hP => (TensorProduct.congr e (LinearEquiv.refl R P)).toEquiv.nontrivial⟩

section

/--
Instance `directSum` / 实例 `directSum`

English:
instance directSum
  signature: {ι : Type*} [Nonempty ι] (M : ι -> Type*) [forall i, AddCommGroup (M i)]
  body: by
  classical
  rw [iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ hN => ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := M i otimes[R] N)
  have : Nontrivial (⨁ (i : ι), M i otimes[R] N) :=
    ⟨DirectSum.of _ i x, DirectSum.of _ i y, fun 

中文:
实例 directSum
  签名: {ι : 类型} [非空 ι] (M : ι -> 类型) [对任意 i, 加法交换群 (M i)]
  定义体: by
  classical
  rw [iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ hN => ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := M i otimes[R] N)
  have : Nontrivial (⨁ (i : ι), M i otimes[R] N) :=
    ⟨DirectSum.of _ i x, DirectSum.of _ i y, fun 

Depends on / 依赖: DirectSum, DirectSum.of, DirectSum.of_injective, Nonempty, Nontrivial, Nontrivial.exists_pair_ne, TensorProduct, TensorProduct.directSumLeft, classical, directSumLeft, exists_pair_ne, iff_flat_and_lTensor_faithful, nontrivial, of_injective, otimes, toEquiv, toEquiv.nontrivial
-/
instance directSum {ι : Type*} [Nonempty ι] (M : ι -> Type*) [forall i, AddCommGroup (M i)]
    [forall i, Module R (M i)] [forall i, FaithfullyFlat R (M i)] : FaithfullyFlat R (⨁ i, M i) := by
  classical
  rw [iff_flat_and_lTensor_faithful]
  refine ⟨inferInstance, fun N _ _ hN => ?_⟩
  obtain ⟨i⟩ := ‹Nonempty ι›
  obtain ⟨x, y, hxy⟩ := Nontrivial.exists_pair_ne (α := M i otimes[R] N)
  have : Nontrivial (⨁ (i : ι), M i otimes[R] N) :=
    ⟨DirectSum.of _ i x, DirectSum.of _ i y, fun h => hxy (DirectSum.of_injective i h)⟩
  apply (TensorProduct.directSumLeft R R M N).toEquiv.nontrivial

/--
Instance `finsupp` / 实例 `finsupp`

English:
instance finsupp
  signature: (ι : Type v) [Nonempty ι]
  body: by
  classical exact of_linearEquiv _ _ (finsuppLEquivDirectSum R R ι)

中文:
实例 finsupp
  签名: (ι : 类型v) [非空 ι]
  定义体: by
  classical exact of_linearEquiv _ _ (finsuppLEquivDirectSum R R ι)

Depends on / 依赖: classical, finsuppLEquivDirectSum, of_linearEquiv
-/
instance finsupp (ι : Type v) [Nonempty ι] : FaithfullyFlat R (ι ->₀ R) := by
  classical exact of_linearEquiv _ _ (finsuppLEquivDirectSum R R ι)

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Nontrivial
  signature: M] [Module.Free R M] : FaithfullyFlat R M
  body: of_linearEquiv _ _ (Free.chooseBasis R M).repr

中文:
实例 [非平凡
  签名: M] [模.自由 R M] : 忠实平坦 R M
  定义体: of_linearEquiv _ _ (Free.chooseBasis R M).repr

Depends on / 依赖: Free.chooseBasis, chooseBasis, of_linearEquiv
-/
instance [Nontrivial M] [Module.Free R M] : FaithfullyFlat R M :=
  of_linearEquiv _ _ (Free.chooseBasis R M).repr

section

variable {N : Type*} [AddCommGroup N] [Module R N]

@[simp]
/--
lemma `subsingleton_tensorProduct_iff_right` / 引理 `subsingleton_tensorProduct_iff_right`

English:
lemma subsingleton_tensorProduct_iff_right
  given: [Module.FaithfullyFlat R M]
  proof: ⟨fun _ => lTensor_reflects_triviality R M N, fun _ => inferInstance⟩

@[simp]

中文:
引理 subsingleton_tensorProduct_iff_right
  条件: [模.忠实平坦 R M]
  证明: ⟨fun _ => lTensor_reflects_triviality R M N, fun _ => inferInstance⟩

@[simp]

Depends on / 依赖: lTensor_reflects_triviality
-/
lemma subsingleton_tensorProduct_iff_right [Module.FaithfullyFlat R M] :
    Subsingleton (M otimes[R] N) ↔ Subsingleton N :=
  ⟨fun _ => lTensor_reflects_triviality R M N, fun _ => inferInstance⟩

@[simp]
/--
lemma `subsingleton_tensorProduct_iff_left` / 引理 `subsingleton_tensorProduct_iff_left`

English:
lemma subsingleton_tensorProduct_iff_left
  given: [Module.FaithfullyFlat R N]
  proof: ⟨fun _ => rTensor_reflects_triviality R N M, fun _ => inferInstance⟩

@[simp]

中文:
引理 subsingleton_tensorProduct_iff_left
  条件: [模.忠实平坦 R N]
  证明: ⟨fun _ => rTensor_reflects_triviality R N M, fun _ => inferInstance⟩

@[simp]

Depends on / 依赖: rTensor_reflects_triviality
-/
lemma subsingleton_tensorProduct_iff_left [Module.FaithfullyFlat R N] :
    Subsingleton (M otimes[R] N) ↔ Subsingleton M :=
  ⟨fun _ => rTensor_reflects_triviality R N M, fun _ => inferInstance⟩

@[simp]
/--
lemma `nontrivial_tensorProduct_iff_right` / 引理 `nontrivial_tensorProduct_iff_right`

English:
lemma nontrivial_tensorProduct_iff_right
  given: [Module.FaithfullyFlat R M]
  proof: by
  contrapose!; exact subsingleton_tensorProduct_iff_right R M

@[simp]

中文:
引理 nontrivial_tensorProduct_iff_right
  条件: [模.忠实平坦 R M]
  证明: by
  contrapose!; exact subsingleton_tensorProduct_iff_right R M

@[simp]

Depends on / 依赖: contrapose, subsingleton_tensorProduct_iff_right
-/
lemma nontrivial_tensorProduct_iff_right [Module.FaithfullyFlat R M] :
    Nontrivial (M otimes[R] N) ↔ Nontrivial N := by
  contrapose!; exact subsingleton_tensorProduct_iff_right R M

@[simp]
/--
lemma `nontrivial_tensorProduct_iff_left` / 引理 `nontrivial_tensorProduct_iff_left`

English:
lemma nontrivial_tensorProduct_iff_left
  given: [Module.FaithfullyFlat R N]
  proof: by
  contrapose!; exact subsingleton_tensorProduct_iff_left R M

中文:
引理 nontrivial_tensorProduct_iff_left
  条件: [模.忠实平坦 R N]
  证明: by
  contrapose!; exact subsingleton_tensorProduct_iff_left R M

Depends on / 依赖: contrapose, subsingleton_tensorProduct_iff_left
-/
lemma nontrivial_tensorProduct_iff_left [Module.FaithfullyFlat R N] :
    Nontrivial (M otimes[R] N) ↔ Nontrivial M := by
  contrapose!; exact subsingleton_tensorProduct_iff_left R M

end

section exact

/-!
### Faithfully flat modules and exact sequences

In this section we prove that an `R`-module `M` is faithfully flat iff tensoring with `M`
preserves and reflects exact sequences.

Let `N₁ -l₁₂-> N₂ -l₂₃-> N₃` be two linear maps.
- We first show that if `N₁ ⊗ M -> N₂ ⊗ M -> N₃ ⊗ M` is exact, then `N₁ -l₁₂-> N₂ -l₂₃-> N₃` is a
  complex, i.e. `range l₁₂ ≤ ker l₂₃`.
  This is `range_le_ker_of_exact_rTensor`.
- Then in `rTensor_reflects_exact`, we show `ker l₂₃ = range l₁₂` by considering the cohomology
  `ker l₂₃ ⧸ range l₁₂`.

This shows that when `M` is faithfully flat, `- ⊗ M` reflects exact sequences. For details, see
comments in the proof. Since `M` is flat, `- ⊗ M` preserves exact sequences.

On the other hand, if `- ⊗ M` preserves and reflects exact sequences, then `M` is faithfully flat.
- `M` is flat because `- ⊗ M` preserves exact sequences.
- We need to show that if `N ⊗ M = 0` then `N = 0`. Consider the sequence `N -0-> N -0-> 0`. After
  tensoring with `M`, we get `N ⊗ M -0-> N ⊗ M -0-> 0` which is exact because `N ⊗ M = 0`.
  Since `- ⊗ M` reflects exact sequences, `N = 0`.
-/

section arbitrary_universe

variable {N1 : Type*} [AddCommGroup N1] [Module R N1]
variable {N2 : Type*} [AddCommGroup N2] [Module R N2]
variable {N3 : Type*} [AddCommGroup N3] [Module R N3]
variable (l12 : N1 ->ₗ[R] N2) (l23 : N2 ->ₗ[R] N3)

/--
lemma `range_le_ker_of_exact_rTensor` / 引理 `range_le_ker_of_exact_rTensor`

English:
lemma range_le_ker_of_exact_rTensor
  statement: [fl : FaithfullyFlat R M]
  proof: by
  -- let `n1 ∈ N1`. We need to show `l23 (l12 n1) = 0`. Suppose this is not the case.
  rintro _ ⟨n1, rfl⟩
  rw [LinearMap.mem_ker]
  by_contra! hn1
  -- Let `E` be the submodule spanned by `l23 (l12 n1)`. Then because `l23 (l12 n1) ≠ 0`, we have
  -- `E ≠ 0`.
  let E : Submodule R N3 := Submodul

中文:
引理 range_le_ker_of_exact_rTensor
  结论: [fl : 忠实平坦 R M]
  证明: by
  -- let `n1 ∈ N1`. We need to show `l23 (l12 n1) = 0`. Suppose this is not the case.
  rintro _ ⟨n1, rfl⟩
  rw [LinearMap.mem_ker]
  by_contra! hn1
  -- Let `E` be the submodule spanned by `l23 (l12 n1)`. Then because `l23 (l12 n1) ≠ 0`, we have
  -- `E ≠ 0`.
  let E : Submodule R N3 := Submodul
-/
lemma range_le_ker_of_exact_rTensor [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
    LinearMap.range l12 <= LinearMap.ker l23 := by
  -- let `n1 ∈ N1`. We need to show `l23 (l12 n1) = 0`. Suppose this is not the case.
  rintro _ ⟨n1, rfl⟩
  rw [LinearMap.mem_ker]
  by_contra! hn1
  -- Let `E` be the submodule spanned by `l23 (l12 n1)`. Then because `l23 (l12 n1) ≠ 0`, we have
  -- `E ≠ 0`.
  let E : Submodule R N3 := Submodule.span R {l23 (l12 n1)}
  have hE : Nontrivial E :=
    ⟨0, ⟨⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩, Subtype.coe_ne_coe.1 hn1.symm⟩⟩
  -- Since `N1 ⊗ M -> N2 ⊗ M -> N3 ⊗ M` is exact, we have `l23 (l12 n1) ⊗ₜ m = 0` for all `m : M`.
  have eq1 : forall (m : M), l23 (l12 n1) otimesₜ[R] m = 0 := fun m =>
    ex.apply_apply_eq_zero (n1 otimesₜ[R] m)
  -- Then `E ⊗ M = 0`. Indeed,
  have eq0 : (⊤ : Submodule R (E otimes[R] M)) = ⊥ := by
    -- suppose `x ∈ E ⊗ M`. We will show `x = 0`.
    ext x
    simp only [Submodule.mem_top, Submodule.mem_bot, true_iff]
    have mem : x in (⊤ : Submodule R _) := ⟨⟩
    rw [← TensorProduct.span_tmul_eq_top]; rw [Submodule.mem_span_set] at mem
    obtain ⟨c, hc, rfl⟩ := mem
    choose b a hy using hc
    let r : ⦃a : E otimes[R] M⦄ -> a in ↑c.support -> R := fun a ha =>
.choose Submodule.mem_span_singleton.1 (b ha).2
    have hr : forall ⦃i : E otimes[R] M⦄ (hi : i in c.support), b hi =
        r hi • ⟨l23 (l12 n1), Submodule.mem_span_singleton_self _⟩ := fun a ha =>
Subtype.ext .choose_spec.symm Submodule.mem_span_singleton.1 (b ha).2
    -- Since `M` is flat and `E -> N1` is injective, we only need to check that x = 0
    -- in `N1 ⊗ M`. We write `x = ∑ μᵢ • (l23 (l12 n1)) ⊗ mᵢ = ∑ μᵢ • 0 = 0`
    -- (remember `E = span {l23 (l12 n1)}` and `eq1`)
    refine Finset.sum_eq_zero fun i hi => show c i • i = 0 from
      (Module.Flat.rTensor_preserves_injective_linearMap (M := M) E.subtype <|
              Submodule.injective_subtype E) ?_
    rw [← hy hi]; rw [hr hi]; rw [smul_tmul]; rw [map_smul]; rw [LinearMap.rTensor_tmul]; rw [Submodule.subtype_apply]; rw [eq1]; rw [smul_zero]; rw [map_zero]
.2 fun x => have : Subsingleton (E otimes[R] M) := subsingleton_iff_forall_eq 0
    show x in (⊥ : Submodule R _) from eq0 ▸ ⟨⟩
  -- but `E ⊗ M = 0` implies `E = 0` because `M` is faithfully flat and this is a contradiction.
exact not_subsingleton_iff_nontrivial.2 inferInstance fl.rTensor_reflects_triviality R M E

/--
lemma `rTensor_reflects_exact` / 引理 `rTensor_reflects_exact`

English:
lemma rTensor_reflects_exact
  statement: [fl : FaithfullyFlat R M]
  proof: LinearMap.exact_iff.2 by
  have complex : LinearMap.range l12 <= LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex
  -- By the previous lemma we have that range l12 ≤ ker l23 and hence the quotient
  -- H := ker l23 ⧸ range l12 makes sense.
  -- Hence our goal ker l23 = range l12 follows

中文:
引理 rTensor_reflects_exact
  结论: [fl : 忠实平坦 R M]
  证明: LinearMap.exact_iff.2 by
  have complex : LinearMap.range l12 <= LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex
  -- By the previous lemma we have that range l12 ≤ ker l23 and hence the quotient
  -- H := ker l23 ⧸ range l12 makes sense.
  -- Hence our goal ker l23 = range l12 follows

Depends on / 依赖: LinearMap, LinearMap.exact_iff, LinearMap.ker, LinearMap.range, complex, exact_iff, range_le_ker_of_exact_rTensor
-/
lemma rTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.rTensor M) (l23.rTensor M)) :
Function.Exact l12 l23 := LinearMap.exact_iff.2 by
  have complex : LinearMap.range l12 <= LinearMap.ker l23 := range_le_ker_of_exact_rTensor R M _ _ ex
  -- By the previous lemma we have that range l12 ≤ ker l23 and hence the quotient
  -- H := ker l23 ⧸ range l12 makes sense.
  -- Hence our goal ker l23 = range l12 follows from the claim that H = 0.
  let H := LinearMap.ker l23 ⧸ LinearMap.range (Submodule.inclusion complex)
  suffices triv_coh : Subsingleton H by
    rw [Submodule.Quotient.subsingleton_iff]; rw [Submodule.range_inclusion]; rw [Submodule.comap_subtype_eq_top] at triv_coh
    exact le_antisymm triv_coh complex
  -- Since `M` is faithfully flat, we need only to show that `H ⊗ M` is trivial.
  suffices Subsingleton (H otimes[R] M) from rTensor_reflects_triviality R M H
  let e : H otimes[R] M ≃ₗ[R] _ := TensorProduct.quotientTensorEquiv _ _
  -- Note that `H ⊗ M` is isomorphic to `ker l12 ⊗ M ⧸ range ((range l12 ⊗ M) -> (ker l23 ⊗ M))`.
  -- So the problem is reduced to proving surjectivity of `range l12 ⊗ M → ker l23 ⊗ M`.
  rw [e.toEquiv.subsingleton_congr]; rw [Submodule.Quotient.subsingleton_iff]; rw [LinearMap.range_eq_top]
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  -- let `x ⊗ m` be an element in `ker l23 ⊗ M`, then `x ⊗ m` is in the kernel of `l23 ⊗ 𝟙M`.
  -- Since `N1 ⊗ M -l12 ⊗ M-> N2 ⊗ M -l23 ⊗ M-> N3 ⊗ M` is exact, we have that `x ⊗ m` is in
  -- the range of `l12 ⊗ 𝟙M`, i.e. `x ⊗ m = (l12 ⊗ 𝟙M) y` for some `y ∈ N1 ⊗ M` as elements of
  -- `N2 ⊗ M`. We need to prove that `x ⊗ m = (l12 ⊗ 𝟙M) y` still holds in `(ker l23) ⊗ M`.
  -- This is okay because `M` is flat and `ker l23 -> N2` is injective.
  | tmul x m =>
    rcases x with ⟨x, (hx : l23 x = 0)⟩
    have mem : x otimesₜ[R] m in LinearMap.ker (l23.rTensor M) := by simp [hx]
    rw [LinearMap.exact_iff.1 ex] at mem
    obtain ⟨y, hy⟩ := mem
    refine ⟨LinearMap.rTensor M (LinearMap.rangeRestrict _ ∘ₗ LinearMap.rangeRestrict l12) y,
      Module.Flat.rTensor_preserves_injective_linearMap (LinearMap.ker l23).subtype
      Subtype.val_injective ?_⟩
    simp only [LinearMap.comp_codRestrict, LinearMap.rTensor_tmul, Submodule.coe_subtype, ← hy]
    rw [← LinearMap.comp_apply]; rw [← LinearMap.rTensor_def]; rw [← LinearMap.rTensor_comp]; rw [← LinearMap.comp_apply]; rw [← LinearMap.rTensor_comp]; rw [LinearMap.comp_assoc]; rw [LinearMap.subtype_comp_codRestrict]; rw [← LinearMap.comp_assoc]; rw [Submodule.subtype_comp_inclusion]; rw [LinearMap.subtype_comp_codRestrict]
  | add x y hx hy =>
    obtain ⟨x, rfl⟩ := hx; obtain ⟨y, rfl⟩ := hy
    exact ⟨x + y, by simp⟩

/--
lemma `lTensor_reflects_exact` / 引理 `lTensor_reflects_exact`

English:
lemma lTensor_reflects_exact
  statement: [fl : FaithfullyFlat R M]
  proof: rTensor_reflects_exact R M _ _ ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)

@[simp]

中文:
引理 lTensor_reflects_exact
  结论: [fl : 忠实平坦 R M]
  证明: rTensor_reflects_exact R M _ _ ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.comm, ex.of_ladder_linearEquiv_of_exact, of_ladder_linearEquiv_of_exact, rTensor_reflects_exact
-/
lemma lTensor_reflects_exact [fl : FaithfullyFlat R M]
    (ex : Function.Exact (l12.lTensor M) (l23.lTensor M)) :
    Function.Exact l12 l23 :=
rTensor_reflects_exact R M _ _ ex.of_ladder_linearEquiv_of_exact
    (e₁ := TensorProduct.comm _ _ _) (e₂ := TensorProduct.comm _ _ _)
    (e₃ := TensorProduct.comm _ _ _) (by ext; rfl) (by ext; rfl)

@[simp]
/--
lemma `rTensor_exact_iff_exact` / 引理 `rTensor_exact_iff_exact`

English:
lemma rTensor_exact_iff_exact
  given: [FaithfullyFlat R M]
  proof: ⟨fun ex => rTensor_reflects_exact R M l12 l23 ex, fun e => Module.Flat.rTensor_exact _ e⟩

@[simp]

中文:
引理 rTensor_exact_iff_exact
  条件: [忠实平坦 R M]
  证明: ⟨fun ex => rTensor_reflects_exact R M l12 l23 ex, fun e => Module.Flat.rTensor_exact _ e⟩

@[simp]

Depends on / 依赖: Module, Module.Flat.rTensor_exact, rTensor_exact, rTensor_reflects_exact
-/
lemma rTensor_exact_iff_exact [FaithfullyFlat R M] :
    Function.Exact (l12.rTensor M) (l23.rTensor M) ↔ Function.Exact l12 l23 :=
  ⟨fun ex => rTensor_reflects_exact R M l12 l23 ex, fun e => Module.Flat.rTensor_exact _ e⟩

@[simp]
/--
lemma `lTensor_exact_iff_exact` / 引理 `lTensor_exact_iff_exact`

English:
lemma lTensor_exact_iff_exact
  given: [FaithfullyFlat R M]
  proof: ⟨fun ex => lTensor_reflects_exact R M l12 l23 ex, fun e => Module.Flat.lTensor_exact _ e⟩

中文:
引理 lTensor_exact_iff_exact
  条件: [忠实平坦 R M]
  证明: ⟨fun ex => lTensor_reflects_exact R M l12 l23 ex, fun e => Module.Flat.lTensor_exact _ e⟩

Depends on / 依赖: Module, Module.Flat.lTensor_exact, lTensor_exact, lTensor_reflects_exact
-/
lemma lTensor_exact_iff_exact [FaithfullyFlat R M] :
    Function.Exact (l12.lTensor M) (l23.lTensor M) ↔ Function.Exact l12 l23 :=
  ⟨fun ex => lTensor_reflects_exact R M l12 l23 ex, fun e => Module.Flat.lTensor_exact _ e⟩

section

variable {N N' : Type*} [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
  (f : N ->ₗ[R] N')

@[simp]
/--
lemma `lTensor_injective_iff_injective` / 引理 `lTensor_injective_iff_injective`

English:
lemma lTensor_injective_iff_injective
  given: [Module.FaithfullyFlat R M]
  proof: by
  rw [← LinearMap.exact_zero_iff_injective (M otimes[R] Unit), ← LinearMap.exact_zero_iff_injective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]

中文:
引理 lTensor_injective_iff_injective
  条件: [模.忠实平坦 R M]
  证明: by
  rw [← LinearMap.exact_zero_iff_injective (M otimes[R] Unit), ← LinearMap.exact_zero_iff_injective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.exact_zero_iff_injective, conv_rhs, exact_zero_iff_injective, lTensor_exact_iff_exact, otimes
-/
lemma lTensor_injective_iff_injective [Module.FaithfullyFlat R M] :
    Function.Injective (f.lTensor M) ↔ Function.Injective f := by
  rw [← LinearMap.exact_zero_iff_injective (M otimes[R] Unit), ← LinearMap.exact_zero_iff_injective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]
/--
lemma `lTensor_surjective_iff_surjective` / 引理 `lTensor_surjective_iff_surjective`

English:
lemma lTensor_surjective_iff_surjective
  given: [Module.FaithfullyFlat R M]
  proof: by
  rw [← LinearMap.exact_zero_iff_surjective (M otimes[R] Unit),
    ← LinearMap.exact_zero_iff_surjective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]

中文:
引理 lTensor_surjective_iff_surjective
  条件: [模.忠实平坦 R M]
  证明: by
  rw [← LinearMap.exact_zero_iff_surjective (M otimes[R] Unit),
    ← LinearMap.exact_zero_iff_surjective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]

Depends on / 依赖: LinearMap, LinearMap.exact_zero_iff_surjective, conv_rhs, exact_zero_iff_surjective, lTensor_exact_iff_exact, otimes
-/
lemma lTensor_surjective_iff_surjective [Module.FaithfullyFlat R M] :
    Function.Surjective (f.lTensor M) ↔ Function.Surjective f := by
  rw [← LinearMap.exact_zero_iff_surjective (M otimes[R] Unit),
    ← LinearMap.exact_zero_iff_surjective Unit]
  conv_rhs => rw [← lTensor_exact_iff_exact R M]
  simp

@[simp]
/--
lemma `lTensor_bijective_iff_bijective` / 引理 `lTensor_bijective_iff_bijective`

English:
lemma lTensor_bijective_iff_bijective
  given: [Module.FaithfullyFlat R M]
  proof: by
  simp [Function.Bijective]

中文:
引理 lTensor_bijective_iff_bijective
  条件: [模.忠实平坦 R M]
  证明: by
  simp [Function.Bijective]

Depends on / 依赖: Bijective, Function, Function.Bijective
-/
lemma lTensor_bijective_iff_bijective [Module.FaithfullyFlat R M] :
    Function.Bijective (f.lTensor M) ↔ Function.Bijective f := by
  simp [Function.Bijective]

end

end arbitrary_universe

section fixed_universe

/--
lemma `iff_exact_iff_rTensor_exact` / 引理 `iff_exact_iff_rTensor_exact`

English:
lemma iff_exact_iff_rTensor_exact
  proof: ⟨fun fl _ _ _ _ _ _ _ _ _ l12 l23 => (rTensor_exact_iff_exact R M l12 l23).symm, fun iff_exact =>
.2 iff_flat_and_rTensor_reflects_triviality _ _
⟨Flat.iff_rTensor_exact.2 .1, fun _ _ _ => iff_exact ..
.2 fun y => by fun N _ _ h => subsingleton_iff_forall_eq 0
      simpa [eq_comm] using (iff_exact 

中文:
引理 iff_exact_iff_rTensor_exact
  证明: ⟨fun fl _ _ _ _ _ _ _ _ _ l12 l23 => (rTensor_exact_iff_exact R M l12 l23).symm, fun iff_exact =>
.2 iff_flat_and_rTensor_reflects_triviality _ _
⟨Flat.iff_rTensor_exact.2 .1, fun _ _ _ => iff_exact ..
.2 fun y => by fun N _ _ h => subsingleton_iff_forall_eq 0
      simpa [eq_comm] using (iff_exact 

Depends on / 依赖: Flat.iff_rTensor_exact, Subsingleton, Subsingleton.elim, eq_comm, iff_exact, iff_flat_and_rTensor_reflects_triviality, iff_rTensor_exact, rTensor_exact_iff_exact, subsingleton_iff_forall_eq
-/
lemma iff_exact_iff_rTensor_exact :
    FaithfullyFlat R M ↔
    (forall {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 ->ₗ[R] N2) (l23 : N2 ->ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.rTensor M) (l23.rTensor M)) :=
  ⟨fun fl _ _ _ _ _ _ _ _ _ l12 l23 => (rTensor_exact_iff_exact R M l12 l23).symm, fun iff_exact =>
.2 iff_flat_and_rTensor_reflects_triviality _ _
⟨Flat.iff_rTensor_exact.2 .1, fun _ _ _ => iff_exact ..
.2 fun y => by fun N _ _ h => subsingleton_iff_forall_eq 0
      simpa [eq_comm] using (iff_exact (0 : PUnit ->ₗ[R] N) (0 : N ->ₗ[R] PUnit) |>.2 fun x => by
        simpa using Subsingleton.elim _ _) y⟩⟩

/--
lemma `iff_exact_iff_lTensor_exact` / 引理 `iff_exact_iff_lTensor_exact`

English:
lemma iff_exact_iff_lTensor_exact
  proof: by
  simp only [iff_exact_iff_rTensor_exact, LinearMap.rTensor_exact_iff_lTensor_exact]

中文:
引理 iff_exact_iff_lTensor_exact
  证明: by
  simp only [iff_exact_iff_rTensor_exact, LinearMap.rTensor_exact_iff_lTensor_exact]

Depends on / 依赖: LinearMap, LinearMap.rTensor_exact_iff_lTensor_exact, iff_exact_iff_rTensor_exact, rTensor_exact_iff_lTensor_exact
-/
lemma iff_exact_iff_lTensor_exact :
    FaithfullyFlat R M ↔
    (forall {N1 : Type max u v} [AddCommGroup N1] [Module R N1]
      {N2 : Type max u v} [AddCommGroup N2] [Module R N2]
      {N3 : Type max u v} [AddCommGroup N3] [Module R N3]
      (l12 : N1 ->ₗ[R] N2) (l23 : N2 ->ₗ[R] N3),
        Function.Exact l12 l23 ↔ Function.Exact (l12.lTensor M) (l23.lTensor M)) := by
  simp only [iff_exact_iff_rTensor_exact, LinearMap.rTensor_exact_iff_lTensor_exact]

end fixed_universe

end exact

section linearMap

/-!
### Faithfully flat modules and linear maps

In this section we prove that an `R`-module `M` is faithfully flat iff the following holds:

- `M` is flat
- for any `R`-linear map `f : N → N'`, `f` = 0 iff `f ⊗ 𝟙M = 0` iff `𝟙M ⊗ f = 0`

-/

section arbitrary_universe

/--
lemma `zero_iff_lTensor_zero` / 引理 `zero_iff_lTensor_zero`

English:
lemma zero_iff_lTensor_zero
  statement: [h : FaithfullyFlat R M]
  proof: ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    have := lTensor_reflects_exact R M f LinearMap.id (by
      rw [LinearMap.exact_iff]; rw [hf]; rw [LinearMap.range_zero]; rw [LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h

中文:
引理 zero_iff_lTensor_zero
  结论: [h : 忠实平坦 R M]
  证明: ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    have := lTensor_reflects_exact R M f LinearMap.id (by
      rw [LinearMap.exact_iff]; rw [hf]; rw [LinearMap.range_zero]; rw [LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h

Depends on / 依赖: LinearMap, LinearMap.exact_iff, LinearMap.id, LinearMap.ker_eq_bot, LinearMap.lTensor_zero, LinearMap.range_zero, Module, Module.Flat.lTensor_preserves_injective_linearMap, exact_iff, hf.symm, ker_eq_bot, lTensor_preserves_injective_linearMap, lTensor_reflects_exact, lTensor_zero, range_zero
-/
lemma zero_iff_lTensor_zero [h : FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N ->ₗ[R] N') :
    f = 0 ↔ LinearMap.lTensor M f = 0 :=
  ⟨fun hf => hf.symm ▸ LinearMap.lTensor_zero M, fun hf => by
    have := lTensor_reflects_exact R M f LinearMap.id (by
      rw [LinearMap.exact_iff]; rw [hf]; rw [LinearMap.range_zero]; rw [LinearMap.ker_eq_bot]
      apply Module.Flat.lTensor_preserves_injective_linearMap
      exact fun _ _ h => h)
    ext x; simpa using this (f x)⟩


/--
lemma `zero_iff_rTensor_zero` / 引理 `zero_iff_rTensor_zero`

English:
lemma zero_iff_rTensor_zero
  statement: [h: FaithfullyFlat R M]
  proof: .trans zero_iff_lTensor_zero R M f
⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective
    (by simpa using congr($h (m otimesₜ n))), fun h => by
ext m n; exact (TensorProduct.comm R M N').injective (by simpa using congr($h (n otimesₜ m)))⟩

中文:
引理 zero_iff_rTensor_zero
  结论: [h: 忠实平坦 R M]
  证明: .trans zero_iff_lTensor_zero R M f
⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective
    (by simpa using congr($h (m otimesₜ n))), fun h => by
ext m n; exact (TensorProduct.comm R M N').injective (by simpa using congr($h (n otimesₜ m)))⟩

Depends on / 依赖: TensorProduct, TensorProduct.comm, injective, zero_iff_lTensor_zero
-/
lemma zero_iff_rTensor_zero [h: FaithfullyFlat R M]
    {N : Type*} [AddCommGroup N] [Module R N]
    {N' : Type*} [AddCommGroup N'] [Module R N']
    (f : N ->ₗ[R] N') :
    f = 0 ↔ LinearMap.rTensor M f = 0 :=
.trans zero_iff_lTensor_zero R M f
⟨fun h => by ext n m; exact (TensorProduct.comm R N' M).injective
    (by simpa using congr($h (m otimesₜ n))), fun h => by
ext m n; exact (TensorProduct.comm R M N').injective (by simpa using congr($h (n otimesₜ m)))⟩

/-- If `A` is a faithfully flat `R`-algebra, and `m` is a term of an `R`-module `M`,
then `1 ⊗ₜ[R] m = 0` if and only if `m = 0`. -/
@[simp]
/--
theorem `one_tmul_eq_zero_iff` / 定理 `one_tmul_eq_zero_iff`

English:
theorem one_tmul_eq_zero_iff
  given: {A : Type*} [Ring A] [Algebra R A] [FaithfullyFlat R A] (m : M)
  proof: by
  constructor; swap
  · rintro rfl; rw [tmul_zero]
  intro h
  let f : R ->ₗ[R] M := (LinearMap.lsmul R M).flip m
  suffices f = 0 by simpa [f] using DFunLike.congr_fun this 1
  rw [Module.FaithfullyFlat.zero_iff_lTensor_zero R A]
  ext a
  apply_fun (a • ·) at h
  rw [smul_zero]; rw [smul_tmul']

中文:
定理 one_tmul_eq_zero_iff
  条件: {A : 类型} [环 A] [代数 R A] [忠实平坦 R A] (m : M)
  证明: by
  constructor; swap
  · rintro rfl; rw [tmul_zero]
  intro h
  let f : R ->ₗ[R] M := (LinearMap.lsmul R M).flip m
  suffices f = 0 by simpa [f] using DFunLike.congr_fun this 1
  rw [Module.FaithfullyFlat.zero_iff_lTensor_zero R A]
  ext a
  apply_fun (a • ·) at h
  rw [smul_zero]; rw [smul_tmul']

Depends on / 依赖: DFunLike, DFunLike.congr_fun, FaithfullyFlat, LinearMap, LinearMap.lsmul, Module, Module.FaithfullyFlat.zero_iff_lTensor_zero, apply_fun, congr_fun, mul_one, smul_eq_mul, smul_tmul, smul_zero, tmul_zero, zero_iff_lTensor_zero
-/
theorem one_tmul_eq_zero_iff {A : Type*} [Ring A] [Algebra R A] [FaithfullyFlat R A] (m : M) :
    (1 : A) otimesₜ[R] m = 0 ↔ m = 0 := by
  constructor; swap
  · rintro rfl; rw [tmul_zero]
  intro h
  let f : R ->ₗ[R] M := (LinearMap.lsmul R M).flip m
  suffices f = 0 by simpa [f] using DFunLike.congr_fun this 1
  rw [Module.FaithfullyFlat.zero_iff_lTensor_zero R A]
  ext a
  apply_fun (a • ·) at h
  rw [smul_zero]; rw [smul_tmul']; rw [smul_eq_mul]; rw [mul_one] at h
  simpa [f]

end arbitrary_universe

section fixed_universe

/--
lemma `iff_zero_iff_lTensor_zero` / 引理 `iff_zero_iff_lTensor_zero`

English:
lemma iff_zero_iff_lTensor_zero
  proof: .symm⟩, ⟨fun fl => ⟨inferInstance, fun f => zero_iff_lTensor_zero R M f
.2 ⟨flat, fun N _ _ _ => by fun ⟨flat, Z⟩ => iff_flat_and_lTensor_reflects_triviality R M
.1 (by ext; exact Subsingleton.elim _ _) have := Z (LinearMap.id : N ->ₗ[R] N)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y =

中文:
引理 iff_zero_iff_lTensor_zero
  证明: .symm⟩, ⟨fun fl => ⟨inferInstance, fun f => zero_iff_lTensor_zero R M f
.2 ⟨flat, fun N _ _ _ => by fun ⟨flat, Z⟩ => iff_flat_and_lTensor_reflects_triviality R M
.1 (by ext; exact Subsingleton.elim _ _) have := Z (LinearMap.id : N ->ₗ[R] N)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y =

Depends on / 依赖: LinearMap, LinearMap.id, Subsingleton, Subsingleton.elim, iff_flat_and_lTensor_reflects_triviality, subsingleton_iff_forall_eq, zero_iff_lTensor_zero
-/
lemma iff_zero_iff_lTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (forall {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N ->ₗ[R] N'), f.lTensor M = 0 ↔ f = 0)) :=
.symm⟩, ⟨fun fl => ⟨inferInstance, fun f => zero_iff_lTensor_zero R M f
.2 ⟨flat, fun N _ _ _ => by fun ⟨flat, Z⟩ => iff_flat_and_lTensor_reflects_triviality R M
.1 (by ext; exact Subsingleton.elim _ _) have := Z (LinearMap.id : N ->ₗ[R] N)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

/--
lemma `iff_zero_iff_rTensor_zero` / 引理 `iff_zero_iff_rTensor_zero`

English:
lemma iff_zero_iff_rTensor_zero
  proof: .symm⟩, ⟨fun fl => ⟨inferInstance, fun f => zero_iff_rTensor_zero R M f
.2 ⟨flat, fun N _ _ _ => by fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M
.1 (by ext; exact Subsingleton.elim _ _) have := Z (LinearMap.id : N ->ₗ[R] N)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y =

中文:
引理 iff_zero_iff_rTensor_zero
  证明: .symm⟩, ⟨fun fl => ⟨inferInstance, fun f => zero_iff_rTensor_zero R M f
.2 ⟨flat, fun N _ _ _ => by fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M
.1 (by ext; exact Subsingleton.elim _ _) have := Z (LinearMap.id : N ->ₗ[R] N)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y =

Depends on / 依赖: LinearMap, LinearMap.id, Subsingleton, Subsingleton.elim, iff_flat_and_rTensor_reflects_triviality, subsingleton_iff_forall_eq, zero_iff_rTensor_zero
-/
lemma iff_zero_iff_rTensor_zero :
    FaithfullyFlat R M ↔
    (Module.Flat R M ∧
      (forall {N : Type max u v} [AddCommGroup N] [Module R N]
        {N' : Type max u v} [AddCommGroup N'] [Module R N']
        (f : N ->ₗ[R] N'), f.rTensor M = 0 ↔ (f = 0))) :=
.symm⟩, ⟨fun fl => ⟨inferInstance, fun f => zero_iff_rTensor_zero R M f
.2 ⟨flat, fun N _ _ _ => by fun ⟨flat, Z⟩ => iff_flat_and_rTensor_reflects_triviality R M
.1 (by ext; exact Subsingleton.elim _ _) have := Z (LinearMap.id : N ->ₗ[R] N)
      rw [subsingleton_iff_forall_eq 0]
      exact fun y => congr($this y)⟩⟩

end fixed_universe

end linearMap

section trans

open TensorProduct LinearMap

variable (R : Type*) [CommRing R]
variable (S : Type*) [CommRing S] [Algebra R S]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [FaithfullyFlat R S] [FaithfullyFlat S M]

include S in
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  statement: FaithfullyFlat R M
  proof: by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.trans R S M, @fun N _ _ N' _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
  rw [zero_iff_lTensor_zero (R := R) (M := S) f]; rw [show f.lTensor S = (AlgebraTensorModule.map (A := S) LinearMap.id f).restrictScalars R by aesop]; rw [show (0 :

中文:
定理 trans
  结论: 忠实平坦 R M
  证明: by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.trans R S M, @fun N _ _ N' _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
  rw [zero_iff_lTensor_zero (R := R) (M := S) f]; rw [show f.lTensor S = (AlgebraTensorModule.map (A := S) LinearMap.id f).restrictScalars R by aesop]; rw [show (0 :

Depends on / 依赖: AlgebraTensorModul, AlgebraTensorModule, AlgebraTensorModule.map, LinearMap, LinearMap.id, Module, Module.Flat.trans, apply_fun, f.lTensor, iff_zero_iff_lTensor_zero, lTensor, otimes, restrictScalars, restrictScalars_inj, zero_iff_lTensor_zero
-/
theorem trans : FaithfullyFlat R M := by
  rw [iff_zero_iff_lTensor_zero]
  refine ⟨Module.Flat.trans R S M, @fun N _ _ N' _ _ f => ⟨fun aux => ?_, fun eq => eq ▸ by simp⟩⟩
  rw [zero_iff_lTensor_zero (R := R) (M := S) f]; rw [show f.lTensor S = (AlgebraTensorModule.map (A := S) LinearMap.id f).restrictScalars R by aesop]; rw [show (0 : S otimes[R] N ->ₗ[R] S otimes[R] N') = (0 : S otimes[R] N ->ₗ[S] S otimes[R] N').restrictScalars R by rfl,
    restrictScalars_inj, zero_iff_lTensor_zero (R := S) (M := M)]
  ext m n
  apply_fun AlgebraTensorModule.cancelBaseChange R S S M N' using LinearEquiv.injective _
  simpa using congr($aux (m otimesₜ[R] n))

end trans

/-- Faithful flatness is preserved by arbitrary base change. -/
instance (S : Type*) [CommRing S] [Algebra R S] [Module.FaithfullyFlat R M] :
    Module.FaithfullyFlat S (S otimes[R] M) := by
  rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
  refine ⟨inferInstance, fun N _ _ hN => ?_⟩
  let _ : Module R N := Module.compHom N (algebraMap R S)
  have : IsScalarTower R S N := IsScalarTower.of_algebraMap_smul fun r => congrFun rfl
  have := (AlgebraTensorModule.cancelBaseChange R S S N M).symm.subsingleton
  exact FaithfullyFlat.rTensor_reflects_triviality R M N

section IsBaseChange

variable {S N : Type*} [CommRing S] [Algebra R S] [FaithfullyFlat R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] {f : M ->ₗ[R] N}

/--
theorem `_root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat` / 定理 `_root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat`

English:
theorem _root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat
  statement: (hf : IsBaseChange S f)
  proof: by
simpa only [← Submodule.Quotient.subsingleton_iff.not] using not_congr
    (tensorQuotEquivQuotSMul N (I.map (algebraMap R S))).symm ≪≫ₗ TensorProduct.comm S N _ ≪≫ₗ
      hf.tensorEquiv _ ≪≫ₗ AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc

中文:
定理 _root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat
  结论: (hf : IsBaseChange S f)
  证明: by
simpa only [← Submodule.Quotient.subsingleton_iff.not] using not_congr
    (tensorQuotEquivQuotSMul N (I.map (algebraMap R S))).symm ≪≫ₗ TensorProduct.comm S N _ ≪≫ₗ
      hf.tensorEquiv _ ≪≫ₗ AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.assoc, AlgebraTensorModule.congr, I.map, I.qoutMapEquivTensorQout, Quotient, Submodule, Submodule.Quotient.subsingleton_iff.not, TensorProduct, TensorProduct.comm, algebraMap, baseChange, hf.tensorEquiv, not_congr, qoutMapEquivTensorQout, subsingleton_congr, subsingleton_congr.trans, subsingleton_iff, subsingleton_tensorProduct_iff_right, tensorEquiv
-/
theorem _root_.IsBaseChange.map_smul_top_ne_top_iff_of_faithfullyFlat (hf : IsBaseChange S f)
    (I : Ideal R) :
    I.map (algebraMap R S) • (⊤ : Submodule S N) != ⊤ ↔ I • (⊤ : Submodule R M) != ⊤ := by
simpa only [← Submodule.Quotient.subsingleton_iff.not] using not_congr
    (tensorQuotEquivQuotSMul N (I.map (algebraMap R S))).symm ≪≫ₗ TensorProduct.comm S N _ ≪≫ₗ
      hf.tensorEquiv _ ≪≫ₗ AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc R R S S _ M ≪≫ₗ (TensorProduct.comm R _ M).baseChange R S _ _ ≪≫ₗ
.subsingleton_congr.trans (tensorQuotEquivQuotSMul M I).baseChange R S _ _
            subsingleton_tensorProduct_iff_right R S

end IsBaseChange

end FaithfullyFlat

/--
lemma `Flat.of_flat_tensorProduct` / 引理 `Flat.of_flat_tensorProduct`

English:
lemma Flat.of_flat_tensorProduct
  statement: (S : Type*) [CommRing S] [Algebra R S]
  proof: by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have : Flat R (S otimes[R] M) := Flat.trans _ S _
  rw [← FaithfullyFlat.lTensor_injective_iff_injective R S]
  have : LinearMap.lTensor S (LinearMap.lTensor M f) =
      (TensorProduct.assoc _ _ _ _).toLinear

中文:
引理 平坦.of_flat_tensorProduct
  结论: (S : 类型) [交换环 S] [代数 R S]
  证明: by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have : Flat R (S otimes[R] M) := Flat.trans _ S _
  rw [← FaithfullyFlat.lTensor_injective_iff_injective R S]
  have : LinearMap.lTensor S (LinearMap.lTensor M f) =
      (TensorProduct.assoc _ _ _ _).toLinear

Depends on / 依赖: FaithfullyFlat, FaithfullyFlat.lTensor_injective_iff_injective, Flat.lTensor_preserves_injective_linearMap, Flat.trans, LinearMap, LinearMap.lTensor, Module, Module.Flat.iff_lTensor_preserves_injective_linearMap, TensorProduct, TensorProduct.assoc, iff_lTensor_preserves_injective_linearMap, lTensor, lTensor_injective_iff_injective, lTensor_preserves_injective_linearMap, otimes, symm.toLinearMap, toLinearMap
-/
lemma Flat.of_flat_tensorProduct (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [Module.Flat S (S otimes[R] M)] : Module.Flat R M := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N P _ _ _ _ f hf
  have : Flat R (S otimes[R] M) := Flat.trans _ S _
  rw [← FaithfullyFlat.lTensor_injective_iff_injective R S]
  have : LinearMap.lTensor S (LinearMap.lTensor M f) =
      (TensorProduct.assoc _ _ _ _).toLinearMap ∘ₗ LinearMap.lTensor (S otimes[R] M) f ∘ₗ
        (TensorProduct.assoc _ _ _ _).symm.toLinearMap := by
    ext
    simp
  simpa [this] using Flat.lTensor_preserves_injective_linearMap f hf

/--
lemma `Flat.iff_flat_tensorProduct` / 引理 `Flat.iff_flat_tensorProduct`

English:
lemma Flat.iff_flat_tensorProduct
  statement: (S : Type*) [CommRing S] [Algebra R S]
  proof: ⟨fun _ => .of_flat_tensorProduct R M S, fun _ => inferInstance⟩

中文:
引理 平坦.iff_flat_tensorProduct
  结论: (S : 类型) [交换环 S] [代数 R S]
  证明: ⟨fun _ => .of_flat_tensorProduct R M S, fun _ => inferInstance⟩

Depends on / 依赖: of_flat_tensorProduct
-/
lemma Flat.iff_flat_tensorProduct (S : Type*) [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] : Module.Flat S (S otimes[R] M) ↔ Module.Flat R M :=
  ⟨fun _ => .of_flat_tensorProduct R M S, fun _ => inferInstance⟩

end Module

namespace Submodule

open LinearMap Module

variable {R M A : Type*} [CommRing R] [Ring A] [Algebra R A] [FaithfullyFlat R A]
  [AddCommGroup M] [Module R M] {p q : Submodule R M}

@[simp]
/--
theorem `baseChange_le_iff` / 定理 `baseChange_le_iff`

English:
theorem baseChange_le_iff
  statement: p.baseChange A <= q.baseChange A ↔ p <= q
  proof: by
  refine ⟨fun h => ?_, baseChange_mono A⟩
  rwa [← q.ker_mkQ, le_ker_iff_comp_subtype_eq_zero, FaithfullyFlat.zero_iff_lTensor_zero R A,
    lTensor_comp, ← range_le_ker_iff, lTensor_mkQ, ← restrictScalars_le R]

中文:
定理 baseChange_le_iff
  结论: p.baseChange A <= q.baseChange A ↔ p <= q
  证明: by
  refine ⟨fun h => ?_, baseChange_mono A⟩
  rwa [← q.ker_mkQ, le_ker_iff_comp_subtype_eq_zero, FaithfullyFlat.zero_iff_lTensor_zero R A,
    lTensor_comp, ← range_le_ker_iff, lTensor_mkQ, ← restrictScalars_le R]

Depends on / 依赖: FaithfullyFlat, FaithfullyFlat.zero_iff_lTensor_zero, baseChange_mono, ker_mkQ, lTensor_comp, lTensor_mkQ, le_ker_iff_comp_subtype_eq_zero, q.ker_mkQ, range_le_ker_iff, restrictScalars_le, zero_iff_lTensor_zero
-/
theorem baseChange_le_iff : p.baseChange A <= q.baseChange A ↔ p <= q := by
  refine ⟨fun h => ?_, baseChange_mono A⟩
  rwa [← q.ker_mkQ, le_ker_iff_comp_subtype_eq_zero, FaithfullyFlat.zero_iff_lTensor_zero R A,
    lTensor_comp, ← range_le_ker_iff, lTensor_mkQ, ← restrictScalars_le R]

/--
theorem `baseChange_inj` / 定理 `baseChange_inj`

English:
theorem baseChange_inj
  statement: p.baseChange A = q.baseChange A ↔ p = q
  proof: by
  simp [le_antisymm_iff]

中文:
定理 baseChange_inj
  结论: p.baseChange A = q.baseChange A ↔ p = q
  证明: by
  simp [le_antisymm_iff]

Depends on / 依赖: le_antisymm_iff
-/
theorem baseChange_inj : p.baseChange A = q.baseChange A ↔ p = q := by
  simp [le_antisymm_iff]

/--
theorem `baseChange_injective` / 定理 `baseChange_injective`

English:
theorem baseChange_injective
  given: (h : p.baseChange A = q.baseChange A)
  statement: p = q
  proof: baseChange_inj.mp h

中文:
定理 baseChange_injective
  条件: (h : p.baseChange A = q.baseChange A)
  结论: p = q
  证明: baseChange_inj.mp h

Depends on / 依赖: baseChange_inj, baseChange_inj.mp
-/
theorem baseChange_injective (h : p.baseChange A = q.baseChange A) : p = q :=
  baseChange_inj.mp h

variable (R M A) in
/-- `Submodule.baseChange` as an order embedding. -/
@[simps]
/--
Definition of `baseChangeOrderEmbedding` / `baseChangeOrderEmbedding` 的定义

English:
definition baseChangeOrderEmbedding
  signature: : Submodule R M ↪o Submodule A (A otimes[R] M) where
  body: baseChange A
  inj' _ _ := baseChange_injective
  map_rel_iff' := baseChange_le_iff

中文:
定义 baseChangeOrderEmbedding
  签名: : 子模 R M ↪o 子模 A (A otimes[R] M) where
  定义体: baseChange A
  inj' _ _ := baseChange_injective
  map_rel_iff' := baseChange_le_iff

Depends on / 依赖: baseChange
-/
def baseChangeOrderEmbedding : Submodule R M ↪o Submodule A (A otimes[R] M) where
  toFun := baseChange A
  inj' _ _ := baseChange_injective
  map_rel_iff' := baseChange_le_iff

/--
theorem `IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat` / 定理 `IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat`

English:
theorem IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
  proof: by
  rw [isNoetherian_iff'] at h ⊢
  exact (baseChangeOrderEmbedding R M A).wellFoundedGT

中文:
定理 是Noether.of_isNoetherian_tensorProduct_of_faithfullyFlat
  证明: by
  rw [isNoetherian_iff'] at h ⊢
  exact (baseChangeOrderEmbedding R M A).wellFoundedGT

Depends on / 依赖: baseChangeOrderEmbedding, isNoetherian_iff, wellFoundedGT
-/
theorem IsNoetherian.of_isNoetherian_tensorProduct_of_faithfullyFlat
    (h : IsNoetherian A (A otimes[R] M)) : IsNoetherian R M := by
  rw [isNoetherian_iff'] at h ⊢
  exact (baseChangeOrderEmbedding R M A).wellFoundedGT

/--
theorem `IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat` / 定理 `IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat`

English:
theorem IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
  proof: (baseChangeOrderEmbedding R M A).wellFoundedLT

中文:
定理 是Artin.of_isArtinian_tensorProduct_of_faithfullyFlat
  证明: (baseChangeOrderEmbedding R M A).wellFoundedLT

Depends on / 依赖: baseChangeOrderEmbedding, wellFoundedLT
-/
theorem IsArtinian.of_isArtinian_tensorProduct_of_faithfullyFlat
    (h : IsArtinian A (A otimes[R] M)) : IsArtinian R M :=
  (baseChangeOrderEmbedding R M A).wellFoundedLT

end Submodule
