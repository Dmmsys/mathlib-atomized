/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Bases of submodules
-/

@[expose] public section

open Function Set Submodule Finsupp Module

assert_not_exists Ordinal

noncomputable section

universe u

variable {ι ι' R R₂ M M' : Type*}

namespace Module.Basis
variable [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid M'] [Module R M']

variable (b : Basis ι R M)

/--
theorem `mem_submodule_iff` / 定理 `mem_submodule_iff`

English:
theorem mem_submodule_iff
  given: {P : Submodule R M} (b : Basis ι R P) {x : M}
  proof: by
  conv_lhs =>
    rw [← P.range_subtype]; rw [← Submodule.map_top]; rw [← b.span_eq]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← Finsupp.range_linearCombination]
  simp [@eq_comm _ x, Function.comp, Finsupp.linearCombination_apply]

中文:
定理 mem_submodule_iff
  条件: {P : Submodule R M} (b : Basis ι R P) {x : M}
  证明: by
  conv_lhs =>
    rw [← P.range_subtype]; rw [← Submodule.map_top]; rw [← b.span_eq]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← Finsupp.range_linearCombination]
  simp [@eq_comm _ x, Function.comp, Finsupp.linearCombination_apply]

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Finsupp.range_linearCombination, Function, Function.comp, P.range_subtype, Set.range_comp, Submodule, Submodule.map_span, Submodule.map_top, b.span_eq, conv_lhs, eq_comm, linearCombination_apply, map_span, map_top, range_comp, range_linearCombination, range_subtype, span_eq
-/
theorem mem_submodule_iff {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x in P ↔ exists c : ι ->₀ R, x = Finsupp.sum c fun i x => x • (b i : M) := by
  conv_lhs =>
    rw [← P.range_subtype]; rw [← Submodule.map_top]; rw [← b.span_eq]; rw [Submodule.map_span]; rw [← Set.range_comp]; rw [← Finsupp.range_linearCombination]
  simp [@eq_comm _ x, Function.comp, Finsupp.linearCombination_apply]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `mem_submodule_iff'` / 定理 `mem_submodule_iff'`

English:
theorem mem_submodule_iff'
  given: [Fintype ι] {P : Submodule R M} (b : Basis ι R P) {x : M}
  proof: b.mem_submodule_iff.trans
Finsupp.equivFunOnFinite.exists_congr_left.trans
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

中文:
定理 mem_submodule_iff'
  条件: [Fintype ι] {P : Submodule R M} (b : Basis ι R P) {x : M}
  证明: b.mem_submodule_iff.trans
Finsupp.equivFunOnFinite.exists_congr_left.trans
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

Depends on / 依赖: Finsupp, Finsupp.equivFunOnFinite, Finsupp.equivFunOnFinite.exists_congr_left.trans, Finsupp.sum_fintype, b.mem_submodule_iff.trans, equivFunOnFinite, exists_congr, exists_congr_left, mem_submodule_iff, sum_fintype
-/
theorem mem_submodule_iff' [Fintype ι] {P : Submodule R M} (b : Basis ι R P) {x : M} :
    x in P ↔ exists c : ι -> R, x = ∑ i, c i • (b i : M) :=
b.mem_submodule_iff.trans
Finsupp.equivFunOnFinite.exists_congr_left.trans
      exists_congr fun c => by simp [Finsupp.sum_fintype, Finsupp.equivFunOnFinite]

end Basis

open LinearMap

variable {v : ι -> M}
variable [Ring R] [CommRing R₂] [AddCommGroup M]
variable [Module R M] [Module R₂ M]
variable {x y : M}
variable (b : Basis ι R M)

/--
theorem `Basis.eq_bot_of_rank_eq_zero` / 定理 `Basis.eq_bot_of_rank_eq_zero`

English:
theorem Basis.eq_bot_of_rank_eq_zero
  statement: [IsDomain R] (b : Basis ι R M) (N : Submodule R M)
  proof: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  simp only [Fin.default_eq_zero, Finset.univ_unique,
    Finset.sum_singleton] at sum_eq
  convert! (b.smul_eq_zero.mp

中文:
定理 Basis.eq_bot_of_rank_eq_zero
  结论: [IsDomain R] (b : Basis ι R M) (N : Submodule R M)
  证明: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  simp only [Fin.default_eq_zero, Finset.univ_unique,
    Finset.sum_singleton] at sum_eq
  convert! (b.smul_eq_zero.mp

Depends on / 依赖: Fin.default_eq_zero, Finset, Finset.sum_singleton, Finset.univ_unique, Fintype, Fintype.linearIndependent_iff, Submodule, Submodule.eq_bot_iff, b.smul_eq_zero.mp, contrapose, convert, default_eq_zero, eq_bot_iff, linearIndependent_iff, one_ne_zero, rank_eq, resolve_right, smul_eq_zero, sum_eq, sum_singleton
-/
theorem Basis.eq_bot_of_rank_eq_zero [IsDomain R] (b : Basis ι R M) (N : Submodule R M)
    (rank_eq : forall {m : Nat} (v : Fin m -> N), LinearIndependent R ((↑) ∘ v : Fin m -> M) -> m = 0) :
    N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  contrapose! rank_eq with x_ne
  refine ⟨1, fun _ => ⟨x, hx⟩, ?_, one_ne_zero⟩
  rw [Fintype.linearIndependent_iff]
  rintro g sum_eq i
  simp only [Fin.default_eq_zero, Finset.univ_unique,
    Finset.sum_singleton] at sum_eq
  convert! (b.smul_eq_zero.mp sum_eq).resolve_right x_ne

end Module

section Induction

variable [Ring R] [IsDomain R]
variable [AddCommGroup M] [Module R M] {b : ι -> M}

/--
Definition of `Submodule.inductionOnRankAux` / `Submodule.inductionOnRankAux` 的定义

English:
definition Submodule.inductionOnRankAux
  signature: (b : Basis ι R M) (P : Submodule R M -> Sort*)
  body: by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction n generalizing N with
  | zero =>
    suffices N = ⊥ by rwa [this]
    apply Basis.eq_bo

中文:
定义 Submodule.inductionOnRankAux
  签名: (b : Basis ι R M) (P : Submodule R M -> Sort*)
  定义体: by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction n generalizing N with
  | zero =>
    suffices N = ⊥ by rwa [this]
    apply Basis.eq_bo

Depends on / 依赖: Basis.eq_bot_of_rank_eq_zero, Classical, Classical.decEq, DecidableEq, Fin.cons, N.zero_mem, Nat.le_zero.mp, Nat.succ_le_succ_iff.mp, eq_bot_of_rank_eq_zero, generalizing, le_zero, mem_bot, rank_ih, rank_le, succ_le_succ_iff, x_mem, x_ortho, zero_mem
-/
def Submodule.inductionOnRankAux (b : Basis ι R M) (P : Submodule R M -> Sort*)
    (ih : forall N : Submodule R M,
      (forall N' <= N, forall x in N, (forall (c : R), forall y in N', c • x + y = (0 : M) -> c = 0) -> P N') -> P N)
    (n : Nat) (N : Submodule R M)
    (rank_le : forall {m : Nat} (v : Fin m -> N), LinearIndependent R ((↑) ∘ v : Fin m -> M) -> m <= n) :
    P N := by
  haveI : DecidableEq M := Classical.decEq M
  have Pbot : P ⊥ := by
    apply ih
    intro N _ x x_mem x_ortho
    exfalso
    rw [mem_bot] at x_mem
    simpa [x_mem] using x_ortho 1 0 N.zero_mem
  induction n generalizing N with
  | zero =>
    suffices N = ⊥ by rwa [this]
    apply Basis.eq_bot_of_rank_eq_zero b _ fun m hv => Nat.le_zero.mp (rank_le _ hv)
  | succ n rank_ih =>
    apply ih
    intro N' N'_le x x_mem x_ortho
    apply rank_ih
    intro m v hli
    refine Nat.succ_le_succ_iff.mp (rank_le (Fin.cons ⟨x, x_mem⟩ fun i => ⟨v i, N'_le (v i).2⟩) ?_)
    convert! hli.finCons' x _ ?_
    · ext i
      refine Fin.cases ?_ ?_ i <;> simp
    · intro c y hy hc
      refine x_ortho c y (Submodule.span_le.mpr ?_ hy) hc
      rintro _ ⟨z, rfl⟩
      exact (v z).2

end Induction

namespace Module.Basis

/--
lemma `mem_center_iff` / 引理 `mem_center_iff`

English:
lemma mem_center_iff
  statement: {A}
  proof: by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, h.3 _ _⟩
  · intro h
    rw [center]; rw [mem_ofPred_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y]; rw [linearCombination_apply]; rw

中文:
引理 mem_center_iff
  结论: {A}
  证明: by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, h.3 _ _⟩
  · intro h
    rw [center]; rw [mem_ofPred_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y]; rw [linearCombination_apply]; rw

Depends on / 依赖: Finset, Finset.mul_sum, Finset.sum_mul, b.linearCombination_repr, center, commute_iff_eq, intros, left_assoc, linearCombination_apply, linearCombination_repr, mem_ofPred_eq, mul_smul_comm, mul_sum, simp_rw, smul_mul_assoc, sum_mul
-/
lemma mem_center_iff {A}
    [Semiring R] [NonUnitalNonAssocSemiring A]
    [Module R A] [SMulCommClass R A A] [SMulCommClass R R A] [IsScalarTower R A A]
    (b : Basis ι R A) {z : A} :
    z in Set.center A ↔
      (forall i, Commute (b i) z) ∧ forall i j,
        z * (b i * b j) = (z * b i) * b j
          ∧ (b i * b j) * z = b i * (b j * z) := by
  constructor
  · intro h
    constructor
    · intro i
      apply (h.1 (b i)).symm
    · intros
      exact ⟨h.2 _ _, h.3 _ _⟩
  · intro h
    rw [center]; rw [mem_ofPred_eq]
    constructor
    case comm =>
      intro y
      rw [← b.linearCombination_repr y]; rw [linearCombination_apply]; rw [sum]; rw [commute_iff_eq]; rw [Finset.sum_mul]; rw [Finset.mul_sum]
      simp_rw [mul_smul_comm, smul_mul_assoc, (h.1 _).eq]
    case left_assoc =>
      intro c d
      rw [← b.linearCombination_repr c]; rw [← b.linearCombination_repr d]; rw [linearCombination_apply]; rw [linearCombination_apply]; rw [sum]; rw [sum]; rw [Finset.sum_mul]; rw [Finset.mul_sum]; rw [Finset.mul_sum]; rw [Finset.mul_sum]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
        Finset.smul_sum, smul_mul_assoc, mul_smul_comm, (h.2 _ _).1,
        (@SMulCommClass.smul_comm R R A)]
      rw [Finset.sum_comm]
    case right_assoc =>
      intro c d
      rw [← b.linearCombination_repr c]; rw [← b.linearCombination_repr d]; rw [linearCombination_apply]; rw [linearCombination_apply]; rw [sum]; rw [Finsupp.sum]; rw [Finset.sum_mul]
      simp_rw [smul_mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, Finset.mul_sum,
               Finset.smul_sum, smul_mul_assoc, mul_smul_comm, Finset.sum_mul, smul_mul_assoc,
               (h.2 _ _).2]

section RestrictScalars

variable {S : Type*} [CommRing R] [IsDomain R] [Ring S] [Nontrivial S] [AddCommGroup M]
variable [Algebra R S] [Module S M] [Module R M]
variable [IsScalarTower R S M] [IsTorsionFree R S] (b : Basis ι S M)
variable (R)

open Submodule

/--
Definition of `restrictScalars` / `restrictScalars` 的定义

English:
definition restrictScalars
  signature: : Basis ι R (span R (Set.range b))
  body: Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))

@[simp]

中文:
定义 restrictScalars
  签名: : Basis ι R (span R (Set.range b))
  定义体: Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))

@[simp]

Depends on / 依赖: Basis.span, b.linearIndependent.restrict_scalars, linearIndependent, one_ne_zero, restrict_scalars, smul_left_injective
-/
noncomputable def restrictScalars : Basis ι R (span R (Set.range b)) :=
  Basis.span (b.linearIndependent.restrict_scalars (smul_left_injective R one_ne_zero))

@[simp]
/--
theorem `restrictScalars_apply` / 定理 `restrictScalars_apply`

English:
theorem restrictScalars_apply
  given: (i : ι)
  statement: (b.restrictScalars R i : M) = b i
  proof: by
  simp only [Basis.restrictScalars, Basis.span_apply]

@[simp]

中文:
定理 restrictScalars_apply
  条件: (i : ι)
  结论: (b.restrictScalars R i : M) = b i
  证明: by
  simp only [Basis.restrictScalars, Basis.span_apply]

@[simp]

Depends on / 依赖: Basis.restrictScalars, Basis.span_apply, restrictScalars, span_apply
-/
theorem restrictScalars_apply (i : ι) : (b.restrictScalars R i : M) = b i := by
  simp only [Basis.restrictScalars, Basis.span_apply]

@[simp]
/--
theorem `restrictScalars_repr_apply` / 定理 `restrictScalars_repr_apply`

English:
theorem restrictScalars_repr_apply
  given: (m : span R (Set.range b)) (i : ι)
  proof: by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M ->ₗ[S] ι ->₀ S).restrictScalars R).domRestrict _
    DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only 

中文:
定理 restrictScalars_repr_apply
  条件: (m : span R (Set.range b)) (i : ι)
  证明: by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M ->ₗ[S] ι ->₀ S).restrictScalars R).domRestrict _
    DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only 

Depends on / 依赖: Algebra, Algebra.linearMap, Algebra.linearMap_apply, Basis.ext, Basis.repr_self, Basis.rest, DFunLike, DFunLike.congr_fun, Finsupp, Finsupp.mapRange.linearMap, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single, Function, Function.comp_apply, LinearEquiv, LinearEquiv.coe_toLinearMap, LinearMap, LinearMap.coe_comp, LinearMap.congr_fun, LinearMap.domRestrict_apply
-/
theorem restrictScalars_repr_apply (m : span R (Set.range b)) (i : ι) :
    algebraMap R S ((b.restrictScalars R).repr m i) = b.repr m i := by
  suffices
    Finsupp.mapRange.linearMap (Algebra.linearMap R S) ∘ₗ (b.restrictScalars R).repr.toLinearMap =
      ((b.repr : M ->ₗ[S] ι ->₀ S).restrictScalars R).domRestrict _
    DFunLike.congr_fun (LinearMap.congr_fun this m) i
  refine Basis.ext (b.restrictScalars R) fun _ => ?_
  simp only [LinearMap.coe_comp, LinearEquiv.coe_toLinearMap, Function.comp_apply, map_one,
    Basis.repr_self, Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single,
    Algebra.linearMap_apply, LinearMap.domRestrict_apply,
    Basis.restrictScalars_apply, LinearMap.coe_restrictScalars]

/--
theorem `mem_span_iff_repr_mem` / 定理 `mem_span_iff_repr_mem`

English:
theorem mem_span_iff_repr_mem
  given: (m : M)
  proof: by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, b.restrictScalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m]; rw [Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exa

中文:
定理 mem_span_iff_repr_mem
  条件: (m : M)
  证明: by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, b.restrictScalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m]; rw [Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exa

Depends on / 依赖: Finsupp, Finsupp.linearCombination_apply, Set.mem_range_self, algebraMap_smul, b.linearCombination_repr, b.restrictScalars, b.restrictScalars_repr_apply, linearCombination_apply, linearCombination_repr, mem_range_self, restrictScalars, restrictScalars_repr_apply, simp_rw, smul_mem, subset_span, sum_mem
-/
theorem mem_span_iff_repr_mem (m : M) :
    m in span R (Set.range b) ↔ forall i, b.repr m i in Set.range (algebraMap R S) := by
  refine
    ⟨fun hm i => ⟨(b.restrictScalars R).repr ⟨m, hm⟩ i, b.restrictScalars_repr_apply R ⟨m, hm⟩ i⟩,
      fun h => ?_⟩
  rw [← b.linearCombination_repr m]; rw [Finsupp.linearCombination_apply S _]
  refine sum_mem fun i _ => ?_
  obtain ⟨_, h⟩ := h i
  simp_rw [← h, algebraMap_smul]
  exact smul_mem _ _ (subset_span (Set.mem_range_self i))

end RestrictScalars

section AddSubgroup

variable {M R : Type*} [Ring R] [Nontrivial R] [IsAddTorsionFree R]
  [AddCommGroup M] [Module R M] (A : AddSubgroup M) {ι : Type*} (b : Basis ι R M)

/--
Definition of `addSubgroupOfClosure` / `addSubgroupOfClosure` 的定义

English:
definition addSubgroupOfClosure
  signature: (h : A = .closure (Set.range b))
  body: (b.restrictScalars Int).map
    LinearEquiv.ofEq _ _
      (by rw [h, ← Submodule.span_int_eq_addSubgroupClosure, toAddSubgroup_toIntSubmodule])

@[simp]

中文:
定义 addSubgroupOfClosure
  签名: (h : A = .closure (Set.range b))
  定义体: (b.restrictScalars Int).map
    LinearEquiv.ofEq _ _
      (by rw [h, ← Submodule.span_int_eq_addSubgroupClosure, toAddSubgroup_toIntSubmodule])

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofEq, Submodule, Submodule.span_int_eq_addSubgroupClosure, b.restrictScalars, restrictScalars, span_int_eq_addSubgroupClosure, toAddSubgroup_toIntSubmodule
-/
noncomputable def addSubgroupOfClosure (h : A = .closure (Set.range b)) :
    Basis ι Int A.toIntSubmodule :=
(b.restrictScalars Int).map
    LinearEquiv.ofEq _ _
      (by rw [h, ← Submodule.span_int_eq_addSubgroupClosure, toAddSubgroup_toIntSubmodule])

@[simp]
/--
theorem `addSubgroupOfClosure_apply` / 定理 `addSubgroupOfClosure_apply`

English:
theorem addSubgroupOfClosure_apply
  given: (h : A = .closure (Set.range b)) (i : ι)
  proof: by
  simp [addSubgroupOfClosure]

@[simp]

中文:
定理 addSubgroupOfClosure_apply
  条件: (h : A = .closure (Set.range b)) (i : ι)
  证明: by
  simp [addSubgroupOfClosure]

@[simp]

Depends on / 依赖: addSubgroupOfClosure
-/
theorem addSubgroupOfClosure_apply (h : A = .closure (Set.range b)) (i : ι) :
    b.addSubgroupOfClosure A h i = b i := by
  simp [addSubgroupOfClosure]

@[simp]
/--
theorem `addSubgroupOfClosure_repr_apply` / 定理 `addSubgroupOfClosure_repr_apply`

English:
theorem addSubgroupOfClosure_repr_apply
  given: (h : A = .closure (Set.range b)) (x : A) (i : ι)
  proof: by
  suffices Finsupp.mapRange.linearMap (Algebra.linearMap Int R) ∘ₗ
      (b.addSubgroupOfClosure A h).repr.toLinearMap =
        ((b.repr : M ->ₗ[R] ι ->₀ R).restrictScalars Int).domRestrict A.toIntSubmodule by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  exact (b.addSubgroupOfCl

中文:
定理 addSubgroupOfClosure_repr_apply
  条件: (h : A = .closure (Set.range b)) (x : A) (i : ι)
  证明: by
  suffices Finsupp.mapRange.linearMap (Algebra.linearMap Int R) ∘ₗ
      (b.addSubgroupOfClosure A h).repr.toLinearMap =
        ((b.repr : M ->ₗ[R] ι ->₀ R).restrictScalars Int).domRestrict A.toIntSubmodule by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  exact (b.addSubgroupOfCl

Depends on / 依赖: A.toIntSubmodule, Algebra, Algebra.linearMap, DFunLike, DFunLike.congr_fun, Finsupp, Finsupp.mapRange.linearMap, LinearMap, LinearMap.congr_fun, addSubgroupOfClosure, b.addSubgroupOfClosure, b.repr, congr_fun, domRestrict, linearMap, mapRange, repr.toLinearMap, restrictScalars, toIntSubmodule, toLinearMap
-/
theorem addSubgroupOfClosure_repr_apply (h : A = .closure (Set.range b)) (x : A) (i : ι) :
    (b.addSubgroupOfClosure A h).repr x i = b.repr x i := by
  suffices Finsupp.mapRange.linearMap (Algebra.linearMap Int R) ∘ₗ
      (b.addSubgroupOfClosure A h).repr.toLinearMap =
        ((b.repr : M ->ₗ[R] ι ->₀ R).restrictScalars Int).domRestrict A.toIntSubmodule by
    exact DFunLike.congr_fun (LinearMap.congr_fun this x) i
  exact (b.addSubgroupOfClosure A h).ext fun _ => by simp

end AddSubgroup

end Module.Basis
