/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.AdjointAction.Basic
public import Mathlib.Algebra.Lie.Nilpotent
public import Mathlib.Algebra.Lie.Normalizer

/-!
# Engel's theorem

This file contains a proof of Engel's theorem providing necessary and sufficient conditions for Lie
algebras and Lie modules to be nilpotent.

The key result `LieModule.isNilpotent_iff_forall` says that if `M` is a Lie module of a
Noetherian Lie algebra `L`, then `M` is nilpotent iff the image of `L → End(M)` consists of
nilpotent elements. In the special case that we have the adjoint representation `M = L`, this says
that a Lie algebra is nilpotent iff `ad x : End(L)` is nilpotent for all `x : L`.

Engel's theorem is true for any coefficients (i.e., it is really a theorem about Lie rings) and so
we work with coefficients in any commutative ring `R` throughout.

On the other hand, Engel's theorem is not true for infinite-dimensional Lie algebras and so a
finite-dimensionality assumption is required. We prove the theorem subject to the assumption
that the Lie algebra is Noetherian as an `R`-module, though actually we only need the slightly
weaker property that the relation `>` is well-founded on the complete lattice of Lie subalgebras.

## Remarks about the proof

Engel's theorem is usually proved in the special case that the coefficients are a field, and uses
an inductive argument on the dimension of the Lie algebra. One begins by choosing either a maximal
proper Lie subalgebra (in some proofs) or a maximal nilpotent Lie subalgebra (in other proofs, at
the cost of obtaining a weaker end result).

Since we work with general coefficients, we cannot induct on dimension and an alternate approach
must be taken. The key ingredient is the concept of nilpotency, not just for Lie algebras, but for
Lie modules. Using this concept, we define an _Engelian Lie algebra_ `LieAlgebra.IsEngelian` to
be one for which a Lie module is nilpotent whenever the action consists of nilpotent endomorphisms.
The argument then proceeds by selecting a maximal Engelian Lie subalgebra and showing that it cannot
be proper.

The first part of the traditional statement of Engel's theorem consists of the statement that if `M`
is a non-trivial `R`-module and `L ⊆ End(M)` is a finite-dimensional Lie subalgebra of nilpotent
elements, then there exists a non-zero element `m : M` that is annihilated by every element of `L`.
This follows trivially from the result established here `LieModule.isNilpotent_iff_forall`, that
`M` is a nilpotent Lie module over `L`, since the last non-zero term in the lower central series
will consist of such elements `m` (see: `LieModule.nontrivial_max_triv_of_isNilpotent`). It seems
that this result has not previously been established at this level of generality.

The second part of the traditional statement of Engel's theorem concerns nilpotency of the Lie
algebra and a proof of this for general coefficients appeared in the literature as long ago
[as 1937](zorn1937). This also follows trivially from `LieModule.isNilpotent_iff_forall` simply by
taking `M = L`.

It is pleasing that the two parts of the traditional statements of Engel's theorem are thus unified
into a single statement about nilpotency of Lie modules. This is not usually emphasised.

## Main definitions

  * `LieAlgebra.IsEngelian`
  * `LieAlgebra.isEngelian_of_isNoetherian`
  * `LieModule.isNilpotent_iff_forall`
  * `LieAlgebra.isNilpotent_iff_forall`

-/

@[expose] public section


universe u₁ u₂ u₃ u₄

variable {R : Type u₁} {L : Type u₂} {L₂ : Type u₃} {M : Type u₄}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

namespace LieSubmodule

open LieModule

variable {I : LieIdeal R L} {x : L} (hxI : R ∙ x ⊔ I = ⊤)
include hxI

/--
theorem `exists_smul_add_of_span_sup_eq_top` / 定理 `exists_smul_add_of_span_sup_eq_top`

English:
theorem exists_smul_add_of_span_sup_eq_top
  given: (y : L)
  statement: exists t : R, exists z in I, y = t • x + z
  proof: by
  have hy : y in (⊤ : Submodule R L) := Submodule.mem_top
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  exact ⟨t, z, hz, rfl⟩

中文:
定理 存在_smul_add_of_span_sup_eq_top
  条件: (y : L)
  结论: 存在 t : R, 存在 z in I, y = t • x + z
  证明: by
  have hy : y in (⊤ : Submodule R L) := Submodule.mem_top
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  exact ⟨t, z, hz, rfl⟩

Depends on / 依赖: Submodule, Submodule.mem_span_singleton, Submodule.mem_sup, Submodule.mem_top, mem_span_singleton, mem_sup, mem_top
-/
theorem exists_smul_add_of_span_sup_eq_top (y : L) : exists t : R, exists z in I, y = t • x + z := by
  have hy : y in (⊤ : Submodule R L) := Submodule.mem_top
  simp only [← hxI, Submodule.mem_sup, Submodule.mem_span_singleton] at hy
  obtain ⟨-, ⟨t, rfl⟩, z, hz, rfl⟩ := hy
  exact ⟨t, z, hz, rfl⟩

/--
theorem `lie_top_eq_of_span_sup_eq_top` / 定理 `lie_top_eq_of_span_sup_eq_top`

English:
theorem lie_top_eq_of_span_sup_eq_top
  given: (N : LieSubmodule R L M)
  proof: by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, true_and,
    Submodule.map_coe, toEnd_apply_apply]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono fun z hz => ?_)
  · rintro z ⟨y, n, hn : n in N, rfl⟩
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_

中文:
定理 lie_top_eq_of_span_sup_eq_top
  条件: (N : Lie子模 R L M)
  证明: by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, true_and,
    Submodule.map_coe, toEnd_apply_apply]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono fun z hz => ?_)
  · rintro z ⟨y, n, hn : n in N, rfl⟩
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_

Depends on / 依赖: N.smul_mem, SetLike, SetLike.mem_coe, Submodule, Submodule.map_coe, Submodule.mem_sup, Submodule.span_le.mpr, Submodule.span_mono, Submodule.span_union, Submodule.subset_span, Submodule.sup_span, exists_smul_add_of_span_sup_eq_top, le_antisymm, lieIdeal_oper_eq_linear_span, lie_smul, map_coe, mem_coe, mem_sup, mem_top, smul_mem
-/
theorem lie_top_eq_of_span_sup_eq_top (N : LieSubmodule R L M) :
    (↑⁅(⊤ : LieIdeal R L), N⁆ : Submodule R M) =
      (N : Submodule R M).map (toEnd R L M x) ⊔ (↑⁅I, N⁆ : Submodule R M) := by
  simp only [lieIdeal_oper_eq_linear_span', Submodule.sup_span, mem_top, true_and,
    Submodule.map_coe, toEnd_apply_apply]
  refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_mono fun z hz => ?_)
  · rintro z ⟨y, n, hn : n in N, rfl⟩
    obtain ⟨t, z, hz, rfl⟩ := exists_smul_add_of_span_sup_eq_top hxI y
    simp only [SetLike.mem_coe, Submodule.span_union, Submodule.mem_sup]
    exact
      ⟨t • ⁅x, n⁆, Submodule.subset_span ⟨t • n, N.smul_mem' t hn, lie_smul t x n⟩, ⁅z, n⁆,
        Submodule.subset_span ⟨z, hz, n, hn, rfl⟩, by simp⟩
  · rcases hz with (⟨m, hm, rfl⟩ | ⟨y, -, m, hm, rfl⟩)
    exacts [⟨x, m, hm, rfl⟩, ⟨y, m, hm, rfl⟩]

/--
theorem `lcs_le_lcs_of_is_nilpotent_span_sup_eq_top` / 定理 `lcs_le_lcs_of_is_nilpotent_span_sup_eq_top`

English:
theorem lcs_le_lcs_of_is_nilpotent_span_sup_eq_top
  statement: {n i j : Nat}
  proof: by
  suffices
    forall l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) <=
        (I.lcs M j : Submodule R M).map (toEnd R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using! this n
  intro l
  induc

中文:
定理 lcs_le_lcs_of_is_nilpotent_span_sup_eq_top
  结论: {n i j : 自然数}
  证明: by
  suffices
    forall l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) <=
        (I.lcs M j : Submodule R M).map (toEnd R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using! this n
  intro l
  induc

Depends on / 依赖: I.lcs, LieIdeal, LieIdeal.incl_coe, LieIdeal.lcs_succ, Module, Module.End.one_eq_id, Submodule, Submodule.map_id, Submodule.map_zero, add_succ, add_zero, bot_sup_eq, i.add_succ, incl_coe, lcs_succ, le_sup_of_le_left, lie_top_eq_of_span_sup_eq_top, map_id, map_zero, one_eq_id
-/
theorem lcs_le_lcs_of_is_nilpotent_span_sup_eq_top {n i j : Nat}
    (hxn : toEnd R L M x ^ n = 0) (hIM : lowerCentralSeries R L M i <= I.lcs M j) :
    lowerCentralSeries R L M (i + n) <= I.lcs M (j + 1) := by
  suffices
    forall l,
      ((⊤ : LieIdeal R L).lcs M (i + l) : Submodule R M) <=
        (I.lcs M j : Submodule R M).map (toEnd R L M x ^ l) ⊔
          (I.lcs M (j + 1) : Submodule R M)
    by simpa only [bot_sup_eq, LieIdeal.incl_coe, Submodule.map_zero, hxn] using! this n
  intro l
  induction l with
  | zero =>
    simp only [add_zero, LieIdeal.lcs_succ, pow_zero, Module.End.one_eq_id,
      Submodule.map_id]
    exact le_sup_of_le_left hIM
  | succ l ih =>
    simp only [LieIdeal.lcs_succ, i.add_succ l, lie_top_eq_of_span_sup_eq_top hxI, sup_le_iff]
    refine ⟨(Submodule.map_mono ih).trans ?_, le_sup_of_le_right ?_⟩
    · rw [Submodule.map_sup, ← Submodule.map_comp, ← Module.End.mul_eq_comp, ← pow_succ', ←
        I.lcs_succ]
      grw [coe_map_toEnd_le]
    · norm_cast
      gcongr
      exact le_trans (antitone_lowerCentralSeries R L M le_self_add) hIM

/--
theorem `isNilpotentOfIsNilpotentSpanSupEqTop` / 定理 `isNilpotentOfIsNilpotentSpanSupEqTop`

English:
theorem isNilpotentOfIsNilpotentSpanSupEqTop
  statement: (hnp : IsNilpotent <| toEnd R L M x)
  proof: by
  obtain ⟨n, hn⟩ := hnp
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R I M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← toSubmodule_inj, I.coe_lcs_eq, hk, bot_toSubmodule]
  suffices forall l, lowerCentralSeries R L M (l * n) <= I.lcs M l by
    rw [isNilpotent_iff R]
    use k * n
    simpa [h

中文:
定理 isNilpotentOfIsNilpotentSpanSupEqTop
  结论: (hnp : 是幂零 <| toEnd R L M x)
  证明: by
  obtain ⟨n, hn⟩ := hnp
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R I M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← toSubmodule_inj, I.coe_lcs_eq, hk, bot_toSubmodule]
  suffices forall l, lowerCentralSeries R L M (l * n) <= I.lcs M l by
    rw [isNilpotent_iff R]
    use k * n
    simpa [h

Depends on / 依赖: I.coe_lcs_eq, I.lcs, IsNilpotent, IsNilpotent.nilpotent, bot_toSubmodule, coe_lcs_eq, isNilpotent_iff, l.succ_mul, lcs_le_lcs_of_is_nilpotent_span_sup_eq_top, lowerCentralSeries, nilpotent, succ_mul, toSubmodule_inj
-/
theorem isNilpotentOfIsNilpotentSpanSupEqTop (hnp : IsNilpotent <| toEnd R L M x)
    (hIM : IsNilpotent I M) : IsNilpotent L M := by
  obtain ⟨n, hn⟩ := hnp
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R I M
  have hk' : I.lcs M k = ⊥ := by
    simp only [← toSubmodule_inj, I.coe_lcs_eq, hk, bot_toSubmodule]
  suffices forall l, lowerCentralSeries R L M (l * n) <= I.lcs M l by
    rw [isNilpotent_iff R]
    use k * n
    simpa [hk'] using this k
  intro l
  induction l with
  | zero => simp
  | succ l ih => exact (l.succ_mul n).symm ▸ lcs_le_lcs_of_is_nilpotent_span_sup_eq_top hxI hn ih

end LieSubmodule

section LieAlgebra

open LieModule hiding IsNilpotent

variable (R L)

/--
Definition of `LieAlgebra.IsEngelian` / `LieAlgebra.IsEngelian` 的定义

English:
definition LieAlgebra.IsEngelian
  signature: : Prop
  body: forall (M : Type u₄) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
    (forall x : L, IsNilpotent (toEnd R L M x)) -> LieModule.IsNilpotent L M

中文:
定义 Lie代数.IsEngelian
  签名: : 命题
  定义体: forall (M : Type u₄) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
    (forall x : L, IsNilpotent (toEnd R L M x)) -> LieModule.IsNilpotent L M

Depends on / 依赖: AddCommGroup, IsNilpotent, LieModule, LieModule.IsNilpotent, LieRingModule, Module
-/
def LieAlgebra.IsEngelian : Prop :=
  forall (M : Type u₄) [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M],
    (forall x : L, IsNilpotent (toEnd R L M x)) -> LieModule.IsNilpotent L M

variable {R L}

/--
theorem `LieAlgebra.isEngelian_of_subsingleton` / 定理 `LieAlgebra.isEngelian_of_subsingleton`

English:
theorem LieAlgebra.isEngelian_of_subsingleton
  given: [Subsingleton L]
  statement: LieAlgebra.IsEngelian R L
  proof: by
  intro M _i1 _i2 _i3 _i4 _h
  use 1
  simp

中文:
定理 Lie代数.isEngelian_of_subsingleton
  条件: [子单例 L]
  结论: Lie代数.IsEngelian R L
  证明: by
  intro M _i1 _i2 _i3 _i4 _h
  use 1
  simp
-/
theorem LieAlgebra.isEngelian_of_subsingleton [Subsingleton L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 _h
  use 1
  simp

/--
theorem `Function.Surjective.isEngelian` / 定理 `Function.Surjective.isEngelian`

English:
theorem Function.Surjective.isEngelian
  statement: {f : L ->ₗ⁅R⁆ L₂} (hf : Function.Surjective f)
  proof: by
  intro M _i1 _i2 _i3 _i4 h'
  let : LieRingModule L M := LieRingModule.compLieHom M f
  let : LieModule R L M := compLieHom M f
  have hnp : forall x, IsNilpotent (toEnd R L M x) := fun x => h' (f x)
  have surj_id : Function.Surjective (LinearMap.id : M ->ₗ[R] M) := Function.surjective_id
  hav

中文:
定理 函数.满射.isEngelian
  结论: {f : L ->ₗ⁅R⁆ L₂} (hf : 函数.满射 f)
  证明: by
  intro M _i1 _i2 _i3 _i4 h'
  let : LieRingModule L M := LieRingModule.compLieHom M f
  let : LieModule R L M := compLieHom M f
  have hnp : forall x, IsNilpotent (toEnd R L M x) := fun x => h' (f x)
  have surj_id : Function.Surjective (LinearMap.id : M ->ₗ[R] M) := Function.surjective_id
  hav

Depends on / 依赖: Function, Function.Surjective, Function.surjective_id, IsNilpotent, LieModule, LieModule.IsNilpotent, LieRingModule, LieRingModule.compLieHom, LinearMap, LinearMap.id, Surjective, compLieHom, hf.lieModuleIsNilpotent, lieModuleIsNilpotent, surj_id, surjective_id
-/
theorem Function.Surjective.isEngelian {f : L ->ₗ⁅R⁆ L₂} (hf : Function.Surjective f)
    (h : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L) : LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ := by
  intro M _i1 _i2 _i3 _i4 h'
  let : LieRingModule L M := LieRingModule.compLieHom M f
  let : LieModule R L M := compLieHom M f
  have hnp : forall x, IsNilpotent (toEnd R L M x) := fun x => h' (f x)
  have surj_id : Function.Surjective (LinearMap.id : M ->ₗ[R] M) := Function.surjective_id
  have : LieModule.IsNilpotent L M := h M hnp
  apply hf.lieModuleIsNilpotent _ surj_id
  aesop

/--
theorem `LieEquiv.isEngelian_iff` / 定理 `LieEquiv.isEngelian_iff`

English:
theorem LieEquiv.isEngelian_iff
  given: (e : L ≃ₗ⁅R⁆ L₂)
  proof: ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩

中文:
定理 Lie等价.isEngelian_iff
  条件: (e : L ≃ₗ⁅R⁆ L₂)
  证明: ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩

Depends on / 依赖: e.surjective.isEngelian, e.symm.surjective.isEngelian, isEngelian, surjective
-/
theorem LieEquiv.isEngelian_iff (e : L ≃ₗ⁅R⁆ L₂) :
    LieAlgebra.IsEngelian.{u₁, u₂, u₄} R L ↔ LieAlgebra.IsEngelian.{u₁, u₃, u₄} R L₂ :=
  ⟨e.surjective.isEngelian, e.symm.surjective.isEngelian⟩

/--
theorem `LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer` / 定理 `LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer`

English:
theorem LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer
  statement: {K : LieSubalgebra R L}
  proof: by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x in K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _)

中文:
定理 Lie代数.存在_engelian_lieSubalgebra_of_lt_normalizer
  结论: {K : Lie子代数 R L}
  证明: by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x in K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _)

Depends on / 依赖: K.normalizer, LieSubalgebra, LieSubalgebra.lie_mem_sup_of_mem_normalizer, LieSubalgebra.toSubmodule_le_toSubmodule, Set.mem_singleton, SetLike, SetLike.exists_of_lt, Submodule, Submodule.mem_sup_left, Submodule.span_singleton_le_, Submodule.subset_span, exists_of_lt, le_sup_right, lie_mem, lie_mem_sup_of_mem_normalizer, mem_singleton, mem_sup_left, normalizer, span_singleton_le_, subset_span
-/
theorem LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer {K : LieSubalgebra R L}
    (hK₁ : LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K) (hK₂ : K < K.normalizer) :
    exists (K' : LieSubalgebra R L), LieAlgebra.IsEngelian.{u₁, u₂, u₄} R K' ∧ K < K' := by
  obtain ⟨x, hx₁, hx₂⟩ := SetLike.exists_of_lt hK₂
  let K' : LieSubalgebra R L :=
    { (R ∙ x) ⊔ (K : Submodule R L) with
      lie_mem' := fun {y z} => LieSubalgebra.lie_mem_sup_of_mem_normalizer hx₁ }
  have hxK' : x in K' := Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
  have hKK' : K <= K' := (LieSubalgebra.toSubmodule_le_toSubmodule K K').mp le_sup_right
  have hK' : K' <= K.normalizer := by
    rw [← LieSubalgebra.toSubmodule_le_toSubmodule]
    exact sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr hx₁) hK₂.le
  refine ⟨K', ?_, lt_iff_le_and_ne.mpr ⟨hKK', fun contra => hx₂ (contra.symm ▸ hxK')⟩⟩
  intro M _i1 _i2 _i3 _i4 h
  obtain ⟨I, hI₁ : (I : LieSubalgebra R K') = LieSubalgebra.ofLe hKK'⟩ :=
    LieSubalgebra.exists_nested_lieIdeal_ofLe_normalizer hKK' hK'
  have hI₂ : R ∙ (⟨x, hxK'⟩ : K') ⊔ LieSubmodule.toSubmodule I = ⊤ := by
    rw [← LieIdeal.toLieSubalgebra_toSubmodule R K' I]; rw [hI₁]
    apply Submodule.map_injective_of_injective (K' : Submodule R L).injective_subtype
    simp only [LieSubalgebra.coe_ofLe, Submodule.map_sup, Submodule.map_subtype_range_inclusion,
      Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_subtype_span_singleton]
  have e : K ≃ₗ⁅R⁆ I :=
    (LieSubalgebra.equivOfLe hKK').trans
      (LieEquiv.ofEq _ _ ((LieSubalgebra.coe_set_eq _ _).mpr hI₁.symm))
  have hI₃ : LieAlgebra.IsEngelian R I := e.isEngelian_iff.mp hK₁
  exact LieSubmodule.isNilpotentOfIsNilpotentSpanSupEqTop hI₂ (h _) (hI₃ _ fun x => h x)

attribute [local instance] LieSubalgebra.subsingleton_bot
attribute [local instance 100] LieRing.ofAssociativeRing

/--
theorem `LieAlgebra.isEngelian_of_isNoetherian` / 定理 `LieAlgebra.isEngelian_of_isNoetherian`

English:
theorem LieAlgebra.isEngelian_of_isNoetherian
  given: [IsNoetherian R L]
  statement: LieAlgebra.IsEngelian R L
  proof: by
  intro M _i1 _i2 _i3 _i4 h
  rw [← isNilpotent_range_toEnd_iff R]
  let L' := (toEnd R L M).range
  replace h : forall y : L', IsNilpotent (y : Module.End R M) := by
    rintro ⟨-, ⟨y, rfl⟩⟩
    simp [h]
  change LieModule.IsNilpotent L' M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngeli

中文:
定理 Lie代数.isEngelian_of_isNoetherian
  条件: [是Noether R L]
  结论: Lie代数.IsEngelian R L
  证明: by
  intro M _i1 _i2 _i3 _i4 h
  rw [← isNilpotent_range_toEnd_iff R]
  let L' := (toEnd R L M).range
  replace h : forall y : L', IsNilpotent (y : Module.End R M) := by
    rintro ⟨-, ⟨y, rfl⟩⟩
    simp [h]
  change LieModule.IsNilpotent L' M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngeli

Depends on / 依赖: IsEngelian, IsNilpotent, LieAlgebra, LieAlgebra.IsEngelian, LieAlgebra.isEngelian_of_subsingleton, LieModule, LieModule.IsNilpotent, LieSubalgebra, LieSubalgebra.toEnd_eq, Module, Module.End, Nonempty, isEngelian_of_subsingleton, isNilpotent_of_top_iff, isNilpotent_range_toEnd_iff, replace, s.Nonempty, toEnd_eq
-/
theorem LieAlgebra.isEngelian_of_isNoetherian [IsNoetherian R L] : LieAlgebra.IsEngelian R L := by
  intro M _i1 _i2 _i3 _i4 h
  rw [← isNilpotent_range_toEnd_iff R]
  let L' := (toEnd R L M).range
  replace h : forall y : L', IsNilpotent (y : Module.End R M) := by
    rintro ⟨-, ⟨y, rfl⟩⟩
    simp [h]
  change LieModule.IsNilpotent L' M
  let s := {K : LieSubalgebra R L' | LieAlgebra.IsEngelian R K}
  have hs : s.Nonempty := ⟨⊥, LieAlgebra.isEngelian_of_subsingleton⟩
  suffices ⊤ in s by
    rw [← isNilpotent_of_top_iff (R := R)]
    apply this M
    simp [LieSubalgebra.toEnd_eq, h]
  have : forall K in s, K != ⊤ -> exists K' in s, K < K' := by
    rintro K (hK₁ : LieAlgebra.IsEngelian R K) hK₂
    apply LieAlgebra.exists_engelian_lieSubalgebra_of_lt_normalizer hK₁
    apply lt_of_le_of_ne K.le_normalizer
    rw [Ne]; rw [eq_comm]; rw [K.normalizer_eq_self_iff]; rw [← Ne]; rw [←
      LieSubmodule.nontrivial_iff_ne_bot R K]
have : Nontrivial (L' ⧸ K.toLieSubmodule) := Submodule.Quotient.nontrivial_iff.2 by simpa
    have : LieModule.IsNilpotent K (L' ⧸ K.toLieSubmodule) := by
      refine hK₁ _ fun x => ?_
      have hx := LieAlgebra.isNilpotent_ad_of_isNilpotent (h x)
      apply Module.End.IsNilpotent.mapQ ?_ hx
      intro X HX
      simp only [LieSubalgebra.coe_toLieSubmodule, LieSubalgebra.mem_toSubmodule] at HX
      simp only [LieSubalgebra.coe_toLieSubmodule, Submodule.mem_comap, ad_apply,
        LieSubalgebra.mem_toSubmodule]
      exact LieSubalgebra.lie_mem K x.prop HX
    exact nontrivial_max_triv_of_isNilpotent R K (L' ⧸ K.toLieSubmodule)
  have _i5 : IsNoetherian R L' := by
    refine isNoetherian_of_surjective (LieHom.rangeRestrict (toEnd R L M)).toLinearMap ?_
    simp only [LinearMap.range_eq_top]
    exact LieHom.surjective_rangeRestrict (toEnd R L M)
  obtain ⟨K, hK₁, hK₂⟩ := (LieSubalgebra.wellFoundedGT_of_noetherian R L').wf.has_min s hs
  obtain rfl : K = ⊤ := by grind
  exact hK₁

/--
theorem `LieModule.isNilpotent_iff_forall` / 定理 `LieModule.isNilpotent_iff_forall`

English:
theorem LieModule.isNilpotent_iff_forall
  given: [IsNoetherian R L]
  proof: ⟨fun _ => isNilpotent_toEnd_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩

中文:
定理 Lie模.isNilpotent_iff_对任意
  条件: [是Noether R L]
  证明: ⟨fun _ => isNilpotent_toEnd_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩

Depends on / 依赖: LieAlgebra, LieAlgebra.isEngelian_of_isNoetherian, isEngelian_of_isNoetherian, isNilpotent_toEnd_of_isNilpotent
-/
theorem LieModule.isNilpotent_iff_forall [IsNoetherian R L] :
LieModule.IsNilpotent L M ↔ forall x, _root_.IsNilpotent toEnd R L M x :=
  ⟨fun _ => isNilpotent_toEnd_of_isNilpotent R L M,
   fun h => LieAlgebra.isEngelian_of_isNoetherian M h⟩

/--
theorem `LieModule.isNilpotent_iff_forall'` / 定理 `LieModule.isNilpotent_iff_forall'`

English:
theorem LieModule.isNilpotent_iff_forall'
  given: [IsNoetherian R M]
  proof: by
  rw [← isNilpotent_range_toEnd_iff (R := R)]; rw [LieModule.isNilpotent_iff_forall (R := R)]; simp

中文:
定理 Lie模.isNilpotent_iff_对任意'
  条件: [是Noether R M]
  证明: by
  rw [← isNilpotent_range_toEnd_iff (R := R)]; rw [LieModule.isNilpotent_iff_forall (R := R)]; simp

Depends on / 依赖: LieModule, LieModule.isNilpotent_iff_forall, isNilpotent_iff_forall, isNilpotent_range_toEnd_iff
-/
theorem LieModule.isNilpotent_iff_forall' [IsNoetherian R M] :
LieModule.IsNilpotent L M ↔ forall x, _root_.IsNilpotent toEnd R L M x := by
  rw [← isNilpotent_range_toEnd_iff (R := R)]; rw [LieModule.isNilpotent_iff_forall (R := R)]; simp

/--
theorem `LieAlgebra.isNilpotent_iff_forall` / 定理 `LieAlgebra.isNilpotent_iff_forall`

English:
theorem LieAlgebra.isNilpotent_iff_forall
  given: [IsNoetherian R L]
  proof: LieModule.isNilpotent_iff_forall

中文:
定理 Lie代数.isNilpotent_iff_对任意
  条件: [是Noether R L]
  证明: LieModule.isNilpotent_iff_forall

Depends on / 依赖: LieModule, LieModule.isNilpotent_iff_forall, isNilpotent_iff_forall
-/
theorem LieAlgebra.isNilpotent_iff_forall [IsNoetherian R L] :
LieRing.IsNilpotent L ↔ forall x, IsNilpotent LieAlgebra.ad R L x :=
  LieModule.isNilpotent_iff_forall

end LieAlgebra
