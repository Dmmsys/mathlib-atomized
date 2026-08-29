/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-! # Free modules over PID

A free `R`-module `M` is a module with a basis over `R`,
equivalently it is an `R`-module linearly equivalent to `ι →₀ R` for some `ι`.

This file proves a submodule of a free `R`-module of finite rank is also
a free `R`-module of finite rank, if `R` is a principal ideal domain (PID),
i.e. we have instances `[IsDomain R] [IsPrincipalIdealRing R]`.
We express "free `R`-module of finite rank" as a module `M` which has a basis
`b : ι → R`, where `ι` is a `Fintype`.
We call the cardinality of `ι` the rank of `M` in this file;
it would be equal to `finrank R M` if `R` is a field and `M` is a vector space.

## Main results

In this section, `M` is a free and finitely generated `R`-module, and
`N` is a submodule of `M`.

- `Submodule.inductionOnRank`: if `P` holds for `⊥ : Submodule R M` and if
  `P N` follows from `P N'` for all `N'` that are of lower rank, then `P` holds
  on all submodules

- `Submodule.exists_basis_of_pid`: if `R` is a PID, then `N : Submodule R M` is
  free and finitely generated. This is the first part of the structure theorem
  for modules.

- `Submodule.smithNormalForm`: if `R` is a PID, then `M` has a basis
  `bM` and `N` has a basis `bN` such that `bN i = a i • bM i`.
  Equivalently, a linear map `f : M →ₗ M` with `range f = N` can be written as
  a matrix in Smith normal form, a diagonal matrix with the coefficients `a i`
  along the diagonal.

## Tags

free module, finitely generated module, rank, structure theorem

-/

@[expose] public section

open Module

universe u v

section Ring

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable {ι : Type*} (b : Basis ι R M)

open Submodule.IsPrincipal Submodule

/--
theorem `eq_bot_of_generator_maximal_map_eq_zero` / 定理 `eq_bot_of_generator_maximal_map_eq_zero`

English:
theorem eq_bot_of_generator_maximal_map_eq_zero
  statement: (b : Basis ι R M) {N : Submodule R M}
  proof: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine b.ext_elem fun i => ?_
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero]; rw [Finsupp.zero_apply]
  exact
    (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _
      ⟨x, hx, rfl⟩

中文:
定理 eq_bot_of_generator_maximal_map_eq_zero
  结论: (b : Basis ι R M) {N : Submodule R M}
  证明: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine b.ext_elem fun i => ?_
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero]; rw [Finsupp.zero_apply]
  exact
    (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _
      ⟨x, hx, rfl⟩

Depends on / 依赖: Finsupp, Finsupp.lapply, Finsupp.zero_apply, Submodule, Submodule.eq_bot_iff, b.ext_elem, b.repr, eq_bot_iff, eq_bot_iff_generator_eq_zero, ext_elem, lapply, map_zero, not_bot_lt_iff, zero_apply
-/
theorem eq_bot_of_generator_maximal_map_eq_zero (b : Basis ι R M) {N : Submodule R M}
    {ϕ : M ->ₗ[R] R} (hϕ : forall ψ : M ->ₗ[R] R, ¬N.map ϕ < N.map ψ) [(N.map ϕ).IsPrincipal]
    (hgen : generator (N.map ϕ) = (0 : R)) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine b.ext_elem fun i => ?_
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero]; rw [Finsupp.zero_apply]
  exact
    (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _
      ⟨x, hx, rfl⟩

/--
theorem `eq_bot_of_generator_maximal_submoduleImage_eq_zero` / 定理 `eq_bot_of_generator_maximal_submoduleImage_eq_zero`

English:
theorem eq_bot_of_generator_maximal_submoduleImage_eq_zero
  statement: {N O : Submodule R M} (b : Basis ι R O)
  proof: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine (mk_eq_zero _ _).mp (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i => ?_)
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero]; rw [Finsupp.zero_apply]
  refine (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapp

中文:
定理 eq_bot_of_generator_maximal_submoduleImage_eq_zero
  结论: {N O : Submodule R M} (b : Basis ι R O)
  证明: by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine (mk_eq_zero _ _).mp (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i => ?_)
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero]; rw [Finsupp.zero_apply]
  refine (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapp

Depends on / 依赖: Finsupp, Finsupp.lapply, Finsupp.zero_apply, LinearMap, LinearMap.mem_submoduleImage_of_le, Submodule, Submodule.eq_bot_iff, b.ext_elem, b.repr, eq_bot_iff, eq_bot_iff_generator_eq_zero, ext_elem, lapply, map_zero, mem_submoduleImage_of_le, mk_eq_zero, not_bot_lt_iff, zero_apply
-/
theorem eq_bot_of_generator_maximal_submoduleImage_eq_zero {N O : Submodule R M} (b : Basis ι R O)
    (hNO : N <= O) {ϕ : O ->ₗ[R] R} (hϕ : forall ψ : O ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (hgen : generator (ϕ.submoduleImage N) = 0) : N = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  refine (mk_eq_zero _ _).mp (show (⟨x, hNO hx⟩ : O) = 0 from b.ext_elem fun i => ?_)
  rw [(eq_bot_iff_generator_eq_zero _).mpr hgen] at hϕ
  rw [map_zero]; rw [Finsupp.zero_apply]
  refine (Submodule.eq_bot_iff _).mp (not_bot_lt_iff.1 <| hϕ (Finsupp.lapply i ∘ₗ ↑b.repr)) _ ?_
  exact (LinearMap.mem_submoduleImage_of_le hNO).mpr ⟨x, hx, rfl⟩

end Ring

open Submodule.IsPrincipal in
/--
theorem `dvd_generator_iff` / 定理 `dvd_generator_iff`

English:
theorem dvd_generator_iff
  statement: {R : Type*} [CommSemiring R] {I : Ideal R} [I.IsPrincipal] {x : R}
  proof: by
  simp_rw [le_antisymm_iff, I.span_singleton_le_iff_mem.2 hx, and_true, ← Ideal.mem_span_singleton]
  conv_rhs => rw [← span_singleton_generator I, Submodule.span_singleton_le_iff_mem]

中文:
定理 dvd_generator_iff
  结论: {R : 类型} [CommSemiring R] {I : Ideal R} [I.IsPrincipal] {x : R}
  证明: by
  simp_rw [le_antisymm_iff, I.span_singleton_le_iff_mem.2 hx, and_true, ← Ideal.mem_span_singleton]
  conv_rhs => rw [← span_singleton_generator I, Submodule.span_singleton_le_iff_mem]

Depends on / 依赖: I.span_singleton_le_iff_mem, Ideal.mem_span_singleton, Submodule, Submodule.span_singleton_le_iff_mem, and_true, conv_rhs, le_antisymm_iff, mem_span_singleton, simp_rw, span_singleton_generator, span_singleton_le_iff_mem
-/
theorem dvd_generator_iff {R : Type*} [CommSemiring R] {I : Ideal R} [I.IsPrincipal] {x : R}
    (hx : x in I) : x ∣ generator I ↔ I = Ideal.span {x} := by
  simp_rw [le_antisymm_iff, I.span_singleton_le_iff_mem.2 hx, and_true, ← Ideal.mem_span_singleton]
  conv_rhs => rw [← span_singleton_generator I, Submodule.span_singleton_le_iff_mem]

section PrincipalIdealDomain

open Submodule.IsPrincipal Set Submodule

variable {ι : Type*} {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M] {b : ι -> M}

section StrongRankCondition

variable [IsPrincipalIdealRing R]

open Submodule.IsPrincipal

/--
theorem `generator_maximal_submoduleImage_dvd` / 定理 `generator_maximal_submoduleImage_dvd`

English:
theorem generator_maximal_submoduleImage_dvd
  statement: {N O : Submodule R M} (hNO : N <= O) {ϕ : O ->ₗ[R] R}
  proof: by
  let a : R := generator (ϕ.submoduleImage N)
  let d : R := IsPrincipal.generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ :=
    (mem_iff_generator_dvd _).mp (subset_span

中文:
定理 generator_maximal_submoduleImage_dvd
  结论: {N O : Submodule R M} (hNO : N <= O) {ϕ : O ->ₗ[R] R}
  证明: by
  let a : R := generator (ϕ.submoduleImage N)
  let d : R := IsPrincipal.generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ :=
    (mem_iff_generator_dvd _).mp (subset_span

Depends on / 依赖: Ideal.span, IsPrincipal, IsPrincipal.generator, Submodule, Submodule.span, d_dvd_left, d_dvd_right, dvd_generator_iff, dvd_trans, generator, mem_iff_generator_dvd, mem_insert, mem_insert_of_mem, mem_singleton, span_singleton_generator, submoduleImage, subset_span
-/
theorem generator_maximal_submoduleImage_dvd {N O : Submodule R M} (hNO : N <= O) {ϕ : O ->ₗ[R] R}
    (hϕ : forall ψ : O ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N)
    [(ϕ.submoduleImage N).IsPrincipal] (y : M) (yN : y in N)
    (ϕy_eq : ϕ ⟨y, hNO yN⟩ = generator (ϕ.submoduleImage N)) (ψ : O ->ₗ[R] R) :
    generator (ϕ.submoduleImage N) ∣ ψ ⟨y, hNO yN⟩ := by
  let a : R := generator (ϕ.submoduleImage N)
  let d : R := IsPrincipal.generator (Submodule.span R {a, ψ ⟨y, hNO yN⟩})
  have d_dvd_left : d ∣ a := (mem_iff_generator_dvd _).mp (subset_span (mem_insert _ _))
  have d_dvd_right : d ∣ ψ ⟨y, hNO yN⟩ :=
    (mem_iff_generator_dvd _).mp (subset_span (mem_insert_of_mem _ (mem_singleton _)))
  refine dvd_trans ?_ d_dvd_right
  rw [dvd_generator_iff]; rw [Ideal.span]; rw [←
    span_singleton_generator (Submodule.span R {a]; rw [ψ ⟨y]; rw [hNO yN⟩})]
  · obtain ⟨r₁, r₂, d_eq⟩ : exists r₁ r₂ : R, d = r₁ * a + r₂ * ψ ⟨y, hNO yN⟩ := by
      obtain ⟨r₁, r₂', hr₂', hr₁⟩ :=
        mem_span_insert.mp (IsPrincipal.generator_mem (Submodule.span R {a, ψ ⟨y, hNO yN⟩}))
      obtain ⟨r₂, rfl⟩ := mem_span_singleton.mp hr₂'
      exact ⟨r₁, r₂, hr₁⟩
    let ψ' : O ->ₗ[R] R := r₁ • ϕ + r₂ • ψ
    have : span R {d} <= ψ'.submoduleImage N := by
      rw [span_le]; rw [singleton_subset_iff]; rw [SetLike.mem_coe]; rw [LinearMap.mem_submoduleImage_of_le hNO]
      refine ⟨y, yN, ?_⟩
      change r₁ * ϕ ⟨y, hNO yN⟩ + r₂ * ψ ⟨y, hNO yN⟩ = d
      rw [d_eq]; rw [ϕy_eq]
    refine
      le_antisymm (this.trans (le_of_eq ?_)) (Ideal.span_singleton_le_span_singleton.mpr d_dvd_left)
    rw [span_singleton_generator]
    apply (le_trans _ this).eq_of_not_lt' (hϕ ψ')
    rw [← span_singleton_generator (ϕ.submoduleImage N)]
    exact Ideal.span_singleton_le_span_singleton.mpr d_dvd_left
  · exact subset_span (mem_insert _ _)

variable [IsDomain R]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `Submodule.basis_of_pid_aux` / 定理 `Submodule.basis_of_pid_aux`

English:
theorem Submodule.basis_of_pid_aux
  statement: [Finite ι] {O : Type*} [AddCommGroup O] [Module R O]
  proof: by
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : exists ϕ : M ->ₗ[R] R, forall ψ : M ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_max

中文:
定理 Submodule.basis_of_pid_aux
  结论: [Finite ι] {O : 类型} [AddCommGroup O] [Module R O]
  证明: by
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : exists ϕ : M ->ₗ[R] R, forall ψ : M ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_max
-/
theorem Submodule.basis_of_pid_aux [Finite ι] {O : Type*} [AddCommGroup O] [Module R O]
    (M N : Submodule R O) (b'M : Basis ι R M) (N_bot : N != ⊥) (N_le_M : N <= M) :
    exists y in M, exists a : R, a • y in N ∧ exists M' <= M, exists N' <= N,
      N' <= M' ∧ (forall (c : R) (z : O), z in M' -> c • y + z = 0 -> c = 0) ∧
      (forall (c : R) (z : O), z in N' -> c • a • y + z = 0 -> c = 0) ∧
      forall (n') (bN' : Basis (Fin n') R N'),
        exists bN : Basis (Fin (n' + 1)) R N,
          forall (m') (hn'm' : n' <= m') (bM' : Basis (Fin m') R M'),
            exists (hnm : n' + 1 <= m' + 1) (bM : Basis (Fin (m' + 1)) R M),
              forall as : Fin n' -> R,
                (forall i : Fin n', (bN' i : O) = as i • (bM' (Fin.castLE hn'm' i) : O)) ->
                  exists as' : Fin (n' + 1) -> R,
                    forall i : Fin (n' + 1), (bN i : O) = as' i • (bM (Fin.castLE hnm i) : O) := by
  -- Let `ϕ` be a maximal projection of `M` onto `R`, in the sense that there is
  -- no `ψ` whose image of `N` is larger than `ϕ`'s image of `N`.
  have : exists ϕ : M ->ₗ[R] R, forall ψ : M ->ₗ[R] R, ¬ϕ.submoduleImage N < ψ.submoduleImage N := by
    obtain ⟨P, P_eq, P_max⟩ :=
      set_has_maximal_iff_noetherian.mpr (inferInstance : IsNoetherian R R) _
        (show (Set.range fun ψ : M ->ₗ[R] R => ψ.submoduleImage N).Nonempty from
          ⟨_, Set.mem_range.mpr ⟨0, rfl⟩⟩)
    obtain ⟨ϕ, rfl⟩ := Set.mem_range.mp P_eq
    exact ⟨ϕ, fun ψ hψ => P_max _ ⟨_, rfl⟩ hψ⟩
  let ϕ := this.choose
  have ϕ_max := this.choose_spec
  -- Since `ϕ(N)` is an `R`-submodule of the PID `R`,
  -- it is principal and generated by some `a`.
  let a := generator (ϕ.submoduleImage N)
  have a_mem : a in ϕ.submoduleImage N := generator_mem _
  -- If `a` is zero, then the submodule is trivial. So let's assume `a ≠ 0`, `N ≠ ⊥`.
  by_cases a_zero : a = 0
  · have := eq_bot_of_generator_maximal_submoduleImage_eq_zero b'M N_le_M ϕ_max a_zero
    contradiction
  -- We claim that `ϕ⁻¹ a = y` can be taken as basis element of `N`.
  obtain ⟨y, yN, ϕy_eq⟩ := (LinearMap.mem_submoduleImage_of_le N_le_M).mp a_mem
  -- Write `y` as `a • y'` for some `y'`.
  have hdvd : forall i, a ∣ b'M.coord i ⟨y, N_le_M yN⟩ := fun i =>
    generator_maximal_submoduleImage_dvd N_le_M ϕ_max y yN ϕy_eq (b'M.coord i)
  choose c hc using hdvd
  cases nonempty_fintype ι
  let y' : O := ∑ i, c i • b'M i
  have y'M : y' in M := M.sum_mem fun i _ => M.smul_mem (c i) (b'M i).2
  have mk_y' : (⟨y', y'M⟩ : M) = ∑ i, c i • b'M i :=
    Subtype.ext
      (show y' = M.subtype _ by
        simp only [map_sum, map_smul]
        rfl)
  have a_smul_y' : a • y' = y := by
    refine Subtype.mk_eq_mk.mp (show (a • ⟨y', y'M⟩ : M) = ⟨y, N_le_M yN⟩ from ?_)
    rw [← b'M.sum_repr ⟨y]; rw [N_le_M yN⟩]; rw [mk_y']; rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_smul]; rw [← hc]
    rfl
  -- We found a `y` and an `a`!
  refine ⟨y', y'M, a, a_smul_y'.symm ▸ yN, ?_⟩
  have ϕy'_eq : ϕ ⟨y', y'M⟩ = 1 :=
    mul_left_cancel₀ a_zero
      (calc
        a • ϕ ⟨y', y'M⟩ = ϕ ⟨a • y', _⟩ := (ϕ.map_smul a ⟨y', y'M⟩).symm
        _ = ϕ ⟨y, N_le_M yN⟩ := by simp only [a_smul_y']
        _ = a := ϕy_eq
        _ = a * 1 := (mul_one a).symm)
  have ϕy'_ne_zero : ϕ ⟨y', y'M⟩ != 0 := by simpa only [ϕy'_eq] using one_ne_zero
  -- `M' := ker (ϕ : M → R)` is smaller than `M` and `N' := ker (ϕ : N → R)` is smaller than `N`.
  let M' : Submodule R O := (LinearMap.ker ϕ).map M.subtype
  let N' : Submodule R O := (LinearMap.ker (ϕ.comp (inclusion N_le_M))).map N.subtype
  have M'_le_M : M' <= M := M.map_subtype_le (LinearMap.ker ϕ)
  have N'_le_M' : N' <= M' := by
    intro x hx
    simp only [N', mem_map, LinearMap.mem_ker] at hx ⊢
    obtain ⟨⟨x, xN⟩, hx, rfl⟩ := hx
    exact ⟨⟨x, N_le_M xN⟩, hx, rfl⟩
  have N'_le_N : N' <= N := N.map_subtype_le (LinearMap.ker (ϕ.comp (inclusion N_le_M)))
  -- So fill in those results as well.
  refine ⟨M', M'_le_M, N', N'_le_N, N'_le_M', ?_⟩
  -- Note that `y'` is orthogonal to `M'`.
  have y'_ortho_M' : forall (c : R), forall z in M', c • y' + z = 0 -> c = 0 := by
    intro c x xM' hc
    obtain ⟨⟨x, xM⟩, hx', rfl⟩ := Submodule.mem_map.mp xM'
    rw [LinearMap.mem_ker] at hx'
    have hc' : (c • ⟨y', y'M⟩ + ⟨x, xM⟩ : M) = 0 := by exact @Subtype.coe_injective O (· in M) _ _ hc
    simpa only [map_add, map_zero, map_smul, smul_eq_mul, add_zero, mul_eq_zero, ϕy'_ne_zero, hx',
      or_false] using congr_arg ϕ hc'
  -- And `a • y'` is orthogonal to `N'`.
  have ay'_ortho_N' : forall (c : R), forall z in N', c • a • y' + z = 0 -> c = 0 := by
    intro c z zN' hc
    refine (mul_eq_zero.mp (y'_ortho_M' (a * c) z (N'_le_M' zN') ?_)).resolve_left a_zero
    rw [mul_comm]; rw [mul_smul]; rw [hc]
  -- So we can extend a basis for `N'` with `y`
  refine ⟨y'_ortho_M', ay'_ortho_N', fun n' bN' => ⟨?_, ?_⟩⟩
  · refine Basis.mkFinConsOfLE y yN bN' N'_le_N ?_ ?_
    · intro c z zN' hc
      refine ay'_ortho_N' c z zN' ?_
      rwa [← a_smul_y'] at hc
    · intro z zN
      obtain ⟨b, hb⟩ : _ ∣ ϕ ⟨z, N_le_M zN⟩ := generator_submoduleImage_dvd_of_mem N_le_M ϕ zN
      refine ⟨-b, Submodule.mem_map.mpr ⟨⟨_, N.sub_mem zN (N.smul_mem b yN)⟩, ?_, ?_⟩⟩
      · refine LinearMap.mem_ker.mpr (show ϕ (⟨z, N_le_M zN⟩ - b • ⟨y, N_le_M yN⟩) = 0 from ?_)
        rw [map_sub]; rw [map_smul]; rw [hb]; rw [ϕy_eq]; rw [smul_eq_mul]; rw [mul_comm]; rw [sub_self]
      · simp only [sub_eq_add_neg, neg_smul, coe_subtype]
  -- And extend a basis for `M'` with `y'`
  intro m' hn'm' bM'
  refine ⟨Nat.succ_le_succ hn'm', ?_, ?_⟩
  · refine Basis.mkFinConsOfLE y' y'M bM' M'_le_M y'_ortho_M' ?_
    intro z zM
    refine ⟨-ϕ ⟨z, zM⟩, ⟨⟨z, zM⟩ - ϕ ⟨z, zM⟩ • ⟨y', y'M⟩, LinearMap.mem_ker.mpr ?_, ?_⟩⟩
    · rw [map_sub, map_smul, ϕy'_eq, smul_eq_mul, mul_one, sub_self]
    · rw [map_sub, map_smul, sub_eq_add_neg, neg_smul]
      rfl
  -- It remains to show the extended bases are compatible with each other.
  intro as h
  refine ⟨Fin.cons a as, ?_⟩
  intro i
  rw [Basis.coe_mkFinConsOfLE]; rw [Basis.coe_mkFinConsOfLE]
  refine Fin.cases ?_ (fun i => ?_) i
  · simp only [Fin.cons_zero, Fin.castLE_zero]
    exact a_smul_y'.symm
  · rw [Fin.castLE_succ]
    simp only [Fin.cons_succ, Function.comp_apply, coe_inclusion, h i]

/--
theorem `Submodule.nonempty_basis_of_pid` / 定理 `Submodule.nonempty_basis_of_pid`

English:
theorem Submodule.nonempty_basis_of_pid
  statement: {ι : Type*} [Finite ι] (b : Basis ι R M)
  proof: by
  have := Classical.decEq M
  cases nonempty_fintype ι
  induction N using inductionOnRank b with | ih N ih =>
  let b' := (b.reindex (Fintype.equivFin ι)).map (LinearEquiv.ofTop _ rfl).symm
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, ⟨Basis.empty _⟩⟩
  obtain ⟨y, -, a, hay, M', -, N',

中文:
定理 Submodule.nonempty_basis_of_pid
  结论: {ι : 类型} [Finite ι] (b : Basis ι R M)
  证明: by
  have := Classical.decEq M
  cases nonempty_fintype ι
  induction N using inductionOnRank b with | ih N ih =>
  let b' := (b.reindex (Fintype.equivFin ι)).map (LinearEquiv.ofTop _ rfl).symm
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, ⟨Basis.empty _⟩⟩
  obtain ⟨y, -, a, hay, M', -, N',

Depends on / 依赖: Basis.empty, Classical, Classical.decEq, Fintype, Fintype.equivFin, LinearEquiv, LinearEquiv.ofTop, N_bot, Submodule, Submodule.basis_of_pid_aux, _hbN, _le_N, ay_ortho, b.reindex, basis_of_pid_aux, equivFin, inductionOnRank, le_top, nonempty_fintype, reindex
-/
theorem Submodule.nonempty_basis_of_pid {ι : Type*} [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) : exists n : Nat, Nonempty (Basis (Fin n) R N) := by
  have := Classical.decEq M
  cases nonempty_fintype ι
  induction N using inductionOnRank b with | ih N ih =>
  let b' := (b.reindex (Fintype.equivFin ι)).map (LinearEquiv.ofTop _ rfl).symm
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, ⟨Basis.empty _⟩⟩
  obtain ⟨y, -, a, hay, M', -, N', N'_le_N, -, -, ay_ortho, h'⟩ :=
    Submodule.basis_of_pid_aux ⊤ N b' N_bot le_top
  obtain ⟨n', ⟨bN'⟩⟩ := ih N' N'_le_N _ hay ay_ortho
  obtain ⟨bN, _hbN⟩ := h' n' bN'
  exact ⟨n' + 1, ⟨bN⟩⟩

/--
Definition of `Submodule.basisOfPid` / `Submodule.basisOfPid` 的定义

English:
definition Submodule.basisOfPid
  signature: {ι : Type*} [Finite ι] (b : Basis ι R M)
  body: ⟨_, (N.nonempty_basis_of_pid b).choose_spec.some⟩

中文:
定义 Submodule.basisOfPid
  签名: {ι : 类型} [Finite ι] (b : Basis ι R M)
  定义体: ⟨_, (N.nonempty_basis_of_pid b).choose_spec.some⟩

Depends on / 依赖: IsHaarMeasure, IsHaarMeasure.sigmaFinite, N.nonempty_basis_of_pid, SigmaCompactSpace, SigmaFinite, choose_spec, choose_spec.some, nonempty_basis_of_pid, sigmaFinite
-/
noncomputable def Submodule.basisOfPid {ι : Type*} [Finite ι] (b : Basis ι R M)
    (N : Submodule R M) : Σ n : Nat, Basis (Fin n) R N :=
  ⟨_, (N.nonempty_basis_of_pid b).choose_spec.some⟩

/--
theorem `Submodule.basisOfPid_bot` / 定理 `Submodule.basisOfPid_bot`

English:
theorem Submodule.basisOfPid_bot
  given: {ι : Type*} [Finite ι] (b : Basis ι R M)
  proof: by
  obtain ⟨n, b'⟩ := Submodule.basisOfPid b ⊥
  let e : Fin n ≃ Fin 0 := b'.indexEquiv (Basis.empty _ : Basis (Fin 0) R (⊥ : Submodule R M))
  obtain rfl : n = 0 := by simpa using Fintype.card_eq.mpr ⟨e⟩
  exact Sigma.eq rfl (Basis.eq_of_apply_eq <| finZeroElim)

中文:
定理 Submodule.basisOfPid_bot
  条件: {ι : 类型} [Finite ι] (b : Basis ι R M)
  证明: by
  obtain ⟨n, b'⟩ := Submodule.basisOfPid b ⊥
  let e : Fin n ≃ Fin 0 := b'.indexEquiv (Basis.empty _ : Basis (Fin 0) R (⊥ : Submodule R M))
  obtain rfl : n = 0 := by simpa using Fintype.card_eq.mpr ⟨e⟩
  exact Sigma.eq rfl (Basis.eq_of_apply_eq <| finZeroElim)

Depends on / 依赖: Basis.empty, Basis.eq_of_apply_eq, BorelSpace, Fintype, Fintype.card_eq.mpr, IsHaarMeasure, IsHaarMeasure.nullSingletonClass, IsTopologicalGroup, Sigma.eq, Submodule, Submodule.basisOfPid, basisOfPid, card_eq, eq_of_apply_eq, finZeroElim, indexEquiv, nullSingletonClass
-/
theorem Submodule.basisOfPid_bot {ι : Type*} [Finite ι] (b : Basis ι R M) :
    Submodule.basisOfPid b ⊥ = ⟨0, Basis.empty _⟩ := by
  obtain ⟨n, b'⟩ := Submodule.basisOfPid b ⊥
  let e : Fin n ≃ Fin 0 := b'.indexEquiv (Basis.empty _ : Basis (Fin 0) R (⊥ : Submodule R M))
  obtain rfl : n = 0 := by simpa using Fintype.card_eq.mpr ⟨e⟩
  exact Sigma.eq rfl (Basis.eq_of_apply_eq <| finZeroElim)

/--
Definition of `Submodule.basisOfPidOfLE` / `Submodule.basisOfPidOfLE` 的定义

English:
definition Submodule.basisOfPidOfLE
  signature: {ι : Type*} [Finite ι] {N O : Submodule R M}
  body: let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩

中文:
定义 Submodule.basisOfPidOfLE
  签名: {ι : 类型} [Finite ι] {N O : Submodule R M}
  定义体: let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩

Depends on / 依赖: N.comap, O.subtype, Submodule, Submodule.basisOfPid, Submodule.comapSubtypeEquivOfLe, basisOfPid, comapSubtypeEquivOfLe, subtype
-/
noncomputable def Submodule.basisOfPidOfLE {ι : Type*} [Finite ι] {N O : Submodule R M}
    (hNO : N <= O) (b : Basis ι R O) : Σ n : Nat, Basis (Fin n) R N :=
  let ⟨n, bN'⟩ := Submodule.basisOfPid b (N.comap O.subtype)
  ⟨n, bN'.map (Submodule.comapSubtypeEquivOfLe hNO)⟩

/--
Definition of `Submodule.basisOfPidOfLESpan` / `Submodule.basisOfPidOfLESpan` 的定义

English:
definition Submodule.basisOfPidOfLESpan
  signature: {ι : Type*} [Finite ι] {b : ι -> M}
  body: Submodule.basisOfPidOfLE le (Basis.span hb)

中文:
定义 Submodule.basisOfPidOfLESpan
  签名: {ι : 类型} [Finite ι] {b : ι -> M}
  定义体: Submodule.basisOfPidOfLE le (Basis.span hb)

Depends on / 依赖: Basis.span, Submodule, Submodule.basisOfPidOfLE, basisOfPidOfLE
-/
noncomputable def Submodule.basisOfPidOfLESpan {ι : Type*} [Finite ι] {b : ι -> M}
    (hb : LinearIndependent R b) {N : Submodule R M} (le : N <= Submodule.span R (Set.range b)) :
    Σ n : Nat, Basis (Fin n) R N :=
  Submodule.basisOfPidOfLE le (Basis.span hb)

/--
Definition of `Module.basisOfFiniteTypeTorsionFree` / `Module.basisOfFiniteTypeTorsionFree` 的定义

English:
definition Module.basisOfFiniteTypeTorsionFree
  signature: [Fintype ι] {s : ι -> M}
  body: by
  classical
    -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
    have := exists_maximal_linearIndepOn R s
    let I : Set ι := this.choose
    obtain
      ⟨indepI : LinearIndependent R (s ∘ (fun x => x) : I -> M), hI :
        forall i ∉ I, exists a 

中文:
定义 Module.basisOfFiniteTypeTorsionFree
  签名: [Fintype ι] {s : ι -> M}
  定义体: by
  classical
    -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
    have := exists_maximal_linearIndepOn R s
    let I : Set ι := this.choose
    obtain
      ⟨indepI : LinearIndependent R (s ∘ (fun x => x) : I -> M), hI :
        forall i ∉ I, exists a 

Depends on / 依赖: classical
-/
noncomputable def Module.basisOfFiniteTypeTorsionFree [Fintype ι] {s : ι -> M}
    (hs : span R (range s) = ⊤) [IsTorsionFree R M] : Σ n : Nat, Basis (Fin n) R M := by
  classical
    -- We define `N` as the submodule spanned by a maximal linear independent subfamily of `s`
    have := exists_maximal_linearIndepOn R s
    let I : Set ι := this.choose
    obtain
      ⟨indepI : LinearIndependent R (s ∘ (fun x => x) : I -> M), hI :
        forall i ∉ I, exists a : R, a != 0 ∧ a • s i in span R (s '' I)⟩ :=
      this.choose_spec
    let N := span R (range <| (s ∘ (fun x => x) : I -> M))
    -- same as `span R (s '' I)` but more convenient
    let _sI : I -> N := fun i => ⟨s i.1, subset_span (mem_range_self i)⟩
    -- `s` restricted to `I` is a basis of `N`
    let sI_basis : Basis I R N := Basis.span indepI
    -- Our first goal is to build `A ≠ 0` such that `A • M ⊆ N`
    have exists_a : forall i : ι, exists a : R, a != 0 ∧ a • s i in N := by
      intro i
      by_cases hi : i in I
      · use 1, zero_ne_one.symm
        rw [one_smul]
        exact subset_span (mem_range_self (⟨i, hi⟩ : I))
      · simpa [image_eq_range s I] using! hI i hi
    choose a ha ha' using exists_a
    let A := ∏ i, a i
    have hA : A != 0 := by
      rw [Finset.prod_ne_zero_iff]
      simpa using! ha
    -- `M ≃ A • M` because `M` is torsion free and `A ≠ 0`
    let φ : M ->ₗ[R] M := LinearMap.lsmul R M A
    have : LinearMap.ker φ = ⊥ := LinearMap.ker_lsmul hA
    let ψ := LinearEquiv.ofInjective φ (LinearMap.ker_eq_bot.mp this)
    have : LinearMap.range φ <= N := by
      -- as announced, `A • M ⊆ N`
      suffices forall i, φ (s i) in N by
        rw [LinearMap.range_eq_map]; rw [← hs]; rw [map_span_le]
        rintro _ ⟨i, rfl⟩
        apply this
      intro i
      calc
        (∏ j in {i}ᶜ, a j) • a i • s i in N := N.smul_mem _ (ha' i)
        _ = (∏ j, a j) • s i := by rw [Fintype.prod_eq_prod_compl_mul i, mul_smul]
    -- Since a submodule of a free `R`-module is free, we get that `A • M` is free
    obtain ⟨n, b : Basis (Fin n) R (LinearMap.range φ)⟩ := Submodule.basisOfPidOfLE this sI_basis
    -- hence `M` is free.
    exact ⟨n, b.map ψ.symm⟩

/--
theorem `Module.free_of_finite_type_torsion_free` / 定理 `Module.free_of_finite_type_torsion_free`

English:
theorem Module.free_of_finite_type_torsion_free
  statement: [_root_.Finite ι] {s : ι -> M}
  proof: by
  cases nonempty_fintype ι
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree hs
  exact Module.Free.of_basis b

中文:
定理 Module.free_of_finite_type_torsion_free
  结论: [_root_.Finite ι] {s : ι -> M}
  证明: by
  cases nonempty_fintype ι
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree hs
  exact Module.Free.of_basis b

Depends on / 依赖: Module, Module.Free.of_basis, Module.basisOfFiniteTypeTorsionFree, basisOfFiniteTypeTorsionFree, nonempty_fintype, of_basis
-/
theorem Module.free_of_finite_type_torsion_free [_root_.Finite ι] {s : ι -> M}
    (hs : span R (range s) = ⊤) [IsTorsionFree R M] : Module.Free R M := by
  cases nonempty_fintype ι
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree hs
  exact Module.Free.of_basis b

/--
Definition of `Module.basisOfFiniteTypeTorsionFree'` / `Module.basisOfFiniteTypeTorsionFree'` 的定义

English:
definition Module.basisOfFiniteTypeTorsionFree'
  signature: [Module.Finite R M]
  body: Module.basisOfFiniteTypeTorsionFree Module.Finite.exists_fin.choose_spec.choose_spec

中文:
定义 Module.basisOfFiniteTypeTorsionFree'
  签名: [Module.Finite R M]
  定义体: Module.basisOfFiniteTypeTorsionFree Module.Finite.exists_fin.choose_spec.choose_spec

Depends on / 依赖: Finite, Module, Module.Finite.exists_fin.choose_spec.choose_spec, Module.basisOfFiniteTypeTorsionFree, basisOfFiniteTypeTorsionFree, choose_spec, exists_fin
-/
noncomputable def Module.basisOfFiniteTypeTorsionFree' [Module.Finite R M]
    [IsTorsionFree R M] : Σ n : Nat, Basis (Fin n) R M :=
  Module.basisOfFiniteTypeTorsionFree Module.Finite.exists_fin.choose_spec.choose_spec

/--
Instance `Module.free_of_finite_type_torsion_free'` / 实例 `Module.free_of_finite_type_torsion_free'`

English:
instance Module.free_of_finite_type_torsion_free'
  signature: [Module.Finite R M] [IsTorsionFree R M]
  body: by
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree'
  exact Module.Free.of_basis b

中文:
实例 Module.free_of_finite_type_torsion_free'
  签名: [Module.Finite R M] [IsTorsionFree R M]
  定义体: by
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree'
  exact Module.Free.of_basis b

Depends on / 依赖: Module, Module.Free.of_basis, Module.basisOfFiniteTypeTorsionFree, basisOfFiniteTypeTorsionFree, of_basis
-/
instance Module.free_of_finite_type_torsion_free' [Module.Finite R M] [IsTorsionFree R M] :
    Module.Free R M := by
  obtain ⟨n, b⟩ : Σ n, Basis (Fin n) R M := Module.basisOfFiniteTypeTorsionFree'
  exact Module.Free.of_basis b

instance {S : Type*} [CommRing S] [Algebra R S] {I : Ideal S} [hI₁ : Module.Finite R I]
    [hI₂ : IsTorsionFree R I] : Free R I := by
  have : Module.Finite R (restrictScalars R I) := hI₁
  have : IsTorsionFree R (restrictScalars R I) := hI₂
  change Module.Free R (restrictScalars R I)
  exact Module.free_of_finite_type_torsion_free'

/--
theorem `Module.free_iff_isTorsionFree` / 定理 `Module.free_iff_isTorsionFree`

English:
theorem Module.free_iff_isTorsionFree
  given: [Module.Finite R M]
  statement: Free R M ↔ IsTorsionFree R M
  proof: ⟨fun _ => inferInstance, fun _ => inferInstance⟩

中文:
定理 Module.free_iff_isTorsionFree
  条件: [Module.Finite R M]
  结论: Free R M ↔ IsTorsionFree R M
  证明: ⟨fun _ => inferInstance, fun _ => inferInstance⟩
-/
theorem Module.free_iff_isTorsionFree [Module.Finite R M] : Free R M ↔ IsTorsionFree R M :=
  ⟨fun _ => inferInstance, fun _ => inferInstance⟩

end StrongRankCondition

section SmithNormal

/--
Definition of `Module.Basis.SmithNormalForm` / `Module.Basis.SmithNormalForm` 的定义

English:
structure Module.Basis.SmithNormalForm
  parameters: (N : Submodule R M) (ι : Type*) (n : Nat)
  axioms and operations (5):
    - bM : Basis ι R M
    - bN : Basis (Fin n) R N
    - f : Fin n ↪ ι
    - a : Fin n -> R
    - snf : forall i, (bN i : M) = a i • bM (f i)

中文:
结构 Module.Basis.SmithNormalForm
  参数: (N : Submodule R M) (ι : 类型) (n : 自然数)
  公理与运算 (5 个):
    - bM : Basis ι R M
    - bN : Basis (Fin n) R N
    - f : Fin n ↪ ι
    - a : Fin n -> R
    - snf : 对任意 i, (bN i : M) = a i • bM (f i)
-/
structure Module.Basis.SmithNormalForm (N : Submodule R M) (ι : Type*) (n : Nat) where
  /-- The basis of M. -/
  bM : Basis ι R M
  /-- The basis of N. -/
  bN : Basis (Fin n) R N
  /-- The mapping between the vectors of the bases. -/
  f : Fin n ↪ ι
  /-- The (diagonal) entries of the matrix. -/
  a : Fin n -> R
  /-- The SNF relation between the vectors of the bases. -/
  snf : forall i, (bN i : M) = a i • bM (f i)

namespace Module.Basis.SmithNormalForm

variable {n : Nat} {N : Submodule R M} (snf : Basis.SmithNormalForm N ι n) (m : N)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `repr_eq_zero_of_notMem_range` / 引理 `repr_eq_zero_of_notMem_range`

English:
lemma repr_eq_zero_of_notMem_range
  given: {i : ι} (hi : i ∉ Set.range snf.f)
  proof: by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hi : forall j, snf.f j != i := by simpa using hi
  simp [hi, snf.snf, map_finsuppSum]

中文:
引理 repr_eq_zero_of_notMem_range
  条件: {i : ι} (hi : i ∉ Set.range snf.f)
  证明: by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hi : forall j, snf.f j != i := by simpa using hi
  simp [hi, snf.snf, map_finsuppSum]

Depends on / 依赖: map_finsuppSum, mem_submodule_iff, replace, snf.bN.mem_submodule_iff.mp, snf.f, snf.snf
-/
lemma repr_eq_zero_of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) :
    snf.bM.repr m i = 0 := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hi : forall j, snf.f j != i := by simpa using hi
  simp [hi, snf.snf, map_finsuppSum]

/--
lemma `le_ker_coord_of_notMem_range` / 引理 `le_ker_coord_of_notMem_range`

English:
lemma le_ker_coord_of_notMem_range
  given: {i : ι} (hi : i ∉ Set.range snf.f)
  proof: fun m hm => snf.repr_eq_zero_of_notMem_range ⟨m, hm⟩ hi

中文:
引理 le_ker_coord_of_notMem_range
  条件: {i : ι} (hi : i ∉ Set.range snf.f)
  证明: fun m hm => snf.repr_eq_zero_of_notMem_range ⟨m, hm⟩ hi

Depends on / 依赖: repr_eq_zero_of_notMem_range, snf.repr_eq_zero_of_notMem_range
-/
lemma le_ker_coord_of_notMem_range {i : ι} (hi : i ∉ Set.range snf.f) :
    N <= LinearMap.ker (snf.bM.coord i) :=
  fun m hm => snf.repr_eq_zero_of_notMem_range ⟨m, hm⟩ hi

set_option backward.isDefEq.respectTransparency false in
/--
lemma `repr_apply_embedding_eq_repr_smul` / 引理 `repr_apply_embedding_eq_repr_smul`

English:
lemma repr_apply_embedding_eq_repr_smul
  given: {i : Fin n}
  proof: by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hm : (⟨Finsupp.sum c fun i t => t • (↑(snf.bN i) : M), hm⟩ : N) =
      Finsupp.sum c fun i t => t • ⟨snf.bN i, (snf.bN i).2⟩ := by
    ext; change _ = N.subtype _; simp [map_finsuppSum]
  classical
  simp_rw [hm,

中文:
引理 repr_apply_embedding_eq_repr_smul
  条件: {i : Fin n}
  证明: by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hm : (⟨Finsupp.sum c fun i t => t • (↑(snf.bN i) : M), hm⟩ : N) =
      Finsupp.sum c fun i t => t • ⟨snf.bN i, (snf.bN i).2⟩ := by
    ext; change _ = N.subtype _; simp [map_finsuppSum]
  classical
  simp_rw [hm,
-/
@[simp] lemma repr_apply_embedding_eq_repr_smul {i : Fin n} :
    snf.bM.repr m (snf.f i) = snf.bN.repr (snf.a i • m) i := by
  obtain ⟨m, hm⟩ := m
  obtain ⟨c, rfl⟩ := snf.bN.mem_submodule_iff.mp hm
  replace hm : (⟨Finsupp.sum c fun i t => t • (↑(snf.bN i) : M), hm⟩ : N) =
      Finsupp.sum c fun i t => t • ⟨snf.bN i, (snf.bN i).2⟩ := by
    ext; change _ = N.subtype _; simp [map_finsuppSum]
  classical
  simp_rw [hm, map_smul, map_finsuppSum, map_smul, Subtype.coe_eta, repr_self,
    Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_single, Finsupp.smul_apply, snf.snf,
    map_smul, repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, Finsupp.sum_apply,
    Finsupp.single_apply, EmbeddingLike.apply_eq_iff_eq, Finsupp.sum_ite_eq',
    Finsupp.mem_support_iff, ite_not, mul_comm, ite_eq_right_iff]
  exact fun a => (mul_eq_zero_of_right _ a).symm

set_option backward.isDefEq.respectTransparency false in
/--
lemma `repr_comp_embedding_eq_smul` / 引理 `repr_comp_embedding_eq_smul`

English:
lemma repr_comp_embedding_eq_smul
  proof: by
  ext i
  simp [Pi.smul_apply (snf.a i)]

中文:
引理 repr_comp_embedding_eq_smul
  证明: by
  ext i
  simp [Pi.smul_apply (snf.a i)]
-/
@[simp] lemma repr_comp_embedding_eq_smul :
    snf.bM.repr m ∘ snf.f = snf.a • (snf.bN.repr m : Fin n -> R) := by
  ext i
  simp [Pi.smul_apply (snf.a i)]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `coord_apply_embedding_eq_smul_coord` / 引理 `coord_apply_embedding_eq_smul_coord`

English:
lemma coord_apply_embedding_eq_smul_coord
  given: {i : Fin n}
  proof: by
  ext m
  simp [Pi.smul_apply (snf.a i)]

中文:
引理 coord_apply_embedding_eq_smul_coord
  条件: {i : Fin n}
  证明: by
  ext m
  simp [Pi.smul_apply (snf.a i)]
-/
@[simp] lemma coord_apply_embedding_eq_smul_coord {i : Fin n} :
    snf.bM.coord (snf.f i) ∘ₗ N.subtype = snf.a i • snf.bN.coord i := by
  ext m
  simp [Pi.smul_apply (snf.a i)]

/-- Given a Smith-normal-form pair of bases for `N ⊆ M`, and a linear endomorphism `f` of `M`
that preserves `N`, the diagonal of the matrix of the restriction `f` to `N` does not depend on
which of the two bases for `N` is used. -/
@[simp]
/--
lemma `toMatrix_restrict_eq_toMatrix` / 引理 `toMatrix_restrict_eq_toMatrix`

English:
lemma toMatrix_restrict_eq_toMatrix
  statement: [Fintype ι] [DecidableEq ι]
  proof: by
  rw [LinearMap.toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [snf.repr_apply_embedding_eq_repr_smul ⟨_]; rw [(hf _)⟩]
  congr
  ext
  simp [snf.snf]

中文:
引理 toMatrix_restrict_eq_toMatrix
  结论: [Fintype ι] [DecidableEq ι]
  证明: by
  rw [LinearMap.toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [snf.repr_apply_embedding_eq_repr_smul ⟨_]; rw [(hf _)⟩]
  congr
  ext
  simp [snf.snf]
-/
lemma toMatrix_restrict_eq_toMatrix [Fintype ι] [DecidableEq ι]
    (f : M ->ₗ[R] M) (hf : forall x, f x in N) (hf' : forall x in N, f x in N := fun x _ => hf x) {i : Fin n} :
    LinearMap.toMatrix snf.bN snf.bN (LinearMap.restrict f hf') i i =
    LinearMap.toMatrix snf.bM snf.bM f (snf.f i) (snf.f i) := by
  rw [LinearMap.toMatrix_apply]; rw [LinearMap.toMatrix_apply]; rw [snf.repr_apply_embedding_eq_repr_smul ⟨_]; rw [(hf _)⟩]
  congr
  ext
  simp [snf.snf]

end Module.Basis.SmithNormalForm

variable [IsDomain R] [IsPrincipalIdealRing R]

/--
theorem `Submodule.exists_smith_normal_form_of_le` / 定理 `Submodule.exists_smith_normal_form_of_le`

English:
theorem Submodule.exists_smith_normal_form_of_le
  statement: [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
  proof: by
  cases nonempty_fintype ι
  induction O using inductionOnRank b generalizing N with | ih M0 ih =>
  obtain ⟨m, b'M⟩ := M0.basisOfPid b
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, m, Nat.zero_le _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
  obtain ⟨y, hy, a, _, M', M'_le_M, N', _,

中文:
定理 Submodule.exists_smith_normal_form_of_le
  结论: [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
  证明: by
  cases nonempty_fintype ι
  induction O using inductionOnRank b generalizing N with | ih M0 ih =>
  obtain ⟨m, b'M⟩ := M0.basisOfPid b
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, m, Nat.zero_le _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
  obtain ⟨y, hy, a, _, M', M'_le_M, N', _,

Depends on / 依赖: Basis.empty, M0.basisOfPid, N_bot, N_le_O, Nat.zero_le, Submodule, Submodule.basis_of_pid_aux, _le_M, basisOfPid, basis_of_pid_aux, finZeroElim, generalizing, inductionOnRank, nonempty_fintype, y_ortho, zero_le
-/
theorem Submodule.exists_smith_normal_form_of_le [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
    (N_le_O : N <= O) :
    exists (n o : Nat) (hno : n <= o) (bO : Basis (Fin o) R O) (bN : Basis (Fin n) R N) (a : Fin n -> R),
      forall i, (bN i : M) = a i • bO (Fin.castLE hno i) := by
  cases nonempty_fintype ι
  induction O using inductionOnRank b generalizing N with | ih M0 ih =>
  obtain ⟨m, b'M⟩ := M0.basisOfPid b
  by_cases N_bot : N = ⊥
  · subst N_bot
    exact ⟨0, m, Nat.zero_le _, b'M, Basis.empty _, finZeroElim, finZeroElim⟩
  obtain ⟨y, hy, a, _, M', M'_le_M, N', _, N'_le_M', y_ortho, _, h⟩ :=
    Submodule.basis_of_pid_aux M0 N b'M N_bot N_le_O
  obtain ⟨n', m', hn'm', bM', bN', as', has'⟩ := ih M' M'_le_M y hy y_ortho N' N'_le_M'
  obtain ⟨bN, h'⟩ := h n' bN'
  obtain ⟨hmn, bM, h''⟩ := h' m' hn'm' bM'
  obtain ⟨as, has⟩ := h'' as' has'
  exact ⟨_, _, hmn, bM, bN, as, has⟩

/--
Definition of `Submodule.smithNormalFormOfLE` / `Submodule.smithNormalFormOfLE` 的定义

English:
definition Submodule.smithNormalFormOfLE
  signature: [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
  body: by
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O
  refine
    ⟨o, n, bO, bN.map (comapSubtypeEquivOfLe N_le_O).symm, (Fin.castLEEmb hno), a,
      fun i => ?_⟩
  ext
  simp only [snf, Basis.map_apply, Submodule.comapSubtypeEquivOfLe_symm_apply,
    Submodule.coe_smul

中文:
定义 Submodule.smithNormalFormOfLE
  签名: [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
  定义体: by
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O
  refine
    ⟨o, n, bO, bN.map (comapSubtypeEquivOfLe N_le_O).symm, (Fin.castLEEmb hno), a,
      fun i => ?_⟩
  ext
  simp only [snf, Basis.map_apply, Submodule.comapSubtypeEquivOfLe_symm_apply,
    Submodule.coe_smul

Depends on / 依赖: Basis.map_apply, Fin.castLEEmb, Fin.castLEEmb_apply, N.exists_smith_normal_form_of_le, N_le_O, Submodule, Submodule.coe_smul_of_tower, Submodule.comapSubtypeEquivOfLe_symm_apply, bN.map, castLEEmb, castLEEmb_apply, coe_smul_of_tower, comapSubtypeEquivOfLe, comapSubtypeEquivOfLe_symm_apply, exists_smith_normal_form_of_le, map_apply
-/
noncomputable def Submodule.smithNormalFormOfLE [Finite ι] (b : Basis ι R M) (N O : Submodule R M)
    (N_le_O : N <= O) : Σ o n : Nat, Basis.SmithNormalForm (N.comap O.subtype) (Fin o) n := by
  choose n o hno bO bN a snf using N.exists_smith_normal_form_of_le b O N_le_O
  refine
    ⟨o, n, bO, bN.map (comapSubtypeEquivOfLe N_le_O).symm, (Fin.castLEEmb hno), a,
      fun i => ?_⟩
  ext
  simp only [snf, Basis.map_apply, Submodule.comapSubtypeEquivOfLe_symm_apply,
    Submodule.coe_smul_of_tower, Fin.castLEEmb_apply]

/--
Definition of `Submodule.smithNormalForm` / `Submodule.smithNormalForm` 的定义

English:
definition Submodule.smithNormalForm
  signature: [Finite ι] (b : Basis ι R M) (N : Submodule R M)
  body: let ⟨m, n, bM, bN, f, a, snf⟩ := N.smithNormalFormOfLE b ⊤ le_top
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.indexEquiv b
  ⟨n, bM'.reindex e, bN.map (comapSubtypeEquivOfLe le_top), f.trans e.toEmbedding, a, fun i => by
    simp only [bM', snf, Basis.map_apply, LinearEquiv.ofTop_ap

中文:
定义 Submodule.smithNormalForm
  签名: [Finite ι] (b : Basis ι R M) (N : Submodule R M)
  定义体: let ⟨m, n, bM, bN, f, a, snf⟩ := N.smithNormalFormOfLE b ⊤ le_top
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.indexEquiv b
  ⟨n, bM'.reindex e, bN.map (comapSubtypeEquivOfLe le_top), f.trans e.toEmbedding, a, fun i => by
    simp only [bM', snf, Basis.map_apply, LinearEquiv.ofTop_ap

Depends on / 依赖: Basis.map_apply, Basis.reindex_apply, Embedding, Equiv.symm_apply_apply, Equiv.toEmbedding_apply, Function, Function.Embedding.trans_apply, LinearEquiv, LinearEquiv.ofTop, LinearEquiv.ofTop_apply, N.smithNormalFormOfLE, Submodule, Submodule.coe_smul_of_tower, Submodule.comapSubtypeEquivOfLe_apply_coe, bM.map, bN.map, coe_smul_of_tower, comapSubtypeEquivOfLe, comapSubtypeEquivOfLe_apply_coe, e.toEmbedding
-/
noncomputable def Submodule.smithNormalForm [Finite ι] (b : Basis ι R M) (N : Submodule R M) :
    Σ n : Nat, Basis.SmithNormalForm N ι n :=
  let ⟨m, n, bM, bN, f, a, snf⟩ := N.smithNormalFormOfLE b ⊤ le_top
  let bM' := bM.map (LinearEquiv.ofTop _ rfl)
  let e := bM'.indexEquiv b
  ⟨n, bM'.reindex e, bN.map (comapSubtypeEquivOfLe le_top), f.trans e.toEmbedding, a, fun i => by
    simp only [bM', snf, Basis.map_apply, LinearEquiv.ofTop_apply, Submodule.coe_smul_of_tower,
      Submodule.comapSubtypeEquivOfLe_apply_coe, Basis.reindex_apply,
      Equiv.toEmbedding_apply, Function.Embedding.trans_apply, Equiv.symm_apply_apply]⟩

section full_rank

variable {N : Submodule R M}

/--
Definition of `Submodule.smithNormalFormOfRankEq` / `Submodule.smithNormalFormOfRankEq` 的定义

English:
definition Submodule.smithNormalFormOfRankEq
  signature: [Fintype ι] (b : Basis ι R M)
  body: let ⟨n, bM, bN, f, a, snf⟩ := N.smithNormalForm b
  let e : Fin n ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, ← Module.finrank_eq_card_basis bM, ← h,
      Module.finrank_eq_card_basis bN])
  ⟨bM, bN.reindex e, e.symm.toEmbedding.trans f, a ∘ e.symm, fun i =>

中文:
定义 Submodule.smithNormalFormOfRankEq
  签名: [Fintype ι] (b : Basis ι R M)
  定义体: let ⟨n, bM, bN, f, a, snf⟩ := N.smithNormalForm b
  let e : Fin n ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, ← Module.finrank_eq_card_basis bM, ← h,
      Module.finrank_eq_card_basis bN])
  ⟨bM, bN.reindex e, e.symm.toEmbedding.trans f, a ∘ e.symm, fun i =>

Depends on / 依赖: Basis.coe_reindex, Embedding, Equiv.toEmbedding_apply, Fintype, Fintype.card, Fintype.card_fin, Fintype.equivOfCardEq, Function, Function.Embedding.trans_apply, Module, Module.finrank_eq_card_basis, N.smithNormalForm, bN.reindex, card_fin, coe_reindex, e.symm, e.symm.toEmbedding.trans, equivOfCardEq, finrank_eq_card_basis, reindex
-/
noncomputable def Submodule.smithNormalFormOfRankEq [Fintype ι] (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    Basis.SmithNormalForm N ι (Fintype.card ι) :=
  let ⟨n, bM, bN, f, a, snf⟩ := N.smithNormalForm b
  let e : Fin n ≃ Fin (Fintype.card ι) := Fintype.equivOfCardEq (by
    simp only [Fintype.card_fin, ← Module.finrank_eq_card_basis bM, ← h,
      Module.finrank_eq_card_basis bN])
  ⟨bM, bN.reindex e, e.symm.toEmbedding.trans f, a ∘ e.symm, fun i => by
    simp only [snf, Basis.coe_reindex, Function.Embedding.trans_apply, Equiv.toEmbedding_apply,
      (· ∘ ·)]⟩

variable [Finite ι]

/--
theorem `Submodule.exists_smith_normal_form_of_rank_eq` / 定理 `Submodule.exists_smith_normal_form_of_rank_eq`

English:
theorem Submodule.exists_smith_normal_form_of_rank_eq
  statement: (b : Basis ι R M)
  proof: by
  cases nonempty_fintype ι
  let ⟨bM, bN, f, a, snf⟩ := N.smithNormalFormOfRankEq b h
  let e : Fin (Fintype.card ι) ≃ ι :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, Fintype.card_fin _⟩)
  have fe : forall i, f (e.symm i) = i := e.apply_symm_app

中文:
定理 Submodule.exists_smith_normal_form_of_rank_eq
  结论: (b : Basis ι R M)
  证明: by
  cases nonempty_fintype ι
  let ⟨bM, bN, f, a, snf⟩ := N.smithNormalFormOfRankEq b h
  let e : Fin (Fintype.card ι) ≃ ι :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, Fintype.card_fin _⟩)
  have fe : forall i, f (e.symm i) = i := e.apply_symm_app

Depends on / 依赖: Basis.coe_reindex, Equiv.ofBijective, Fintype, Fintype.bijective_iff_injective_and_card, Fintype.card, Fintype.card_fin, N.smithNormalFormOfRankEq, apply_symm_apply, bN.reindex, bijective_iff_injective_and_card, card_fin, coe_reindex, e.apply_symm_apply, e.symm, f.injective, injective, nonempty_fintype, ofBijective, reindex, smithNormalFormOfRankEq
-/
theorem Submodule.exists_smith_normal_form_of_rank_eq (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    exists (b' : Basis ι R M) (a : ι -> R) (ab' : Basis ι R N), forall i, (ab' i : M) = a i • b' i := by
  cases nonempty_fintype ι
  let ⟨bM, bN, f, a, snf⟩ := N.smithNormalFormOfRankEq b h
  let e : Fin (Fintype.card ι) ≃ ι :=
    Equiv.ofBijective f
      ((Fintype.bijective_iff_injective_and_card f).mpr ⟨f.injective, Fintype.card_fin _⟩)
  have fe : forall i, f (e.symm i) = i := e.apply_symm_apply
  exact
    ⟨bM, a ∘ e.symm, bN.reindex e, fun i => by
      simp only [snf, fe,
          Basis.coe_reindex, (· ∘ ·)]⟩

/--
Definition of `Submodule.smithNormalFormTopBasis` / `Submodule.smithNormalFormTopBasis` 的定义

English:
definition Submodule.smithNormalFormTopBasis
  signature: (b : Basis ι R M)
  body: (exists_smith_normal_form_of_rank_eq b h).choose

中文:
定义 Submodule.smithNormalFormTopBasis
  签名: (b : Basis ι R M)
  定义体: (exists_smith_normal_form_of_rank_eq b h).choose

Depends on / 依赖: exists_smith_normal_form_of_rank_eq
-/
noncomputable def Submodule.smithNormalFormTopBasis (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) : Basis ι R M :=
  (exists_smith_normal_form_of_rank_eq b h).choose

/--
Definition of `Submodule.smithNormalFormBotBasis` / `Submodule.smithNormalFormBotBasis` 的定义

English:
definition Submodule.smithNormalFormBotBasis
  signature: (b : Basis ι R M)
  body: (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose

中文:
定义 Submodule.smithNormalFormBotBasis
  签名: (b : Basis ι R M)
  定义体: (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose, exists_smith_normal_form_of_rank_eq
-/
noncomputable def Submodule.smithNormalFormBotBasis (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) : Basis ι R N :=
  (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose

/--
Definition of `Submodule.smithNormalFormCoeffs` / `Submodule.smithNormalFormCoeffs` 的定义

English:
definition Submodule.smithNormalFormCoeffs
  signature: (b : Basis ι R M)
  body: (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose

@[simp]

中文:
定义 Submodule.smithNormalFormCoeffs
  签名: (b : Basis ι R M)
  定义体: (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose

@[simp]

Depends on / 依赖: choose_spec, choose_spec.choose, exists_smith_normal_form_of_rank_eq
-/
noncomputable def Submodule.smithNormalFormCoeffs (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) : ι -> R :=
  (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose

@[simp]
/--
theorem `Submodule.smithNormalFormBotBasis_def` / 定理 `Submodule.smithNormalFormBotBasis_def`

English:
theorem Submodule.smithNormalFormBotBasis_def
  statement: (b : Basis ι R M)
  proof: (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose_spec

@[simp]

中文:
定理 Submodule.smithNormalFormBotBasis_def
  结论: (b : Basis ι R M)
  证明: (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose_spec

@[simp]

Depends on / 依赖: choose_spec, choose_spec.choose_spec.choose_spec, exists_smith_normal_form_of_rank_eq
-/
theorem Submodule.smithNormalFormBotBasis_def (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) :
    forall i, (smithNormalFormBotBasis b h i : M) =
      smithNormalFormCoeffs b h i • smithNormalFormTopBasis b h i :=
  (exists_smith_normal_form_of_rank_eq b h).choose_spec.choose_spec.choose_spec

@[simp]
/--
theorem `Submodule.smithNormalFormCoeffs_ne_zero` / 定理 `Submodule.smithNormalFormCoeffs_ne_zero`

English:
theorem Submodule.smithNormalFormCoeffs_ne_zero
  statement: (b : Basis ι R M)
  proof: by
  intro hi
  apply Basis.ne_zero (smithNormalFormBotBasis b h) i
  refine Subtype.coe_injective ?_
  simp [hi]

中文:
定理 Submodule.smithNormalFormCoeffs_ne_zero
  结论: (b : Basis ι R M)
  证明: by
  intro hi
  apply Basis.ne_zero (smithNormalFormBotBasis b h) i
  refine Subtype.coe_injective ?_
  simp [hi]

Depends on / 依赖: Basis.ne_zero, Subtype, Subtype.coe_injective, coe_injective, ne_zero, smithNormalFormBotBasis
-/
theorem Submodule.smithNormalFormCoeffs_ne_zero (b : Basis ι R M)
    (h : Module.finrank R N = Module.finrank R M) (i : ι) :
    smithNormalFormCoeffs b h i != 0 := by
  intro hi
  apply Basis.ne_zero (smithNormalFormBotBasis b h) i
  refine Subtype.coe_injective ?_
  simp [hi]

end full_rank

section Ideal

variable {S : Type*} [CommRing S] [IsDomain S] [Algebra R S]

/--
theorem `Ideal.finrank_eq_finrank` / 定理 `Ideal.finrank_eq_finrank`

English:
theorem Ideal.finrank_eq_finrank
  given: [Finite ι] (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  proof: by
  obtain ⟨_, bS, bI, _, _, _⟩ := (I.restrictScalars R).smithNormalForm b
  cases nonempty_fintype ι
  rw [Module.finrank_eq_card_basis bS]; rw [Module.finrank_eq_card_basis bI]
  exact Ideal.rank_eq bS hI (bI.map ((restrictScalarsEquiv R S S I).restrictScalars R))

中文:
定理 Ideal.finrank_eq_finrank
  条件: [Finite ι] (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  证明: by
  obtain ⟨_, bS, bI, _, _, _⟩ := (I.restrictScalars R).smithNormalForm b
  cases nonempty_fintype ι
  rw [Module.finrank_eq_card_basis bS]; rw [Module.finrank_eq_card_basis bI]
  exact Ideal.rank_eq bS hI (bI.map ((restrictScalarsEquiv R S S I).restrictScalars R))

Depends on / 依赖: I.restrictScalars, Ideal.rank_eq, Module, Module.finrank_eq_card_basis, bI.map, finrank_eq_card_basis, nonempty_fintype, rank_eq, restrictScalars, restrictScalarsEquiv, smithNormalForm
-/
theorem Ideal.finrank_eq_finrank [Finite ι] (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) :
    Module.finrank R (restrictScalars R I) = Module.finrank R S := by
  obtain ⟨_, bS, bI, _, _, _⟩ := (I.restrictScalars R).smithNormalForm b
  cases nonempty_fintype ι
  rw [Module.finrank_eq_card_basis bS]; rw [Module.finrank_eq_card_basis bI]
  exact Ideal.rank_eq bS hI (bI.map ((restrictScalarsEquiv R S S I).restrictScalars R))

/--
Definition of `Ideal.smithNormalForm` / `Ideal.smithNormalForm` 的定义

English:
definition Ideal.smithNormalForm
  signature: [Fintype ι] (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  body: Submodule.smithNormalFormOfRankEq b (finrank_eq_finrank b I hI)

中文:
定义 Ideal.smithNormalForm
  签名: [Fintype ι] (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  定义体: Submodule.smithNormalFormOfRankEq b (finrank_eq_finrank b I hI)

Depends on / 依赖: Submodule, Submodule.smithNormalFormOfRankEq, finrank_eq_finrank, smithNormalFormOfRankEq
-/
noncomputable def Ideal.smithNormalForm [Fintype ι] (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) :
    Basis.SmithNormalForm (I.restrictScalars R) ι (Fintype.card ι) :=
  Submodule.smithNormalFormOfRankEq b (finrank_eq_finrank b I hI)

variable [Finite ι]

/--
theorem `Ideal.exists_smith_normal_form` / 定理 `Ideal.exists_smith_normal_form`

English:
theorem Ideal.exists_smith_normal_form
  given: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  proof: Submodule.exists_smith_normal_form_of_rank_eq b (finrank_eq_finrank b I hI)

中文:
定理 Ideal.exists_smith_normal_form
  条件: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  证明: Submodule.exists_smith_normal_form_of_rank_eq b (finrank_eq_finrank b I hI)

Depends on / 依赖: Submodule, Submodule.exists_smith_normal_form_of_rank_eq, exists_smith_normal_form_of_rank_eq, finrank_eq_finrank
-/
theorem Ideal.exists_smith_normal_form (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) :
    exists (b' : Basis ι R S) (a : ι -> R) (ab' : Basis ι R I), forall i, (ab' i : S) = a i • b' i :=
  Submodule.exists_smith_normal_form_of_rank_eq b (finrank_eq_finrank b I hI)

/--
Definition of `Ideal.ringBasis` / `Ideal.ringBasis` 的定义

English:
definition Ideal.ringBasis
  signature: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  body: (Ideal.exists_smith_normal_form b I hI).choose

中文:
定义 Ideal.ringBasis
  签名: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  定义体: (Ideal.exists_smith_normal_form b I hI).choose

Depends on / 依赖: Ideal.exists_smith_normal_form, exists_smith_normal_form
-/
noncomputable def Ideal.ringBasis (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : Basis ι R S :=
  (Ideal.exists_smith_normal_form b I hI).choose

/--
Definition of `Ideal.selfBasis` / `Ideal.selfBasis` 的定义

English:
definition Ideal.selfBasis
  signature: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  body: (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose

中文:
定义 Ideal.selfBasis
  签名: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  定义体: (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose

Depends on / 依赖: Ideal.exists_smith_normal_form, choose_spec, choose_spec.choose_spec.choose, exists_smith_normal_form
-/
noncomputable def Ideal.selfBasis (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : Basis ι R I :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose

/--
Definition of `Ideal.smithCoeffs` / `Ideal.smithCoeffs` 的定义

English:
definition Ideal.smithCoeffs
  signature: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  body: (Ideal.exists_smith_normal_form b I hI).choose_spec.choose

中文:
定义 Ideal.smithCoeffs
  签名: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  定义体: (Ideal.exists_smith_normal_form b I hI).choose_spec.choose

Depends on / 依赖: Ideal.exists_smith_normal_form, choose_spec, choose_spec.choose, exists_smith_normal_form
-/
noncomputable def Ideal.smithCoeffs (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) : ι -> R :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose

/-- If `S` a finite-dimensional ring extension of a PID `R` which is free as an `R`-module,
then any nonzero `S`-ideal `I` is free as an `R`-submodule of `S`, and we can
find a basis for `S` and `I` such that the inclusion map is a square diagonal
matrix.
-/
@[simp]
/--
theorem `Ideal.selfBasis_def` / 定理 `Ideal.selfBasis_def`

English:
theorem Ideal.selfBasis_def
  given: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  proof: (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose_spec

@[simp]

中文:
定理 Ideal.selfBasis_def
  条件: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥)
  证明: (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose_spec

@[simp]

Depends on / 依赖: Ideal.exists_smith_normal_form, choose_spec, choose_spec.choose_spec.choose_spec, exists_smith_normal_form
-/
theorem Ideal.selfBasis_def (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) :
    forall i, (Ideal.selfBasis b I hI i : S) = Ideal.smithCoeffs b I hI i • Ideal.ringBasis b I hI i :=
  (Ideal.exists_smith_normal_form b I hI).choose_spec.choose_spec.choose_spec

@[simp]
/--
theorem `Ideal.smithCoeffs_ne_zero` / 定理 `Ideal.smithCoeffs_ne_zero`

English:
theorem Ideal.smithCoeffs_ne_zero
  given: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) (i)
  proof: by
  intro hi
  apply Basis.ne_zero (Ideal.selfBasis b I hI) i
  refine Subtype.coe_injective ?_
  simp [hi]

中文:
定理 Ideal.smithCoeffs_ne_zero
  条件: (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) (i)
  证明: by
  intro hi
  apply Basis.ne_zero (Ideal.selfBasis b I hI) i
  refine Subtype.coe_injective ?_
  simp [hi]

Depends on / 依赖: Basis.ne_zero, Ideal.selfBasis, Subtype, Subtype.coe_injective, coe_injective, ne_zero, selfBasis
-/
theorem Ideal.smithCoeffs_ne_zero (b : Basis ι R S) (I : Ideal S) (hI : I != ⊥) (i) :
    Ideal.smithCoeffs b I hI i != 0 := by
  intro hi
  apply Basis.ne_zero (Ideal.selfBasis b I hI) i
  refine Subtype.coe_injective ?_
  simp [hi]

end Ideal

end SmithNormal

end PrincipalIdealDomain
