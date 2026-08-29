/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import Mathlib.LinearAlgebra.Matrix.Basis
public import Mathlib.LinearAlgebra.Matrix.BaseChange

/-!
# Restriction to submodules and restriction of scalars for perfect pairings.

We provide API for restricting perfect pairings to submodules and for restricting their scalars.

## Main definitions
* `PerfectPairing.restrict`: restriction of a perfect pairing to submodules.
* `PerfectPairing.restrictScalars`: restriction of scalars for a perfect pairing taking values in a
  subring.
* `PerfectPairing.restrictScalarsField`: simultaneously restrict both the domains and scalars
  of a perfect pairing with coefficients in a field.

-/

public section

open Function Module Set
open Submodule (span subset_span)

noncomputable section

namespace LinearMap

section CommRing

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (p : M ->ₗ[R] N ->ₗ[R] R) [p.IsPerfPair]

section Restrict

variable {M' N' : Type*} [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (i : M' ->ₗ[R] M) (j : N' ->ₗ[R] N) (hi : Injective i) (hj : Injective j)
  (hij : p.IsPerfectCompl (LinearMap.range i) (LinearMap.range j))

include hi hj hij

/--
lemma `restrict_aux` / 引理 `restrict_aux`

English:
lemma restrict_aux
  statement: Bijective (p.compl₁₂ i j)
  proof: by
refine ⟨LinearMap.ker_eq_bot.mp eq_bot_iff.mpr fun m hm => ?_, fun f => ?_⟩
  · replace hm : i m in j.range.dualAnnihilator.map (p.toPerfPair.symm : Dual R N ->ₗ[R] M) := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      refine ⟨p.toPerfPair (i m), ?_, LinearEquiv.symm_apply_apply _ _⟩
      rintro - ⟨n, rfl⟩
      simpa using LinearMap.congr_fun hm n
    suffices i m in (⊥ : Submodule R M) by simpa [hi] using this
    simpa only [← hij.isCompl_left.inf_eq_bot, Submodule.mem_inf]
      using ⟨LinearMap.mem_range_self i m, hm⟩
  · set F : Module.Dual R N := f ∘ₗ j.linearProjOfIsCompl _ hj hij.isCompl_right with hF
    have hF (n : N') : F (j n) = f n := by simp [hF]
    set m : M := p.toPerfPair.symm F with hm
    obtain ⟨-, y, ⟨m₀, rfl⟩, hy, hm'⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hij.isCompl_left.codisjoint m
    refine ⟨m₀, LinearMap.ext fun n => ?_⟩
    replace hy : (p y) (j n) = 0 := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      simpa using hg _ (LinearMap.mem_range_self j n)
    rw [hm]; rw [← LinearEquiv.symm_apply_eq]; rw [map_add]; rw [LinearEquiv.symm_symm] at hm'
    simpa [← hF, ← LinearMap.congr_fun hm' (j n)]

中文:
引理 restrict_aux
  结论: 双射 (p.compl₁₂ i j)
  证明: by
refine ⟨LinearMap.ker_eq_bot.mp eq_bot_iff.mpr fun m hm => ?_, fun f => ?_⟩
  · replace hm : i m in j.range.dualAnnihilator.map (p.toPerfPair.symm : Dual R N ->ₗ[R] M) := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      refine ⟨p.toPerfPair (i m), ?_, LinearEquiv.symm_apply_apply _ _⟩
      rintro - ⟨n, rfl⟩
      simpa using LinearMap.congr_fun hm n
    suffices i m in (⊥ : Submodule R M) by simpa [hi] using this
    simpa only [← hij.isCompl_left.inf_eq_bot, Submodule.mem_inf]
      using ⟨LinearMap.mem_range_self i m, hm⟩
  · set F : Module.Dual R N := f ∘ₗ j.linearProjOfIsCompl _ hj hij.isCompl_right with hF
    have hF (n : N') : F (j n) = f n := by simp [hF]
    set m : M := p.toPerfPair.symm F with hm
    obtain ⟨-, y, ⟨m₀, rfl⟩, hy, hm'⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hij.isCompl_left.codisjoint m
    refine ⟨m₀, LinearMap.ext fun n => ?_⟩
    replace hy : (p y) (j n) = 0 := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      simpa using hg _ (LinearMap.mem_range_self j n)
    rw [hm]; rw [← LinearEquiv.symm_apply_eq]; rw [map_add]; rw [LinearEquiv.symm_symm] at hm'
    simpa [← hF, ← LinearMap.congr_fun hm' (j n)]
-/
private lemma restrict_aux : Bijective (p.compl₁₂ i j) := by
refine ⟨LinearMap.ker_eq_bot.mp eq_bot_iff.mpr fun m hm => ?_, fun f => ?_⟩
  · replace hm : i m in j.range.dualAnnihilator.map (p.toPerfPair.symm : Dual R N ->ₗ[R] M) := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator]
      refine ⟨p.toPerfPair (i m), ?_, LinearEquiv.symm_apply_apply _ _⟩
      rintro - ⟨n, rfl⟩
      simpa using LinearMap.congr_fun hm n
    suffices i m in (⊥ : Submodule R M) by simpa [hi] using this
    simpa only [← hij.isCompl_left.inf_eq_bot, Submodule.mem_inf]
      using ⟨LinearMap.mem_range_self i m, hm⟩
  · set F : Module.Dual R N := f ∘ₗ j.linearProjOfIsCompl _ hj hij.isCompl_right with hF
    have hF (n : N') : F (j n) = f n := by simp [hF]
    set m : M := p.toPerfPair.symm F with hm
    obtain ⟨-, y, ⟨m₀, rfl⟩, hy, hm'⟩ :=
      Submodule.codisjoint_iff_exists_add_eq.mp hij.isCompl_left.codisjoint m
    refine ⟨m₀, LinearMap.ext fun n => ?_⟩
    replace hy : (p y) (j n) = 0 := by
      simp only [Submodule.mem_map, Submodule.mem_dualAnnihilator] at hy
      obtain ⟨g, hg, rfl⟩ := hy
      simpa using hg _ (LinearMap.mem_range_self j n)
    rw [hm]; rw [← LinearEquiv.symm_apply_eq]; rw [map_add]; rw [LinearEquiv.symm_symm] at hm'
    simpa [← hF, ← LinearMap.congr_fun hm' (j n)]

/--
lemma `IsPerfPair.restrict` / 引理 `IsPerfPair.restrict`

English:
lemma IsPerfPair.restrict
  statement: (p.compl₁₂ i j).IsPerfPair where
  proof: p.restrict_aux i j hi hj hij
  bijective_right := p.flip.restrict_aux j i hj hi hij.flip

中文:
引理 是PerfPair.restrict
  结论: (p.compl₁₂ i j).是PerfPair where
  证明: p.restrict_aux i j hi hj hij
  bijective_right := p.flip.restrict_aux j i hj hi hij.flip

Depends on / 依赖: p.restrict_aux, restrict_aux
-/
lemma IsPerfPair.restrict : (p.compl₁₂ i j).IsPerfPair where
  bijective_left := p.restrict_aux i j hi hj hij
  bijective_right := p.flip.restrict_aux j i hj hi hij.flip

end Restrict

section RestrictScalars

variable {S M' N' : Type*}
  [CommRing S] [IsDomain S] [Algebra S R] [Module S M] [Module S N] [IsScalarTower S R M]
  [IsScalarTower S R N] [IsTorsionFree S R] [Nontrivial R]
  [AddCommGroup M'] [Module S M'] [AddCommGroup N'] [Module S N']
  (i : M' ->ₗ[S] M) (j : N' ->ₗ[S] N)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `restrictScalars_injective_aux` / 引理 `restrictScalars_injective_aux`

English:
lemma restrictScalars_injective_aux
  proof: by
  let f := LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x (hx : f x = 0) => ?_
  replace hx (n : N) : p (i x) n = 0 := by
    have hn : n in span R (LinearMap.range j : Set N) := hN ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n', rfl⟩ := hz
      simpa [f] using LinearMap.congr_fun hx n'
    | zero => simp
    | add => rw [map_add]; aesop
    | smul => rw [map_smul]; aesop
  rw [← i.map_eq_zero_iff hi]; rw [← p.map_eq_zero_iff p.toPerfPair.injective]
  ext n
  simpa using hx n

中文:
引理 restrictScalars_injective_aux
  证明: by
  let f := LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x (hx : f x = 0) => ?_
  replace hx (n : N) : p (i x) n = 0 := by
    have hn : n in span R (LinearMap.range j : Set N) := hN ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n', rfl⟩ := hz
      simpa [f] using LinearMap.congr_fun hx n'
    | zero => simp
    | add => rw [map_add]; aesop
    | smul => rw [map_smul]; aesop
  rw [← i.map_eq_zero_iff hi]; rw [← p.map_eq_zero_iff p.toPerfPair.injective]
  ext n
  simpa using hx n
-/
private lemma restrictScalars_injective_aux
    (hi : Injective i)
    (hN : span R (LinearMap.range j : Set N) = ⊤)
    (hp : forall m n, p (i m) (j n) in (algebraMap S R).range) :
    Injective ((LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp)) := by
  let f := LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp
  rw [← LinearMap.ker_eq_bot]
  refine (Submodule.eq_bot_iff _).mpr fun x (hx : f x = 0) => ?_
  replace hx (n : N) : p (i x) n = 0 := by
    have hn : n in span R (LinearMap.range j : Set N) := hN ▸ Submodule.mem_top
    induction hn using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨n', rfl⟩ := hz
      simpa [f] using LinearMap.congr_fun hx n'
    | zero => simp
    | add => rw [map_add]; aesop
    | smul => rw [map_smul]; aesop
  rw [← i.map_eq_zero_iff hi]; rw [← p.map_eq_zero_iff p.toPerfPair.injective]
  ext n
  simpa using hx n

set_option backward.isDefEq.respectTransparency false in
/--
lemma `restrictScalars_surjective_aux` / 引理 `restrictScalars_surjective_aux`

English:
lemma restrictScalars_surjective_aux
  proof: by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.mpr fun g : Module.Dual S N' => ?_
  obtain ⟨m, hm⟩ := h g
  refine ⟨m, ?_⟩
  ext n
  apply FaithfulSMul.algebraMap_injective S R
  change Algebra.linearMap S R _ = _
  simpa using LinearMap.congr_fun hm n

中文:
引理 restrictScalars_surjective_aux
  证明: by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.mpr fun g : Module.Dual S N' => ?_
  obtain ⟨m, hm⟩ := h g
  refine ⟨m, ?_⟩
  ext n
  apply FaithfulSMul.algebraMap_injective S R
  change Algebra.linearMap S R _ = _
  simpa using LinearMap.congr_fun hm n
-/
private lemma restrictScalars_surjective_aux
    (h : forall g : Module.Dual S N', exists m,
      (p.toPerfPair (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (hp : forall m n, p (i m) (j n) in (algebraMap S R).range) :
    Surjective ((LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp)) := by
  rw [← LinearMap.range_eq_top]
  refine Submodule.eq_top_iff'.mpr fun g : Module.Dual S N' => ?_
  obtain ⟨m, hm⟩ := h g
  refine ⟨m, ?_⟩
  ext n
  apply FaithfulSMul.algebraMap_injective S R
  change Algebra.linearMap S R _ = _
  simpa using LinearMap.congr_fun hm n

/--
lemma `IsPerfPair.restrictScalars` / 引理 `IsPerfPair.restrictScalars`

English:
lemma IsPerfPair.restrictScalars
  statement: (hi : Injective i) (hj : Injective j)
  proof: ⟨p.restrictScalars_injective_aux i j hi hN hp,
    p.restrictScalars_surjective_aux i j h₁ hp⟩
  bijective_right := ⟨p.flip.restrictScalars_injective_aux j i hj hM fun m n => hp n m,
    p.flip.restrictScalars_surjective_aux j i h₂ fun m n => hp n m⟩

中文:
引理 是PerfPair.restrictScalars
  结论: (hi : 单射 i) (hj : 单射 j)
  证明: ⟨p.restrictScalars_injective_aux i j hi hN hp,
    p.restrictScalars_surjective_aux i j h₁ hp⟩
  bijective_right := ⟨p.flip.restrictScalars_injective_aux j i hj hM fun m n => hp n m,
    p.flip.restrictScalars_surjective_aux j i h₂ fun m n => hp n m⟩

Depends on / 依赖: p.restrictScalars_injective_aux, restrictScalars_injective_aux
-/
lemma IsPerfPair.restrictScalars (hi : Injective i) (hj : Injective j)
    (hM : span R (LinearMap.range i : Set M) = ⊤) (hN : span R (LinearMap.range j : Set N) = ⊤)
    (h₁ : forall g : Module.Dual S N', exists m,
      (p.toPerfPair (i m)).restrictScalars S ∘ₗ j = Algebra.linearMap S R ∘ₗ g)
    (h₂ : forall g : Module.Dual S M', exists n,
      (p.flip.toPerfPair (j n)).restrictScalars S ∘ₗ i = Algebra.linearMap S R ∘ₗ g)
    (hp : forall m n, p (i m) (j n) in (algebraMap S R).range) :
    (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap S R)
      (FaithfulSMul.algebraMap_injective S R) p hp).IsPerfPair where
  bijective_left := ⟨p.restrictScalars_injective_aux i j hi hN hp,
    p.restrictScalars_surjective_aux i j h₁ hp⟩
  bijective_right := ⟨p.flip.restrictScalars_injective_aux j i hj hM fun m n => hp n m,
    p.flip.restrictScalars_surjective_aux j i h₂ fun m n => hp n m⟩

end RestrictScalars

end CommRing

section Field

variable {K L M N : Type*} [Field K] [Field L] [Algebra K L]
  [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]
  [Module K M] [Module K N] [IsScalarTower K L M]
  (p : M ->ₗ[L] N ->ₗ[L] L) [p.IsPerfPair]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exists_basis_basis_of_span_eq_top_of_mem_algebraMap` / 引理 `exists_basis_basis_of_span_eq_top_of_mem_algebraMap`

English:
lemma exists_basis_basis_of_span_eq_top_of_mem_algebraMap
  proof: by
  classical
  have : IsReflexive L M := .of_isPerfPair p
  have : IsReflexive L N := .of_isPerfPair p.flip
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_linearIndependent L (M' : Set M)
  rw [hM] at hv₂
let b : Basis _ L M := Basis.mk hv₃ by rw [← hv₂, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
have : Fintype v := Set.Finite.fintype Module.Finite.finite_basis b
  set v' : v -> M' := fun i => ⟨i, hv₁ (Subtype.coe_prop i)⟩
  have hv' : LinearIndependent K v' := by
replace hv₃ := hv₃.restrict_scalars (R := K) by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact FaithfulSMul.algebraMap_injective K L
    rw [show ((↑) : v -> M) = M'.subtype ∘ v' by ext; simp [v']] at hv₃
    exact hv₃.of_comp
  suffices span K (Set.range v') = ⊤ by
    let e := (Module.Finite.finite_basis b).equivFin
    let b' : Basis _ K M' := Basis.mk hv' (by rw [this])
    exact ⟨_, b.reindex e, b'.reindex e, fun i => by simp [b, b', v']⟩
  suffices span K v = M' by
    apply Submodule.map_injective_of_injective M'.injective_subtype
    rw [Submodule.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
    simpa [v']
  refine le_antisymm (Submodule.span_le.mpr hv₁) fun m hm => ?_
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := exists_linearIndependent L (N' : Set N)
  rw [hN] at hw₂
let bN : Basis _ L N := Basis.mk hw₃ by
    rw [← hw₂]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]
have : Fintype w := Set.Finite.fintype Module.Finite.finite_basis bN
have e : v ≃ w := Fintype.equivOfCardEq by rw [← Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis bN, Module.finrank_of_isPerfPair p]
  let bM := bN.dualBasis.map p.toPerfPair.symm
  have hbM (j : w) (x : M) (hx : x in M') : bM.repr x j = p x (j : N) := by simp [bM, bN]
  have hj (j : w) : bM.repr m j in (algebraMap K L).range := (hbM _ _ hm) ▸ hp m hm j (hw₁ j.2)
  replace hp (i : w) (j : v) :
      (bN.dualBasis.map p.toPerfPair.symm).toMatrix b i j in (algebraMap K L).fieldRange := by
    simp only [Basis.toMatrix, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      Basis.dualBasis_repr]
    exact hp (b j) (by simpa [b] using hv₁ j.2) (bN i) (by simpa [bN] using hw₁ i.2)
  have hA (i j) : b.toMatrix bM i j in (algebraMap K L).range :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left e _ (by simp [bM]) hp i j
  have h_span : span K v = span K (Set.range b) := by simp [b]
  rw [h_span]; rw [Basis.mem_span_iff_repr_mem]; rw [← Basis.toMatrix_mulVec_repr bM b m]
  exact fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hj j)

中文:
引理 存在_basis_basis_of_span_eq_top_of_mem_algebraMap
  证明: by
  classical
  have : IsReflexive L M := .of_isPerfPair p
  have : IsReflexive L N := .of_isPerfPair p.flip
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_linearIndependent L (M' : Set M)
  rw [hM] at hv₂
let b : Basis _ L M := Basis.mk hv₃ by rw [← hv₂, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
have : Fintype v := Set.Finite.fintype Module.Finite.finite_basis b
  set v' : v -> M' := fun i => ⟨i, hv₁ (Subtype.coe_prop i)⟩
  have hv' : LinearIndependent K v' := by
replace hv₃ := hv₃.restrict_scalars (R := K) by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact FaithfulSMul.algebraMap_injective K L
    rw [show ((↑) : v -> M) = M'.subtype ∘ v' by ext; simp [v']] at hv₃
    exact hv₃.of_comp
  suffices span K (Set.range v') = ⊤ by
    let e := (Module.Finite.finite_basis b).equivFin
    let b' : Basis _ K M' := Basis.mk hv' (by rw [this])
    exact ⟨_, b.reindex e, b'.reindex e, fun i => by simp [b, b', v']⟩
  suffices span K v = M' by
    apply Submodule.map_injective_of_injective M'.injective_subtype
    rw [Submodule.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
    simpa [v']
  refine le_antisymm (Submodule.span_le.mpr hv₁) fun m hm => ?_
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := exists_linearIndependent L (N' : Set N)
  rw [hN] at hw₂
let bN : Basis _ L N := Basis.mk hw₃ by
    rw [← hw₂]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]
have : Fintype w := Set.Finite.fintype Module.Finite.finite_basis bN
have e : v ≃ w := Fintype.equivOfCardEq by rw [← Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis bN, Module.finrank_of_isPerfPair p]
  let bM := bN.dualBasis.map p.toPerfPair.symm
  have hbM (j : w) (x : M) (hx : x in M') : bM.repr x j = p x (j : N) := by simp [bM, bN]
  have hj (j : w) : bM.repr m j in (algebraMap K L).range := (hbM _ _ hm) ▸ hp m hm j (hw₁ j.2)
  replace hp (i : w) (j : v) :
      (bN.dualBasis.map p.toPerfPair.symm).toMatrix b i j in (algebraMap K L).fieldRange := by
    simp only [Basis.toMatrix, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      Basis.dualBasis_repr]
    exact hp (b j) (by simpa [b] using hv₁ j.2) (bN i) (by simpa [bN] using hw₁ i.2)
  have hA (i j) : b.toMatrix bM i j in (algebraMap K L).range :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left e _ (by simp [bM]) hp i j
  have h_span : span K v = span K (Set.range b) := by simp [b]
  rw [h_span]; rw [Basis.mem_span_iff_repr_mem]; rw [← Basis.toMatrix_mulVec_repr bM b m]
  exact fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hj j)

Depends on / 依赖: Basis.mk, Finite, Fintype, IsReflexive, LinearIndependent, Module, Module.Finite.finite_basis, Set.Finite.fintype, Set.ofPred_mem_eq, Subtype, Subtype.coe_prop, Subtype.range_coe_subtype, classical, coe_prop, exists_linearIndependent, finite_basis, fintype, ofPred_mem_eq, of_isPerfPair, p.flip
-/
lemma exists_basis_basis_of_span_eq_top_of_mem_algebraMap
    (M' : Submodule K M) (N' : Submodule K N)
    (hM : span L (M' : Set M) = ⊤)
    (hN : span L (N' : Set N) = ⊤)
    (hp : forallᵉ (x in M') (y in N'), p x y in (algebraMap K L).range) :
    exists (n : Nat) (b : Basis (Fin n) L M) (b' : Basis (Fin n) K M'), forall i, b i = b' i := by
  classical
  have : IsReflexive L M := .of_isPerfPair p
  have : IsReflexive L N := .of_isPerfPair p.flip
  obtain ⟨v, hv₁, hv₂, hv₃⟩ := exists_linearIndependent L (M' : Set M)
  rw [hM] at hv₂
let b : Basis _ L M := Basis.mk hv₃ by rw [← hv₂, Subtype.range_coe_subtype, Set.ofPred_mem_eq]
have : Fintype v := Set.Finite.fintype Module.Finite.finite_basis b
  set v' : v -> M' := fun i => ⟨i, hv₁ (Subtype.coe_prop i)⟩
  have hv' : LinearIndependent K v' := by
replace hv₃ := hv₃.restrict_scalars (R := K) by
      simp_rw [← Algebra.algebraMap_eq_smul_one]
      exact FaithfulSMul.algebraMap_injective K L
    rw [show ((↑) : v -> M) = M'.subtype ∘ v' by ext; simp [v']] at hv₃
    exact hv₃.of_comp
  suffices span K (Set.range v') = ⊤ by
    let e := (Module.Finite.finite_basis b).equivFin
    let b' : Basis _ K M' := Basis.mk hv' (by rw [this])
    exact ⟨_, b.reindex e, b'.reindex e, fun i => by simp [b, b', v']⟩
  suffices span K v = M' by
    apply Submodule.map_injective_of_injective M'.injective_subtype
    rw [Submodule.map_span]; rw [← Set.image_univ]; rw [Set.image_image]
    simpa [v']
  refine le_antisymm (Submodule.span_le.mpr hv₁) fun m hm => ?_
  obtain ⟨w, hw₁, hw₂, hw₃⟩ := exists_linearIndependent L (N' : Set N)
  rw [hN] at hw₂
let bN : Basis _ L N := Basis.mk hw₃ by
    rw [← hw₂]; rw [Subtype.range_coe_subtype]; rw [Set.ofPred_mem_eq]
have : Fintype w := Set.Finite.fintype Module.Finite.finite_basis bN
have e : v ≃ w := Fintype.equivOfCardEq by rw [← Module.finrank_eq_card_basis b,
    ← Module.finrank_eq_card_basis bN, Module.finrank_of_isPerfPair p]
  let bM := bN.dualBasis.map p.toPerfPair.symm
  have hbM (j : w) (x : M) (hx : x in M') : bM.repr x j = p x (j : N) := by simp [bM, bN]
  have hj (j : w) : bM.repr m j in (algebraMap K L).range := (hbM _ _ hm) ▸ hp m hm j (hw₁ j.2)
  replace hp (i : w) (j : v) :
      (bN.dualBasis.map p.toPerfPair.symm).toMatrix b i j in (algebraMap K L).fieldRange := by
    simp only [Basis.toMatrix, Basis.map_repr, LinearEquiv.symm_symm, LinearEquiv.trans_apply,
      Basis.dualBasis_repr]
    exact hp (b j) (by simpa [b] using hv₁ j.2) (bN i) (by simpa [bN] using hw₁ i.2)
  have hA (i j) : b.toMatrix bM i j in (algebraMap K L).range :=
    Matrix.mem_subfield_of_mul_eq_one_of_mem_subfield_left e _ (by simp [bM]) hp i j
  have h_span : span K v = span K (Set.range b) := by simp [b]
  rw [h_span]; rw [Basis.mem_span_iff_repr_mem]; rw [← Basis.toMatrix_mulVec_repr bM b m]
  exact fun i => Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hA i j) (hj j)

/--
lemma `finrank_eq_of_isPerfPair` / 引理 `finrank_eq_of_isPerfPair`

English:
lemma finrank_eq_of_isPerfPair
  proof: by
  obtain ⟨n, b, b', hb⟩ := exists_basis_basis_of_span_eq_top_of_mem_algebraMap p M' N' hM hN hp
  rw [finrank_eq_card_basis b]; rw [finrank_eq_card_basis b']

中文:
引理 finrank_eq_of_isPerfPair
  证明: by
  obtain ⟨n, b, b', hb⟩ := exists_basis_basis_of_span_eq_top_of_mem_algebraMap p M' N' hM hN hp
  rw [finrank_eq_card_basis b]; rw [finrank_eq_card_basis b']

Depends on / 依赖: exists_basis_basis_of_span_eq_top_of_mem_algebraMap, finrank_eq_card_basis
-/
lemma finrank_eq_of_isPerfPair
    (M' : Submodule K M) (N' : Submodule K N)
    (hM : span L (M' : Set M) = ⊤)
    (hN : span L (N' : Set N) = ⊤)
    (hp : forallᵉ (x in M') (y in N'), p x y in (algebraMap K L).range) :
    finrank K M' = finrank L M := by
  obtain ⟨n, b, b', hb⟩ := exists_basis_basis_of_span_eq_top_of_mem_algebraMap p M' N' hM hN hp
  rw [finrank_eq_card_basis b]; rw [finrank_eq_card_basis b']

variable {M' N' : Type*}
  [AddCommGroup M'] [AddCommGroup N'] [Module K M'] [Module K N'] [IsScalarTower K L N]
  (i : M' ->ₗ[K] M) (j : N' ->ₗ[K] N) (hi : Injective i) (hj : Injective j)

include hi hj in
/--
lemma `restrictScalars_field_aux` / 引理 `restrictScalars_field_aux`

English:
lemma restrictScalars_field_aux
  proof: by
  suffices FiniteDimensional K M' from .of_injective (p.restrictScalars_injective_aux i j hi hN hp)
    (p.flip.restrictScalars_injective_aux j i hj hM (fun m n => hp n m))
obtain ⟨n, -, b', -⟩ := p.exists_basis_basis_of_span_eq_top_of_mem_algebraMap _ _ hM hN by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact hp m n
  have : FiniteDimensional K (LinearMap.range i) := b'.finiteDimensional_of_finite
  exact Finite.equiv (LinearEquiv.ofInjective i hi).symm

中文:
引理 restrictScalars_field_aux
  证明: by
  suffices FiniteDimensional K M' from .of_injective (p.restrictScalars_injective_aux i j hi hN hp)
    (p.flip.restrictScalars_injective_aux j i hj hM (fun m n => hp n m))
obtain ⟨n, -, b', -⟩ := p.exists_basis_basis_of_span_eq_top_of_mem_algebraMap _ _ hM hN by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact hp m n
  have : FiniteDimensional K (LinearMap.range i) := b'.finiteDimensional_of_finite
  exact Finite.equiv (LinearEquiv.ofInjective i hi).symm
-/
private lemma restrictScalars_field_aux
    (hM : span L (LinearMap.range i : Set M) = ⊤)
    (hN : span L (LinearMap.range j : Set N) = ⊤)
    (hp : forall m n, p (i m) (j n) in (algebraMap K L).range) :
    (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap K L)
      (FaithfulSMul.algebraMap_injective K L) p hp).IsPerfPair := by
  suffices FiniteDimensional K M' from .of_injective (p.restrictScalars_injective_aux i j hi hN hp)
    (p.flip.restrictScalars_injective_aux j i hj hM (fun m n => hp n m))
obtain ⟨n, -, b', -⟩ := p.exists_basis_basis_of_span_eq_top_of_mem_algebraMap _ _ hM hN by
    rintro - ⟨m, rfl⟩ - ⟨n, rfl⟩
    exact hp m n
  have : FiniteDimensional K (LinearMap.range i) := b'.finiteDimensional_of_finite
  exact Finite.equiv (LinearEquiv.ofInjective i hi).symm

set_option backward.isDefEq.respectTransparency false in
include hi hj in
/--
lemma `IsPerfPair.restrictScalars_of_field` / 引理 `IsPerfPair.restrictScalars_of_field`

English:
lemma IsPerfPair.restrictScalars_of_field
  proof: by
  have : (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype).IsPerfPair :=
    .restrict _ _ _ (by simp) (by simp) (by simpa)
  exact restrictScalars_field_aux
    (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype)
    ((LinearMap.range i).inclusionSpan L ∘ₗ i.rangeRestrict)
    ((LinearMap.range j).inclusionSpan L ∘ₗ j.rangeRestrict)
    (((LinearMap.range i).injective_inclusionSpan L).comp (by simpa))
    (((LinearMap.range j).injective_inclusionSpan L).comp (by simpa))
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range i).span_range_inclusionSpan L)
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range j).span_range_inclusionSpan L)
    fun x y => LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (LinearMap.range <| Algebra.linearMap K L) (range i) (range j)
      ((LinearMap.restrictScalarsₗ K L _ _ _).comp (p.restrictScalars K))
      (by simpa) (i x) (j y) (subset_span <| by simp) (subset_span <| by simp)

omit [p.IsPerfPair] in

中文:
引理 是PerfPair.restrictScalars_of_field
  证明: by
  have : (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype).IsPerfPair :=
    .restrict _ _ _ (by simp) (by simp) (by simpa)
  exact restrictScalars_field_aux
    (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype)
    ((LinearMap.range i).inclusionSpan L ∘ₗ i.rangeRestrict)
    ((LinearMap.range j).inclusionSpan L ∘ₗ j.rangeRestrict)
    (((LinearMap.range i).injective_inclusionSpan L).comp (by simpa))
    (((LinearMap.range j).injective_inclusionSpan L).comp (by simpa))
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range i).span_range_inclusionSpan L)
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range j).span_range_inclusionSpan L)
    fun x y => LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (LinearMap.range <| Algebra.linearMap K L) (range i) (range j)
      ((LinearMap.restrictScalarsₗ K L _ _ _).comp (p.restrictScalars K))
      (by simpa) (i x) (j y) (subset_span <| by simp) (subset_span <| by simp)

omit [p.IsPerfPair] in

Depends on / 依赖: IsPerfPair, LinearMap, LinearMap.range, i.rangeRestrict, inclusionSpan, injective_inclusionSpan, j.rangeRestrict, p.compl, rangeRestrict, restrict, restrictScalars_field_aux, subtype
-/
lemma IsPerfPair.restrictScalars_of_field
    (hij : p.IsPerfectCompl (span L <| LinearMap.range i) (span L <| LinearMap.range j))
    (hp : forall m n, p (i m) (j n) in (algebraMap K L).range) :
    (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap K L)
      (FaithfulSMul.algebraMap_injective K L) p hp).IsPerfPair := by
  have : (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype).IsPerfPair :=
    .restrict _ _ _ (by simp) (by simp) (by simpa)
  exact restrictScalars_field_aux
    (p.compl₁₂ (span L <| .range i).subtype (span L <| .range j).subtype)
    ((LinearMap.range i).inclusionSpan L ∘ₗ i.rangeRestrict)
    ((LinearMap.range j).inclusionSpan L ∘ₗ j.rangeRestrict)
    (((LinearMap.range i).injective_inclusionSpan L).comp (by simpa))
    (((LinearMap.range j).injective_inclusionSpan L).comp (by simpa))
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range i).span_range_inclusionSpan L)
    (by rw [LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_rangeRestrict _)]
        exact (LinearMap.range j).span_range_inclusionSpan L)
    fun x y => LinearMap.BilinMap.apply_apply_mem_of_mem_span
      (LinearMap.range <| Algebra.linearMap K L) (range i) (range j)
      ((LinearMap.restrictScalarsₗ K L _ _ _).comp (p.restrictScalars K))
      (by simpa) (i x) (j y) (subset_span <| by simp) (subset_span <| by simp)

omit [p.IsPerfPair] in
/--
lemma `restrictScalarsField_apply_apply` / 引理 `restrictScalarsField_apply_apply`

English:
lemma restrictScalarsField_apply_apply
  statement: (hp : forall m n, p (i m) (j n) in (algebraMap K L).range)
  proof: LinearMap.restrictScalarsRange₂_apply i j (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) p hp x y

中文:
引理 restrictScalarsField_apply_apply
  结论: (hp : 对任意 m n, p (i m) (j n) in (algebraMap K L).range)
  证明: LinearMap.restrictScalarsRange₂_apply i j (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) p hp x y
-/
@[simp] lemma restrictScalarsField_apply_apply (hp : forall m n, p (i m) (j n) in (algebraMap K L).range)
    (x : M') (y : N') :
    algebraMap K L (LinearMap.restrictScalarsRange₂ i j (Algebra.linearMap K L)
      (FaithfulSMul.algebraMap_injective K L) p hp x y) = p (i x) (j y) :=
  LinearMap.restrictScalarsRange₂_apply i j (Algebra.linearMap K L)
    (FaithfulSMul.algebraMap_injective K L) p hp x y

end Field

end LinearMap
