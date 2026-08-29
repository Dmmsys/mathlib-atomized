/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lattices

Let `A` be an `R`-algebra and `V` an `A`-module. Then an `R`-submodule `M` of `V` is a lattice,
if `M` is finitely generated and spans `V` as an `A`-module.

The typical use case is `A = K` is the fraction field of an integral domain `R` and `V = ι → K`
for some finite `ι`. The scalar multiple a lattice by a unit in `K` is again a lattice. This gives
rise to a homothety relation.

When `R` is a DVR and `ι = Fin 2`, then by taking the quotient of the type of `R`-lattices in
`ι → K` by the homothety relation, one obtains the vertices of what is called the Bruhat-Tits tree
of `GL 2 K`.

## Main definitions

- `Submodule.IsLattice`: An `R`-submodule `M` of `V` is a lattice, if it is finitely generated
  and its `A`-span is `V`.

## Main properties

Let `R` be a PID and `A = K` its field of fractions.

- `Submodule.IsLattice.free`: Every lattice in `V` is `R`-free.
- `Basis.extendOfIsLattice`: Any `R`-basis of a lattice `M` in `V` defines a `K`-basis of `V`.
- `Submodule.IsLattice.rank`: The `R`-rank of a lattice in `V` is equal to the `K`-rank of `V`.
- `Submodule.IsLattice.inf`: The intersection of two lattices is a lattice.

## Note

In the case `R = ℤ` and `A = K` a field, there is also `IsZLattice` where the finitely
generated condition is replaced by having the discrete topology. This is for example used
for complex tori.
-/

@[expose] public section

open Module
open scoped Pointwise

universe u

variable {R : Type*} [CommRing R]

namespace Submodule

/--
Definition of `IsLattice` / `IsLattice` 的定义

English:
class IsLattice
  parameters: (A : outParam Type*) [CommRing A] [Algebra R A]
  axioms and operations (2):
    - fg : M.FG
    - span_eq_top : Submodule.span A (M : Set V) = ⊤

中文:
类 IsLattice
  参数: (A : outParam 类型) [CommRing A] [Algebra R A]
  公理与运算 (2 个):
    - fg : M.FG
    - span_eq_top : Submodule.span A (M : Set V) = ⊤
-/
class IsLattice (A : outParam Type*) [CommRing A] [Algebra R A]
    {V : Type*} [AddCommMonoid V] [Module R V] [Module A V] [IsScalarTower R A V]
    [IsScalarTower R A V] (M : Submodule R V) : Prop where
  fg : M.FG
  span_eq_top : Submodule.span A (M : Set V) = ⊤

namespace IsLattice

section

variable (A : Type*) [CommRing A] [Algebra R A]
variable {V : Type*} [AddCommGroup V] [Module R V] [Module A V] [IsScalarTower R A V]
variable (M : Submodule R V)

/--
Instance `finite` / 实例 `finite`

English:
instance finite
  signature: [IsLattice A M]
  body: by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg

中文:
实例 finite
  签名: [IsLattice A M]
  定义体: by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg

Depends on / 依赖: Finite, IsLattice, IsLattice.fg, Module, Module.Finite.iff_fg, iff_fg
-/
instance finite [IsLattice A M] : Module.Finite R M := by
  rw [Module.Finite.iff_fg]
  exact IsLattice.fg

set_option backward.isDefEq.respectTransparency false in
/--
Instance `smul` / 实例 `smul`

English:
instance smul
  signature: [IsLattice A M] (a : Aˣ)
  body: by
    obtain ⟨s, rfl⟩ := IsLattice.fg (M := M)
    rw [Submodule.smul_span]
    have : Finite (a • (s : Set V) : Set V) := Finite.Set.finite_image _ _
    exact Submodule.fg_span (Set.toFinite (a • (s : Set V)))
  span_eq_top := by
    rw [Submodule.coe_pointwise_smul]; rw [← Submodule.smul_span]; 

中文:
实例 smul
  签名: [IsLattice A M] (a : Aˣ)
  定义体: by
    obtain ⟨s, rfl⟩ := IsLattice.fg (M := M)
    rw [Submodule.smul_span]
    have : Finite (a • (s : Set V) : Set V) := Finite.Set.finite_image _ _
    exact Submodule.fg_span (Set.toFinite (a • (s : Set V)))
  span_eq_top := by
    rw [Submodule.coe_pointwise_smul]; rw [← Submodule.smul_span]; 

Depends on / 依赖: Finite, Finite.Set.finite_image, IsLattice, IsLattice.fg, IsLattice.span_eq_top, Set.toFinite, Submodule, Submodule.coe_pointwise_smul, Submodule.fg_span, Submodule.smul_mem_pointwise_smul, Submodule.smul_span, coe_pointwise_smul, fg_span, finite_image, smul_mem_pointwise_smul, smul_span, span_eq_top, toFinite
-/
instance smul [IsLattice A M] (a : Aˣ) : IsLattice A (a • M : Submodule R V) where
  fg := by
    obtain ⟨s, rfl⟩ := IsLattice.fg (M := M)
    rw [Submodule.smul_span]
    have : Finite (a • (s : Set V) : Set V) := Finite.Set.finite_image _ _
    exact Submodule.fg_span (Set.toFinite (a • (s : Set V)))
  span_eq_top := by
    rw [Submodule.coe_pointwise_smul]; rw [← Submodule.smul_span]; rw [IsLattice.span_eq_top]
    ext x
    refine ⟨fun _ => trivial, fun _ => ?_⟩
    rw [show x = a • a⁻¹ • x by simp]
    exact Submodule.smul_mem_pointwise_smul _ _ _ (by trivial)

/--
lemma `of_le_of_isLattice_of_fg` / 引理 `of_le_of_isLattice_of_fg`

English:
lemma of_le_of_isLattice_of_fg
  statement: {M N : Submodule R V} (hle : M <= N) [IsLattice A M]
  proof: ⟨hfg, eq_top_iff.mpr
    le_trans (by rw [IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

中文:
引理 of_le_of_isLattice_of_fg
  结论: {M N : Submodule R V} (hle : M <= N) [IsLattice A M]
  证明: ⟨hfg, eq_top_iff.mpr
    le_trans (by rw [IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

Depends on / 依赖: IsLattice, IsLattice.span_eq_top, Submodule, Submodule.span_mono, eq_top_iff, eq_top_iff.mpr, le_trans, span_eq_top, span_mono
-/
lemma of_le_of_isLattice_of_fg {M N : Submodule R V} (hle : M <= N) [IsLattice A M]
    (hfg : N.FG) : IsLattice A N :=
⟨hfg, eq_top_iff.mpr
    le_trans (by rw [IsLattice.span_eq_top]) (Submodule.span_mono hle)⟩

/--
Instance `sup` / 实例 `sup`

English:
instance sup
  signature: (M N : Submodule R V) [IsLattice A M] [IsLattice A N]
  body: of_le_of_isLattice_of_fg A le_sup_left (Submodule.FG.sup IsLattice.fg IsLattice.fg)

中文:
实例 sup
  签名: (M N : Submodule R V) [IsLattice A M] [IsLattice A N]
  定义体: of_le_of_isLattice_of_fg A le_sup_left (Submodule.FG.sup IsLattice.fg IsLattice.fg)

Depends on / 依赖: IsLattice, IsLattice.fg, Submodule, Submodule.FG.sup, le_sup_left, of_le_of_isLattice_of_fg
-/
instance sup (M N : Submodule R V) [IsLattice A M] [IsLattice A N] :
    IsLattice A (M ⊔ N) :=
  of_le_of_isLattice_of_fg A le_sup_left (Submodule.FG.sup IsLattice.fg IsLattice.fg)

end

section Field

variable {K : Type*} [Field K] [Algebra R K]

/--
lemma `_root_.Submodule.span_range_eq_top_of_injective_of_rank_le` / 引理 `_root_.Submodule.span_range_eq_top_of_injective_of_rank_le`

English:
lemma _root_.Submodule.span_range_eq_top_of_injective_of_rank_le
  statement: {M N : Type u} [IsDomain R]
  proof: by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h

中文:
引理 _root_.Submodule.span_range_eq_top_of_injective_of_rank_le
  结论: {M N : 类型u} [IsDomain R]
  证明: by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h

Depends on / 依赖: Cardinal, Cardinal.mk, Cardinal.mk_eq_nat_iff_fintype, LinearIndependent, LinearIndependent.cardinal_le_rank, LinearIndependent.iff_fractionRing, LinearMap, LinearMap.ker_eq_bot.mpr, LinearMap.range, Module, Module.finrank_eq_rank, Module.rank, Set.range, cardinal_le_rank, exists_set_linearIndependent, finrank_eq_rank, hli.map, hsubset, iff_fractionRing, ker_eq_bot
-/
lemma _root_.Submodule.span_range_eq_top_of_injective_of_rank_le {M N : Type u} [IsDomain R]
    [IsFractionRing R K] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module K N] [IsScalarTower R K N] [Module.Finite K N]
    {f : M ->ₗ[R] N} (hf : Function.Injective f) (h : Module.rank K N <= Module.rank R M) :
    Submodule.span K (LinearMap.range f : Set N) = ⊤ := by
  obtain ⟨s, hs, hli⟩ := exists_set_linearIndependent R M
  replace hli := hli.map' f (LinearMap.ker_eq_bot.mpr hf)
  rw [LinearIndependent.iff_fractionRing (R := R) (K := K)] at hli
  replace hs : Cardinal.mk s = Module.rank K N :=
    le_antisymm (LinearIndependent.cardinal_le_rank hli) (hs ▸ h)
  rw [← Module.finrank_eq_rank]; rw [Cardinal.mk_eq_nat_iff_fintype] at hs
  obtain ⟨hfin, hcard⟩ := hs
  have hsubset : Set.range (fun x : s => f x.val) subseteq (LinearMap.range f : Set N) := by
    rintro x ⟨a, rfl⟩
    simp
  rw [eq_top_iff]; rw [← LinearIndependent.span_eq_top_of_card_eq_finrank' hli hcard]
  exact Submodule.span_mono hsubset

variable (K) {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

/--
Definition of `_root_.Module.Basis.extendOfIsLattice` / `_root_.Module.Basis.extendOfIsLattice` 的定义

English:
definition _root_.Module.Basis.extendOfIsLattice
  signature: [IsFractionRing R K] {κ : Type*}
  body: have hli : LinearIndependent K (fun i => (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]; rw [linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearInd

中文:
定义 _root_.Module.Basis.extendOfIsLattice
  签名: [IsFractionRing R K] {κ : 类型}
  定义体: have hli : LinearIndependent K (fun i => (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]; rw [linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearInd

Depends on / 依赖: LinearIndependent, LinearIndependent.iff_fractionRing, M.subtype, Set.range, Set.range_comp, Submodule, Submodule.coe_eq_zero, Submodule.coe_smul_of_tower, Submodule.coe_sum, Submodule.map_span, Submodule.map_top, Submodule.span_span_of_tower, b.linearIndependent, b.span_eq, coe_eq_zero, coe_smul_of_tower, coe_sum, iff_fractionRing, linearIndependent, linearIndependent_iff
-/
noncomputable def _root_.Module.Basis.extendOfIsLattice [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) :
    Basis κ K V :=
  have hli : LinearIndependent K (fun i => (b i).val) := by
    rw [← LinearIndependent.iff_fractionRing (R := R)]; rw [linearIndependent_iff']
    intro s g hs
    simp_rw [← Submodule.coe_smul_of_tower, ← Submodule.coe_sum, Submodule.coe_eq_zero] at hs
    exact linearIndependent_iff'.mp b.linearIndependent s g hs
  have hsp : ⊤ <= span K (Set.range fun i => (M.subtype ∘ b) i) := by
    rw [← Submodule.span_span_of_tower R]; rw [Set.range_comp]; rw [← Submodule.map_span]
    simp [b.span_eq, Submodule.map_top, span_eq_top]
  Basis.mk hli hsp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `_root_.Module.Basis.extendOfIsLattice_apply` / 引理 `_root_.Module.Basis.extendOfIsLattice_apply`

English:
lemma _root_.Module.Basis.extendOfIsLattice_apply
  statement: [IsFractionRing R K] {κ : Type*}
  proof: by
  simp [Basis.extendOfIsLattice]

中文:
引理 _root_.Module.Basis.extendOfIsLattice_apply
  结论: [IsFractionRing R K] {κ : 类型}
  证明: by
  simp [Basis.extendOfIsLattice]

Depends on / 依赖: Basis.extendOfIsLattice, extendOfIsLattice
-/
lemma _root_.Module.Basis.extendOfIsLattice_apply [IsFractionRing R K] {κ : Type*}
    {M : Submodule R V} [IsLattice K M] (b : Basis κ R M) (k : κ) :
    b.extendOfIsLattice K k = (b k).val := by
  simp [Basis.extendOfIsLattice]

variable [IsDomain R]

/--
lemma `of_rank_le` / 引理 `of_rank_le`

English:
lemma of_rank_le
  statement: [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
  proof: hfg
  span_eq_top := by
    simpa using Submodule.span_range_eq_top_of_injective_of_rank_le M.injective_subtype hr

中文:
引理 of_rank_le
  结论: [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
  证明: hfg
  span_eq_top := by
    simpa using Submodule.span_range_eq_top_of_injective_of_rank_le M.injective_subtype hr
-/
lemma of_rank_le [Module.Finite K V] [IsFractionRing R K] {M : Submodule R V}
    (hfg : M.FG) (hr : Module.rank K V <= Module.rank R M) : IsLattice K M where
  fg := hfg
  span_eq_top := by
    simpa using Submodule.span_range_eq_top_of_injective_of_rank_le M.injective_subtype hr

variable [IsPrincipalIdealRing R]

/--
Instance `free` / 实例 `free`

English:
instance free
  signature: [Module.IsTorsionFree R K] (M : Submodule R V) [IsLattice K M]
  body: by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  -- any torsion free finite module over a PID is free
  infer_instance

中文:
实例 free
  签名: [Module.IsTorsionFree R K] (M : Submodule R V) [IsLattice K M]
  定义体: by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  -- any torsion free finite module over a PID is free
  infer_instance

Depends on / 依赖: IsTorsionFree, Module, Module.IsTorsionFree.trans_faithfulSMul, trans_faithfulSMul
-/
instance free [Module.IsTorsionFree R K] (M : Submodule R V) [IsLattice K M] : Module.Free R M := by
  have := Module.IsTorsionFree.trans_faithfulSMul R K V
  -- any torsion free finite module over a PID is free
  infer_instance

/--
lemma `rank'` / 引理 `rank'`

English:
lemma rank'
  given: [IsFractionRing R K] (M : Submodule R V) [IsLattice K M]
  proof: by
  let b := Module.Free.chooseBasis R M
  rw [rank_eq_card_basis b]; rw [← rank_eq_card_basis (b.extendOfIsLattice K)]

中文:
引理 rank'
  条件: [IsFractionRing R K] (M : Submodule R V) [IsLattice K M]
  证明: by
  let b := Module.Free.chooseBasis R M
  rw [rank_eq_card_basis b]; rw [← rank_eq_card_basis (b.extendOfIsLattice K)]

Depends on / 依赖: IsAddTorsionFree, IsAddTorsionFree.of_isDomain_charZero, Module, Module.Free.chooseBasis, b.extendOfIsLattice, chooseBasis, extendOfIsLattice, of_isDomain_charZero, rank_eq_card_basis
-/
lemma rank' [IsFractionRing R K] (M : Submodule R V) [IsLattice K M] :
    Module.rank R M = Module.rank K V := by
  let b := Module.Free.chooseBasis R M
  rw [rank_eq_card_basis b]; rw [← rank_eq_card_basis (b.extendOfIsLattice K)]

/--
lemma `rank_of_pi` / 引理 `rank_of_pi`

English:
lemma rank_of_pi
  statement: {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι -> K))
  proof: by
  rw [IsLattice.rank' K M]
  simp

中文:
引理 rank_of_pi
  结论: {ι : 类型} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι -> K))
  证明: by
  rw [IsLattice.rank' K M]
  simp

Depends on / 依赖: IsLattice, IsLattice.rank
-/
lemma rank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι -> K))
    [IsLattice K M] : Module.rank R M = Fintype.card ι := by
  rw [IsLattice.rank' K M]
  simp

/--
lemma `finrank_of_pi` / 引理 `finrank_of_pi`

English:
lemma finrank_of_pi
  statement: {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι -> K))
  proof: Module.finrank_eq_of_rank_eq (IsLattice.rank_of_pi K M)

中文:
引理 finrank_of_pi
  结论: {ι : 类型} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι -> K))
  证明: Module.finrank_eq_of_rank_eq (IsLattice.rank_of_pi K M)

Depends on / 依赖: IsLattice, IsLattice.rank_of_pi, Module, Module.finrank_eq_of_rank_eq, finrank_eq_of_rank_eq, rank_of_pi
-/
lemma finrank_of_pi {ι : Type*} [Fintype ι] [IsFractionRing R K] (M : Submodule R (ι -> K))
    [IsLattice K M] : Module.finrank R M = Fintype.card ι :=
  Module.finrank_eq_of_rank_eq (IsLattice.rank_of_pi K M)

/--
Instance `inf` / 实例 `inf`

English:
instance inf
  signature: [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V)
  body: by
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [← range_subtype (M ⊓ N)]
    apply Submodule.span_range_eq_top_of_injective_of_rank_le (M ⊓ N).injective_subtype
    have h := Submodule.rank_sup_add

中文:
实例 inf
  签名: [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V)
  定义体: by
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [← range_subtype (M ⊓ N)]
    apply Submodule.span_range_eq_top_of_injective_of_rank_le (M ⊓ N).injective_subtype
    have h := Submodule.rank_sup_add

Depends on / 依赖: Cardinal, Cardinal.eq_of_add_eq_add_left, Finite, IsLattice, IsLattice.rank, IsNoetherian, Module, Module.Finite.iff_fg, Module.rank_lt_aleph0, Submodule, Submodule.rank_sup_add_rank_inf_eq, Submodule.span_range_eq_top_of_injective_of_rank_le, eq_of_add_eq_add_left, iff_fg, inf_le_left, infer_instance, injective_subtype, isNoetherian_of_le, range_subtype, rank_lt_aleph0
-/
instance inf [Module.Finite K V] [IsFractionRing R K] (M N : Submodule R V)
    [IsLattice K M] [IsLattice K N] : IsLattice K (M ⊓ N) where
  fg := by
    have : IsNoetherian R ↥(M ⊓ N) := isNoetherian_of_le inf_le_left
    rw [← Module.Finite.iff_fg]
    infer_instance
  span_eq_top := by
    rw [← range_subtype (M ⊓ N)]
    apply Submodule.span_range_eq_top_of_injective_of_rank_le (M ⊓ N).injective_subtype
    have h := Submodule.rank_sup_add_rank_inf_eq M N
    rw [IsLattice.rank' K M]; rw [IsLattice.rank' K N]; rw [IsLattice.rank'] at h
    rw [Cardinal.eq_of_add_eq_add_left h (Module.rank_lt_aleph0 K V)]

end Field

end IsLattice

end Submodule
