/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Module.Submodule.Order
public import Mathlib.Algebra.Order.Module.Archimedean
public import Mathlib.Algebra.Order.Module.Equiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.LinearPMap
public import Mathlib.RingTheory.HahnSeries.Lex

/-!
# Hahn embedding theorem on ordered modules

This file proves a variant of the Hahn embedding theorem:

For a linearly ordered module `M` over an Archimedean division ring `K`,
there exists a strictly monotone linear map to lexicographically ordered
`R⟦FiniteArchimedeanClass M⟧` with an archimedean `K`-module `R`,
as long as there are embeddings from a certain family of Archimedean submodules to `R`.

The family of Archimedean submodules `HahnEmbedding.ArchimedeanStrata K M` is indexed by
`(c : ArchimedeanClass M)`, and each submodule is a complement of `ArchimedeanClass.ball K c`
under `ArchimedeanClass.closedBall K c`. The embeddings from these submodules are specified by
`HahnEmbedding.Seed K M R`.

By setting `K = ℚ` and `R = ℝ`, the condition can be trivially satisfied, leading
to a proof of the classic Hahn embedding theorem. (See `hahnEmbedding_isOrderedAddMonoid`)

## Main theorem

* `hahnEmbedding_isOrderedModule`:
  there exists a strictly monotone `M →ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧` that maps
  `ArchimedeanClass M` to `HahnSeries.orderTop` in the expected way, as long as
  `HahnEmbedding.Seed K M R` is nonempty.

## References

* [M. Hausner, J.G. Wendel, *Ordered vector spaces*][hausnerwendel1952]
-/

@[expose] public section

/-! ### Step 1: base embedding

We start with `HahnEmbedding.ArchimedeanStrata` that gives a family of Archimedean submodules,
and a "seed" `HahnEmbedding.Seed` that specifies how to embed each
`HahnEmbedding.ArchimedeanStrata.stratum` into `R`.

From these, we create a partial map from the direct sum of all `stratum` to `R⟦Γ⟧`.
If `ArchimedeanClass M` is finite, the direct sum is the entire `M` and we are done
(though we don't handle this case separately). Otherwise, we will extend the map to `M` in the
following steps.
-/

open FiniteArchimedeanClass DirectSum HahnSeries

variable {K : Type*} [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable {M : Type*} [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]
variable [Module K M] [IsOrderedModule K M]
variable {R : Type*} [AddCommGroup R] [LinearOrder R]
variable [Module K R]

namespace HahnEmbedding

variable (K M) in
/--
Definition of `ArchimedeanStrata` / `ArchimedeanStrata` 的定义

English:
structure ArchimedeanStrata
  parameters: where
  axioms and operations (3):
    - stratum : FiniteArchimedeanClass M -> Submodule K M
    - disjoint_ball_stratum((c : FiniteArchimedeanClass M)) : Disjoint (ball K c) (stratum c)
    - ball_sup_stratum_eq((c : FiniteArchimedeanClass M)) : ball K c ⊔ stratum c = closedBall K c

中文:
结构 ArchimedeanStrata
  参数: where
  公理与运算 (3 个):
    - stratum : FiniteArchimedeanClass M -> Submodule K M
    - disjoint_ball_stratum((c : FiniteArchimedeanClass M)) : Disjoint (ball K c) (stratum c)
    - ball_sup_stratum_eq((c : FiniteArchimedeanClass M)) : ball K c ⊔ stratum c = closedBall K c
-/
structure ArchimedeanStrata where
  /-- For each `FiniteArchimedeanClass`, specify a corresponding submodule. -/
  stratum : FiniteArchimedeanClass M -> Submodule K M
  /-- `stratum` and `FiniteArchimedeanClass.ball` are disjoint. -/
  disjoint_ball_stratum (c : FiniteArchimedeanClass M) : Disjoint (ball K c) (stratum c)
  /-- `stratum` and `FiniteArchimedeanClass.ball`
    are codisjoint under `FiniteArchimedeanClass.closedBall`. -/
  ball_sup_stratum_eq (c : FiniteArchimedeanClass M) : ball K c ⊔ stratum c = closedBall K c

namespace ArchimedeanStrata
variable (u : ArchimedeanStrata K M) {c : FiniteArchimedeanClass M}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nonempty (ArchimedeanStrata K M)
  body: by
  have hstratum (c : FiniteArchimedeanClass M) :
      exists G : Submodule K M, Disjoint (ball K c) G ∧ ball K c ⊔ G = closedBall K c :=
    IsModularLattice.exists_disjoint_and_sup_eq (ball_lt_closedBall _).le
  choose g h1 h2 using hstratum
  exact ⟨g, h1, h2⟩

中文:
实例 :
  签名: Nonempty (ArchimedeanStrata K M)
  定义体: by
  have hstratum (c : FiniteArchimedeanClass M) :
      exists G : Submodule K M, Disjoint (ball K c) G ∧ ball K c ⊔ G = closedBall K c :=
    IsModularLattice.exists_disjoint_and_sup_eq (ball_lt_closedBall _).le
  choose g h1 h2 using hstratum
  exact ⟨g, h1, h2⟩

Depends on / 依赖: Disjoint, FiniteArchimedeanClass, IsModularLattice, IsModularLattice.exists_disjoint_and_sup_eq, Submodule, ball_lt_closedBall, closedBall, exists_disjoint_and_sup_eq, hstratum
-/
instance : Nonempty (ArchimedeanStrata K M) := by
  have hstratum (c : FiniteArchimedeanClass M) :
      exists G : Submodule K M, Disjoint (ball K c) G ∧ ball K c ⊔ G = closedBall K c :=
    IsModularLattice.exists_disjoint_and_sup_eq (ball_lt_closedBall _).le
  choose g h1 h2 using hstratum
  exact ⟨g, h1, h2⟩

/--
theorem `stratum_ne_bot` / 定理 `stratum_ne_bot`

English:
theorem stratum_ne_bot
  statement: u.stratum c != ⊥
  proof: fun eq => (eq ▸ u.ball_sup_stratum_eq c).not_lt by simpa using ball_lt_closedBall _

中文:
定理 stratum_ne_bot
  结论: u.stratum c != ⊥
  证明: fun eq => (eq ▸ u.ball_sup_stratum_eq c).not_lt by simpa using ball_lt_closedBall _

Depends on / 依赖: ball_lt_closedBall, ball_sup_stratum_eq, not_lt, u.ball_sup_stratum_eq
-/
theorem stratum_ne_bot : u.stratum c != ⊥ :=
fun eq => (eq ▸ u.ball_sup_stratum_eq c).not_lt by simpa using ball_lt_closedBall _

/--
Instance `nontrivial_stratum` / 实例 `nontrivial_stratum`

English:
instance nontrivial_stratum
  signature: : Nontrivial (u.stratum c)
  body: (Submodule.nontrivial_iff_ne_bot).mpr (stratum_ne_bot _)

中文:
实例 nontrivial_stratum
  签名: : Nontrivial (u.stratum c)
  定义体: (Submodule.nontrivial_iff_ne_bot).mpr (stratum_ne_bot _)

Depends on / 依赖: Submodule, Submodule.nontrivial_iff_ne_bot, nontrivial_iff_ne_bot, stratum_ne_bot
-/
instance nontrivial_stratum : Nontrivial (u.stratum c) :=
  (Submodule.nontrivial_iff_ne_bot).mpr (stratum_ne_bot _)

/--
theorem `archimedeanClassMk_of_mem_stratum` / 定理 `archimedeanClassMk_of_mem_stratum`

English:
theorem archimedeanClassMk_of_mem_stratum
  statement: {a : M}
  proof: by
  apply le_antisymm
  · contrapose! h0 with hlt
    have ha' : a in ball K c := (mem_ball_iff K).mpr fun _ => hlt
    exact (Submodule.disjoint_def.mp (u.disjoint_ball_stratum _)) _ ha' ha
  · apply (mem_closedBall_iff K).mp _ h0
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_righ

中文:
定理 archimedeanClassMk_of_mem_stratum
  结论: {a : M}
  证明: by
  apply le_antisymm
  · contrapose! h0 with hlt
    have ha' : a in ball K c := (mem_ball_iff K).mpr fun _ => hlt
    exact (Submodule.disjoint_def.mp (u.disjoint_ball_stratum _)) _ ha' ha
  · apply (mem_closedBall_iff K).mp _ h0
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_righ

Depends on / 依赖: Submodule, Submodule.disjoint_def.mp, Submodule.mem_sup_right, ball_sup_stratum_eq, contrapose, disjoint_ball_stratum, disjoint_def, le_antisymm, mem_ball_iff, mem_closedBall_iff, mem_sup_right, u.ball_sup_stratum_eq, u.disjoint_ball_stratum
-/
theorem archimedeanClassMk_of_mem_stratum {a : M}
    (ha : a in u.stratum c) (h0 : a != 0) : ArchimedeanClass.mk a = c := by
  apply le_antisymm
  · contrapose! h0 with hlt
    have ha' : a in ball K c := (mem_ball_iff K).mpr fun _ => hlt
    exact (Submodule.disjoint_def.mp (u.disjoint_ball_stratum _)) _ ha' ha
  · apply (mem_closedBall_iff K).mp _ h0
    rw [← u.ball_sup_stratum_eq c]
    exact Submodule.mem_sup_right ha

/--
Instance `archimedean_stratum` / 实例 `archimedean_stratum`

English:
instance archimedean_stratum
  signature: : Archimedean (u.stratum c)
  body: by
  apply ArchimedeanClass.archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [ArchimedeanClass.mk_eq_mk] at this ⊢
    exact this
  rw [u.archimedeanClassMk_of_mem_stratum a.prop (by simpa using ha)]
  rw [u.archimedeanClassMk_of_me

中文:
实例 archimedean_stratum
  签名: : Archimedean (u.stratum c)
  定义体: by
  apply ArchimedeanClass.archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [ArchimedeanClass.mk_eq_mk] at this ⊢
    exact this
  rw [u.archimedeanClassMk_of_mem_stratum a.prop (by simpa using ha)]
  rw [u.archimedeanClassMk_of_me

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.archimedean_of_mk_eq_mk, ArchimedeanClass.mk, ArchimedeanClass.mk_eq_mk, a.prop, a.val, archimedeanClassMk_of_mem_stratum, archimedean_of_mk_eq_mk, b.prop, b.val, mk_eq_mk, u.archimedeanClassMk_of_mem_stratum
-/
instance archimedean_stratum : Archimedean (u.stratum c) := by
  apply ArchimedeanClass.archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [ArchimedeanClass.mk_eq_mk] at this ⊢
    exact this
  rw [u.archimedeanClassMk_of_mem_stratum a.prop (by simpa using ha)]
  rw [u.archimedeanClassMk_of_mem_stratum b.prop (by simpa using hb)]

/--
theorem `iSupIndep_stratum` / 定理 `iSupIndep_stratum`

English:
theorem iSupIndep_stratum
  statement: iSupIndep u.stratum
  proof: by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congr(ArchimedeanClass.mk $hf)
  contrapose! hf' with h0
  rw [← hab]; rw [DFinsupp.sum]
  by_cases! hnonempty : f.support.Nonempty
  · have hmem 

中文:
定理 iSupIndep_stratum
  结论: iSupIndep u.stratum
  证明: by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congr(ArchimedeanClass.mk $hf)
  contrapose! hf' with h0
  rw [← hab]; rw [DFinsupp.sum]
  by_cases! hnonempty : f.support.Nonempty
  · have hmem 

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk, DFinsupp, DFinsupp.sum, FiniteArchimedeanClass, Nonempty, Set.mem_of_mem_of_subset, StrictMonoOn, Submodule, Submodule.disjoint_def, Submodule.mem_iSup_iff_exists_dfinsupp, contrapose, disjoint_def, f.support, f.support.Nonempty, hnonempty, mem_iSup_iff_exists_dfinsupp, mem_of_mem_of_subset, stratum, support
-/
theorem iSupIndep_stratum : iSupIndep u.stratum := by
  intro c
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congr(ArchimedeanClass.mk $hf)
  contrapose! hf' with h0
  rw [← hab]; rw [DFinsupp.sum]
  by_cases! hnonempty : f.support.Nonempty
  · have hmem (x : FiniteArchimedeanClass M) : (f x).val in u.stratum x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i => ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      change ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [u.archimedeanClassMk_of_mem_stratum (hmem x) (by simpa using hx)]
      rw [u.archimedeanClassMk_of_mem_stratum (hmem y) (by simpa using hy)]
      exact hxy
    rw [ArchimedeanClass.mk_sum hnonempty hmono]; rw [u.archimedeanClassMk_of_mem_stratum (hmem _)
      (by simpa using f.support.min'_mem hnonempty)]; rw [← val_mk h0]; rw [Subtype.coe_ne_coe]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    have := u.archimedeanClassMk_of_mem_stratum ha h0
    rw [← val_mk h0]; rw [← Subtype.ext_iff] at this
    simpa [DFinsupp.notMem_support_iff, this] using (f c).prop
  · rw [hnonempty]
    symm
    simpa using h0

/--
Definition of `baseDomain` / `baseDomain` 的定义

English:
definition baseDomain
  body: ⨆ c, u.stratum c

中文:
定义 baseDomain
  定义体: ⨆ c, u.stratum c

Depends on / 依赖: stratum, u.stratum
-/
def baseDomain := ⨆ c, u.stratum c

/--
Definition of `stratum'` / `stratum'` 的定义

English:
abbreviation stratum'
  signature: (c : FiniteArchimedeanClass M)
  body: (u.stratum c).comap u.baseDomain.subtype

中文:
缩写 stratum'
  签名: (c : FiniteArchimedeanClass M)
  定义体: (u.stratum c).comap u.baseDomain.subtype

Depends on / 依赖: baseDomain, stratum, subtype, u.baseDomain.subtype, u.stratum
-/
abbrev stratum' (c : FiniteArchimedeanClass M) : Submodule K (baseDomain u) :=
  (u.stratum c).comap u.baseDomain.subtype

/--
theorem `iSupIndep_stratum'` / 定理 `iSupIndep_stratum'`

English:
theorem iSupIndep_stratum'
  statement: iSupIndep u.stratum'
  proof: by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert! u.iSupIndep_stratum
  ext1 c
  simpa using! le_iSup _ _

中文:
定理 iSupIndep_stratum'
  结论: iSupIndep u.stratum'
  证明: by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert! u.iSupIndep_stratum
  ext1 c
  simpa using! le_iSup _ _

Depends on / 依赖: Submodule, Submodule.mapIic, baseDomain, convert, iSupIndep, iSupIndep.of_coe_Iic_comp, iSupIndep_map_orderIso_iff, iSupIndep_stratum, le_iSup, mapIic, of_coe_Iic_comp, u.baseDomain, u.iSupIndep_stratum
-/
theorem iSupIndep_stratum' : iSupIndep u.stratum' := by
  apply (iSupIndep_map_orderIso_iff (Submodule.mapIic u.baseDomain)).mp
  apply iSupIndep.of_coe_Iic_comp
  convert! u.iSupIndep_stratum
  ext1 c
  simpa using! le_iSup _ _

/--
theorem `isInternal_stratum'` / 定理 `isInternal_stratum'`

English:
theorem isInternal_stratum'
  statement: DirectSum.IsInternal u.stratum'
  proof: by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top u.iSupIndep_stratum'
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using! this
  apply iSup_congr
  intro c
  simpa using! le_iSup _ 

中文:
定理 isInternal_stratum'
  结论: DirectSum.Is整数ernal u.stratum'
  证明: by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top u.iSupIndep_stratum'
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using! this
  apply iSup_congr
  intro c
  simpa using! le_iSup _ 

Depends on / 依赖: DirectSum, DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top, Submodule, Submodule.map_injective_of_injective, baseDomain, iSupIndep_stratum, iSup_congr, isInternal_submodule_of_iSupIndep_of_iSup_eq_top, le_iSup, map_injective_of_injective, stratum, subtype_injective, u.baseDomain, u.baseDomain.subtype_injective, u.iSupIndep_stratum, u.stratum
-/
theorem isInternal_stratum' : DirectSum.IsInternal u.stratum' := by
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top u.iSupIndep_stratum'
  apply Submodule.map_injective_of_injective u.baseDomain.subtype_injective
  suffices ⨆ i, u.baseDomain ⊓ u.stratum i = u.baseDomain by simpa using! this
  apply iSup_congr
  intro c
  simpa using! le_iSup _ _

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DirectSum.Decomposition u.stratum'
  body: (u.isInternal_stratum').chooseDecomposition _

中文:
实例 :
  签名: DirectSum.Decomposition u.stratum'
  定义体: (u.isInternal_stratum').chooseDecomposition _

Depends on / 依赖: chooseDecomposition, isInternal_stratum, u.isInternal_stratum
-/
instance : DirectSum.Decomposition u.stratum' := (u.isInternal_stratum').chooseDecomposition _

end ArchimedeanStrata

variable (K M R) in
/--
Definition of `Seed` / `Seed` 的定义

English:
structure Seed
  parameters: extends ArchimedeanStrata K M
  extends: ArchimedeanStrata K M
  axioms and operations (2):
    - coeff((c : FiniteArchimedeanClass M)) : stratum c ->ₗ[K] R
    - strictMono_coeff((c : FiniteArchimedeanClass M)) : StrictMono (coeff c)

中文:
结构 Seed
  参数: extends ArchimedeanStrata K M
  继承: ArchimedeanStrata K M
  公理与运算 (2 个):
    - coeff((c : FiniteArchimedeanClass M)) : stratum c ->ₗ[K] R
    - strictMono_coeff((c : FiniteArchimedeanClass M)) : StrictMono (coeff c)
-/
structure Seed extends ArchimedeanStrata K M where
  /-- For each stratum, specify a linear map to `R` as the Hahn series coefficient. -/
  coeff (c : FiniteArchimedeanClass M) : stratum c ->ₗ[K] R
  /-- `coeff` is strictly monotone. -/
  strictMono_coeff (c : FiniteArchimedeanClass M) : StrictMono (coeff c)

variable (seed : Seed K M R)

namespace Seed

/--
Definition of `coeff'` / `coeff'` 的定义

English:
definition coeff'
  signature: (c : FiniteArchimedeanClass M)
  body: (seed.coeff c).comp (LinearMap.submoduleComap _ _)

中文:
定义 coeff'
  签名: (c : FiniteArchimedeanClass M)
  定义体: (seed.coeff c).comp (LinearMap.submoduleComap _ _)

Depends on / 依赖: LinearMap, LinearMap.submoduleComap, seed.coeff, submoduleComap
-/
def coeff' (c : FiniteArchimedeanClass M) : seed.stratum' c ->ₗ[K] R :=
  (seed.coeff c).comp (LinearMap.submoduleComap _ _)

/-- Coefficients of Hahn series for each `baseDomain` element. -/
noncomputable
/--
Definition of `hahnCoeff` / `hahnCoeff` 的定义

English:
definition hahnCoeff
  signature: : seed.baseDomain ->ₗ[K] (⨁ _ : FiniteArchimedeanClass M, R)
  body: (DirectSum.lmap seed.coeff') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap

中文:
定义 hahnCoeff
  签名: : seed.baseDomain ->ₗ[K] (⨁ _ : FiniteArchimedeanClass M, R)
  定义体: (DirectSum.lmap seed.coeff') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap

Depends on / 依赖: DirectSum, DirectSum.decomposeLinearEquiv, DirectSum.lmap, decomposeLinearEquiv, seed.coeff, toLinearMap
-/
def hahnCoeff : seed.baseDomain ->ₗ[K] (⨁ _ : FiniteArchimedeanClass M, R) :=
  (DirectSum.lmap seed.coeff') ∘ₗ (DirectSum.decomposeLinearEquiv _).toLinearMap

/--
theorem `hahnCoeff_apply` / 定理 `hahnCoeff_apply`

English:
theorem hahnCoeff_apply
  statement: {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
  proof: by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [Seed.hahnCoeff, coeff', decomposeLinearEquiv_apply, this]
  have hxm {c : FiniteArchimedeanClass M} (x : seed.stratum c) : x.val in seed.baseDomain := by
    apply S

中文:
定理 hahnCoeff_apply
  结论: {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
  证明: by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [Seed.hahnCoeff, coeff', decomposeLinearEquiv_apply, this]
  have hxm {c : FiniteArchimedeanClass M} (x : seed.stratum c) : x.val in seed.baseDomain := by
    apply S

Depends on / 依赖: DirectSum, DirectSum.decompose, FiniteArchimedeanClass, Seed.hahnCoeff, Set.mem_of_mem_of_subset, baseDomain, decompose, decomposeLinearEquiv_apply, f.mapRange, hahnCoeff, le_iSup, mapRange, mem_of_mem_of_subset, seed.baseDomain, seed.baseDomain.subtype.submodul, seed.baseDomain.subtype.submoduleComap, seed.stratum, stratum, submodul, submoduleComap
-/
theorem hahnCoeff_apply {x : seed.baseDomain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c => (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    seed.hahnCoeff x c = seed.coeff c (f c) := by
  suffices seed.baseDomain.subtype.submoduleComap
      (seed.stratum c) (DirectSum.decompose seed.stratum' x c) = f c by
    simp [Seed.hahnCoeff, coeff', decomposeLinearEquiv_apply, this]
  have hxm {c : FiniteArchimedeanClass M} (x : seed.stratum c) : x.val in seed.baseDomain := by
    apply Set.mem_of_mem_of_subset x.prop
    simpa using! le_iSup _ _
  let f' : ⨁ c, seed.stratum' c :=
    f.mapRange (fun c x => (⟨⟨x.val, hxm x⟩, by simp⟩ : seed.stratum' c)) (by simp)
  have hf : f c = (seed.baseDomain.subtype.submoduleComap (seed.stratum c)) (f' c) := by
    set_option backward.isDefEq.respectTransparency false in
    apply Subtype.ext
    simp [f']
  have hx : x = (decompose seed.stratum').symm f' := by
    change x = f'.coeAddMonoidHom _
    apply Submodule.subtype_injective
    rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]; rw [DFinsupp.sum_mapRange_index (by simp)]
    simp [h]
  simp [hf, hx]

/-- Combining all `HahnEmbedding.Seed.coeff` as
a partial linear map from `HahnEmbedding.Seed.baseDomain` to `HahnSeries`. -/
noncomputable
/--
Definition of `baseEmbedding` / `baseEmbedding` 的定义

English:
definition baseEmbedding
  signature: : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ where
  body: seed.baseDomain
  toFun := (toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff

中文:
定义 baseEmbedding
  签名: : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ where
  定义体: seed.baseDomain
  toFun := (toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff

Depends on / 依赖: baseDomain, seed.baseDomain
-/
def baseEmbedding : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ where
  domain := seed.baseDomain
  toFun := (toLexLinearEquiv _ _).toLinearMap ∘ₗ (HahnSeries.ofFinsuppLinearMap _) ∘ₗ
    (finsuppLequivDFinsupp K).symm.toLinearMap ∘ₗ seed.hahnCoeff

/--
theorem `domain_baseEmbedding` / 定理 `domain_baseEmbedding`

English:
theorem domain_baseEmbedding
  statement: seed.baseEmbedding.domain = seed.baseDomain
  proof: rfl

中文:
定理 domain_baseEmbedding
  结论: seed.baseEmbedding.domain = seed.baseDomain
  证明: rfl
-/
theorem domain_baseEmbedding : seed.baseEmbedding.domain = seed.baseDomain := rfl

/--
theorem `coeff_baseEmbedding` / 定理 `coeff_baseEmbedding`

English:
theorem coeff_baseEmbedding
  statement: {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
  proof: by
  simpa [baseEmbedding] using! seed.hahnCoeff_apply h c

中文:
定理 coeff_baseEmbedding
  结论: {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
  证明: by
  simpa [baseEmbedding] using! seed.hahnCoeff_apply h c

Depends on / 依赖: baseEmbedding, hahnCoeff_apply, seed.hahnCoeff_apply
-/
theorem coeff_baseEmbedding {x : seed.baseEmbedding.domain} {f : Π₀ c, seed.stratum c}
    (h : x.val = f.sum fun c => (seed.stratum c).subtype) (c : FiniteArchimedeanClass M) :
    (ofLex ((baseEmbedding seed) x)).coeff c = seed.coeff c (f c) := by
  simpa [baseEmbedding] using! seed.hahnCoeff_apply h c

/--
theorem `mem_domain_baseEmbedding` / 定理 `mem_domain_baseEmbedding`

English:
theorem mem_domain_baseEmbedding
  given: {x : M} {c : FiniteArchimedeanClass M} (h : x in seed.stratum c)
  proof: by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseEmbedding]
  simpa using! le_iSup_iff.mpr fun _ h => h c

中文:
定理 mem_domain_baseEmbedding
  条件: {x : M} {c : FiniteArchimedeanClass M} (h : x in seed.stratum c)
  证明: by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseEmbedding]
  simpa using! le_iSup_iff.mpr fun _ h => h c

Depends on / 依赖: Set.mem_of_mem_of_subset, domain_baseEmbedding, le_iSup_iff, le_iSup_iff.mpr, mem_of_mem_of_subset
-/
theorem mem_domain_baseEmbedding {x : M} {c : FiniteArchimedeanClass M} (h : x in seed.stratum c) :
    x in seed.baseEmbedding.domain := by
  apply Set.mem_of_mem_of_subset h
  rw [domain_baseEmbedding]
  simpa using! le_iSup_iff.mpr fun _ h => h c

end Seed

/-! ### Step 2: characterize partial embedding

We characterize the base embedding as a member of a class of partial linear embeddings
`HahnEmbedding.Partial`. These embeddings share nice properties, including being strictly monotone,
transferring `ArchimedeanClass` to `HahnEmbedding.orderTop`, and being "truncation-closed"
(see `HahnEmbedding.IsPartial.truncLT_mem_range`).
-/

/--
Definition of `IsPartial` / `IsPartial` 的定义

English:
structure IsPartial
  parameters: (f : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧)
  extends: `baseEmbedding`. -/
  axioms and operations (3):
    - strictMono : StrictMono f
    - baseEmbedding_le : seed.baseEmbedding <= f
    - truncLT_mem_range : forall x, forall c, toLex (HahnSeries.truncLTLinearMap K c (ofLex (f x))) in LinearMap.range f.toFun

中文:
结构 IsPartial
  参数: (f : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧)
  继承: `baseEmbedding`. -/
  公理与运算 (3 个):
    - strictMono : StrictMono f
    - baseEmbedding_le : seed.baseEmbedding <= f
    - truncLT_mem_range : 对任意 x, 对任意 c, toLex (HahnSeries.truncLTLinearMap K c (ofLex (f x))) in LinearMap.range f.toFun
-/
structure IsPartial (f : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧) : Prop where
  /-- A partial Hahn embedding is strictly monotone. -/
  strictMono : StrictMono f
  /-- A partial Hahn embedding always extends `baseEmbedding`. -/
  baseEmbedding_le : seed.baseEmbedding <= f
  /-- If a Hahn series $f$ is in the range, then any truncation of $f$ is also in the range. -/
  truncLT_mem_range : forall x, forall c,
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f x))) in LinearMap.range f.toFun

namespace Seed

/--
theorem `baseEmbedding_pos` / 定理 `baseEmbedding_pos`

English:
theorem baseEmbedding_pos
  given: {x : seed.baseEmbedding.domain} (hx : 0 < x)
  proof: by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val in seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x => x.val) := by
    rw [hf]
    simpa using! 

中文:
定理 baseEmbedding_pos
  条件: {x : seed.baseEmbedding.domain} (hx : 0 < x)
  证明: by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val in seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x => x.val) := by
    rw [hf]
    simpa using! 
-/
theorem baseEmbedding_pos {x : seed.baseEmbedding.domain} (hx : 0 < x) :
    0 < seed.baseEmbedding x := by
  -- decompose `x` to sum of `stratum`
  have hmem : x.val in seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  have hfpos : 0 < (f.sum fun _ x => x.val) := by
    rw [hf]
    simpa using! hx
  have hsupport : f.support.Nonempty := by
    obtain hne := hfpos.ne.symm
    contrapose! hne with hempty
    apply DFinsupp.sum_eq_zero
    intro c
    simpa using! DFinsupp.notMem_support_iff.mp (Finset.eq_empty_iff_forall_notMem.mp hempty c)
  -- The dictating term for `HahnSeries` < is at the lowest archimedean class of `f.support`
  refine (HahnSeries.lt_iff _ _).mpr ⟨f.support.min' hsupport, ?_, ?_⟩
  · intro j hj
    rw [seed.coeff_baseEmbedding hf.symm]
    rw [DFinsupp.notMem_support_iff.mp ?_]
    · simp
    contrapose! hj
    rw [← Subtype.coe_le_coe]; rw [Subtype.coe_mk]
    exact Finset.min'_le f.support _ hj
  -- Show that `f`'s value at dominating archimedean class is positive
  rw [seed.coeff_baseEmbedding hf.symm]
  suffices (seed.coeff (f.support.min' hsupport)) 0 <
      (seed.coeff (f.support.min' hsupport)) (f (f.support.min' hsupport)) by
    simpa using! this
  suffices 0 < (f (f.support.min' hsupport)).val by
    apply (seed.strictMono_coeff (f.support.min' hsupport))
    simpa using! this
  -- using the fact that `f.sum` is positive, we only needs to show that
  -- the remaining terms of f after removing the dominating class is of higher class
  apply ArchimedeanClass.pos_of_pos_of_mk_lt hfpos
  rw [ArchimedeanClass.mk_sub_comm]
  have hferase : (f.sum fun _ x => x.val) - (f (f.support.min' hsupport)).val =
      ∑ x in f.support.erase (f.support.min' hsupport), (f x).val :=
    sub_eq_of_eq_add (Finset.sum_erase_add _ _ (Finset.min'_mem _ hsupport)).symm
  rw [hferase]
  -- Now both sides are `mk (∑ ...)`
  -- We rewrite them to `mk (dominating term)`
  have hmono : StrictMonoOn (fun x => ArchimedeanClass.mk (f x).val) f.support := by
    intro c hc d hd h
    simp only
    rw [seed.archimedeanClassMk_of_mem_stratum (f c).prop (by simpa using! hc)]
    rw [seed.archimedeanClassMk_of_mem_stratum (f d).prop (by simpa using! hd)]
    exact h
  rw [DFinsupp.sum]; rw [ArchimedeanClass.mk_sum hsupport hmono]
  rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop
    (by simpa using! f.support.min'_mem hsupport)]
  by_cases! hsupport' : (f.support.erase (f.support.min' hsupport)).Nonempty
  · rw [ArchimedeanClass.mk_sum hsupport' (hmono.mono (by simp))]
    rw [seed.archimedeanClassMk_of_mem_stratum (f _).prop (by
      simpa using! (Finset.mem_erase.mp <| (f.support.erase _).min'_mem hsupport').2)]
    apply Finset.min'_lt_of_mem_erase_min' (α := FiniteArchimedeanClass M)
    apply Finset.min'_mem _ _
  · -- special case: `f` has a single term, and becomes 0 after removing it
    simpa [hsupport'] using! (f.support.min' hsupport).2.lt_top

/--
theorem `baseEmbedding_strictMono` / 定理 `baseEmbedding_strictMono`

English:
theorem baseEmbedding_strictMono
  given: [IsOrderedAddMonoid R]
  statement: StrictMono seed.baseEmbedding
  proof: by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
exact baseEmbedding_pos _ by simpa using h

中文:
定理 baseEmbedding_strictMono
  条件: [IsOrderedAddMonoid R]
  结论: StrictMono seed.baseEmbedding
  证明: by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
exact baseEmbedding_pos _ by simpa using h

Depends on / 依赖: LinearPMap, LinearPMap.map_sub, baseEmbedding_pos, lt_of_sub_pos, map_sub
-/
theorem baseEmbedding_strictMono [IsOrderedAddMonoid R] : StrictMono seed.baseEmbedding := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
exact baseEmbedding_pos _ by simpa using h

/--
theorem `truncLT_mem_range_baseEmbedding` / 定理 `truncLT_mem_range_baseEmbedding`

English:
theorem truncLT_mem_range_baseEmbedding
  statement: (x : seed.baseEmbedding.domain)
  proof: by
  -- decompose `x` to `stratum`
  have hmem : x.val in seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f'

中文:
定理 truncLT_mem_range_baseEmbedding
  结论: (x : seed.baseEmbedding.domain)
  证明: by
  -- decompose `x` to `stratum`
  have hmem : x.val in seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f'
-/
theorem truncLT_mem_range_baseEmbedding (x : seed.baseEmbedding.domain)
    (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (seed.baseEmbedding x))) in
    LinearMap.range seed.baseEmbedding.toFun := by
  -- decompose `x` to `stratum`
  have hmem : x.val in seed.baseEmbedding.domain := x.prop
  simp_rw [seed.domain_baseEmbedding] at hmem
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ _).mp hmem
  -- Truncating in the codomain is the same as truncating away some submodule
  let f' : Π₀ (i : FiniteArchimedeanClass M), seed.stratum i :=
    DFinsupp.mk f.support fun d => if c.val <= d.val then 0 else f d.val
  refine ⟨⟨f'.sum fun d x => x.val, ?_⟩, ?_⟩
  · rw [seed.domain_baseEmbedding, ArchimedeanStrata.baseDomain,
      Submodule.mem_iSup_iff_exists_dfinsupp']
    use f'
  apply_fun ofLex
  rw [ofLex_toLex]; rw [LinearPMap.toFun_eq_coe]
  ext d
  rw [seed.coeff_baseEmbedding rfl]
  unfold f'
  obtain hdc | hdc := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc,
      seed.coeff_baseEmbedding hf.symm]
    apply congrArg
    have hcd : ¬ c.val <= d.val := not_le_of_gt hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    aesop
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
    have hcd : c.val <= d.val := hdc
    simp only [DFinsupp.mk_apply, hcd, ↓reduceIte]
    convert! LinearMap.map_zero _
    simp

/--
theorem `isPartial_baseEmbedding` / 定理 `isPartial_baseEmbedding`

English:
theorem isPartial_baseEmbedding
  given: [IsOrderedAddMonoid R]
  statement: IsPartial seed seed.baseEmbedding where
  proof: seed.baseEmbedding_strictMono
  baseEmbedding_le := le_refl _
  truncLT_mem_range := seed.truncLT_mem_range_baseEmbedding

中文:
定理 isPartial_baseEmbedding
  条件: [IsOrderedAddMonoid R]
  结论: IsPartial seed seed.baseEmbedding where
  证明: seed.baseEmbedding_strictMono
  baseEmbedding_le := le_refl _
  truncLT_mem_range := seed.truncLT_mem_range_baseEmbedding

Depends on / 依赖: baseEmbedding_strictMono, seed.baseEmbedding_strictMono
-/
theorem isPartial_baseEmbedding [IsOrderedAddMonoid R] : IsPartial seed seed.baseEmbedding where
  strictMono := seed.baseEmbedding_strictMono
  baseEmbedding_le := le_refl _
  truncLT_mem_range := seed.truncLT_mem_range_baseEmbedding

end Seed

/--
Definition of `Partial` / `Partial` 的定义

English:
abbreviation Partial
  body: {f : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ // IsPartial seed f}

中文:
缩写 Partial
  定义体: {f : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ // IsPartial seed f}

Depends on / 依赖: FiniteArchimedeanClass, IsPartial
-/
abbrev Partial := {f : M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ // IsPartial seed f}

namespace Partial
variable {seed} (f : Partial seed)

noncomputable
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsOrderedAddMonoid
  signature: R] : Inhabited (Partial seed) where
  body: ⟨seed.baseEmbedding, seed.isPartial_baseEmbedding⟩

中文:
实例 [IsOrderedAddMonoid
  签名: R] : Inhabited (Partial seed) where
  定义体: ⟨seed.baseEmbedding, seed.isPartial_baseEmbedding⟩

Depends on / 依赖: baseEmbedding, isPartial_baseEmbedding, seed.baseEmbedding, seed.isPartial_baseEmbedding
-/
instance [IsOrderedAddMonoid R] : Inhabited (Partial seed) where
  default := ⟨seed.baseEmbedding, seed.isPartial_baseEmbedding⟩

/--
Definition of `toOrderAddMonoidHom` / `toOrderAddMonoidHom` 的定义

English:
definition toOrderAddMonoidHom
  signature: : f.val.domain ->+o Lex R⟦FiniteArchimedeanClass M⟧ where
  body: f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone

中文:
定义 toOrderAddMonoidHom
  签名: : f.val.domain ->+o Lex R⟦FiniteArchimedeanClass M⟧ where
  定义体: f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone

Depends on / 依赖: f.val.toFun
-/
noncomputable def toOrderAddMonoidHom : f.val.domain ->+o Lex R⟦FiniteArchimedeanClass M⟧ where
  __ := f.val.toFun
  map_zero' := by simp
  monotone' := f.prop.strictMono.monotone

/--
theorem `toOrderAddMonoidHom_apply` / 定理 `toOrderAddMonoidHom_apply`

English:
theorem toOrderAddMonoidHom_apply
  given: (x : f.val.domain)
  statement: f.toOrderAddMonoidHom x = f.val x
  proof: rfl

中文:
定理 toOrderAddMonoidHom_apply
  条件: (x : f.val.domain)
  结论: f.toOrderAddMonoidHom x = f.val x
  证明: rfl
-/
theorem toOrderAddMonoidHom_apply (x : f.val.domain) : f.toOrderAddMonoidHom x = f.val x := rfl

/--
theorem `toOrderAddMonoidHom_injective` / 定理 `toOrderAddMonoidHom_injective`

English:
theorem toOrderAddMonoidHom_injective
  statement: Function.Injective f.toOrderAddMonoidHom
  proof: f.prop.strictMono.injective

中文:
定理 toOrderAddMonoidHom_injective
  结论: Function.Injective f.toOrderAddMonoidHom
  证明: f.prop.strictMono.injective

Depends on / 依赖: f.prop.strictMono.injective, injective, strictMono
-/
theorem toOrderAddMonoidHom_injective : Function.Injective f.toOrderAddMonoidHom :=
  f.prop.strictMono.injective

/--
theorem `mem_domain` / 定理 `mem_domain`

English:
theorem mem_domain
  given: {x : M} {c : FiniteArchimedeanClass M} (hx : x in seed.stratum c)
  proof: by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply seed.mem_domain_baseEmbedding hx

中文:
定理 mem_domain
  条件: {x : M} {c : FiniteArchimedeanClass M} (hx : x in seed.stratum c)
  证明: by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply seed.mem_domain_baseEmbedding hx

Depends on / 依赖: Set.mem_of_subset_of_mem, baseEmbedding_le, f.prop.baseEmbedding_le, mem_domain_baseEmbedding, mem_of_subset_of_mem, seed.mem_domain_baseEmbedding
-/
theorem mem_domain {x : M} {c : FiniteArchimedeanClass M} (hx : x in seed.stratum c) :
    x in f.val.domain := by
  apply Set.mem_of_subset_of_mem f.prop.baseEmbedding_le.1
  apply seed.mem_domain_baseEmbedding hx

/--
theorem `apply_of_mem_stratum` / 定理 `apply_of_mem_stratum`

English:
theorem apply_of_mem_stratum
  statement: {x : f.val.domain} {c : FiniteArchimedeanClass M}
  proof: by
  have hx' : x.val in seed.baseEmbedding.domain := seed.mem_domain_baseEmbedding hx
  have heq : (⟨x.val, hx'⟩ : seed.baseEmbedding.domain).val = x.val := rfl
  rw [← f.prop.baseEmbedding_le.2 heq]
  let fx : Π₀ c, seed.stratum c := DFinsupp.single c ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun c 

中文:
定理 apply_of_mem_stratum
  结论: {x : f.val.domain} {c : FiniteArchimedeanClass M}
  证明: by
  have hx' : x.val in seed.baseEmbedding.domain := seed.mem_domain_baseEmbedding hx
  have heq : (⟨x.val, hx'⟩ : seed.baseEmbedding.domain).val = x.val := rfl
  rw [← f.prop.baseEmbedding_le.2 heq]
  let fx : Π₀ c, seed.stratum c := DFinsupp.single c ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun c 

Depends on / 依赖: DFinsupp, DFinsupp.single, DFinsupp.sum_single_index, HahnSeries, apply_fun, baseEmbedding, baseEmbedding_le, coeff_baseEmbedding, domain, eq_or_ne, f.prop.baseEmbedding_le, fx.sum, mem_domain_baseEmbedding, ofLex_toLex, seed.baseEmbedding.domain, seed.coeff_baseEmbedding, seed.mem_domain_baseEmbedding, seed.stratum, single, stratum
-/
theorem apply_of_mem_stratum {x : f.val.domain} {c : FiniteArchimedeanClass M}
    (hx : x.val in seed.stratum c) :
    f.val x = toLex (HahnSeries.single c (seed.coeff c ⟨x.val, hx⟩)) := by
  have hx' : x.val in seed.baseEmbedding.domain := seed.mem_domain_baseEmbedding hx
  have heq : (⟨x.val, hx'⟩ : seed.baseEmbedding.domain).val = x.val := rfl
  rw [← f.prop.baseEmbedding_le.2 heq]
  let fx : Π₀ c, seed.stratum c := DFinsupp.single c ⟨x.val, hx⟩
  have hfx : x.val = fx.sum fun c => (seed.stratum c).subtype := by
    simp [fx, DFinsupp.sum_single_index]
  apply_fun ofLex
  rw [ofLex_toLex]
  ext d
  rw [seed.coeff_baseEmbedding hfx]
  unfold fx
  obtain rfl | hdc := eq_or_ne d c
  · simp
  simp [HahnSeries.coeff_single_of_ne hdc, hdc.symm]

open ArchimedeanClass in
/--
theorem `archimedeanClassMk_eq_iff` / 定理 `archimedeanClassMk_eq_iff`

English:
theorem archimedeanClassMk_eq_iff
  given: [IsOrderedAddMonoid R] (x y : f.val.domain)
  proof: by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans ArchimedeanClass.mk x = .mk y
· exact Function.Injective.eq_iff orderHom_injective toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

中文:
定理 archimedeanClassMk_eq_iff
  条件: [IsOrderedAddMonoid R] (x y : f.val.domain)
  证明: by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans ArchimedeanClass.mk x = .mk y
· exact Function.Injective.eq_iff orderHom_injective toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk, Function, Function.Injective.eq_iff, Injective, eq_iff, mk_eq_mk, orderHom_injective, orderHom_mk, simp_rw, toOrderAddMonoidHom_apply, toOrderAddMonoidHom_injective
-/
theorem archimedeanClassMk_eq_iff [IsOrderedAddMonoid R] (x y : f.val.domain) :
    ArchimedeanClass.mk (f.val x) = .mk (f.val y) ↔ ArchimedeanClass.mk x.val = .mk y.val := by
  simp_rw [← toOrderAddMonoidHom_apply, ← orderHom_mk]
  trans ArchimedeanClass.mk x = .mk y
· exact Function.Injective.eq_iff orderHom_injective toOrderAddMonoidHom_injective _
  · simp_rw [mk_eq_mk]
    aesop

/--
theorem `orderTop_eq_iff` / 定理 `orderTop_eq_iff`

English:
theorem orderTop_eq_iff
  given: [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain)
  proof: by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
· have : y = x := Subtype.ext hsubsingleton.allEq _ _
    simp [this]
  have hnonempty : Nonempty (FiniteArchimedeanClass M) := inferInstance
  obtain c := hnonempty.some
  have : Nontrivial R := (seed.strictMono_coeff c).inject

中文:
定理 orderTop_eq_iff
  条件: [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain)
  证明: by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
· have : y = x := Subtype.ext hsubsingleton.allEq _ _
    simp [this]
  have hnonempty : Nonempty (FiniteArchimedeanClass M) := inferInstance
  obtain c := hnonempty.some
  have : Nontrivial R := (seed.strictMono_coeff c).inject

Depends on / 依赖: FiniteArchimedeanClass, HahnSeries, HahnSeries.archimedeanClassOrderIsoWithTop, HahnSeries.archimedeanClassOrderIsoWithTop_apply, Nonempty, Nontrivial, Subtype, Subtype.ext, archimedeanClassMk_eq_iff, archimedeanClassOrderIsoWithTop, archimedeanClassOrderIsoWithTop_apply, eq_iff, hnonempty, hnonempty.some, hnontrivial, hsubsingleton, hsubsingleton.allEq, injective, injective.eq_iff, injective.nontrivial
-/
theorem orderTop_eq_iff [IsOrderedAddMonoid R] [Archimedean R] (x y : f.val.domain) :
    (ofLex (f.val x)).orderTop = (ofLex (f.val y)).orderTop ↔
    ArchimedeanClass.mk x.val = .mk y.val := by
  obtain hsubsingleton | hnontrivial := subsingleton_or_nontrivial M
· have : y = x := Subtype.ext hsubsingleton.allEq _ _
    simp [this]
  have hnonempty : Nonempty (FiniteArchimedeanClass M) := inferInstance
  obtain c := hnonempty.some
  have : Nontrivial R := (seed.strictMono_coeff c).injective.nontrivial
  rw [← archimedeanClassMk_eq_iff]
  simp_rw [← HahnSeries.archimedeanClassOrderIsoWithTop_apply]
  rw [(HahnSeries.archimedeanClassOrderIsoWithTop (FiniteArchimedeanClass M) R).injective.eq_iff]

/--
theorem `orderTop_eq_archimedeanClassMk` / 定理 `orderTop_eq_archimedeanClassMk`

English:
theorem orderTop_eq_archimedeanClassMk
  given: [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain)
  proof: by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val != 0 := by simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (.mk x hx

中文:
定理 orderTop_eq_archimedeanClassMk
  条件: [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain)
  证明: by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val != 0 := by simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (.mk x hx

Depends on / 依赖: x.val
-/
theorem orderTop_eq_archimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R] (x : f.val.domain) :
    FiniteArchimedeanClass.withTopOrderIso M (ofLex (f.val x)).orderTop = .mk x.val := by
  by_cases hx0 : x = 0
  · simp [hx0]
  have hx0' : x.val != 0 := by simpa using hx0
  -- Pick a representative `x'` from `stratum` with the same class as `x`.
  -- `f.val x'` is a `HahnSeries.single` whose `orderTop` is known
  obtain ⟨⟨x', hx'mem⟩, hx'0⟩ := exists_ne (0 : seed.stratum (.mk x hx0'))
  have heq : ArchimedeanClass.mk x' = .mk x.val := by
    apply seed.archimedeanClassMk_of_mem_stratum hx'mem
    simpa using hx'0
  let x'' : f.val.domain := ⟨x', mem_domain f hx'mem⟩
  have hx''mem : x''.val in seed.stratum (mk x.val hx0') := hx'mem
  have h0 : (seed.coeff (mk x.val hx0')) ⟨x''.val, hx''mem⟩ != 0 := by
    rw [(LinearMap.map_eq_zero_iff _ (seed.strictMono_coeff _).injective).ne]
    unfold x''
    simpa using hx'0
  have heq' : ArchimedeanClass.mk x''.val = .mk x.val := heq
  rw [← orderTop_eq_iff]; rw [apply_of_mem_stratum f hx''mem]; rw [ofLex_toLex]; rw [HahnSeries.orderTop_single h0] at heq'
  simp [← heq']

/--
theorem `orderTop_eq_finiteArchimedeanClassMk` / 定理 `orderTop_eq_finiteArchimedeanClassMk`

English:
theorem orderTop_eq_finiteArchimedeanClassMk
  statement: [IsOrderedAddMonoid R] [Archimedean R]
  proof: by
  apply_fun FiniteArchimedeanClass.withTopOrderIso M
  simp [orderTop_eq_archimedeanClassMk]

中文:
定理 orderTop_eq_finiteArchimedeanClassMk
  结论: [IsOrderedAddMonoid R] [Archimedean R]
  证明: by
  apply_fun FiniteArchimedeanClass.withTopOrderIso M
  simp [orderTop_eq_archimedeanClassMk]

Depends on / 依赖: FiniteArchimedeanClass, FiniteArchimedeanClass.withTopOrderIso, apply_fun, orderTop_eq_archimedeanClassMk, withTopOrderIso
-/
theorem orderTop_eq_finiteArchimedeanClassMk [IsOrderedAddMonoid R] [Archimedean R]
    {x : f.val.domain} (hx0 : x.val != 0) :
    (ofLex (f.val x)).orderTop = FiniteArchimedeanClass.mk x.val hx0 := by
  apply_fun FiniteArchimedeanClass.withTopOrderIso M
  simp [orderTop_eq_archimedeanClassMk]

/--
theorem `coeff_eq_zero_of_mem` / 定理 `coeff_eq_zero_of_mem`

English:
theorem coeff_eq_zero_of_mem
  statement: [IsOrderedAddMonoid R] [Archimedean R]
  proof: by
  obtain rfl | ne := eq_or_ne x 0
  · simp
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [orderTop_eq_archimedeanClassMk]; rw [FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa using! hx (by simpa using!

中文:
定理 coeff_eq_zero_of_mem
  结论: [IsOrderedAddMonoid R] [Archimedean R]
  证明: by
  obtain rfl | ne := eq_or_ne x 0
  · simp
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [orderTop_eq_archimedeanClassMk]; rw [FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa using! hx (by simpa using!

Depends on / 依赖: FiniteArchimedeanClass, FiniteArchimedeanClass.withTopOrderIso, FiniteArchimedeanClass.withTopOrderIso_apply_coe, HahnSeries, HahnSeries.coeff_eq_zero_of_lt_orderTop, apply_fun, coeff_eq_zero_of_lt_orderTop, eq_or_ne, lt_of_le_of_lt, orderTop_eq_archimedeanClassMk, withTopOrderIso, withTopOrderIso_apply_coe
-/
theorem coeff_eq_zero_of_mem [IsOrderedAddMonoid R] [Archimedean R]
    {c : FiniteArchimedeanClass M} {x : f.val.domain} (hx : x.val in ball K c)
    {d : FiniteArchimedeanClass M} (hd : d.val <= c) : (ofLex (f.val x)).coeff d = 0 := by
  obtain rfl | ne := eq_or_ne x 0
  · simp
  apply HahnSeries.coeff_eq_zero_of_lt_orderTop
  apply_fun FiniteArchimedeanClass.withTopOrderIso _
  rw [orderTop_eq_archimedeanClassMk]; rw [FiniteArchimedeanClass.withTopOrderIso_apply_coe]
  apply lt_of_le_of_lt hd
  simpa using! hx (by simpa using! ne)

/--
theorem `coeff_ne_zero` / 定理 `coeff_ne_zero`

English:
theorem coeff_ne_zero
  given: [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (hx0 : x.val != 0)
  proof: HahnSeries.coeff_orderTop_ne f.orderTop_eq_finiteArchimedeanClassMk hx0

中文:
定理 coeff_ne_zero
  条件: [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (hx0 : x.val != 0)
  证明: HahnSeries.coeff_orderTop_ne f.orderTop_eq_finiteArchimedeanClassMk hx0

Depends on / 依赖: HahnSeries, HahnSeries.coeff_orderTop_ne, coeff_orderTop_ne, f.orderTop_eq_finiteArchimedeanClassMk, orderTop_eq_finiteArchimedeanClassMk
-/
theorem coeff_ne_zero [IsOrderedAddMonoid R] [Archimedean R] {x : f.val.domain} (hx0 : x.val != 0) :
    (ofLex (f.val x)).coeff (FiniteArchimedeanClass.mk x.val hx0) != 0 :=
HahnSeries.coeff_orderTop_ne f.orderTop_eq_finiteArchimedeanClassMk hx0

/--
theorem `coeff_eq_of_mem` / 定理 `coeff_eq_of_mem`

English:
theorem coeff_eq_of_mem
  statement: [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.val.domain}
  proof: by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub]; rw [← ofLex_sub]; rw [← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hd
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

中文:
定理 coeff_eq_of_mem
  结论: [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.val.domain}
  证明: by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub]; rw [← ofLex_sub]; rw [← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hd
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

Depends on / 依赖: HahnSeries, HahnSeries.coeff_sub, LinearPMap, LinearPMap.map_sub, Submodule, Submodule.sub_mem, coeff_eq_zero_of_mem, coeff_sub, eq_of_sub_eq_zero, map_sub, ofLex_sub, sub_mem, y.val, z.val
-/
theorem coeff_eq_of_mem [IsOrderedAddMonoid R] [Archimedean R] (x : M) {y z : f.val.domain}
    {c : FiniteArchimedeanClass M} (hy : y.val - x in ball K c) (hz : z.val - x in ball K c)
    {d : FiniteArchimedeanClass M} (hd : d <= c) :
    (ofLex (f.val y)).coeff d = (ofLex (f.val z)).coeff d := by
  apply eq_of_sub_eq_zero
  rw [← HahnSeries.coeff_sub]; rw [← ofLex_sub]; rw [← LinearPMap.map_sub]
  refine coeff_eq_zero_of_mem f ?_ hd
  have : (y - z).val = (y.val - x) - (z.val - x) := by
    push_cast
    simp
  rw [this]
  exact Submodule.sub_mem _ hy hz

/-! ### Step 3: extend the embedding

We create a larger `HahnEmbedding.Partial` from an existing one by adding a new element to the
domain and assigning an appropriate output that preserves all `HahnEmbedding.Partial`'s properties.
-/

/-- Evaluate coefficients of the `HahnSeries` given an arbitrary input that's not necessarily in
`f`'s domain. The coefficient is picked from `y` that is "close enough" to `x` (their difference
is in a higher `ArchimedeanClass`). If no such `y` exists (in other words, x is "isolated"), set the
coefficient to 0.

This doesn't immediately extend `f`'s domain to the entire module in a consistent way. Such
extension isn't necessarily linear.
-/
noncomputable
/--
Definition of `evalCoeff` / `evalCoeff` 的定义

English:
definition evalCoeff
  signature: (x : M) (c : FiniteArchimedeanClass M)
  body: open scoped Classical in
  if h : exists y : f.val.domain, y.val - x in ball K c then
    (ofLex (f.val h.choose)).coeff c
  else
    0

中文:
定义 evalCoeff
  签名: (x : M) (c : FiniteArchimedeanClass M)
  定义体: open scoped Classical in
  if h : exists y : f.val.domain, y.val - x in ball K c then
    (ofLex (f.val h.choose)).coeff c
  else
    0

Depends on / 依赖: Classical, domain, f.val, f.val.domain, h.choose, scoped, y.val
-/
def evalCoeff (x : M) (c : FiniteArchimedeanClass M) : R :=
  open scoped Classical in
  if h : exists y : f.val.domain, y.val - x in ball K c then
    (ofLex (f.val h.choose)).coeff c
  else
    0

/--
theorem `evalCoeff_eq` / 定理 `evalCoeff_eq`

English:
theorem evalCoeff_eq
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
  proof: by
  have hnonempty : exists y : f.val.domain, y.val - x in ball K c := ⟨y, hy⟩
  simpa [evalCoeff, dif_pos hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy le_rfl

中文:
定理 evalCoeff_eq
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
  证明: by
  have hnonempty : exists y : f.val.domain, y.val - x in ball K c := ⟨y, hy⟩
  simpa [evalCoeff, dif_pos hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy le_rfl

Depends on / 依赖: choose_spec, coeff_eq_of_mem, dif_pos, domain, evalCoeff, f.val.domain, hnonempty, hnonempty.choose_spec, le_rfl, y.val
-/
theorem evalCoeff_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M} {c : FiniteArchimedeanClass M}
    {y : f.val.domain} (hy : y.val - x in ball K c) :
    evalCoeff f x c = (ofLex (f.val y)).coeff c := by
  have hnonempty : exists y : f.val.domain, y.val - x in ball K c := ⟨y, hy⟩
  simpa [evalCoeff, dif_pos hnonempty] using coeff_eq_of_mem f x hnonempty.choose_spec hy le_rfl

/--
theorem `evalCoeff_eq_zero` / 定理 `evalCoeff_eq_zero`

English:
theorem evalCoeff_eq_zero
  statement: {x : M} {c : FiniteArchimedeanClass M}
  proof: by
  rw [evalCoeff]; rw [dif_neg h]

中文:
定理 evalCoeff_eq_zero
  结论: {x : M} {c : FiniteArchimedeanClass M}
  证明: by
  rw [evalCoeff]; rw [dif_neg h]

Depends on / 依赖: dif_neg, evalCoeff
-/
theorem evalCoeff_eq_zero {x : M} {c : FiniteArchimedeanClass M}
    (h : ¬exists y : f.val.domain, y.val - x in ball K c) :
    f.evalCoeff x c = 0 := by
  rw [evalCoeff]; rw [dif_neg h]

/--
theorem `isWF_support_evalCoeff` / 定理 `isWF_support_evalCoeff`

English:
theorem isWF_support_evalCoeff
  given: [IsOrderedAddMonoid R] [Archimedean R] (x : M)
  proof: by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra! ⟨seq, ⟨hanti, hmem⟩⟩
  have hnonempty : exists y : f.val.domain, y.val - x in ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [evalCoeff, dif_neg hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : Nat) : s

中文:
定理 isWF_support_evalCoeff
  条件: [IsOrderedAddMonoid R] [Archimedean R] (x : M)
  证明: by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra! ⟨seq, ⟨hanti, hmem⟩⟩
  have hnonempty : exists y : f.val.domain, y.val - x in ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [evalCoeff, dif_neg hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : Nat) : s

Depends on / 依赖: Function, Function.mem_support, Set.isWF_iff_no_descending_seq, antitone, ball_strictAnti, coeff.support, contrapose, convert, dif_neg, domain, evalCoeff, evalCoeff_eq, f.evalCoeff_eq, f.val, f.val.domain, hanti.antitone, hempty, hnonempty, isWF_iff_no_descending_seq, mem_support
-/
theorem isWF_support_evalCoeff [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    (evalCoeff f x).support.IsWF := by
  rw [Set.isWF_iff_no_descending_seq]
  by_contra! ⟨seq, ⟨hanti, hmem⟩⟩
  have hnonempty : exists y : f.val.domain, y.val - x in ball K (seq 0) := by
    specialize hmem 0
    contrapose hmem with hempty
    simp [evalCoeff, dif_neg hempty]
  obtain ⟨y, hy⟩ := hnonempty
  have hmem' (n : Nat) : seq n in (ofLex (f.val y)).coeff.support := by
    specialize hmem n
    rw [Function.mem_support] at ⊢ hmem
    convert hmem
    refine (f.evalCoeff_eq ((ball_strictAnti K).antitone ?_ hy)).symm
    simpa using hanti.antitone (show 0 <= n by simp)
  obtain hwf := (ofLex (f.val y)).isWF_support
  contrapose! hwf
  rw [Set.isWF_iff_no_descending_seq]
  simpa using ⟨seq, hanti, hmem'⟩

/-- Promote `HahnEmbedding.Partial.evalCoeff`'s output to a new `HahnSeries`. -/
noncomputable
/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: [IsOrderedAddMonoid R] [Archimedean R] (x : M)
  body: toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.isWF_support_evalCoeff x).isPWO }

@[simp]

中文:
定义 eval
  签名: [IsOrderedAddMonoid R] [Archimedean R] (x : M)
  定义体: toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.isWF_support_evalCoeff x).isPWO }

@[simp]

Depends on / 依赖: evalCoeff, f.evalCoeff, f.isWF_support_evalCoeff, isPWO_support, isWF_support_evalCoeff
-/
def eval [IsOrderedAddMonoid R] [Archimedean R] (x : M) :
    Lex R⟦FiniteArchimedeanClass M⟧ :=
  toLex { coeff := f.evalCoeff x
          isPWO_support' := (f.isWF_support_evalCoeff x).isPWO }

@[simp]
/--
theorem `eval_zero` / 定理 `eval_zero`

English:
theorem eval_zero
  given: [IsOrderedAddMonoid R] [Archimedean R]
  statement: f.eval 0 = 0
  proof: by
  unfold eval
  convert! toLex_zero
  ext c
  rw [f.evalCoeff_eq (y := 0) (by simp)]
  simp

中文:
定理 eval_zero
  条件: [IsOrderedAddMonoid R] [Archimedean R]
  结论: f.eval 0 = 0
  证明: by
  unfold eval
  convert! toLex_zero
  ext c
  rw [f.evalCoeff_eq (y := 0) (by simp)]
  simp

Depends on / 依赖: convert, evalCoeff_eq, f.evalCoeff_eq, toLex_zero
-/
theorem eval_zero [IsOrderedAddMonoid R] [Archimedean R] : f.eval 0 = 0 := by
  unfold eval
  convert! toLex_zero
  ext c
  rw [f.evalCoeff_eq (y := 0) (by simp)]
  simp

/--
theorem `eval_smul` / 定理 `eval_smul`

English:
theorem eval_smul
  given: [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M)
  proof: by
  by_cases hk : k = 0
  · simp [hk]
  unfold eval
  rw [← toLex_smul]; rw [toLex.injective.eq_iff]
  ext c
  suffices f.evalCoeff (k • x) c = k • f.evalCoeff x c by simpa using this
  by_cases h : exists y : f.val.domain, y.val - x in ball K c
  · obtain ⟨y, hy⟩ := h
    have heq : (k • y).val - 

中文:
定理 eval_smul
  条件: [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M)
  证明: by
  by_cases hk : k = 0
  · simp [hk]
  unfold eval
  rw [← toLex_smul]; rw [toLex.injective.eq_iff]
  ext c
  suffices f.evalCoeff (k • x) c = k • f.evalCoeff x c by simpa using this
  by_cases h : exists y : f.val.domain, y.val - x in ball K c
  · obtain ⟨y, hy⟩ := h
    have heq : (k • y).val - 

Depends on / 依赖: LinearPMap, LinearPMap.map_smul, Submodule, Submodule.smul_mem, domain, eq_iff, evalCoeff, evalCoeff_eq, f.evalCoeff, f.evalCoeff_eq, f.val.domain, injective, map_smul, smul_mem, smul_sub, toLex.injective.eq_iff, toLex_smul, y.val
-/
theorem eval_smul [IsOrderedAddMonoid R] [Archimedean R] (k : K) (x : M) :
    f.eval (k • x) = k • f.eval x := by
  by_cases hk : k = 0
  · simp [hk]
  unfold eval
  rw [← toLex_smul]; rw [toLex.injective.eq_iff]
  ext c
  suffices f.evalCoeff (k • x) c = k • f.evalCoeff x c by simpa using this
  by_cases h : exists y : f.val.domain, y.val - x in ball K c
  · obtain ⟨y, hy⟩ := h
    have heq : (k • y).val - k • x = k • (y.val - x) := by simp [smul_sub]
    have hy' : (k • y).val - k • x in ball K c := by
      rw [heq]
      exact Submodule.smul_mem _ _ hy
    simp [f.evalCoeff_eq hy, f.evalCoeff_eq hy', LinearPMap.map_smul]
  have h' : ¬exists y : f.val.domain, y.val - k • x in ball K c := by
    contrapose h
    obtain ⟨y, hy⟩ := h
    use k⁻¹ • y
    have heq : (k⁻¹ • y).val - x = k⁻¹ • (y.val - k • x) := by
      simp [smul_sub, smul_smul, inv_mul_cancel₀ hk]
    exact heq ▸ Submodule.smul_mem _ _ hy
  simp [f.evalCoeff_eq_zero h, f.evalCoeff_eq_zero h']

/--
theorem `archimedeanClassMk_le_of_eval_eq` / 定理 `archimedeanClassMk_le_of_eval_eq`

English:
theorem archimedeanClassMk_le_of_eval_eq
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply ArchimedeanClass.mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (c : FiniteArchimedeanClass M) (hc : c.val < .mk (x - z.val)) :
      (ofLex (f.eval x)).coeff c = (ofLex (f.val z)).coeff

中文:
定理 archimedeanClassMk_le_of_eval_eq
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply ArchimedeanClass.mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (c : FiniteArchimedeanClass M) (hc : c.val < .mk (x - z.val)) :
      (ofLex (f.eval x)).coeff c = (ofLex (f.val z)).coeff

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk_left_le_mk_add, ArchimedeanClass.mk_sub_comm, FiniteArchimedeanClass, c.prop, c.val, evalCoeff_eq, f.eval, f.val, mk_left_le_mk_add, mk_sub_comm, ofLex_toLex, simp_rw, y.val, z.val
-/
theorem archimedeanClassMk_le_of_eval_eq [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {y : f.val.domain} (h : f.eval x = f.val y) (z : f.val.domain) :
    ArchimedeanClass.mk (x - z.val) <= .mk (x - y.val) := by
  have : x - y.val = x - z.val + (z.val - y.val) := by abel
  rw [this]
  apply ArchimedeanClass.mk_left_le_mk_add
  by_cases hyz : z.val - y.val = 0
  · simp [hyz]
  have h1 (c : FiniteArchimedeanClass M) (hc : c.val < .mk (x - z.val)) :
      (ofLex (f.eval x)).coeff c = (ofLex (f.val z)).coeff c := by
    rw [ArchimedeanClass.mk_sub_comm] at hc
    simp_rw [eval, ofLex_toLex]
    apply evalCoeff_eq
    simpa [c.prop] using! fun _ => hc
  have h2 : forall c : FiniteArchimedeanClass M, c.val < .mk (x - z.val) ->
      (ofLex (f.val (z - y))).coeff c = 0 := by
    intro c hc
    rw [LinearPMap.map_sub]; rw [ofLex_sub]; rw [HahnSeries.coeff_sub]; rw [sub_eq_zero]; rw [← h]
    exact (h1 c hc).symm
  contrapose! h2
  exact ⟨FiniteArchimedeanClass.mk (z.val - y.val) hyz, h2, coeff_ne_zero _ _⟩

/--
theorem `val_sub_ne_zero` / 定理 `val_sub_ne_zero`

English:
theorem val_sub_ne_zero
  given: {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain)
  statement: y.val - x != 0
  proof: by
  contrapose hx
  obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
  simp

中文:
定理 val_sub_ne_zero
  条件: {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain)
  结论: y.val - x != 0
  证明: by
  contrapose hx
  obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
  simp

Depends on / 依赖: contrapose, sub_eq_zero, sub_eq_zero.mp, y.val
-/
theorem val_sub_ne_zero {x : M} (hx : x ∉ f.val.domain) (y : f.val.domain) : y.val - x != 0 := by
  contrapose hx
  obtain rfl : x = y.val := (sub_eq_zero.mp hx).symm
  simp

/--
theorem `eval_ne` / 定理 `eval_ne`

English:
theorem eval_ne
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  proof: by
  -- decompose `x - y = u + v`, where `v ∈ submodule (x - y)` and
  -- `u` is at higher class than `x - y`
  have := val_sub_ne_zero f hx y
  rw [sub_ne_zero]; rw [ne_comm]; rw [← sub_ne_zero] at this
  let xy := mk _ this
  have hxy : x - y.val in closedBall K xy := fun _ => by simp; rfl
  rw [←

中文:
定理 eval_ne
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  证明: by
  -- decompose `x - y = u + v`, where `v ∈ submodule (x - y)` and
  -- `u` is at higher class than `x - y`
  have := val_sub_ne_zero f hx y
  rw [sub_ne_zero]; rw [ne_comm]; rw [← sub_ne_zero] at this
  let xy := mk _ this
  have hxy : x - y.val in closedBall K xy := fun _ => by simp; rfl
  rw [←
-/
theorem eval_ne [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) : f.eval x != f.val y := by
  -- decompose `x - y = u + v`, where `v ∈ submodule (x - y)` and
  -- `u` is at higher class than `x - y`
  have := val_sub_ne_zero f hx y
  rw [sub_ne_zero]; rw [ne_comm]; rw [← sub_ne_zero] at this
  let xy := mk _ this
  have hxy : x - y.val in closedBall K xy := fun _ => by simp; rfl
  rw [← seed.ball_sup_stratum_eq xy]; rw [Submodule.mem_sup] at hxy
  obtain ⟨u, hu, v, hv, huv⟩ := hxy
  have huv' : x - y.val - v = u := by simp [← huv]
  rw [mem_ball_iff K] at hu
  -- `z = x - u = y + v` is also in the domain.
  -- Assuming `f.eval x = f.val y` allows us to use `archimedeanClassMk_le_of_eval_eq` on `z`
  have hyv : y.val + v in f.val.domain := Submodule.add_mem _ (by simp) (f.mem_domain hv)
  by_contra! h
  obtain h := f.archimedeanClassMk_le_of_eval_eq h ⟨y.val + v, hyv⟩
  contrapose! h
  simp_rw [← sub_sub, huv']
  obtain rfl | ne := eq_or_ne u 0
  exacts [Ne.lt_top (by simpa), (mk_lt_mk ..).mp (hu ne)]

/--
theorem `eval_eq_truncLT` / 定理 `eval_eq_truncLT`

English:
theorem eval_eq_truncLT
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: by
  unfold eval
  rw [toLex.injective.eq_iff]
  ext d
  simp only
  obtain hd | hd := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hd]
    exact evalCoeff_eq _ fun _ => by simpa [hy]
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hd]


中文:
定理 eval_eq_truncLT
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: by
  unfold eval
  rw [toLex.injective.eq_iff]
  ext d
  simp only
  obtain hd | hd := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hd]
    exact evalCoeff_eq _ fun _ => by simpa [hy]
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hd]


Depends on / 依赖: HahnSeries, HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le, HahnSeries.coeff_truncLT_of_lt, antitone, ball_strictAnti, coe_truncLTLinearMap, coeff_truncLT_of_le, coeff_truncLT_of_lt, contrapose, eq_iff, evalCoeff_eq, evalCoeff_eq_zero, injective, lt_or_ge, toLex.injective.eq_iff
-/
theorem eval_eq_truncLT [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    {c : FiniteArchimedeanClass M} {y : f.val.domain}
    (hy : ArchimedeanClass.mk (y.val - x) = c.val) (h : forall z : f.val.domain, z.val - x ∉ ball K c) :
    f.eval x = toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.val y))) := by
  unfold eval
  rw [toLex.injective.eq_iff]
  ext d
  simp only
  obtain hd | hd := lt_or_ge d c
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hd]
    exact evalCoeff_eq _ fun _ => by simpa [hy]
  · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hd]
    apply evalCoeff_eq_zero
    contrapose! h
    obtain ⟨z, hz⟩ := h
    exact ⟨z, (ball_strictAnti K).antitone (by simpa using hd) hz⟩

/--
theorem `exists_sub_mem_ball` / 定理 `exists_sub_mem_ball`

English:
theorem exists_sub_mem_ball
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  proof: by
  set c := mk _ (val_sub_ne_zero f hx y)
  have hc : ArchimedeanClass.mk (y.val - x) = c := rfl
  by_contra!; apply hx
  have h := f.eval_eq_truncLT hc this
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
  rw [← hx'] at h
  contrapose! h
  exact f.eval_ne h _

中文:
定理 exists_sub_mem_ball
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  证明: by
  set c := mk _ (val_sub_ne_zero f hx y)
  have hc : ArchimedeanClass.mk (y.val - x) = c := rfl
  by_contra!; apply hx
  have h := f.eval_eq_truncLT hc this
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
  rw [← hx'] at h
  contrapose! h
  exact f.eval_ne h _

Depends on / 依赖: ArchimedeanClass, ArchimedeanClass.mk, LinearMap, LinearMap.mem_range.mp, contrapose, eval_eq_truncLT, eval_ne, f.eval_eq_truncLT, f.eval_ne, f.prop.truncLT_mem_range, mem_range, truncLT_mem_range, val_sub_ne_zero, y.val
-/
theorem exists_sub_mem_ball [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) :
    exists z : f.val.domain, z.val - x in ball K (mk _ (val_sub_ne_zero f hx y)) := by
  set c := mk _ (val_sub_ne_zero f hx y)
  have hc : ArchimedeanClass.mk (y.val - x) = c := rfl
  by_contra!; apply hx
  have h := f.eval_eq_truncLT hc this
  obtain ⟨x', hx'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
  rw [← hx'] at h
  contrapose! h
  exact f.eval_ne h _

/--
theorem `eval_lt` / 定理 `eval_lt`

English:
theorem eval_lt
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  proof: by
  -- Expand the definition of `HahnSeries`' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of `y - x`
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x != 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨mk (y.val - x)

中文:
定理 eval_lt
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  证明: by
  -- Expand the definition of `HahnSeries`' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of `y - x`
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x != 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨mk (y.val - x)
-/
theorem eval_lt [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
    (y : f.val.domain) (h : x < y.val) : f.eval x < f.val y := by
  -- Expand the definition of `HahnSeries`' order. We need to find the first coefficient that
  -- dictates the < relation. This coefficient is exactly at the Archimedean class of `y - x`
  rw [HahnSeries.lt_iff]
  have hxy0 : y.val - x != 0 := sub_ne_zero_of_ne h.ne.symm
  refine ⟨mk (y.val - x) hxy0, ?_, ?_⟩
  · -- All coefficients before the dictating term are the same
    intro j hj
    apply evalCoeff_eq
    simpa [j.prop] using! fun _ => hj
  -- Show the dictating coefficient
  suffices f.evalCoeff x (mk (y.val - x) hxy0) < (ofLex (f.val y)).coeff (mk _ hxy0) by
    simpa [eval] using! this
  -- We find `z` from `f`'s domain to approximate `x`. Such approximation obeys:
  -- * `f.eval x = f.val z`
  -- * `x < y → z < y`
  -- * `mk (x - y) = mk (z - y)`
  obtain ⟨z, hz⟩ := f.exists_sub_mem_ball hx y
  rw [f.evalCoeff_eq hz]
  have : z != x := by rintro rfl; exact hx z.2
  have hzy : z < y := by
    change z.val < y.val
refine (sub_lt_sub_iff_right x).mp
      ArchimedeanClass.lt_of_mk_lt_mk_of_nonneg ?_ (sub_nonneg_of_le h.le)
    simpa using! hz (by simpa [sub_eq_zero])
  have hzyne : z.val - y.val != 0 := by
    apply sub_ne_zero_of_ne
    simpa using! hzy.ne
  have hzyclass : mk (y.val - x) hxy0 = mk (z.val - y.val) hzyne := by
    suffices ArchimedeanClass.mk (y.val - x) = .mk (z.val - y.val) by
      simpa [Subtype.ext_iff] using! this
    have : y.val - z.val = y.val - x + (x - z.val) := by abel
    rw [ArchimedeanClass.mk_sub_comm z.val y.val]; rw [this]
    refine (ArchimedeanClass.mk_add_eq_mk_left ?_).symm
    rw [ArchimedeanClass.mk_sub_comm x z.val]
    simpa using! hz (by simpa [sub_eq_zero])
  -- Since both `y` and `z` are in the domain, we can apply `f`'s monotonicity on them
  rw [← f.prop.strictMono.lt_iff_lt]; rw [HahnSeries.lt_iff] at hzy
  obtain ⟨i, hj, hi⟩ := hzy
  -- We show that the dictating coefficient of `f.val y < f.val z`
  -- is at the same position as the dictating coefficient of `f.eval x < f.val y`
  have hieq : i = mk (y.val - x) hxy0 := by
    apply le_antisymm
    · by_contra! hlt
      obtain hj := sub_eq_zero_of_eq (hj (mk _ hxy0) hlt)
      contrapose! hj
      rw [← HahnSeries.coeff_sub]; rw [← ofLex_sub]; rw [← LinearPMap.map_sub]; rw [hzyclass]
      apply f.coeff_ne_zero
    · contrapose! hi
      rw [hzyclass] at hi
      have hzy : z.val - y.val in ball K i := fun _ => hi
      exact (f.coeff_eq_of_mem y.val (by simp) hzy (by simp)).le
  exact hieq ▸ hi

/-- Extend `f` to a larger partial linear map by adding a new `x`. -/
noncomputable
/--
Definition of `extendFun` / `extendFun` 的定义

English:
definition extendFun
  signature: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  body: .supSpanSingleton f.val x (eval f x) hx

中文:
定义 extendFun
  签名: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  定义体: .supSpanSingleton f.val x (eval f x) hx

Depends on / 依赖: f.val, supSpanSingleton
-/
def extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ :=
  .supSpanSingleton f.val x (eval f x) hx

/--
theorem `extendFun_strictMono` / 定理 `extendFun_strictMono`

English:
theorem extendFun_strictMono
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: by
  have hx' {c : K} (hc : c != 0) : -c • x ∉ f.val.domain := by
    contrapose hx
    rwa [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
  -- only need to prove `0 < f v` for `0 < v = z - y`
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obt

中文:
定理 extendFun_strictMono
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: by
  have hx' {c : K} (hc : c != 0) : -c • x ∉ f.val.domain := by
    contrapose hx
    rwa [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
  -- only need to prove `0 < f v` for `0 < v = z - y`
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obt

Depends on / 依赖: Submodule, Submodule.smul_mem_iff, contrapose, domain, f.val.domain, neg_mem_iff, neg_smul, smul_mem_iff
-/
theorem extendFun_strictMono [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : StrictMono (f.extendFun hx) := by
  have hx' {c : K} (hc : c != 0) : -c • x ∉ f.val.domain := by
    contrapose hx
    rwa [neg_smul, neg_mem_iff, Submodule.smul_mem_iff _ hc] at hx
  -- only need to prove `0 < f v` for `0 < v = z - y`
  intro y z hyz
  rw [← sub_pos] at hyz
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyzmem := (z - y).prop
  nth_rw 1 [extendFun, LinearPMap.domain_supSpanSingleton] at hyzmem
  -- decompose `v = a + c • x`, reducing this to eval_lt
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hyzmem
  have : z - y = ⟨a + b, hab.symm ▸ (z - y).prop⟩ := by simp_rw [hab]
  rw [this] at ⊢ hyz
  have habpos : 0 < a + b := by exact hyz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hb
  rw [← hc] at habpos
  simp_rw [← hc, extendFun]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ hx _ ha]
  suffices f.eval (-c • x) < f.val ⟨a, ha⟩ by
    rw [eval_smul]; rw [neg_smul] at this
    exact neg_lt_iff_pos_add.mp this
  have hac : -c • x < a := by
    rw [neg_smul]
    exact neg_lt_iff_pos_add.mpr habpos
  by_cases hc : c = 0
  · rw [hc] at ⊢ hac
    suffices f.val 0 < f.val ⟨a, ha⟩ by simpa using! this
    exact f.prop.strictMono (by simpa using! hac)
  · exact f.eval_lt (hx' hc) ⟨a, ha⟩ hac

/--
theorem `baseEmbedding_le_extendFun` / 定理 `baseEmbedding_le_extendFun`

English:
theorem baseEmbedding_le_extendFun
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: by
  rw [extendFun]
exact le_trans f.prop.baseEmbedding_le LinearPMap.left_le_sup _ _ _

中文:
定理 baseEmbedding_le_extendFun
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: by
  rw [extendFun]
exact le_trans f.prop.baseEmbedding_le LinearPMap.left_le_sup _ _ _

Depends on / 依赖: LinearPMap, LinearPMap.left_le_sup, baseEmbedding_le, extendFun, f.prop.baseEmbedding_le, le_trans, left_le_sup
-/
theorem baseEmbedding_le_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : seed.baseEmbedding <= f.extendFun hx := by
  rw [extendFun]
exact le_trans f.prop.baseEmbedding_le LinearPMap.left_le_sup _ _ _

/--
theorem `truncLT_eval_mem_range_extendFun` / 定理 `truncLT_eval_mem_range_extendFun`

English:
theorem truncLT_eval_mem_range_extendFun
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: by
  rw [extendFun]; rw [LinearMap.mem_range]
  by_cases h : exists y : f.val.domain, y.val - x in ball K c
  · -- if `x` is not isolated within `c`, the truncation at `c` equals to truncating
    -- a nearby `y` in the domain
    obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (f.p

中文:
定理 truncLT_eval_mem_range_extendFun
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: by
  rw [extendFun]; rw [LinearMap.mem_range]
  by_cases h : exists y : f.val.domain, y.val - x in ball K c
  · -- if `x` is not isolated within `c`, the truncation at `c` equals to truncating
    -- a nearby `y` in the domain
    obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (f.p

Depends on / 依赖: LinearMap, LinearMap.mem_range, domain, equals, extendFun, f.val.domain, isolated, mem_range, truncating, truncation, within, y.val
-/
theorem truncLT_eval_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.eval x))) in
    LinearMap.range (f.extendFun hx).toFun := by
  rw [extendFun]; rw [LinearMap.mem_range]
  by_cases h : exists y : f.val.domain, y.val - x in ball K c
  · -- if `x` is not isolated within `c`, the truncation at `c` equals to truncating
    -- a nearby `y` in the domain
    obtain ⟨y, hy⟩ := h
    obtain ⟨z, hz⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range y c)
    refine ⟨⟨z.val, by simpa using Submodule.mem_sup_left z.prop⟩, ?_⟩
    rw [LinearPMap.toFun_eq_coe] at hz
    rw [LinearPMap.toFun_eq_coe]; rw [LinearPMap.supSpanSingleton_apply_mk_of_mem _ _ _ z.prop]
    rw [hz]; rw [toLex_inj]
    ext d
    obtain hdc | hdc := lt_or_ge d c
    · simp_rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc]
      refine (f.evalCoeff_eq (Set.mem_of_mem_of_subset hy ?_)).symm
      simpa using (ball_strictAnti K hdc).le
    · simp_rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_le hdc]
  · -- if `x` is isolated within c, truncating has no effect because the trailing coefficients
    -- are already 0
    refine ⟨⟨x, by simpa using Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)⟩, ?_⟩
    apply_fun ofLex
    rw [ofLex_toLex]; rw [LinearPMap.toFun_eq_coe]; rw [LinearPMap.supSpanSingleton_apply_self]
    ext d
    obtain hdc | hdc := lt_or_ge d c
    · rw [HahnSeries.coe_truncLTLinearMap, HahnSeries.coeff_truncLT_of_lt hdc]
    rw [HahnSeries.coe_truncLTLinearMap]; rw [HahnSeries.coeff_truncLT_of_le hdc]; rw [eval]; rw [ofLex_toLex]
    apply f.evalCoeff_eq_zero
    contrapose h
    obtain ⟨y, hy⟩ := h
    exact ⟨y, Set.mem_of_mem_of_subset hy (by simpa using (ball_strictAnti K).antitone hdc)⟩

/--
theorem `truncLT_mem_range_extendFun` / 定理 `truncLT_mem_range_extendFun`

English:
theorem truncLT_mem_range_extendFun
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: by
  obtain ⟨y', hy'⟩ := y
  rw [extendFun]; rw [LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [extendFun, ← hab, ← hk]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw

中文:
定理 truncLT_mem_range_extendFun
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: by
  obtain ⟨y', hy'⟩ := y
  rw [extendFun]; rw [LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [extendFun, ← hab, ← hk]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw

Depends on / 依赖: LinearMap, LinearMap.mem_range.mp, LinearPMap, LinearPMap.domain_supSpanSingleton, LinearPMap.supSpanSingleton_apply_mk, Submodule, Submodule.add_mem, Submodule.mem_span_singleton.mp, Submodule.mem_sup.mp, Submodule.smul_mem, add_mem, domain_supSpanSingleton, extendFun, f.prop.t, map_add, map_smul, mem_range, mem_span_singleton, mem_sup, ofLex_add
-/
theorem truncLT_mem_range_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) (y : (f.extendFun hx).domain) (c : FiniteArchimedeanClass M) :
    toLex (HahnSeries.truncLTLinearMap K c (ofLex (f.extendFun hx y))) in
    LinearMap.range (f.extendFun hx).toFun := by
  obtain ⟨y', hy'⟩ := y
  rw [extendFun]; rw [LinearPMap.domain_supSpanSingleton] at hy'
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hy'
  obtain ⟨k, hk⟩ := Submodule.mem_span_singleton.mp hb
  simp_rw [extendFun, ← hab, ← hk]
  rw [LinearPMap.supSpanSingleton_apply_mk _ _ _ _ _ ha]
  rw [ofLex_add]; rw [map_add]; rw [toLex_add]; rw [ofLex_smul]; rw [map_smul]; rw [toLex_smul]
  refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
  · obtain ⟨⟨a', ha'mem⟩, ha'⟩ := LinearMap.mem_range.mp (f.prop.truncLT_mem_range ⟨a, ha⟩ c)
    refine LinearMap.mem_range.mpr ⟨⟨a', by simpa using Submodule.mem_sup_left ha'mem⟩, ?_⟩
    rw [← ha']
    exact LinearPMap.supSpanSingleton_apply_mk_of_mem f.val _ hx ha'mem
  · apply truncLT_eval_mem_range_extendFun

/--
theorem `isPartial_extendFun` / 定理 `isPartial_extendFun`

English:
theorem isPartial_extendFun
  statement: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  proof: f.extendFun_strictMono hx
  baseEmbedding_le := f.baseEmbedding_le_extendFun hx
  truncLT_mem_range := f.truncLT_mem_range_extendFun hx

中文:
定理 isPartial_extendFun
  结论: [IsOrderedAddMonoid R] [Archimedean R] {x : M}
  证明: f.extendFun_strictMono hx
  baseEmbedding_le := f.baseEmbedding_le_extendFun hx
  truncLT_mem_range := f.truncLT_mem_range_extendFun hx

Depends on / 依赖: extendFun_strictMono, f.extendFun_strictMono
-/
theorem isPartial_extendFun [IsOrderedAddMonoid R] [Archimedean R] {x : M}
    (hx : x ∉ f.val.domain) : IsPartial seed (extendFun f hx) where
  strictMono := f.extendFun_strictMono hx
  baseEmbedding_le := f.baseEmbedding_le_extendFun hx
  truncLT_mem_range := f.truncLT_mem_range_extendFun hx

/-- Promote `HahnEmbedding.Partial.extendFun` to a new `HahnEmbedding.Partial`. -/
noncomputable
/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  body: ⟨f.extendFun hx, f.isPartial_extendFun hx⟩

中文:
定义 extend
  签名: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  定义体: ⟨f.extendFun hx, f.isPartial_extendFun hx⟩

Depends on / 依赖: extendFun, f.extendFun, f.isPartial_extendFun, isPartial_extendFun
-/
def extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    Partial seed := ⟨f.extendFun hx, f.isPartial_extendFun hx⟩

/--
theorem `lt_extend` / 定理 `lt_extend`

English:
theorem lt_extend
  given: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  proof: by
  apply lt_of_le_of_ne
  · change f.val <= (f.extend hx).val
    simpa [extend, extendFun] using! LinearPMap.left_le_sup _ _ _
  by_contra!
  have : f.val.domain = (f.extend hx).val.domain := by congr
  rw [this] at hx
  contrapose! hx with h
  simpa using! Submodule.mem_sup_right (by simp)

中文:
定理 lt_extend
  条件: [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain)
  证明: by
  apply lt_of_le_of_ne
  · change f.val <= (f.extend hx).val
    simpa [extend, extendFun] using! LinearPMap.left_le_sup _ _ _
  by_contra!
  have : f.val.domain = (f.extend hx).val.domain := by congr
  rw [this] at hx
  contrapose! hx with h
  simpa using! Submodule.mem_sup_right (by simp)

Depends on / 依赖: LinearPMap, LinearPMap.left_le_sup, Submodule, Submodule.mem_sup_right, contrapose, domain, extend, extendFun, f.extend, f.val, f.val.domain, left_le_sup, lt_of_le_of_ne, mem_sup_right, val.domain
-/
theorem lt_extend [IsOrderedAddMonoid R] [Archimedean R] {x : M} (hx : x ∉ f.val.domain) :
    f < f.extend hx := by
  apply lt_of_le_of_ne
  · change f.val <= (f.extend hx).val
    simpa [extend, extendFun] using! LinearPMap.left_le_sup _ _ _
  by_contra!
  have : f.val.domain = (f.extend hx).val.domain := by congr
  rw [this] at hx
  contrapose! hx with h
  simpa using! Submodule.mem_sup_right (by simp)

/-! ### Step 4: use Zorn's lemma

We show that `sSup` makes sense on `HahnEmbedding.Partial`, which allows us to use Zorn's lemma
to assert the existence of maximal embedding. Since we already show that we can create greater
embeddings by adding new elements, the maximal embedding must have the maximal domain.
-/

/-- A partial linear map that contains every element in a directed set of
`HahnEmbedding.Partial`. -/
noncomputable
/--
Definition of `sSupFun` / `sSupFun` 的定义

English:
definition sSupFun
  signature: {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c)
  body: LinearPMap.sSup ((·.val) '' c) (hc.mono_comp (by simp))

中文:
定义 sSupFun
  签名: {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c)
  定义体: LinearPMap.sSup ((·.val) '' c) (hc.mono_comp (by simp))

Depends on / 依赖: LinearPMap, LinearPMap.sSup, hc.mono_comp, mono_comp
-/
def sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c) :
    M ->ₗ.[K] Lex R⟦FiniteArchimedeanClass M⟧ :=
  LinearPMap.sSup ((·.val) '' c) (hc.mono_comp (by simp))

/--
theorem `sSupFun_strictMono` / 定理 `sSupFun_strictMono`

English:
theorem sSupFun_strictMono
  statement: [IsOrderedAddMonoid R] {c : Set (Partial seed)}
  proof: by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (sSupFun hc) (y - x) = f ⟨(y 

中文:
定理 sSupFun_strictMono
  结论: [IsOrderedAddMonoid R] {c : Set (Partial seed)}
  证明: by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (sSupFun hc) (y - x) = f ⟨(y 

Depends on / 依赖: LinearPMap, LinearPMap.domain_sSup, LinearPMap.map_sub, LinearPMap.mem_domain_sSup_iff, LinearPMap.sSup_apply, Set.mem_image, StrictMono, domain_sSup, hc.mono_comp, hnonempty, hnonempty.image, lt_of_sub_pos, map_sub, mem_domain_sSup_iff, mem_image, mono_comp, prop.strictMono, sSupFun, sSup_apply, simp_rw
-/
theorem sSupFun_strictMono [IsOrderedAddMonoid R] {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) : StrictMono (sSupFun hc) := by
  intro x y h
  apply lt_of_sub_pos
  rw [← LinearPMap.map_sub]
  obtain hyx := (y - x).prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hyx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hyx
  have : (sSupFun hc) (y - x) = f ⟨(y - x).val, hf⟩ :=
    LinearPMap.sSup_apply _ hmem ⟨(y - x).val, hf⟩
  rw [this]
  obtain ⟨f', _, hf'⟩ := (Set.mem_image _ _ _).mp hmem
  have hmono : StrictMono f := hf'.symm ▸ f'.prop.strictMono
  rw [show 0 = f 0 by simp]
  apply hmono
  rw [← Subtype.coe_lt_coe]
  simp [h]

/--
theorem `le_sSupFun` / 定理 `le_sSupFun`

English:
theorem le_sSupFun
  statement: {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c)
  proof: LinearPMap.le_sSup _ (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩

中文:
定理 le_sSupFun
  结论: {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c)
  证明: LinearPMap.le_sSup _ (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩

Depends on / 依赖: LinearPMap, LinearPMap.le_sSup, Set.mem_image, le_sSup, mem_image
-/
theorem le_sSupFun {c : Set (Partial seed)} (hc : DirectedOn (· <= ·) c)
    {f : Partial seed} (hf : f in c) :
    f.val <= sSupFun hc :=
LinearPMap.le_sSup _ (Set.mem_image _ _ _).mpr ⟨f, hf, rfl⟩

/--
theorem `baseEmbedding_le_sSupFun` / 定理 `baseEmbedding_le_sSupFun`

English:
theorem baseEmbedding_le_sSupFun
  statement: {c : Set (Partial seed)}
  proof: by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseEmbedding_le (le_sSupFun hc hf)

中文:
定理 baseEmbedding_le_sSupFun
  结论: {c : Set (Partial seed)}
  证明: by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseEmbedding_le (le_sSupFun hc hf)

Depends on / 依赖: baseEmbedding_le, f.prop.baseEmbedding_le, hnonempty, le_sSupFun, le_trans
-/
theorem baseEmbedding_le_sSupFun {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) : seed.baseEmbedding <= sSupFun hc := by
  obtain ⟨f, hf⟩ := hnonempty
  exact le_trans f.prop.baseEmbedding_le (le_sSupFun hc hf)

/--
theorem `truncLT_mem_range_sSupFun` / 定理 `truncLT_mem_range_sSupFun`

English:
theorem truncLT_mem_range_sSupFun
  statement: {c : Set (Partial seed)}
  proof: by
  obtain hx := x.prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncLT_mem_range)

中文:
定理 truncLT_mem_range_sSupFun
  结论: {c : Set (Partial seed)}
  证明: by
  obtain hx := x.prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncLT_mem_range)

Depends on / 依赖: LinearMap, LinearMap.mem_range, LinearPMap, LinearPMap.domain_sSup, LinearPMap.mem_domain_sSup_iff, LinearPMap.toFun_eq_coe, Set.mem_image, Set.mem_of_mem_of_subset, domain, domain_sSup, hc.mono_comp, hnonempty, hnonempty.image, le_sSupFun, mem_domain_sSup_iff, mem_image, mem_of_mem_of_subset, mem_range, mono_comp, prop.truncLT_mem_range
-/
theorem truncLT_mem_range_sSupFun {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) (x : (sSupFun hc).domain)
    (c : FiniteArchimedeanClass M) :
    toLex ((HahnSeries.truncLTLinearMap K c) (ofLex (sSupFun hc x))) in
    LinearMap.range (sSupFun hc).toFun := by
  obtain hx := x.prop
  simp_rw [sSupFun, LinearPMap.domain_sSup] at hx
  obtain ⟨f, hmem, hf⟩ :=
    (LinearPMap.mem_domain_sSup_iff (hnonempty.image _) (hc.mono_comp (by simp))).mp hx
  obtain ⟨f', hmem', hf'⟩ := (Set.mem_image _ _ _).mp hmem
  obtain h := (hf'.symm ▸ f'.prop.truncLT_mem_range) ⟨x, hf⟩ c
  simp_rw [LinearMap.mem_range, LinearPMap.toFun_eq_coe] at ⊢ h
  obtain ⟨x', hx'⟩ := h
  have hmem' : x'.val in (sSupFun hc).domain := by
    apply Set.mem_of_mem_of_subset x'.prop
    exact hf'.symm ▸ (le_sSupFun hc hmem').1
  refine ⟨⟨x'.val, hmem'⟩, ?_⟩
  have hleft : sSupFun hc ⟨x'.val, hmem'⟩ = f x' := LinearPMap.sSup_apply _ hmem _
  have hright : sSupFun hc x = f ⟨x, hf⟩ := LinearPMap.sSup_apply _ hmem ⟨x, hf⟩
  simpa [hleft, hright] using hx'

/--
theorem `isPartial_sSupFun` / 定理 `isPartial_sSupFun`

English:
theorem isPartial_sSupFun
  statement: [IsOrderedAddMonoid R]
  proof: sSupFun_strictMono hnonempty hc
  baseEmbedding_le := baseEmbedding_le_sSupFun hnonempty hc
  truncLT_mem_range := truncLT_mem_range_sSupFun hnonempty hc

中文:
定理 isPartial_sSupFun
  结论: [IsOrderedAddMonoid R]
  证明: sSupFun_strictMono hnonempty hc
  baseEmbedding_le := baseEmbedding_le_sSupFun hnonempty hc
  truncLT_mem_range := truncLT_mem_range_sSupFun hnonempty hc

Depends on / 依赖: hnonempty, sSupFun_strictMono
-/
theorem isPartial_sSupFun [IsOrderedAddMonoid R]
    {c : Set (Partial seed)} (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) :
    IsPartial seed (sSupFun hc) where
  strictMono := sSupFun_strictMono hnonempty hc
  baseEmbedding_le := baseEmbedding_le_sSupFun hnonempty hc
  truncLT_mem_range := truncLT_mem_range_sSupFun hnonempty hc

/-- Promote `HahnEmbedding.Partial.sSupFun` to a `HahnEmbedding.Partial`. -/
noncomputable
/--
Definition of `sSup` / `sSup` 的定义

English:
definition sSup
  signature: [IsOrderedAddMonoid R] {c : Set (Partial seed)}
  body: ⟨_, isPartial_sSupFun hnonempty hc⟩

中文:
定义 sSup
  签名: [IsOrderedAddMonoid R] {c : Set (Partial seed)}
  定义体: ⟨_, isPartial_sSupFun hnonempty hc⟩

Depends on / 依赖: hnonempty, isPartial_sSupFun
-/
def sSup [IsOrderedAddMonoid R] {c : Set (Partial seed)}
    (hnonempty : c.Nonempty) (hc : DirectedOn (· <= ·) c) : Partial seed :=
  ⟨_, isPartial_sSupFun hnonempty hc⟩

variable (seed) in
/--
theorem `exists_isMax` / 定理 `exists_isMax`

English:
theorem exists_isMax
  given: [IsOrderedAddMonoid R]
  proof: by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf => le_sSupFun hc.directedOn hf⟩

中文:
定理 exists_isMax
  条件: [IsOrderedAddMonoid R]
  证明: by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf => le_sSupFun hc.directedOn hf⟩

Depends on / 依赖: directedOn, hc.directedOn, hnonempty, le_sSupFun, mem_upperBounds, mem_upperBounds.mpr, zorn_le_nonempty
-/
theorem exists_isMax [IsOrderedAddMonoid R] :
    exists f : Partial seed, IsMax f := by
  apply zorn_le_nonempty
  intro c hc hnonempty
  exact ⟨sSup hnonempty hc.directedOn, mem_upperBounds.mpr fun _ hf => le_sSupFun hc.directedOn hf⟩

variable (seed) in
/--
theorem `exists_domain_eq_top` / 定理 `exists_domain_eq_top`

English:
theorem exists_domain_eq_top
  given: [IsOrderedAddMonoid R] [Archimedean R]
  proof: by
  obtain ⟨f, hf⟩ := exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, f.lt_extend hx⟩

中文:
定理 exists_domain_eq_top
  条件: [IsOrderedAddMonoid R] [Archimedean R]
  证明: by
  obtain ⟨f, hf⟩ := exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, f.lt_extend hx⟩

Depends on / 依赖: Submodule, Submodule.eq_top_iff, contrapose, eq_top_iff, exists_isMax, extend, f.extend, f.lt_extend, isMax_iff_forall_not_lt, lt_extend
-/
theorem exists_domain_eq_top [IsOrderedAddMonoid R] [Archimedean R] :
    exists f : Partial seed, f.val.domain = ⊤ := by
  obtain ⟨f, hf⟩ := exists_isMax seed
  refine ⟨f, Submodule.eq_top_iff'.mpr ?_⟩
  rw [isMax_iff_forall_not_lt] at hf
  contrapose! hf with hx
  obtain ⟨x, hx⟩ := hx
  exact ⟨f.extend hx, f.lt_extend hx⟩

end Partial

end HahnEmbedding

/--
theorem `hahnEmbedding_isOrderedModule` / 定理 `hahnEmbedding_isOrderedModule`

English:
theorem hahnEmbedding_isOrderedModule
  statement: [IsOrderedAddMonoid R] [Archimedean R]
  proof: by
  obtain ⟨e, hdomain⟩ := HahnEmbedding.Partial.exists_domain_eq_top h.some
  obtain harch := e.orderTop_eq_archimedeanClassMk
  obtain ⟨⟨fdomain, f⟩, hpartial⟩ := e
  obtain rfl := hdomain
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_, ?_⟩
  · apply hpartial.strictMono.comp
    intro _ 

中文:
定理 hahnEmbedding_isOrderedModule
  结论: [IsOrderedAddMonoid R] [Archimedean R]
  证明: by
  obtain ⟨e, hdomain⟩ := HahnEmbedding.Partial.exists_domain_eq_top h.some
  obtain harch := e.orderTop_eq_archimedeanClassMk
  obtain ⟨⟨fdomain, f⟩, hpartial⟩ := e
  obtain rfl := hdomain
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_, ?_⟩
  · apply hpartial.strictMono.comp
    intro _ 

Depends on / 依赖: HahnEmbedding, HahnEmbedding.Partial.exists_domain_eq_top, LinearMap, LinearMap.id.codRestrict, LinearPMap, LinearPMap.mk_apply, Partial, Subtype, Subtype.coe_lt_coe, codRestrict, coe_lt_coe, e.orderTop_eq_archimedeanClassMk, exists_domain_eq_top, fdomain, h.some, hdomain, hpartial, hpartial.strictMono.comp, mk_apply, orderTop_eq_archimedeanClassMk
-/
theorem hahnEmbedding_isOrderedModule [IsOrderedAddMonoid R] [Archimedean R]
    [h : Nonempty (HahnEmbedding.Seed K M R)] :
    exists f : M ->ₗ[K] Lex R⟦FiniteArchimedeanClass M⟧, StrictMono f ∧
      forall (a : M), .mk a = FiniteArchimedeanClass.withTopOrderIso M (ofLex (f a)).orderTop := by
  obtain ⟨e, hdomain⟩ := HahnEmbedding.Partial.exists_domain_eq_top h.some
  obtain harch := e.orderTop_eq_archimedeanClassMk
  obtain ⟨⟨fdomain, f⟩, hpartial⟩ := e
  obtain rfl := hdomain
  refine ⟨f ∘ₗ LinearMap.id.codRestrict ⊤ (by simp), ?_, ?_⟩
  · apply hpartial.strictMono.comp
    intro _ _ h
    simpa [← Subtype.coe_lt_coe] using h
  · simp_rw [LinearPMap.mk_apply] at harch
    simp [harch]
