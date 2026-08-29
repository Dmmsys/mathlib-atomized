/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Solvable
public import Mathlib.Algebra.Lie.Quotient
public import Mathlib.Algebra.Lie.Normalizer
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Nilpotent.Lemmas

/-!
# Nilpotent Lie algebras

Like groups, Lie algebras admit a natural concept of nilpotency. More generally, any Lie module
carries a natural concept of nilpotency. We define these here via the lower central series.

## Main definitions

  * `LieModule.lowerCentralSeries`
  * `LieModule.IsNilpotent`
  * `LieModule.maxNilpotentSubmodule`
  * `LieAlgebra.maxNilpotentIdeal`

## Tags

lie algebra, lower central series, nilpotent, max nilpotent ideal
-/

@[expose] public section

universe u v w w₁ w₂

section NilpotentModules

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
variable (k : Nat) (N : LieSubmodule R L M)

namespace LieSubmodule

/--
Definition of `lcs` / `lcs` 的定义

English:
definition lcs
  signature: : LieSubmodule R L M -> LieSubmodule R L M
  body: (fun N => ⁅(⊤ : LieIdeal R L), N⁆)^[k]

@[simp]

中文:
定义 lcs
  签名: : LieSubmodule R L M -> LieSubmodule R L M
  定义体: (fun N => ⁅(⊤ : LieIdeal R L), N⁆)^[k]

@[simp]

Depends on / 依赖: LieIdeal
-/
def lcs : LieSubmodule R L M -> LieSubmodule R L M :=
  (fun N => ⁅(⊤ : LieIdeal R L), N⁆)^[k]

@[simp]
/--
theorem `lcs_zero` / 定理 `lcs_zero`

English:
theorem lcs_zero
  given: (N : LieSubmodule R L M)
  statement: N.lcs 0 = N
  proof: rfl

@[simp]

中文:
定理 lcs_zero
  条件: (N : LieSubmodule R L M)
  结论: N.lcs 0 = N
  证明: rfl

@[simp]
-/
theorem lcs_zero (N : LieSubmodule R L M) : N.lcs 0 = N :=
  rfl

@[simp]
/--
theorem `lcs_succ` / 定理 `lcs_succ`

English:
theorem lcs_succ
  statement: N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆
  proof: Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N

@[simp]

中文:
定理 lcs_succ
  结论: N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆
  证明: Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N

@[simp]

Depends on / 依赖: Function, Function.iterate_succ_apply, SnakeLemma, iterate_succ_apply
-/
theorem lcs_succ : N.lcs (k + 1) = ⁅(⊤ : LieIdeal R L), N.lcs k⁆ :=
  Function.iterate_succ_apply' (fun N' => ⁅⊤, N'⁆) k N

@[simp]
/--
lemma `lcs_sup` / 引理 `lcs_sup`

English:
lemma lcs_sup
  given: {N₁ N₂ : LieSubmodule R L M} {k : Nat}
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp only [LieSubmodule.lcs_succ, ih, LieSubmodule.lie_sup]

中文:
引理 lcs_sup
  条件: {N₁ N₂ : LieSubmodule R L M} {k : 自然数}
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp only [LieSubmodule.lcs_succ, ih, LieSubmodule.lie_sup]

Depends on / 依赖: LieSubmodule, LieSubmodule.lcs_succ, LieSubmodule.lie_sup, lcs_succ, lie_sup
-/
lemma lcs_sup {N₁ N₂ : LieSubmodule R L M} {k : Nat} :
    (N₁ ⊔ N₂).lcs k = N₁.lcs k ⊔ N₂.lcs k := by
  induction k with
  | zero => simp
  | succ k ih => simp only [LieSubmodule.lcs_succ, ih, LieSubmodule.lie_sup]

end LieSubmodule

namespace LieModule

variable (R L M)

/--
Definition of `lowerCentralSeries` / `lowerCentralSeries` 的定义

English:
definition lowerCentralSeries
  signature: : LieSubmodule R L M
  body: (⊤ : LieSubmodule R L M).lcs k

@[simp]

中文:
定义 lowerCentralSeries
  签名: : LieSubmodule R L M
  定义体: (⊤ : LieSubmodule R L M).lcs k

@[simp]

Depends on / 依赖: LieSubmodule, SnakeLemma, SnakeLemma.exact_
-/
def lowerCentralSeries : LieSubmodule R L M :=
  (⊤ : LieSubmodule R L M).lcs k

@[simp]
/--
theorem `lowerCentralSeries_zero` / 定理 `lowerCentralSeries_zero`

English:
theorem lowerCentralSeries_zero
  statement: lowerCentralSeries R L M 0 = ⊤
  proof: rfl

@[simp]

中文:
定理 lowerCentralSeries_zero
  结论: lowerCentralSeries R L M 0 = ⊤
  证明: rfl

@[simp]
-/
theorem lowerCentralSeries_zero : lowerCentralSeries R L M 0 = ⊤ :=
  rfl

@[simp]
/--
theorem `lowerCentralSeries_succ` / 定理 `lowerCentralSeries_succ`

English:
theorem lowerCentralSeries_succ
  proof: (⊤ : LieSubmodule R L M).lcs_succ k

中文:
定理 lowerCentralSeries_succ
  证明: (⊤ : LieSubmodule R L M).lcs_succ k

Depends on / 依赖: LieSubmodule, lcs_succ
-/
theorem lowerCentralSeries_succ :
    lowerCentralSeries R L M (k + 1) = ⁅(⊤ : LieIdeal R L), lowerCentralSeries R L M k⁆ :=
  (⊤ : LieSubmodule R L M).lcs_succ k

/--
theorem `coe_lowerCentralSeries_eq_int_aux` / 定理 `coe_lowerCentralSeries_eq_int_aux`

English:
theorem coe_lowerCentralSeries_eq_int_aux
  statement: (R₁ R₂ L M : Type*)
  proof: lowerCentralSeries R₂ L M k; let S : Set M := {⁅a, b⁆ | (a : L) (b in I)}
    (Submodule.span R₁ S : Set M) <= (Submodule.span R₂ S : Set M) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | a

中文:
定理 coe_lowerCentralSeries_eq_int_aux
  结论: (R₁ R₂ L M : 类型)
  证明: lowerCentralSeries R₂ L M k; let S : Set M := {⁅a, b⁆ | (a : L) (b in I)}
    (Submodule.span R₁ S : Set M) <= (Submodule.span R₂ S : Set M) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | a
-/
private theorem coe_lowerCentralSeries_eq_int_aux (R₁ R₂ L M : Type*)
    [CommRing R₁] [CommRing R₂] [AddCommGroup M]
    [LieRing L] [LieAlgebra R₁ L] [LieAlgebra R₂ L] [Module R₁ M] [Module R₂ M] [LieRingModule L M]
    [LieModule R₁ L M] (k : Nat) :
    let I := lowerCentralSeries R₂ L M k; let S : Set M := {⁅a, b⁆ | (a : L) (b in I)}
    (Submodule.span R₁ S : Set M) <= (Submodule.span R₂ S : Set M) := by
  intro I S x hx
  simp only [SetLike.mem_coe] at hx ⊢
  induction hx using Submodule.closure_induction with
  | zero => exact Submodule.zero_mem _
  | add y z hy₁ hz₁ hy₂ hz₂ => exact Submodule.add_mem _ hy₂ hz₂
  | smul_mem c y hy =>
      obtain ⟨a, b, hb, rfl⟩ := hy
      rw [← smul_lie]
      exact Submodule.subset_span ⟨c • a, b, hb, rfl⟩

/--
theorem `coe_lowerCentralSeries_eq_int` / 定理 `coe_lowerCentralSeries_eq_int`

English:
theorem coe_lowerCentralSeries_eq_int
  given: [LieModule R L M] (k : Nat)
  proof: by
  rw [← LieSubmodule.coe_toSubmodule]; rw [← LieSubmodule.coe_toSubmodule]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lowerCentralSeries_succ]; rw [lowerCentralSeries_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw

中文:
定理 coe_lowerCentralSeries_eq_int
  条件: [LieModule R L M] (k : 自然数)
  证明: by
  rw [← LieSubmodule.coe_toSubmodule]; rw [← LieSubmodule.coe_toSubmodule]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lowerCentralSeries_succ]; rw [lowerCentralSeries_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw

Depends on / 依赖: LieSubmodule, LieSubmodule.coe_toSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top, Set.ext_iff, SetLike, SetLike.mem_coe, coe_lowerCentralSeries_eq_int_aux, coe_toSubmodule, ext_iff, le_antisymm, lieIdeal_oper_eq_linear_span, lowerCentralSeries_succ, mem_coe, mem_toSubmodule, mem_top, true_and
-/
theorem coe_lowerCentralSeries_eq_int [LieModule R L M] (k : Nat) :
    (lowerCentralSeries R L M k : Set M) = (lowerCentralSeries Int L M k : Set M) := by
  rw [← LieSubmodule.coe_toSubmodule]; rw [← LieSubmodule.coe_toSubmodule]
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lowerCentralSeries_succ]; rw [lowerCentralSeries_succ]
    rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']
    rw [Set.ext_iff] at ih
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule] at ih
    simp only [LieSubmodule.mem_top, ih, true_and]
    apply le_antisymm
    · exact coe_lowerCentralSeries_eq_int_aux _ _ L M k
    · simp only [← ih]
      exact coe_lowerCentralSeries_eq_int_aux _ _ L M k

end LieModule

namespace LieSubmodule

open LieModule

/--
theorem `lcs_le_self` / 定理 `lcs_le_self`

English:
theorem lcs_le_self
  statement: N.lcs k <= N
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ]
    exact (LieSubmodule.mono_lie_right ⊤ ih).trans (N.lie_le_right ⊤)

中文:
定理 lcs_le_self
  结论: N.lcs k <= N
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ]
    exact (LieSubmodule.mono_lie_right ⊤ ih).trans (N.lie_le_right ⊤)

Depends on / 依赖: LieSubmodule, LieSubmodule.mono_lie_right, N.lie_le_right, lcs_succ, lie_le_right, mono_lie_right
-/
theorem lcs_le_self : N.lcs k <= N := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ]
    exact (LieSubmodule.mono_lie_right ⊤ ih).trans (N.lie_le_right ⊤)

variable [LieModule R L M]

/--
theorem `lowerCentralSeries_eq_lcs_comap` / 定理 `lowerCentralSeries_eq_lcs_comap`

English:
theorem lowerCentralSeries_eq_lcs_comap
  statement: lowerCentralSeries R L N k = (N.lcs k).comap N.incl
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ, lowerCentralSeries_succ] at ih ⊢
    have : N.lcs k <= N.incl.range := by
      rw [N.range_incl]
      apply lcs_le_self
    rw [ih]; rw [LieSubmodule.comap_bracket_eq _ N.incl _ N.ker_incl this]

中文:
定理 lowerCentralSeries_eq_lcs_comap
  结论: lowerCentralSeries R L N k = (N.lcs k).comap N.incl
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ, lowerCentralSeries_succ] at ih ⊢
    have : N.lcs k <= N.incl.range := by
      rw [N.range_incl]
      apply lcs_le_self
    rw [ih]; rw [LieSubmodule.comap_bracket_eq _ N.incl _ N.ker_incl this]

Depends on / 依赖: LieSubmodule, LieSubmodule.comap_bracket_eq, N.incl, N.incl.range, N.ker_incl, N.lcs, N.range_incl, comap_bracket_eq, ker_incl, lcs_le_self, lcs_succ, lowerCentralSeries_succ, range_incl
-/
theorem lowerCentralSeries_eq_lcs_comap : lowerCentralSeries R L N k = (N.lcs k).comap N.incl := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lcs_succ, lowerCentralSeries_succ] at ih ⊢
    have : N.lcs k <= N.incl.range := by
      rw [N.range_incl]
      apply lcs_le_self
    rw [ih]; rw [LieSubmodule.comap_bracket_eq _ N.incl _ N.ker_incl this]

/--
theorem `lowerCentralSeries_map_eq_lcs` / 定理 `lowerCentralSeries_map_eq_lcs`

English:
theorem lowerCentralSeries_map_eq_lcs
  statement: (lowerCentralSeries R L N k).map N.incl = N.lcs k
  proof: by
  rw [lowerCentralSeries_eq_lcs_comap]; rw [LieSubmodule.map_comap_incl]; rw [inf_eq_right]
  apply lcs_le_self

中文:
定理 lowerCentralSeries_map_eq_lcs
  结论: (lowerCentralSeries R L N k).map N.incl = N.lcs k
  证明: by
  rw [lowerCentralSeries_eq_lcs_comap]; rw [LieSubmodule.map_comap_incl]; rw [inf_eq_right]
  apply lcs_le_self

Depends on / 依赖: LieSubmodule, LieSubmodule.map_comap_incl, inf_eq_right, lcs_le_self, lowerCentralSeries_eq_lcs_comap, map_comap_incl
-/
theorem lowerCentralSeries_map_eq_lcs : (lowerCentralSeries R L N k).map N.incl = N.lcs k := by
  rw [lowerCentralSeries_eq_lcs_comap]; rw [LieSubmodule.map_comap_incl]; rw [inf_eq_right]
  apply lcs_le_self

/--
theorem `lowerCentralSeries_eq_bot_iff_lcs_eq_bot` / 定理 `lowerCentralSeries_eq_bot_iff_lcs_eq_bot`

English:
theorem lowerCentralSeries_eq_bot_iff_lcs_eq_bot
  proof: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← N.lowerCentralSeries_map_eq_lcs, ← LieModuleHom.le_ker_iff_map]
    simpa
  · rw [N.lowerCentralSeries_eq_lcs_comap, comap_incl_eq_bot]
    simp [h]

中文:
定理 lowerCentralSeries_eq_bot_iff_lcs_eq_bot
  证明: by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← N.lowerCentralSeries_map_eq_lcs, ← LieModuleHom.le_ker_iff_map]
    simpa
  · rw [N.lowerCentralSeries_eq_lcs_comap, comap_incl_eq_bot]
    simp [h]

Depends on / 依赖: LieModuleHom, LieModuleHom.le_ker_iff_map, N.lowerCentralSeries_eq_lcs_comap, N.lowerCentralSeries_map_eq_lcs, comap_incl_eq_bot, le_ker_iff_map, lowerCentralSeries_eq_lcs_comap, lowerCentralSeries_map_eq_lcs
-/
theorem lowerCentralSeries_eq_bot_iff_lcs_eq_bot :
    lowerCentralSeries R L N k = ⊥ ↔ lcs k N = ⊥ := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← N.lowerCentralSeries_map_eq_lcs, ← LieModuleHom.le_ker_iff_map]
    simpa
  · rw [N.lowerCentralSeries_eq_lcs_comap, comap_incl_eq_bot]
    simp [h]

end LieSubmodule

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
variable (R L M)

/--
theorem `antitone_lowerCentralSeries` / 定理 `antitone_lowerCentralSeries`

English:
theorem antitone_lowerCentralSeries
  statement: Antitone lowerCentralSeries R L M
  proof: by
  intro l k
  induction k generalizing l with
  | zero => exact fun h => (Nat.le_zero.mp h).symm ▸ le_rfl
  | succ k ih =>
    intro h
    rcases Nat.of_le_succ h with (hk | hk)
    · rw [lowerCentralSeries_succ]
      exact (LieSubmodule.mono_lie_right ⊤ (ih hk)).trans (LieSubmodule.lie_le_right

中文:
定理 antitone_lowerCentralSeries
  结论: Antitone lowerCentralSeries R L M
  证明: by
  intro l k
  induction k generalizing l with
  | zero => exact fun h => (Nat.le_zero.mp h).symm ▸ le_rfl
  | succ k ih =>
    intro h
    rcases Nat.of_le_succ h with (hk | hk)
    · rw [lowerCentralSeries_succ]
      exact (LieSubmodule.mono_lie_right ⊤ (ih hk)).trans (LieSubmodule.lie_le_right

Depends on / 依赖: LieSubmodule, LieSubmodule.lie_le_right, LieSubmodule.mono_lie_right, Nat.le_zero.mp, Nat.of_le_succ, generalizing, hk.symm, le_rfl, le_zero, lie_le_right, lowerCentralSeries_succ, mono_lie_right, of_le_succ
-/
theorem antitone_lowerCentralSeries : Antitone lowerCentralSeries R L M := by
  intro l k
  induction k generalizing l with
  | zero => exact fun h => (Nat.le_zero.mp h).symm ▸ le_rfl
  | succ k ih =>
    intro h
    rcases Nat.of_le_succ h with (hk | hk)
    · rw [lowerCentralSeries_succ]
      exact (LieSubmodule.mono_lie_right ⊤ (ih hk)).trans (LieSubmodule.lie_le_right _ _)
    · exact hk.symm ▸ le_rfl

/--
theorem `eventually_iInf_lowerCentralSeries_eq` / 定理 `eventually_iInf_lowerCentralSeries_eq`

English:
theorem eventually_iInf_lowerCentralSeries_eq
  given: [IsArtinian R M]
  proof: by
  have h_wf : WellFoundedGT (LieSubmodule R L M)ᵒᵈ :=
    LieSubmodule.wellFoundedLT_of_isArtinian R L M
  obtain ⟨n, hn : forall m, n <= m -> lowerCentralSeries R L M n = lowerCentralSeries R L M m⟩ :=
    h_wf.monotone_chain_condition ⟨_, antitone_lowerCentralSeries R L M⟩
  refine Filter.event

中文:
定理 eventually_iInf_lowerCentralSeries_eq
  条件: [IsArtinian R M]
  证明: by
  have h_wf : WellFoundedGT (LieSubmodule R L M)ᵒᵈ :=
    LieSubmodule.wellFoundedLT_of_isArtinian R L M
  obtain ⟨n, hn : forall m, n <= m -> lowerCentralSeries R L M n = lowerCentralSeries R L M m⟩ :=
    h_wf.monotone_chain_condition ⟨_, antitone_lowerCentralSeries R L M⟩
  refine Filter.event

Depends on / 依赖: Filter, Filter.eventually_atTop.mpr, LieSubmodule, LieSubmodule.wellFoundedLT_of_isArtinian, WellFoundedGT, antitone_lowerCentralSeries, eventually_atTop, h_wf, h_wf.monotone_chain_condition, hl.trans, iInf_le, le_antisymm, le_iInf, le_of_lt, le_or_gt, lowerCentralSeries, monotone_chain_condition, wellFoundedLT_of_isArtinian
-/
theorem eventually_iInf_lowerCentralSeries_eq [IsArtinian R M] :
    forallᶠ l in Filter.atTop, ⨅ k, lowerCentralSeries R L M k = lowerCentralSeries R L M l := by
  have h_wf : WellFoundedGT (LieSubmodule R L M)ᵒᵈ :=
    LieSubmodule.wellFoundedLT_of_isArtinian R L M
  obtain ⟨n, hn : forall m, n <= m -> lowerCentralSeries R L M n = lowerCentralSeries R L M m⟩ :=
    h_wf.monotone_chain_condition ⟨_, antitone_lowerCentralSeries R L M⟩
  refine Filter.eventually_atTop.mpr ⟨n, fun l hl => le_antisymm (iInf_le _ _) (le_iInf fun m => ?_)⟩
  rcases le_or_gt l m with h | h
  · rw [← hn _ hl, ← hn _ (hl.trans h)]
  · exact antitone_lowerCentralSeries R L M (le_of_lt h)

/--
theorem `trivial_iff_lower_central_eq_bot` / 定理 `trivial_iff_lower_central_eq_bot`

English:
theorem trivial_iff_lower_central_eq_bot
  statement: IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥
  proof: by
  constructor <;> intro h
  · simp
  · rw [LieSubmodule.eq_bot_iff] at h; apply IsTrivial.mk; intro x m; apply h
    apply LieSubmodule.subset_lieSpan
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_prop, true_and, Set.mem_ofPred]
    exact ⟨x, m, rfl⟩

中文:
定理 trivial_iff_lower_central_eq_bot
  结论: IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥
  证明: by
  constructor <;> intro h
  · simp
  · rw [LieSubmodule.eq_bot_iff] at h; apply IsTrivial.mk; intro x m; apply h
    apply LieSubmodule.subset_lieSpan
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_prop, true_and, Set.mem_ofPred]
    exact ⟨x, m, rfl⟩

Depends on / 依赖: IsTrivial, IsTrivial.mk, LieSubmodule, LieSubmodule.eq_bot_iff, LieSubmodule.mem_top, LieSubmodule.subset_lieSpan, Set.mem_ofPred, Subtype, Subtype.exists, eq_bot_iff, exists_prop, mem_ofPred, mem_top, subset_lieSpan, true_and
-/
theorem trivial_iff_lower_central_eq_bot : IsTrivial L M ↔ lowerCentralSeries R L M 1 = ⊥ := by
  constructor <;> intro h
  · simp
  · rw [LieSubmodule.eq_bot_iff] at h; apply IsTrivial.mk; intro x m; apply h
    apply LieSubmodule.subset_lieSpan
    simp only [Subtype.exists, LieSubmodule.mem_top, exists_prop, true_and, Set.mem_ofPred]
    exact ⟨x, m, rfl⟩

section
variable [LieModule R L M]

/--
theorem `iterate_toEnd_mem_lowerCentralSeries` / 定理 `iterate_toEnd_mem_lowerCentralSeries`

English:
theorem iterate_toEnd_mem_lowerCentralSeries
  given: (x : L) (m : M) (k : Nat)
  proof: by
  induction k with
  | zero => simp only [Function.iterate_zero, lowerCentralSeries_zero, LieSubmodule.mem_top]
  | succ k ih =>
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ',
      toEnd_apply_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x

中文:
定理 iterate_toEnd_mem_lowerCentralSeries
  条件: (x : L) (m : M) (k : 自然数)
  证明: by
  induction k with
  | zero => simp only [Function.iterate_zero, lowerCentralSeries_zero, LieSubmodule.mem_top]
  | succ k ih =>
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ',
      toEnd_apply_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, Function.iterate_zero, LieSubmodule, LieSubmodule.lie_mem_lie, LieSubmodule.mem_top, comp_apply, iterate_succ, iterate_zero, lie_mem_lie, lowerCentralSeries_succ, lowerCentralSeries_zero, mem_top, toEnd_apply_apply
-/
theorem iterate_toEnd_mem_lowerCentralSeries (x : L) (m : M) (k : Nat) :
    (toEnd R L M x)^[k] m in lowerCentralSeries R L M k := by
  induction k with
  | zero => simp only [Function.iterate_zero, lowerCentralSeries_zero, LieSubmodule.mem_top]
  | succ k ih =>
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ',
      toEnd_apply_apply]
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ih

/--
theorem `iterate_toEnd_mem_lowerCentralSeries₂` / 定理 `iterate_toEnd_mem_lowerCentralSeries₂`

English:
theorem iterate_toEnd_mem_lowerCentralSeries₂
  given: (x y : L) (m : M) (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 * k.succ = (2 * k + 1) + 1 := rfl
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ', hk,
      toEnd_apply_apply, LinearMap.coe_comp, toEnd_apply_apply]
    refine LieSubmodule.lie_mem_lie (LieS

中文:
定理 iterate_toEnd_mem_lowerCentralSeries₂
  条件: (x y : L) (m : M) (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 * k.succ = (2 * k + 1) + 1 := rfl
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ', hk,
      toEnd_apply_apply, LinearMap.coe_comp, toEnd_apply_apply]
    refine LieSubmodule.lie_mem_lie (LieS

Depends on / 依赖: Function, Function.comp_apply, Function.iterate_succ, LieSubmodule, LieSubmodule.lie_mem_lie, LieSubmodule.mem_top, LinearMap, LinearMap.coe_comp, coe_comp, comp_apply, iterate_succ, k.succ, lie_mem_lie, lowerCentralSeries_succ, mem_top, toEnd_apply_apply
-/
theorem iterate_toEnd_mem_lowerCentralSeries₂ (x y : L) (m : M) (k : Nat) :
    (toEnd R L M x ∘ₗ toEnd R L M y)^[k] m in
      lowerCentralSeries R L M (2 * k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : 2 * k.succ = (2 * k + 1) + 1 := rfl
    simp only [lowerCentralSeries_succ, Function.comp_apply, Function.iterate_succ', hk,
      toEnd_apply_apply, LinearMap.coe_comp, toEnd_apply_apply]
    refine LieSubmodule.lie_mem_lie (LieSubmodule.mem_top x) ?_
    exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top y) ih

variable {R L M}

/--
theorem `map_lowerCentralSeries_le` / 定理 `map_lowerCentralSeries_le`

English:
theorem map_lowerCentralSeries_le
  given: (f : M ->ₗ⁅R,L⁆ M₂)
  proof: by
  induction k with
  | zero => simp only [lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    exact LieSubmodule.mono_lie_right ⊤ ih

中文:
定理 map_lowerCentralSeries_le
  条件: (f : M ->ₗ⁅R,L⁆ M₂)
  证明: by
  induction k with
  | zero => simp only [lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    exact LieSubmodule.mono_lie_right ⊤ ih

Depends on / 依赖: LieModule, LieModule.lowerCentralSeries_succ, LieSubmodule, LieSubmodule.map_bracket_eq, LieSubmodule.mono_lie_right, le_top, lowerCentralSeries_succ, lowerCentralSeries_zero, map_bracket_eq, mono_lie_right
-/
theorem map_lowerCentralSeries_le (f : M ->ₗ⁅R,L⁆ M₂) :
    (lowerCentralSeries R L M k).map f <= lowerCentralSeries R L M₂ k := by
  induction k with
  | zero => simp only [lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    exact LieSubmodule.mono_lie_right ⊤ ih

/--
lemma `map_lowerCentralSeries_eq` / 引理 `map_lowerCentralSeries_eq`

English:
lemma map_lowerCentralSeries_eq
  given: {f : M ->ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f)
  proof: by
  apply le_antisymm (map_lowerCentralSeries_le k f)
  induction k with
  | zero =>
    rwa [lowerCentralSeries_zero, lowerCentralSeries_zero, top_le_iff, f.map_top,
      f.range_eq_top]
  | succ =>
    simp only [lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    apply LieSubmodule.mono_l

中文:
引理 map_lowerCentralSeries_eq
  条件: {f : M ->ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f)
  证明: by
  apply le_antisymm (map_lowerCentralSeries_le k f)
  induction k with
  | zero =>
    rwa [lowerCentralSeries_zero, lowerCentralSeries_zero, top_le_iff, f.map_top,
      f.range_eq_top]
  | succ =>
    simp only [lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    apply LieSubmodule.mono_l

Depends on / 依赖: LieSubmodule, LieSubmodule.map_bracket_eq, LieSubmodule.mono_lie_right, f.map_top, f.range_eq_top, le_antisymm, lowerCentralSeries_succ, lowerCentralSeries_zero, map_bracket_eq, map_lowerCentralSeries_le, map_top, mono_lie_right, range_eq_top, top_le_iff
-/
lemma map_lowerCentralSeries_eq {f : M ->ₗ⁅R,L⁆ M₂} (hf : Function.Surjective f) :
    (lowerCentralSeries R L M k).map f = lowerCentralSeries R L M₂ k := by
  apply le_antisymm (map_lowerCentralSeries_le k f)
  induction k with
  | zero =>
    rwa [lowerCentralSeries_zero, lowerCentralSeries_zero, top_le_iff, f.map_top,
      f.range_eq_top]
  | succ =>
    simp only [lowerCentralSeries_succ, LieSubmodule.map_bracket_eq]
    apply LieSubmodule.mono_lie_right
    assumption

end

open LieAlgebra

/--
theorem `derivedSeries_le_lowerCentralSeries` / 定理 `derivedSeries_le_lowerCentralSeries`

English:
theorem derivedSeries_le_lowerCentralSeries
  given: (k : Nat)
  proof: by
  induction k with
  | zero => rw [derivedSeries_def, derivedSeriesOfIdeal_zero, lowerCentralSeries_zero]
  | succ k h =>
    have h' : derivedSeries R L k <= ⊤ := by simp only [le_top]
    rw [derivedSeries_def]; rw [derivedSeriesOfIdeal_succ]; rw [lowerCentralSeries_succ]
    exact LieSubmodule

中文:
定理 derivedSeries_le_lowerCentralSeries
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => rw [derivedSeries_def, derivedSeriesOfIdeal_zero, lowerCentralSeries_zero]
  | succ k h =>
    have h' : derivedSeries R L k <= ⊤ := by simp only [le_top]
    rw [derivedSeries_def]; rw [derivedSeriesOfIdeal_succ]; rw [lowerCentralSeries_succ]
    exact LieSubmodule

Depends on / 依赖: LieSubmodule, LieSubmodule.mono_lie, derivedSeries, derivedSeriesOfIdeal_succ, derivedSeriesOfIdeal_zero, derivedSeries_def, le_top, lowerCentralSeries_succ, lowerCentralSeries_zero, mono_lie
-/
theorem derivedSeries_le_lowerCentralSeries (k : Nat) :
    derivedSeries R L k <= lowerCentralSeries R L L k := by
  induction k with
  | zero => rw [derivedSeries_def, derivedSeriesOfIdeal_zero, lowerCentralSeries_zero]
  | succ k h =>
    have h' : derivedSeries R L k <= ⊤ := by simp only [le_top]
    rw [derivedSeries_def]; rw [derivedSeriesOfIdeal_succ]; rw [lowerCentralSeries_succ]
    exact LieSubmodule.mono_lie h' h

/-- A Lie module is nilpotent if its lower central series reaches 0 (in a finite number of
steps). -/
@[mk_iff isNilpotent_iff_int]
/--
Definition of `IsNilpotent` / `IsNilpotent` 的定义

English:
class IsNilpotent
  parameters: : Prop where
  axioms and operations (2):
    - mk_int : :
    - nilpotent_int : exists k, lowerCentralSeries Int L M k = ⊥

中文:
类 IsNilpotent
  参数: : 命题 where
  公理与运算 (2 个):
    - mk_int : :
    - nilpotent_int : 存在 k, lowerCentralSeries 整数 L M k = ⊥
-/
class IsNilpotent : Prop where
  mk_int ::
  nilpotent_int : exists k, lowerCentralSeries Int L M k = ⊥

section

variable [LieModule R L M]

/--
lemma `isNilpotent_iff` / 引理 `isNilpotent_iff`

English:
lemma isNilpotent_iff
  proof: by
  simp [isNilpotent_iff_int, SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]

中文:
引理 isNilpotent_iff
  证明: by
  simp [isNilpotent_iff_int, SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]

Depends on / 依赖: SetLike, SetLike.ext, _iff, coe_lowerCentralSeries_eq_int, isNilpotent_iff_int
-/
lemma isNilpotent_iff :
    IsNilpotent L M ↔ exists k, lowerCentralSeries R L M k = ⊥ := by
  simp [isNilpotent_iff_int, SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]

/--
lemma `IsNilpotent.nilpotent` / 引理 `IsNilpotent.nilpotent`

English:
lemma IsNilpotent.nilpotent
  given: [IsNilpotent L M]
  statement: exists k, lowerCentralSeries R L M k = ⊥
  proof: (isNilpotent_iff R L M).mp ‹_›

中文:
引理 IsNilpotent.nilpotent
  条件: [IsNilpotent L M]
  结论: 存在 k, lowerCentralSeries R L M k = ⊥
  证明: (isNilpotent_iff R L M).mp ‹_›

Depends on / 依赖: isNilpotent_iff
-/
lemma IsNilpotent.nilpotent [IsNilpotent L M] : exists k, lowerCentralSeries R L M k = ⊥ :=
  (isNilpotent_iff R L M).mp ‹_›

variable {R L} in
/--
lemma `IsNilpotent.mk` / 引理 `IsNilpotent.mk`

English:
lemma IsNilpotent.mk
  given: {k : Nat} (h : lowerCentralSeries R L M k = ⊥)
  statement: IsNilpotent L M
  proof: (isNilpotent_iff R L M).mpr ⟨k, h⟩

中文:
引理 IsNilpotent.mk
  条件: {k : 自然数} (h : lowerCentralSeries R L M k = ⊥)
  结论: IsNilpotent L M
  证明: (isNilpotent_iff R L M).mpr ⟨k, h⟩
-/
lemma IsNilpotent.mk {k : Nat} (h : lowerCentralSeries R L M k = ⊥) : IsNilpotent L M :=
  (isNilpotent_iff R L M).mpr ⟨k, h⟩

/--
lemma `iInf_lowerCentralSeries_eq_bot_of_isNilpotent` / 引理 `iInf_lowerCentralSeries_eq_bot_of_isNilpotent`

English:
lemma iInf_lowerCentralSeries_eq_bot_of_isNilpotent
  given: [IsNilpotent L M]
  proof: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [eq_bot_iff]; rw [← hk]
  exact iInf_le _ _

中文:
引理 iInf_lowerCentralSeries_eq_bot_of_isNilpotent
  条件: [IsNilpotent L M]
  证明: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [eq_bot_iff]; rw [← hk]
  exact iInf_le _ _
-/
@[simp] lemma iInf_lowerCentralSeries_eq_bot_of_isNilpotent [IsNilpotent L M] :
    ⨅ k, lowerCentralSeries R L M k = ⊥ := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [eq_bot_iff]; rw [← hk]
  exact iInf_le _ _

end

section
variable {R L M}
variable [LieModule R L M]

/--
theorem `_root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot` / 定理 `_root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot`

English:
theorem _root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot
  given: (N : LieSubmodule R L M)
  proof: by
  rw [isNilpotent_iff R L N]
  refine exists_congr fun k => ?_
  rw [N.lowerCentralSeries_eq_lcs_comap k]; rw [LieSubmodule.comap_incl_eq_bot]; rw [inf_eq_right.mpr (N.lcs_le_self k)]

中文:
定理 _root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot
  条件: (N : LieSubmodule R L M)
  证明: by
  rw [isNilpotent_iff R L N]
  refine exists_congr fun k => ?_
  rw [N.lowerCentralSeries_eq_lcs_comap k]; rw [LieSubmodule.comap_incl_eq_bot]; rw [inf_eq_right.mpr (N.lcs_le_self k)]

Depends on / 依赖: LieSubmodule, LieSubmodule.comap_incl_eq_bot, N.lcs_le_self, N.lowerCentralSeries_eq_lcs_comap, comap_incl_eq_bot, exists_congr, inf_eq_right, inf_eq_right.mpr, isNilpotent_iff, lcs_le_self, lowerCentralSeries_eq_lcs_comap
-/
theorem _root_.LieSubmodule.isNilpotent_iff_exists_lcs_eq_bot (N : LieSubmodule R L M) :
    LieModule.IsNilpotent L N ↔ exists k, N.lcs k = ⊥ := by
  rw [isNilpotent_iff R L N]
  refine exists_congr fun k => ?_
  rw [N.lowerCentralSeries_eq_lcs_comap k]; rw [LieSubmodule.comap_incl_eq_bot]; rw [inf_eq_right.mpr (N.lcs_le_self k)]

variable (R L M)

instance (priority := 100) trivialIsNilpotent [IsTrivial L M] : IsNilpotent L M :=
  ⟨by use 1; simp⟩

/--
Instance `instIsNilpotentSup` / 实例 `instIsNilpotentSup`

English:
instance instIsNilpotentSup
  signature: (M₁ M₂ : LieSubmodule R L M) [IsNilpotent L M₁] [IsNilpotent L M₂]
  body: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M₁
  obtain ⟨l, hl⟩ := IsNilpotent.nilpotent R L M₂
  let lcs_eq_bot {m n} (N : LieSubmodule R L M) (le : m <= n) (hn : lowerCentralSeries R L N m = ⊥) :
    lowerCentralSeries R L N n = ⊥ := by
    simpa [hn] using antitone_lowerCentralSeries R L N l

中文:
实例 instIsNilpotentSup
  签名: (M₁ M₂ : LieSubmodule R L M) [IsNilpotent L M₁] [IsNilpotent L M₂]
  定义体: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M₁
  obtain ⟨l, hl⟩ := IsNilpotent.nilpotent R L M₂
  let lcs_eq_bot {m n} (N : LieSubmodule R L M) (le : m <= n) (hn : lowerCentralSeries R L N m = ⊥) :
    lowerCentralSeries R L N n = ⊥ := by
    simpa [hn] using antitone_lowerCentralSeries R L N l

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubmodule, Nat.le_max_left, Nat.le_max_right, antitone_lowerCentralSeries, isNilpotent_iff, lcs_eq_bot, le_max_left, le_max_right, lowerCentralSeries, nilpotent
-/
instance instIsNilpotentSup (M₁ M₂ : LieSubmodule R L M) [IsNilpotent L M₁] [IsNilpotent L M₂] :
    IsNilpotent L (M₁ ⊔ M₂ : LieSubmodule R L M) := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M₁
  obtain ⟨l, hl⟩ := IsNilpotent.nilpotent R L M₂
  let lcs_eq_bot {m n} (N : LieSubmodule R L M) (le : m <= n) (hn : lowerCentralSeries R L N m = ⊥) :
    lowerCentralSeries R L N n = ⊥ := by
    simpa [hn] using antitone_lowerCentralSeries R L N le
  have h₁ : lowerCentralSeries R L M₁ (k ⊔ l) = ⊥ := lcs_eq_bot M₁ (Nat.le_max_left k l) hk
  have h₂ : lowerCentralSeries R L M₂ (k ⊔ l) = ⊥ := lcs_eq_bot M₂ (Nat.le_max_right k l) hl
  refine (isNilpotent_iff R L (M₁ + M₂)).mpr ⟨k ⊔ l, ?_⟩
  simp [LieSubmodule.add_eq_sup, (M₁ ⊔ M₂).lowerCentralSeries_eq_lcs_comap, LieSubmodule.lcs_sup,
    (M₁.lowerCentralSeries_eq_bot_iff_lcs_eq_bot (k ⊔ l)).1 h₁,
    (M₂.lowerCentralSeries_eq_bot_iff_lcs_eq_bot (k ⊔ l)).1 h₂, LieSubmodule.comap_incl_eq_bot]

/--
theorem `exists_forall_pow_toEnd_eq_zero` / 定理 `exists_forall_pow_toEnd_eq_zero`

English:
theorem exists_forall_pow_toEnd_eq_zero
  given: [IsNilpotent L M]
  proof: by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  use k
  intro x; ext m
  rw [Module.End.pow_apply]; rw [LinearMap.zero_apply]; rw [← @LieSubmodule.mem_bot R L M]; rw [← hM]
  exact iterate_toEnd_mem_lowerCentralSeries R L M x m k

中文:
定理 exists_forall_pow_toEnd_eq_zero
  条件: [IsNilpotent L M]
  证明: by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  use k
  intro x; ext m
  rw [Module.End.pow_apply]; rw [LinearMap.zero_apply]; rw [← @LieSubmodule.mem_bot R L M]; rw [← hM]
  exact iterate_toEnd_mem_lowerCentralSeries R L M x m k

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubmodule, LieSubmodule.mem_bot, LinearMap, LinearMap.zero_apply, Module, Module.End.pow_apply, iterate_toEnd_mem_lowerCentralSeries, mem_bot, nilpotent, pow_apply, zero_apply
-/
theorem exists_forall_pow_toEnd_eq_zero [IsNilpotent L M] :
    exists k : Nat, forall x : L, toEnd R L M x ^ k = 0 := by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  use k
  intro x; ext m
  rw [Module.End.pow_apply]; rw [LinearMap.zero_apply]; rw [← @LieSubmodule.mem_bot R L M]; rw [← hM]
  exact iterate_toEnd_mem_lowerCentralSeries R L M x m k

/--
theorem `isNilpotent_toEnd_of_isNilpotent` / 定理 `isNilpotent_toEnd_of_isNilpotent`

English:
theorem isNilpotent_toEnd_of_isNilpotent
  given: [IsNilpotent L M] (x : L)
  proof: by
  change exists k, toEnd R L M x ^ k = 0
  have := exists_forall_pow_toEnd_eq_zero R L M
  tauto

中文:
定理 isNilpotent_toEnd_of_isNilpotent
  条件: [IsNilpotent L M] (x : L)
  证明: by
  change exists k, toEnd R L M x ^ k = 0
  have := exists_forall_pow_toEnd_eq_zero R L M
  tauto

Depends on / 依赖: exists_forall_pow_toEnd_eq_zero
-/
theorem isNilpotent_toEnd_of_isNilpotent [IsNilpotent L M] (x : L) :
    _root_.IsNilpotent (toEnd R L M x) := by
  change exists k, toEnd R L M x ^ k = 0
  have := exists_forall_pow_toEnd_eq_zero R L M
  tauto

/--
theorem `isNilpotent_toEnd_of_isNilpotent₂` / 定理 `isNilpotent_toEnd_of_isNilpotent₂`

English:
theorem isNilpotent_toEnd_of_isNilpotent₂
  given: [IsNilpotent L M] (x y : L)
  proof: by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  replace hM : lowerCentralSeries R L M (2 * k) = ⊥ := by
    rw [eq_bot_iff]; rw [← hM]; exact antitone_lowerCentralSeries R L M (by lia)
  use k
  ext m
  rw [Module.End.pow_apply]; rw [LinearMap.zero_apply]; rw [← LieSubmodule.mem_bot (R := R) (L

中文:
定理 isNilpotent_toEnd_of_isNilpotent₂
  条件: [IsNilpotent L M] (x y : L)
  证明: by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  replace hM : lowerCentralSeries R L M (2 * k) = ⊥ := by
    rw [eq_bot_iff]; rw [← hM]; exact antitone_lowerCentralSeries R L M (by lia)
  use k
  ext m
  rw [Module.End.pow_apply]; rw [LinearMap.zero_apply]; rw [← LieSubmodule.mem_bot (R := R) (L

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubmodule, LieSubmodule.mem_bot, LinearMap, LinearMap.zero_apply, Module, Module.End.pow_apply, antitone_lowerCentralSeries, eq_bot_iff, lowerCentralSeries, mem_bot, nilpotent, pow_apply, replace, zero_apply
-/
theorem isNilpotent_toEnd_of_isNilpotent₂ [IsNilpotent L M] (x y : L) :
    _root_.IsNilpotent (toEnd R L M x ∘ₗ toEnd R L M y) := by
  obtain ⟨k, hM⟩ := IsNilpotent.nilpotent R L M
  replace hM : lowerCentralSeries R L M (2 * k) = ⊥ := by
    rw [eq_bot_iff]; rw [← hM]; exact antitone_lowerCentralSeries R L M (by lia)
  use k
  ext m
  rw [Module.End.pow_apply]; rw [LinearMap.zero_apply]; rw [← LieSubmodule.mem_bot (R := R) (L := L)]; rw [← hM]
  exact iterate_toEnd_mem_lowerCentralSeries₂ R L M x y m k

/--
lemma `maxGenEigenSpace_toEnd_eq_top` / 引理 `maxGenEigenSpace_toEnd_eq_top`

English:
lemma maxGenEigenSpace_toEnd_eq_top
  given: [IsNilpotent L M] (x : L)
  proof: by
  ext m
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, Submodule.mem_top,
    iff_true]
  obtain ⟨k, hk⟩ := exists_forall_pow_toEnd_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩

中文:
引理 maxGenEigenSpace_toEnd_eq_top
  条件: [IsNilpotent L M] (x : L)
  证明: by
  ext m
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, Submodule.mem_top,
    iff_true]
  obtain ⟨k, hk⟩ := exists_forall_pow_toEnd_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩
-/
@[simp] lemma maxGenEigenSpace_toEnd_eq_top [IsNilpotent L M] (x : L) :
    ((toEnd R L M x).maxGenEigenspace 0) = ⊤ := by
  ext m
  simp only [Module.End.mem_maxGenEigenspace, zero_smul, sub_zero, Submodule.mem_top,
    iff_true]
  obtain ⟨k, hk⟩ := exists_forall_pow_toEnd_eq_zero R L M
  exact ⟨k, by simp [hk x]⟩

/--
theorem `nilpotentOfNilpotentQuotient` / 定理 `nilpotentOfNilpotentQuotient`

English:
theorem nilpotentOfNilpotentQuotient
  statement: {N : LieSubmodule R L M} (h₁ : N <= maxTrivSubmodule R L M)
  proof: by
  rw [isNilpotent_iff R L] at h₂ ⊢
  obtain ⟨k, hk⟩ := h₂
  use k + 1
  simp only [lowerCentralSeries_succ]
  suffices lowerCentralSeries R L M k <= N by
    replace this := LieSubmodule.mono_lie_right ⊤ (le_trans this h₁)
    rwa [ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff] at this
  rw [← L

中文:
定理 nilpotentOfNilpotentQuotient
  结论: {N : LieSubmodule R L M} (h₁ : N <= maxTrivSubmodule R L M)
  证明: by
  rw [isNilpotent_iff R L] at h₂ ⊢
  obtain ⟨k, hk⟩ := h₂
  use k + 1
  simp only [lowerCentralSeries_succ]
  suffices lowerCentralSeries R L M k <= N by
    replace this := LieSubmodule.mono_lie_right ⊤ (le_trans this h₁)
    rwa [ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff] at this
  rw [← L

Depends on / 依赖: LieSubmodule, LieSubmodule.Quotient.map_mk, LieSubmodule.Quotient.mk, LieSubmodule.mono_lie_right, Quotient, _eq_bot_le, ideal_oper_maxTrivSubmodule_eq_bot, isNilpotent_iff, le_bot_iff, le_trans, lowerCentralSeries, lowerCentralSeries_succ, map_lowerCentralSeries_le, map_mk, mono_lie_right, replace
-/
theorem nilpotentOfNilpotentQuotient {N : LieSubmodule R L M} (h₁ : N <= maxTrivSubmodule R L M)
    (h₂ : IsNilpotent L (M ⧸ N)) : IsNilpotent L M := by
  rw [isNilpotent_iff R L] at h₂ ⊢
  obtain ⟨k, hk⟩ := h₂
  use k + 1
  simp only [lowerCentralSeries_succ]
  suffices lowerCentralSeries R L M k <= N by
    replace this := LieSubmodule.mono_lie_right ⊤ (le_trans this h₁)
    rwa [ideal_oper_maxTrivSubmodule_eq_bot, le_bot_iff] at this
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le]; rw [← le_bot_iff]; rw [← hk]
  exact map_lowerCentralSeries_le k (LieSubmodule.Quotient.mk' N)

/--
theorem `isNilpotent_quotient_iff` / 定理 `isNilpotent_quotient_iff`

English:
theorem isNilpotent_quotient_iff
  proof: by
  rw [isNilpotent_iff R L]
  refine exists_congr fun k => ?_
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le]; rw [map_lowerCentralSeries_eq k
    (LieSubmodule.Quotient.surjective_mk' N)]

中文:
定理 isNilpotent_quotient_iff
  证明: by
  rw [isNilpotent_iff R L]
  refine exists_congr fun k => ?_
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le]; rw [map_lowerCentralSeries_eq k
    (LieSubmodule.Quotient.surjective_mk' N)]

Depends on / 依赖: LieSubmodule, LieSubmodule.Quotient.map_mk, LieSubmodule.Quotient.surjective_mk, Quotient, _eq_bot_le, exists_congr, isNilpotent_iff, map_lowerCentralSeries_eq, map_mk, surjective_mk
-/
theorem isNilpotent_quotient_iff :
    IsNilpotent L (M ⧸ N) ↔ exists k, lowerCentralSeries R L M k <= N := by
  rw [isNilpotent_iff R L]
  refine exists_congr fun k => ?_
  rw [← LieSubmodule.Quotient.map_mk'_eq_bot_le]; rw [map_lowerCentralSeries_eq k
    (LieSubmodule.Quotient.surjective_mk' N)]

/--
theorem `iInf_lcs_le_of_isNilpotent_quot` / 定理 `iInf_lcs_le_of_isNilpotent_quot`

English:
theorem iInf_lcs_le_of_isNilpotent_quot
  given: (h : IsNilpotent L (M ⧸ N))
  proof: by
  obtain ⟨k, hk⟩ := (isNilpotent_quotient_iff R L M N).mp h
  exact iInf_le_of_le k hk

中文:
定理 iInf_lcs_le_of_isNilpotent_quot
  条件: (h : IsNilpotent L (M ⧸ N))
  证明: by
  obtain ⟨k, hk⟩ := (isNilpotent_quotient_iff R L M N).mp h
  exact iInf_le_of_le k hk

Depends on / 依赖: iInf_le_of_le, isNilpotent_quotient_iff
-/
theorem iInf_lcs_le_of_isNilpotent_quot (h : IsNilpotent L (M ⧸ N)) :
    ⨅ k, lowerCentralSeries R L M k <= N := by
  obtain ⟨k, hk⟩ := (isNilpotent_quotient_iff R L M N).mp h
  exact iInf_le_of_le k hk

end

/--
Definition of `nilpotencyLength` / `nilpotencyLength` 的定义

English:
definition nilpotencyLength
  signature: : Nat
  body: sInf {k | lowerCentralSeries Int L M k = ⊥}

@[simp]

中文:
定义 nilpotencyLength
  签名: : 自然数
  定义体: sInf {k | lowerCentralSeries Int L M k = ⊥}

@[simp]

Depends on / 依赖: lowerCentralSeries
-/
noncomputable def nilpotencyLength : Nat :=
  sInf {k | lowerCentralSeries Int L M k = ⊥}

@[simp]
/--
theorem `nilpotencyLength_eq_zero_iff` / 定理 `nilpotencyLength_eq_zero_iff`

English:
theorem nilpotencyLength_eq_zero_iff
  given: [IsNilpotent L M]
  proof: by
  let s := {k | lowerCentralSeries Int L M k = ⊥}
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := IsNilpotent.nilpotent Int L M
    exact ⟨k, hk⟩
  change sInf s = 0 ↔ _
  rw [← LieSubmodule.subsingleton_iff Int L M]; rw [← subsingleton_iff_bot_eq_top]; rw [←
    lowerCentralSeries_zero]; rw [

中文:
定理 nilpotencyLength_eq_zero_iff
  条件: [IsNilpotent L M]
  证明: by
  let s := {k | lowerCentralSeries Int L M k = ⊥}
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := IsNilpotent.nilpotent Int L M
    exact ⟨k, hk⟩
  change sInf s = 0 ↔ _
  rw [← LieSubmodule.subsingleton_iff Int L M]; rw [← subsingleton_iff_bot_eq_top]; rw [←
    lowerCentralSeries_zero]; rw [

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubmodule, LieSubmodule.subsingleton_iff, Nat.sInf_eq_zero, Nat.sInf_mem, Nonempty, Or.inl, eq_comm, lowerCentralSeries, lowerCentralSeries_zero, nilpotent, s.Nonempty, sInf_eq_zero, sInf_mem, subsingleton_iff, subsingleton_iff_bot_eq_top
-/
theorem nilpotencyLength_eq_zero_iff [IsNilpotent L M] :
    nilpotencyLength L M = 0 ↔ Subsingleton M := by
  let s := {k | lowerCentralSeries Int L M k = ⊥}
  have hs : s.Nonempty := by
    obtain ⟨k, hk⟩ := IsNilpotent.nilpotent Int L M
    exact ⟨k, hk⟩
  change sInf s = 0 ↔ _
  rw [← LieSubmodule.subsingleton_iff Int L M]; rw [← subsingleton_iff_bot_eq_top]; rw [←
    lowerCentralSeries_zero]; rw [@eq_comm (LieSubmodule Int L M)]
  refine ⟨fun h => h ▸ Nat.sInf_mem hs, fun h => ?_⟩
  rw [Nat.sInf_eq_zero]
  exact Or.inl h

section

variable [LieModule R L M]

/--
theorem `nilpotencyLength_eq_succ_iff` / 定理 `nilpotencyLength_eq_succ_iff`

English:
theorem nilpotencyLength_eq_succ_iff
  given: (k : Nat)
  proof: by
  have aux (k : Nat) : lowerCentralSeries R L M k = ⊥ ↔ lowerCentralSeries Int L M k = ⊥ := by
    simp [SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]
  let s := {k | lowerCentralSeries Int L M k = ⊥}
  rw [aux]; rw [ne_eq]; rw [aux]
  change sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
  have hs

中文:
定理 nilpotencyLength_eq_succ_iff
  条件: (k : 自然数)
  证明: by
  have aux (k : Nat) : lowerCentralSeries R L M k = ⊥ ↔ lowerCentralSeries Int L M k = ⊥ := by
    simp [SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]
  let s := {k | lowerCentralSeries Int L M k = ⊥}
  rw [aux]; rw [ne_eq]; rw [aux]
  change sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
  have hs

Depends on / 依赖: Nat.sInf_upward_closed_eq_su, SetLike, SetLike.ext, _iff, antitone_lowerCentralSeries, coe_lowerCentralSeries_eq_int, eq_bot_iff, eq_bot_iff.mpr, lowerCentralSeries, ne_eq, sInf_upward_closed_eq_su
-/
theorem nilpotencyLength_eq_succ_iff (k : Nat) :
    nilpotencyLength L M = k + 1 ↔
      lowerCentralSeries R L M (k + 1) = ⊥ ∧ lowerCentralSeries R L M k != ⊥ := by
  have aux (k : Nat) : lowerCentralSeries R L M k = ⊥ ↔ lowerCentralSeries Int L M k = ⊥ := by
    simp [SetLike.ext'_iff, coe_lowerCentralSeries_eq_int R L M]
  let s := {k | lowerCentralSeries Int L M k = ⊥}
  rw [aux]; rw [ne_eq]; rw [aux]
  change sInf s = k + 1 ↔ k + 1 in s ∧ k ∉ s
  have hs : forall k₁ k₂, k₁ <= k₂ -> k₁ in s -> k₂ in s := by
    rintro k₁ k₂ h₁₂ (h₁ : lowerCentralSeries Int L M k₁ = ⊥)
    exact eq_bot_iff.mpr (h₁ ▸ antitone_lowerCentralSeries Int L M h₁₂)
  exact Nat.sInf_upward_closed_eq_succ_iff hs k

@[simp]
/--
theorem `nilpotencyLength_eq_one_iff` / 定理 `nilpotencyLength_eq_one_iff`

English:
theorem nilpotencyLength_eq_one_iff
  given: [Nontrivial M]
  proof: by
  rw [nilpotencyLength_eq_succ_iff Int]; rw [← trivial_iff_lower_central_eq_bot]
  simp

中文:
定理 nilpotencyLength_eq_one_iff
  条件: [Nontrivial M]
  证明: by
  rw [nilpotencyLength_eq_succ_iff Int]; rw [← trivial_iff_lower_central_eq_bot]
  simp

Depends on / 依赖: nilpotencyLength_eq_succ_iff, trivial_iff_lower_central_eq_bot
-/
theorem nilpotencyLength_eq_one_iff [Nontrivial M] :
    nilpotencyLength L M = 1 ↔ IsTrivial L M := by
  rw [nilpotencyLength_eq_succ_iff Int]; rw [← trivial_iff_lower_central_eq_bot]
  simp

/--
theorem `isTrivial_of_nilpotencyLength_le_one` / 定理 `isTrivial_of_nilpotencyLength_le_one`

English:
theorem isTrivial_of_nilpotencyLength_le_one
  given: [IsNilpotent L M] (h : nilpotencyLength L M <= 1)
  proof: by
  nontriviality M
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · rw [nilpotencyLength_eq_zero_iff] at h; infer_instance
  · rwa [nilpotencyLength_eq_one_iff] at h

中文:
定理 isTrivial_of_nilpotencyLength_le_one
  条件: [IsNilpotent L M] (h : nilpotencyLength L M <= 1)
  证明: by
  nontriviality M
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · rw [nilpotencyLength_eq_zero_iff] at h; infer_instance
  · rwa [nilpotencyLength_eq_one_iff] at h

Depends on / 依赖: Nat.le_one_iff_eq_zero_or_eq_one.mp, infer_instance, le_one_iff_eq_zero_or_eq_one, nilpotencyLength_eq_one_iff, nilpotencyLength_eq_zero_iff, nontriviality
-/
theorem isTrivial_of_nilpotencyLength_le_one [IsNilpotent L M] (h : nilpotencyLength L M <= 1) :
    IsTrivial L M := by
  nontriviality M
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h | h
  · rw [nilpotencyLength_eq_zero_iff] at h; infer_instance
  · rwa [nilpotencyLength_eq_one_iff] at h

end

/--
Definition of `lowerCentralSeriesLast` / `lowerCentralSeriesLast` 的定义

English:
definition lowerCentralSeriesLast
  signature: : LieSubmodule R L M
  body: match nilpotencyLength L M with
  | 0 => ⊥
  | k + 1 => lowerCentralSeries R L M k

中文:
定义 lowerCentralSeriesLast
  签名: : LieSubmodule R L M
  定义体: match nilpotencyLength L M with
  | 0 => ⊥
  | k + 1 => lowerCentralSeries R L M k

Depends on / 依赖: lowerCentralSeries, nilpotencyLength
-/
noncomputable def lowerCentralSeriesLast : LieSubmodule R L M :=
  match nilpotencyLength L M with
  | 0 => ⊥
  | k + 1 => lowerCentralSeries R L M k

/--
theorem `lowerCentralSeriesLast_le_max_triv` / 定理 `lowerCentralSeriesLast_le_max_triv`

English:
theorem lowerCentralSeriesLast_le_max_triv
  given: [LieModule R L M]
  proof: by
  rw [lowerCentralSeriesLast]
  rcases h : nilpotencyLength L M with - | k
  · exact bot_le
  · rw [le_max_triv_iff_bracket_eq_bot]
    rw [nilpotencyLength_eq_succ_iff R]; rw [lowerCentralSeries_succ] at h
    exact h.1

中文:
定理 lowerCentralSeriesLast_le_max_triv
  条件: [LieModule R L M]
  证明: by
  rw [lowerCentralSeriesLast]
  rcases h : nilpotencyLength L M with - | k
  · exact bot_le
  · rw [le_max_triv_iff_bracket_eq_bot]
    rw [nilpotencyLength_eq_succ_iff R]; rw [lowerCentralSeries_succ] at h
    exact h.1

Depends on / 依赖: bot_le, le_max_triv_iff_bracket_eq_bot, lowerCentralSeriesLast, lowerCentralSeries_succ, nilpotencyLength, nilpotencyLength_eq_succ_iff
-/
theorem lowerCentralSeriesLast_le_max_triv [LieModule R L M] :
    lowerCentralSeriesLast R L M <= maxTrivSubmodule R L M := by
  rw [lowerCentralSeriesLast]
  rcases h : nilpotencyLength L M with - | k
  · exact bot_le
  · rw [le_max_triv_iff_bracket_eq_bot]
    rw [nilpotencyLength_eq_succ_iff R]; rw [lowerCentralSeries_succ] at h
    exact h.1

/--
theorem `nontrivial_lowerCentralSeriesLast` / 定理 `nontrivial_lowerCentralSeriesLast`

English:
theorem nontrivial_lowerCentralSeriesLast
  given: [LieModule R L M] [Nontrivial M] [IsNilpotent L M]
  proof: by
  rw [LieSubmodule.nontrivial_iff_ne_bot]; rw [lowerCentralSeriesLast]
  cases h : nilpotencyLength L M
  · rw [nilpotencyLength_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h
    contradiction
  · rw [nilpotencyLength_eq_succ_iff R] at h
    exact h.2

中文:
定理 nontrivial_lowerCentralSeriesLast
  条件: [LieModule R L M] [Nontrivial M] [IsNilpotent L M]
  证明: by
  rw [LieSubmodule.nontrivial_iff_ne_bot]; rw [lowerCentralSeriesLast]
  cases h : nilpotencyLength L M
  · rw [nilpotencyLength_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h
    contradiction
  · rw [nilpotencyLength_eq_succ_iff R] at h
    exact h.2

Depends on / 依赖: LieSubmodule, LieSubmodule.nontrivial_iff_ne_bot, lowerCentralSeriesLast, nilpotencyLength, nilpotencyLength_eq_succ_iff, nilpotencyLength_eq_zero_iff, nontrivial_iff_ne_bot, not_nontrivial_iff_subsingleton
-/
theorem nontrivial_lowerCentralSeriesLast [LieModule R L M] [Nontrivial M] [IsNilpotent L M] :
    Nontrivial (lowerCentralSeriesLast R L M) := by
  rw [LieSubmodule.nontrivial_iff_ne_bot]; rw [lowerCentralSeriesLast]
  cases h : nilpotencyLength L M
  · rw [nilpotencyLength_eq_zero_iff, ← not_nontrivial_iff_subsingleton] at h
    contradiction
  · rw [nilpotencyLength_eq_succ_iff R] at h
    exact h.2

/--
theorem `lowerCentralSeriesLast_le_of_not_isTrivial` / 定理 `lowerCentralSeriesLast_le_of_not_isTrivial`

English:
theorem lowerCentralSeriesLast_le_of_not_isTrivial
  given: [IsNilpotent L M] (h : ¬ IsTrivial L M)
  proof: by
  rw [lowerCentralSeriesLast]
  replace h : 1 < nilpotencyLength L M := by
    by_contra contra
    have := isTrivial_of_nilpotencyLength_le_one L M (not_lt.mp contra)
    contradiction
  rcases hk : nilpotencyLength L M with - | k <;> rw [hk] at h
  · contradiction
  · exact antitone_lowerCentra

中文:
定理 lowerCentralSeriesLast_le_of_not_isTrivial
  条件: [IsNilpotent L M] (h : ¬ IsTrivial L M)
  证明: by
  rw [lowerCentralSeriesLast]
  replace h : 1 < nilpotencyLength L M := by
    by_contra contra
    have := isTrivial_of_nilpotencyLength_le_one L M (not_lt.mp contra)
    contradiction
  rcases hk : nilpotencyLength L M with - | k <;> rw [hk] at h
  · contradiction
  · exact antitone_lowerCentra

Depends on / 依赖: Nat.le_of_lt_succ, antitone_lowerCentralSeries, contra, isTrivial_of_nilpotencyLength_le_one, le_of_lt_succ, lowerCentralSeriesLast, nilpotencyLength, not_lt, not_lt.mp, replace
-/
theorem lowerCentralSeriesLast_le_of_not_isTrivial [IsNilpotent L M] (h : ¬ IsTrivial L M) :
    lowerCentralSeriesLast R L M <= lowerCentralSeries R L M 1 := by
  rw [lowerCentralSeriesLast]
  replace h : 1 < nilpotencyLength L M := by
    by_contra contra
    have := isTrivial_of_nilpotencyLength_le_one L M (not_lt.mp contra)
    contradiction
  rcases hk : nilpotencyLength L M with - | k <;> rw [hk] at h
  · contradiction
  · exact antitone_lowerCentralSeries _ _ _ (Nat.le_of_lt_succ h)

variable [LieModule R L M]
attribute [local instance 100] LieRing.ofAssociativeRing

/--
lemma `disjoint_lowerCentralSeries_maxTrivSubmodule_iff` / 引理 `disjoint_lowerCentralSeries_maxTrivSubmodule_iff`

English:
lemma disjoint_lowerCentralSeries_maxTrivSubmodule_iff
  given: [IsNilpotent L M]
  proof: by
  refine ⟨fun h => ?_, fun h => by simp⟩
  nontriviality M
  by_contra contra
  have : lowerCentralSeriesLast R L M <= lowerCentralSeries R L M 1 ⊓ maxTrivSubmodule R L M :=
    le_inf_iff.mpr ⟨lowerCentralSeriesLast_le_of_not_isTrivial R L M contra,
      lowerCentralSeriesLast_le_max_triv R L M

中文:
引理 disjoint_lowerCentralSeries_maxTrivSubmodule_iff
  条件: [IsNilpotent L M]
  证明: by
  refine ⟨fun h => ?_, fun h => by simp⟩
  nontriviality M
  by_contra contra
  have : lowerCentralSeriesLast R L M <= lowerCentralSeries R L M 1 ⊓ maxTrivSubmodule R L M :=
    le_inf_iff.mpr ⟨lowerCentralSeriesLast_le_of_not_isTrivial R L M contra,
      lowerCentralSeriesLast_le_max_triv R L M

Depends on / 依赖: Nontrivial, contra, eq_bot, h.eq_bot, le_bot_iff, le_inf_iff, le_inf_iff.mpr, lowerCentralSeries, lowerCentralSeriesLast, lowerCentralSeriesLast_le_max_triv, lowerCentralSeriesLast_le_of_not_isTrivial, maxTrivSubmodule, nontrivial_lowerCentralSeriesLast, nontriviality, not_nontrivial
-/
lemma disjoint_lowerCentralSeries_maxTrivSubmodule_iff [IsNilpotent L M] :
    Disjoint (lowerCentralSeries R L M 1) (maxTrivSubmodule R L M) ↔ IsTrivial L M := by
  refine ⟨fun h => ?_, fun h => by simp⟩
  nontriviality M
  by_contra contra
  have : lowerCentralSeriesLast R L M <= lowerCentralSeries R L M 1 ⊓ maxTrivSubmodule R L M :=
    le_inf_iff.mpr ⟨lowerCentralSeriesLast_le_of_not_isTrivial R L M contra,
      lowerCentralSeriesLast_le_max_triv R L M⟩
  suffices ¬ Nontrivial (lowerCentralSeriesLast R L M) by
    exact this (nontrivial_lowerCentralSeriesLast R L M)
  rw [h.eq_bot]; rw [le_bot_iff] at this
  exact this ▸ not_nontrivial _

/--
theorem `nontrivial_max_triv_of_isNilpotent` / 定理 `nontrivial_max_triv_of_isNilpotent`

English:
theorem nontrivial_max_triv_of_isNilpotent
  given: [Nontrivial M] [IsNilpotent L M]
  proof: Set.nontrivial_mono (lowerCentralSeriesLast_le_max_triv R L M)
    (nontrivial_lowerCentralSeriesLast R L M)

@[simp]

中文:
定理 nontrivial_max_triv_of_isNilpotent
  条件: [Nontrivial M] [IsNilpotent L M]
  证明: Set.nontrivial_mono (lowerCentralSeriesLast_le_max_triv R L M)
    (nontrivial_lowerCentralSeriesLast R L M)

@[simp]

Depends on / 依赖: Set.nontrivial_mono, lowerCentralSeriesLast_le_max_triv, nontrivial_lowerCentralSeriesLast, nontrivial_mono
-/
theorem nontrivial_max_triv_of_isNilpotent [Nontrivial M] [IsNilpotent L M] :
    Nontrivial (maxTrivSubmodule R L M) :=
  Set.nontrivial_mono (lowerCentralSeriesLast_le_max_triv R L M)
    (nontrivial_lowerCentralSeriesLast R L M)

@[simp]
/--
theorem `coe_lcs_range_toEnd_eq` / 定理 `coe_lcs_range_toEnd_eq`

English:
theorem coe_lcs_range_toEnd_eq
  given: (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (lowerCentralSeries R (toEnd R L M).range M k).mem_toSubmodule, ih]
    simp

@[simp]

中文:
定理 coe_lcs_range_toEnd_eq
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (lowerCentralSeries R (toEnd R L M).range M k).mem_toSubmodule, ih]
    simp

@[simp]

Depends on / 依赖: LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, lieIdeal_oper_eq_linear_span, lowerCentralSeries, lowerCentralSeries_succ, mem_toSubmodule
-/
theorem coe_lcs_range_toEnd_eq (k : Nat) :
    (lowerCentralSeries R (toEnd R L M).range M k : Submodule R M) =
      lowerCentralSeries R L M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (lowerCentralSeries R (toEnd R L M).range M k).mem_toSubmodule, ih]
    simp

@[simp]
/--
theorem `isNilpotent_range_toEnd_iff` / 定理 `isNilpotent_range_toEnd_iff`

English:
theorem isNilpotent_range_toEnd_iff
  proof: by
  simp only [isNilpotent_iff R _ M]
  constructor <;> rintro ⟨k, hk⟩ <;> use k <;>
      rw [← LieSubmodule.toSubmodule_inj] at hk ⊢ <;>
    simpa using hk

中文:
定理 isNilpotent_range_toEnd_iff
  证明: by
  simp only [isNilpotent_iff R _ M]
  constructor <;> rintro ⟨k, hk⟩ <;> use k <;>
      rw [← LieSubmodule.toSubmodule_inj] at hk ⊢ <;>
    simpa using hk

Depends on / 依赖: LieSubmodule, LieSubmodule.toSubmodule_inj, isNilpotent_iff, toSubmodule_inj
-/
theorem isNilpotent_range_toEnd_iff :
    IsNilpotent (toEnd R L M).range M ↔ IsNilpotent L M := by
  simp only [isNilpotent_iff R _ M]
  constructor <;> rintro ⟨k, hk⟩ <;> use k <;>
      rw [← LieSubmodule.toSubmodule_inj] at hk ⊢ <;>
    simpa using hk

end LieModule

namespace LieSubmodule

variable {N₁ N₂ : LieSubmodule R L M}
variable [LieModule R L M]

/--
Definition of `ucs` / `ucs` 的定义

English:
definition ucs
  signature: (k : Nat)
  body: normalizer^[k]

@[simp]

中文:
定义 ucs
  签名: (k : 自然数)
  定义体: normalizer^[k]

@[simp]

Depends on / 依赖: normalizer
-/
def ucs (k : Nat) : LieSubmodule R L M -> LieSubmodule R L M :=
  normalizer^[k]

@[simp]
/--
theorem `ucs_zero` / 定理 `ucs_zero`

English:
theorem ucs_zero
  statement: N.ucs 0 = N
  proof: rfl

@[simp]

中文:
定理 ucs_zero
  结论: N.ucs 0 = N
  证明: rfl

@[simp]
-/
theorem ucs_zero : N.ucs 0 = N :=
  rfl

@[simp]
/--
theorem `ucs_succ` / 定理 `ucs_succ`

English:
theorem ucs_succ
  given: (k : Nat)
  statement: N.ucs (k + 1) = (N.ucs k).normalizer
  proof: Function.iterate_succ_apply' normalizer k N

中文:
定理 ucs_succ
  条件: (k : 自然数)
  结论: N.ucs (k + 1) = (N.ucs k).normalizer
  证明: Function.iterate_succ_apply' normalizer k N

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply, normalizer
-/
theorem ucs_succ (k : Nat) : N.ucs (k + 1) = (N.ucs k).normalizer :=
  Function.iterate_succ_apply' normalizer k N

/--
theorem `ucs_add` / 定理 `ucs_add`

English:
theorem ucs_add
  given: (k l : Nat)
  statement: N.ucs (k + l) = (N.ucs l).ucs k
  proof: Function.iterate_add_apply normalizer k l N

@[gcongr, mono]

中文:
定理 ucs_add
  条件: (k l : 自然数)
  结论: N.ucs (k + l) = (N.ucs l).ucs k
  证明: Function.iterate_add_apply normalizer k l N

@[gcongr, mono]

Depends on / 依赖: Function, Function.iterate_add_apply, iterate_add_apply, normalizer
-/
theorem ucs_add (k l : Nat) : N.ucs (k + l) = (N.ucs l).ucs k :=
  Function.iterate_add_apply normalizer k l N

@[gcongr, mono]
/--
theorem `ucs_mono` / 定理 `ucs_mono`

English:
theorem ucs_mono
  given: (k : Nat) (h : N₁ <= N₂)
  statement: N₁.ucs k <= N₂.ucs k
  proof: by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [ucs_succ]
    gcongr

中文:
定理 ucs_mono
  条件: (k : 自然数) (h : N₁ <= N₂)
  结论: N₁.ucs k <= N₂.ucs k
  证明: by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [ucs_succ]
    gcongr

Depends on / 依赖: ucs_succ
-/
theorem ucs_mono (k : Nat) (h : N₁ <= N₂) : N₁.ucs k <= N₂.ucs k := by
  induction k with
  | zero => simpa
  | succ k ih =>
    simp only [ucs_succ]
    gcongr

/--
theorem `ucs_eq_self_of_normalizer_eq_self` / 定理 `ucs_eq_self_of_normalizer_eq_self`

English:
theorem ucs_eq_self_of_normalizer_eq_self
  given: (h : N₁.normalizer = N₁) (k : Nat)
  statement: N₁.ucs k = N₁
  proof: by
  induction k with
  | zero => simp
  | succ k ih => rwa [ucs_succ, ih]

中文:
定理 ucs_eq_self_of_normalizer_eq_self
  条件: (h : N₁.normalizer = N₁) (k : 自然数)
  结论: N₁.ucs k = N₁
  证明: by
  induction k with
  | zero => simp
  | succ k ih => rwa [ucs_succ, ih]

Depends on / 依赖: ucs_succ
-/
theorem ucs_eq_self_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : Nat) : N₁.ucs k = N₁ := by
  induction k with
  | zero => simp
  | succ k ih => rwa [ucs_succ, ih]

/--
theorem `ucs_le_of_normalizer_eq_self` / 定理 `ucs_le_of_normalizer_eq_self`

English:
theorem ucs_le_of_normalizer_eq_self
  given: (h : N₁.normalizer = N₁) (k : Nat)
  proof: by
  rw [← ucs_eq_self_of_normalizer_eq_self h k]
  gcongr
  simp

中文:
定理 ucs_le_of_normalizer_eq_self
  条件: (h : N₁.normalizer = N₁) (k : 自然数)
  证明: by
  rw [← ucs_eq_self_of_normalizer_eq_self h k]
  gcongr
  simp

Depends on / 依赖: ucs_eq_self_of_normalizer_eq_self
-/
theorem ucs_le_of_normalizer_eq_self (h : N₁.normalizer = N₁) (k : Nat) :
    (⊥ : LieSubmodule R L M).ucs k <= N₁ := by
  rw [← ucs_eq_self_of_normalizer_eq_self h k]
  gcongr
  simp

/--
theorem `lcs_add_le_iff` / 定理 `lcs_add_le_iff`

English:
theorem lcs_add_le_iff
  given: (l k : Nat)
  statement: N₁.lcs (l + k) <= N₂ ↔ N₁.lcs l <= N₂.ucs k
  proof: by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [(by abel : l + (k + 1) = l + 1 + k)]; rw [ih]; rw [ucs_succ]; rw [lcs_succ]; rw [top_lie_le_iff_le_normalizer]

中文:
定理 lcs_add_le_iff
  条件: (l k : 自然数)
  结论: N₁.lcs (l + k) <= N₂ ↔ N₁.lcs l <= N₂.ucs k
  证明: by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [(by abel : l + (k + 1) = l + 1 + k)]; rw [ih]; rw [ucs_succ]; rw [lcs_succ]; rw [top_lie_le_iff_le_normalizer]

Depends on / 依赖: generalizing, lcs_succ, top_lie_le_iff_le_normalizer, ucs_succ
-/
theorem lcs_add_le_iff (l k : Nat) : N₁.lcs (l + k) <= N₂ ↔ N₁.lcs l <= N₂.ucs k := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [(by abel : l + (k + 1) = l + 1 + k)]; rw [ih]; rw [ucs_succ]; rw [lcs_succ]; rw [top_lie_le_iff_le_normalizer]

/--
theorem `lcs_le_iff` / 定理 `lcs_le_iff`

English:
theorem lcs_le_iff
  given: (k : Nat)
  statement: N₁.lcs k <= N₂ ↔ N₁ <= N₂.ucs k
  proof: by
  convert! lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  rw [zero_add]

中文:
定理 lcs_le_iff
  条件: (k : 自然数)
  结论: N₁.lcs k <= N₂ ↔ N₁ <= N₂.ucs k
  证明: by
  convert! lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  rw [zero_add]

Depends on / 依赖: convert, lcs_add_le_iff, zero_add
-/
theorem lcs_le_iff (k : Nat) : N₁.lcs k <= N₂ ↔ N₁ <= N₂.ucs k := by
  convert! lcs_add_le_iff (R := R) (L := L) (M := M) 0 k
  rw [zero_add]

/--
theorem `gc_lcs_ucs` / 定理 `gc_lcs_ucs`

English:
theorem gc_lcs_ucs
  given: (k : Nat)
  proof: fun _ _ => lcs_le_iff k

中文:
定理 gc_lcs_ucs
  条件: (k : 自然数)
  证明: fun _ _ => lcs_le_iff k

Depends on / 依赖: lcs_le_iff
-/
theorem gc_lcs_ucs (k : Nat) :
    GaloisConnection (fun N : LieSubmodule R L M => N.lcs k) fun N : LieSubmodule R L M =>
      N.ucs k :=
  fun _ _ => lcs_le_iff k

/--
theorem `ucs_eq_top_iff` / 定理 `ucs_eq_top_iff`

English:
theorem ucs_eq_top_iff
  given: (k : Nat)
  statement: N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L M k <= N
  proof: by
  rw [eq_top_iff]; rw [← lcs_le_iff]; rfl

中文:
定理 ucs_eq_top_iff
  条件: (k : 自然数)
  结论: N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L M k <= N
  证明: by
  rw [eq_top_iff]; rw [← lcs_le_iff]; rfl

Depends on / 依赖: eq_top_iff, lcs_le_iff
-/
theorem ucs_eq_top_iff (k : Nat) : N.ucs k = ⊤ ↔ LieModule.lowerCentralSeries R L M k <= N := by
  rw [eq_top_iff]; rw [← lcs_le_iff]; rfl

variable (R) in
/--
theorem `_root_.LieModule.isNilpotent_iff_exists_ucs_eq_top` / 定理 `_root_.LieModule.isNilpotent_iff_exists_ucs_eq_top`

English:
theorem _root_.LieModule.isNilpotent_iff_exists_ucs_eq_top
  proof: by
  rw [LieModule.isNilpotent_iff R]; exact exists_congr fun k => by simp [ucs_eq_top_iff]

中文:
定理 _root_.LieModule.isNilpotent_iff_exists_ucs_eq_top
  证明: by
  rw [LieModule.isNilpotent_iff R]; exact exists_congr fun k => by simp [ucs_eq_top_iff]

Depends on / 依赖: LieModule, LieModule.isNilpotent_iff, exists_congr, isNilpotent_iff, ucs_eq_top_iff
-/
theorem _root_.LieModule.isNilpotent_iff_exists_ucs_eq_top :
    LieModule.IsNilpotent L M ↔ exists k, (⊥ : LieSubmodule R L M).ucs k = ⊤ := by
  rw [LieModule.isNilpotent_iff R]; exact exists_congr fun k => by simp [ucs_eq_top_iff]

/--
theorem `ucs_comap_incl` / 定理 `ucs_comap_incl`

English:
theorem ucs_comap_incl
  given: (k : Nat)
  proof: by
  induction k with
  | zero => exact N.ker_incl
  | succ k ih => simp [← ih]

中文:
定理 ucs_comap_incl
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => exact N.ker_incl
  | succ k ih => simp [← ih]

Depends on / 依赖: N.ker_incl, ker_incl
-/
theorem ucs_comap_incl (k : Nat) :
    ((⊥ : LieSubmodule R L M).ucs k).comap N.incl = (⊥ : LieSubmodule R L N).ucs k := by
  induction k with
  | zero => exact N.ker_incl
  | succ k ih => simp [← ih]

/--
theorem `isNilpotent_iff_exists_self_le_ucs` / 定理 `isNilpotent_iff_exists_self_le_ucs`

English:
theorem isNilpotent_iff_exists_self_le_ucs
  proof: by
  simp_rw [LieModule.isNilpotent_iff_exists_ucs_eq_top R, ← ucs_comap_incl, comap_incl_eq_top]

中文:
定理 isNilpotent_iff_exists_self_le_ucs
  证明: by
  simp_rw [LieModule.isNilpotent_iff_exists_ucs_eq_top R, ← ucs_comap_incl, comap_incl_eq_top]

Depends on / 依赖: LieModule, LieModule.isNilpotent_iff_exists_ucs_eq_top, comap_incl_eq_top, isNilpotent_iff_exists_ucs_eq_top, simp_rw, ucs_comap_incl
-/
theorem isNilpotent_iff_exists_self_le_ucs :
    LieModule.IsNilpotent L N ↔ exists k, N <= (⊥ : LieSubmodule R L M).ucs k := by
  simp_rw [LieModule.isNilpotent_iff_exists_ucs_eq_top R, ← ucs_comap_incl, comap_incl_eq_top]

/--
theorem `ucs_bot_one` / 定理 `ucs_bot_one`

English:
theorem ucs_bot_one
  statement: (⊥ : LieSubmodule R L M).ucs 1 = LieModule.maxTrivSubmodule R L M
  proof: by
  simp [LieSubmodule.normalizer_bot_eq_maxTrivSubmodule]

中文:
定理 ucs_bot_one
  结论: (⊥ : LieSubmodule R L M).ucs 1 = LieModule.maxTrivSubmodule R L M
  证明: by
  simp [LieSubmodule.normalizer_bot_eq_maxTrivSubmodule]

Depends on / 依赖: LieSubmodule, LieSubmodule.normalizer_bot_eq_maxTrivSubmodule, normalizer_bot_eq_maxTrivSubmodule
-/
theorem ucs_bot_one : (⊥ : LieSubmodule R L M).ucs 1 = LieModule.maxTrivSubmodule R L M := by
  simp [LieSubmodule.normalizer_bot_eq_maxTrivSubmodule]

end LieSubmodule

section Morphisms

open LieModule Function

variable [LieModule R L M]
variable {L₂ M₂ : Type*} [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L₂ M₂]
variable {f : L ->ₗ⁅R⁆ L₂} {g : M ->ₗ[R] M₂}
variable (hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆)

include hfg in
/--
theorem `lieModule_lcs_map_le` / 定理 `lieModule_lcs_map_le`

English:
theorem lieModule_lcs_map_le
  given: (k : Nat)
  proof: by
  induction k with
  | zero =>
    simp [Submodule.map_top]
  | succ k ih =>
    rw [lowerCentralSeries_succ]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [Submodule.map_span]; rw [Submodule.span_le]
    rintro m₂ ⟨m, ⟨x, n, m_n, ⟨h₁, h₂⟩⟩, rfl⟩
    simp only [lowerCentralSeries_succ, Set

中文:
定理 lieModule_lcs_map_le
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero =>
    simp [Submodule.map_top]
  | succ k ih =>
    rw [lowerCentralSeries_succ]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [Submodule.map_span]; rw [Submodule.span_le]
    rintro m₂ ⟨m, ⟨x, n, m_n, ⟨h₁, h₂⟩⟩, rfl⟩
    simp only [lowerCentralSeries_succ, Set

Depends on / 依赖: LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, SetLike, SetLike.mem_coe, Submodule, Submodule.map_span, Submodule.map_top, Submodule.mem_map_of_mem, Submodule.span_le, lieIdeal_oper_eq_linear_span, lowerCentralSeries, lowerCentralSeries_succ, map_span, map_top, mem_coe, mem_map_of_mem, mem_toSubmodule, span_le
-/
theorem lieModule_lcs_map_le (k : Nat) :
    (lowerCentralSeries R L M k : Submodule R M).map g <= lowerCentralSeries R L₂ M₂ k := by
  induction k with
  | zero =>
    simp [Submodule.map_top]
  | succ k ih =>
    rw [lowerCentralSeries_succ]; rw [LieSubmodule.lieIdeal_oper_eq_linear_span']; rw [Submodule.map_span]; rw [Submodule.span_le]
    rintro m₂ ⟨m, ⟨x, n, m_n, ⟨h₁, h₂⟩⟩, rfl⟩
    simp only [lowerCentralSeries_succ, SetLike.mem_coe, LieSubmodule.mem_toSubmodule]
    have : exists y : L₂, exists n : lowerCentralSeries R L₂ M₂ k, ⁅y, n⁆ = g m := by
      use f x, ⟨g m_n, ih (Submodule.mem_map_of_mem h₁)⟩
      simp [hfg x m_n, h₂]
    obtain ⟨y, n, hn⟩ := this
    rw [← hn]
    apply LieSubmodule.lie_mem_lie
    · simp
    · exact SetLike.coe_mem n

variable [LieModule R L₂ M₂] (hg_inj : Injective g)

include hg_inj hfg in
/--
theorem `Function.Injective.lieModuleIsNilpotent` / 定理 `Function.Injective.lieModuleIsNilpotent`

English:
theorem Function.Injective.lieModuleIsNilpotent
  given: [IsNilpotent L₂ M₂]
  statement: IsNilpotent L M
  proof: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L₂ M₂
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  apply Submodule.map_injective_of_injective hg_inj
  simpa [hk] using lieModule_lcs_map_le hfg k

中文:
定理 Function.Injective.lieModuleIsNilpotent
  条件: [IsNilpotent L₂ M₂]
  结论: IsNilpotent L M
  证明: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L₂ M₂
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  apply Submodule.map_injective_of_injective hg_inj
  simpa [hk] using lieModule_lcs_map_le hfg k

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubmodule, LieSubmodule.toSubmodule_inj, Submodule, Submodule.map_injective_of_injective, hg_inj, isNilpotent_iff, lieModule_lcs_map_le, map_injective_of_injective, nilpotent, toSubmodule_inj
-/
theorem Function.Injective.lieModuleIsNilpotent [IsNilpotent L₂ M₂] : IsNilpotent L M := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L₂ M₂
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  apply Submodule.map_injective_of_injective hg_inj
  simpa [hk] using lieModule_lcs_map_le hfg k

variable (hf_surj : Surjective f) (hg_surj : Surjective g)

include hf_surj hg_surj hfg in
/--
theorem `Function.Surjective.lieModule_lcs_map_eq` / 定理 `Function.Surjective.lieModule_lcs_map_eq`

English:
theorem Function.Surjective.lieModule_lcs_map_eq
  given: (k : Nat)
  proof: by
  refine le_antisymm (lieModule_lcs_map_le hfg k) ?_
  induction k with
  | zero => simpa [LinearMap.range_eq_top]
  | succ k ih =>
    suffices
      {m | exists (x : L₂) (n : _), n in lowerCentralSeries R L M k ∧ ⁅x, g n⁆ = m} subseteq
        g '' {m | exists (x : L) (n : _), n in lowerCentral

中文:
定理 Function.Surjective.lieModule_lcs_map_eq
  条件: (k : 自然数)
  证明: by
  refine le_antisymm (lieModule_lcs_map_le hfg k) ?_
  induction k with
  | zero => simpa [LinearMap.range_eq_top]
  | succ k ih =>
    suffices
      {m | exists (x : L₂) (n : _), n in lowerCentralSeries R L M k ∧ ⁅x, g n⁆ = m} subseteq
        g '' {m | exists (x : L) (n : _), n in lowerCentral

Depends on / 依赖: LieSubmodul, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top, LinearMap, LinearMap.range_eq_top, Submodule, Submodule.map_span, le_antisymm, lieIdeal_oper_eq_linear_span, lieModule_lcs_map_le, lowerCentralSeries, lowerCentralSeries_succ, map_span, mem_toSubmodule, mem_top, range_eq_top, simp_rw, subseteq
-/
theorem Function.Surjective.lieModule_lcs_map_eq (k : Nat) :
    (lowerCentralSeries R L M k : Submodule R M).map g = lowerCentralSeries R L₂ M₂ k := by
  refine le_antisymm (lieModule_lcs_map_le hfg k) ?_
  induction k with
  | zero => simpa [LinearMap.range_eq_top]
  | succ k ih =>
    suffices
      {m | exists (x : L₂) (n : _), n in lowerCentralSeries R L M k ∧ ⁅x, g n⁆ = m} subseteq
        g '' {m | exists (x : L) (n : _), n in lowerCentralSeries R L M k ∧ ⁅x, n⁆ = m} by
      simp only [← LieSubmodule.mem_toSubmodule] at this
      simp_rw [lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span',
        Submodule.map_span, LieSubmodule.mem_top, true_and, ← LieSubmodule.mem_toSubmodule]
      refine Submodule.span_mono (Set.Subset.trans ?_ this)
      rintro m₁ ⟨x, n, hn, rfl⟩
      obtain ⟨n', hn', rfl⟩ := ih hn
      exact ⟨x, n', hn', rfl⟩
    rintro m₂ ⟨x, n, hn, rfl⟩
    obtain ⟨y, rfl⟩ := hf_surj x
    exact ⟨⁅y, n⁆, ⟨y, n, hn, rfl⟩, (hfg y n).symm⟩

include hf_surj hg_surj hfg in
/--
theorem `Function.Surjective.lieModuleIsNilpotent` / 定理 `Function.Surjective.lieModuleIsNilpotent`

English:
theorem Function.Surjective.lieModuleIsNilpotent
  given: [IsNilpotent L M]
  statement: IsNilpotent L₂ M₂
  proof: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  simp [← hf_surj.lieModule_lcs_map_eq hfg hg_surj k, hk]

中文:
定理 Function.Surjective.lieModuleIsNilpotent
  条件: [IsNilpotent L M]
  结论: IsNilpotent L₂ M₂
  证明: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  simp [← hf_surj.lieModule_lcs_map_eq hfg hg_surj k, hk]

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, LieSubmodule, LieSubmodule.toSubmodule_inj, hf_surj, hf_surj.lieModule_lcs_map_eq, hg_surj, isNilpotent_iff, lieModule_lcs_map_eq, nilpotent, toSubmodule_inj
-/
theorem Function.Surjective.lieModuleIsNilpotent [IsNilpotent L M] : IsNilpotent L₂ M₂ := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff R]
  use k
  rw [← LieSubmodule.toSubmodule_inj] at hk ⊢
  simp [← hf_surj.lieModule_lcs_map_eq hfg hg_surj k, hk]

/--
theorem `Equiv.lieModule_isNilpotent_iff` / 定理 `Equiv.lieModule_isNilpotent_iff`

English:
theorem Equiv.lieModule_isNilpotent_iff
  statement: (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
  proof: by
  constructor <;> intro h
  · have hg : Surjective (g : M ->ₗ[R] M₂) := g.surjective
    exact f.surjective.lieModuleIsNilpotent hfg hg
  · have hg : Surjective (g.symm : M₂ ->ₗ[R] M) := g.symm.surjective
    refine f.symm.surjective.lieModuleIsNilpotent (fun x m => ?_) hg
    rw [LinearEquiv.coe

中文:
定理 Equiv.lieModule_isNilpotent_iff
  结论: (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
  证明: by
  constructor <;> intro h
  · have hg : Surjective (g : M ->ₗ[R] M₂) := g.surjective
    exact f.surjective.lieModuleIsNilpotent hfg hg
  · have hg : Surjective (g.symm : M₂ ->ₗ[R] M) := g.symm.surjective
    refine f.symm.surjective.lieModuleIsNilpotent (fun x m => ?_) hg
    rw [LinearEquiv.coe

Depends on / 依赖: LieEquiv, LieEquiv.coe_toLieHom, LinearEquiv, LinearEquiv.coe_coe, Surjective, apply_symm_apply, coe_coe, coe_toLieHom, f.apply_symm_apply, f.surjective.lieModuleIsNilpotent, f.symm, f.symm.surjective.lieModuleIsNilpotent, g.apply_symm_apply, g.surjective, g.symm, g.symm.surjective, g.symm_apply_apply, lieModuleIsNilpotent, surjective, symm_apply_apply
-/
theorem Equiv.lieModule_isNilpotent_iff (f : L ≃ₗ⁅R⁆ L₂) (g : M ≃ₗ[R] M₂)
    (hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆) : IsNilpotent L M ↔ IsNilpotent L₂ M₂ := by
  constructor <;> intro h
  · have hg : Surjective (g : M ->ₗ[R] M₂) := g.surjective
    exact f.surjective.lieModuleIsNilpotent hfg hg
  · have hg : Surjective (g.symm : M₂ ->ₗ[R] M) := g.symm.surjective
    refine f.symm.surjective.lieModuleIsNilpotent (fun x m => ?_) hg
    rw [LinearEquiv.coe_coe]; rw [LieEquiv.coe_toLieHom]; rw [← g.symm_apply_apply ⁅f.symm x]; rw [g.symm m⁆]; rw [←
      hfg]; rw [f.apply_symm_apply]; rw [g.apply_symm_apply]

@[simp]
/--
theorem `LieModule.isNilpotent_of_top_iff` / 定理 `LieModule.isNilpotent_of_top_iff`

English:
theorem LieModule.isNilpotent_of_top_iff
  proof: Equiv.lieModule_isNilpotent_iff LieSubalgebra.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl

中文:
定理 LieModule.isNilpotent_of_top_iff
  证明: Equiv.lieModule_isNilpotent_iff LieSubalgebra.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl

Depends on / 依赖: Equiv.lieModule_isNilpotent_iff, LieSubalgebra, LieSubalgebra.topEquiv, lieModule_isNilpotent_iff, topEquiv
-/
theorem LieModule.isNilpotent_of_top_iff :
    IsNilpotent (⊤ : LieSubalgebra R L) M ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff LieSubalgebra.topEquiv (1 : M ≃ₗ[R] M) fun _ _ => rfl

/--
lemma `LieModule.isNilpotent_of_top_iff'` / 引理 `LieModule.isNilpotent_of_top_iff'`

English:
lemma LieModule.isNilpotent_of_top_iff'
  proof: Equiv.lieModule_isNilpotent_iff 1 (LinearEquiv.ofTop ⊤ rfl) fun _ _ => rfl

中文:
引理 LieModule.isNilpotent_of_top_iff'
  证明: Equiv.lieModule_isNilpotent_iff 1 (LinearEquiv.ofTop ⊤ rfl) fun _ _ => rfl
-/
@[simp] lemma LieModule.isNilpotent_of_top_iff' :
    IsNilpotent L {x // x in (⊤ : LieSubmodule R L M)} ↔ IsNilpotent L M :=
  Equiv.lieModule_isNilpotent_iff 1 (LinearEquiv.ofTop ⊤ rfl) fun _ _ => rfl

end Morphisms

namespace LieModule

variable (R L M)
variable [LieModule R L M]

/--
theorem `isNilpotent_of_le` / 定理 `isNilpotent_of_le`

English:
theorem isNilpotent_of_le
  given: (M₁ M₂ : LieSubmodule R L M) (h₁ : M₁ <= M₂) [IsNilpotent L M₂]
  proof: by
  let f : L ->ₗ⁅R⁆ L := LieHom.id
  let g : M₁ ->ₗ[R] M₂ := Submodule.inclusion h₁
  have hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact (Submodule.inclusion_injective h₁).lieModuleIsNilpotent hfg

中文:
定理 isNilpotent_of_le
  条件: (M₁ M₂ : LieSubmodule R L M) (h₁ : M₁ <= M₂) [IsNilpotent L M₂]
  证明: by
  let f : L ->ₗ⁅R⁆ L := LieHom.id
  let g : M₁ ->ₗ[R] M₂ := Submodule.inclusion h₁
  have hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact (Submodule.inclusion_injective h₁).lieModuleIsNilpotent hfg

Depends on / 依赖: LieHom, LieHom.id, Submodule, Submodule.inclusion, Submodule.inclusion_injective, inclusion, inclusion_injective, lieModuleIsNilpotent
-/
theorem isNilpotent_of_le (M₁ M₂ : LieSubmodule R L M) (h₁ : M₁ <= M₂) [IsNilpotent L M₂] :
    IsNilpotent L M₁ := by
  let f : L ->ₗ⁅R⁆ L := LieHom.id
  let g : M₁ ->ₗ[R] M₂ := Submodule.inclusion h₁
  have hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact (Submodule.inclusion_injective h₁).lieModuleIsNilpotent hfg

/--
Definition of `maxNilpotentSubmodule` / `maxNilpotentSubmodule` 的定义

English:
definition maxNilpotentSubmodule
  body: sSup { N : LieSubmodule R L M | IsNilpotent L N }

中文:
定义 maxNilpotentSubmodule
  定义体: sSup { N : LieSubmodule R L M | IsNilpotent L N }

Depends on / 依赖: IsNilpotent, LieSubmodule
-/
def maxNilpotentSubmodule :=
  sSup { N : LieSubmodule R L M | IsNilpotent L N }

-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/--
Instance `instMaxNilpotentSubmoduleIsNilpotent` / 实例 `instMaxNilpotentSubmoduleIsNilpotent`

English:
instance instMaxNilpotentSubmoduleIsNilpotent
  signature: [IsNoetherian R M]
  body: by
  have hwf := CompleteLattice.WellFoundedGT.isSupClosedCompact (LieSubmodule R L M) inferInstance
  refine hwf { N : LieSubmodule R L M | IsNilpotent L N } ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all <;> infer_instance

中文:
实例 instMaxNilpotentSubmoduleIsNilpotent
  签名: [IsNoetherian R M]
  定义体: by
  have hwf := CompleteLattice.WellFoundedGT.isSupClosedCompact (LieSubmodule R L M) inferInstance
  refine hwf { N : LieSubmodule R L M | IsNilpotent L N } ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all <;> infer_instance

Depends on / 依赖: CompleteLattice, CompleteLattice.WellFoundedGT.isSupClosedCompact, IsNilpotent, LieSubmodule, WellFoundedGT, infer_instance, isSupClosedCompact
-/
instance instMaxNilpotentSubmoduleIsNilpotent [IsNoetherian R M] :
    IsNilpotent L (maxNilpotentSubmodule R L M) := by
  have hwf := CompleteLattice.WellFoundedGT.isSupClosedCompact (LieSubmodule R L M) inferInstance
  refine hwf { N : LieSubmodule R L M | IsNilpotent L N } ⟨⊥, ?_⟩ fun N₁ h₁ N₂ h₂ => ?_ <;>
  simp_all <;> infer_instance

/--
theorem `isNilpotent_iff_le_maxNilpotentSubmodule` / 定理 `isNilpotent_iff_le_maxNilpotentSubmodule`

English:
theorem isNilpotent_iff_le_maxNilpotentSubmodule
  given: [IsNoetherian R M] (N : LieSubmodule R L M)
  proof: ⟨fun h => le_sSup h, fun h => isNilpotent_of_le R L M N (maxNilpotentSubmodule R L M) h⟩

中文:
定理 isNilpotent_iff_le_maxNilpotentSubmodule
  条件: [IsNoetherian R M] (N : LieSubmodule R L M)
  证明: ⟨fun h => le_sSup h, fun h => isNilpotent_of_le R L M N (maxNilpotentSubmodule R L M) h⟩

Depends on / 依赖: isNilpotent_of_le, le_sSup, maxNilpotentSubmodule
-/
theorem isNilpotent_iff_le_maxNilpotentSubmodule [IsNoetherian R M] (N : LieSubmodule R L M) :
    IsNilpotent L N ↔ N <= maxNilpotentSubmodule R L M :=
  ⟨fun h => le_sSup h, fun h => isNilpotent_of_le R L M N (maxNilpotentSubmodule R L M) h⟩

/--
lemma `maxNilpotentSubmodule_eq_top_of_isNilpotent` / 引理 `maxNilpotentSubmodule_eq_top_of_isNilpotent`

English:
lemma maxNilpotentSubmodule_eq_top_of_isNilpotent
  given: [LieModule.IsNilpotent L M]
  proof: by
  rw [eq_top_iff]
  apply le_sSup
  simpa

中文:
引理 maxNilpotentSubmodule_eq_top_of_isNilpotent
  条件: [LieModule.IsNilpotent L M]
  证明: by
  rw [eq_top_iff]
  apply le_sSup
  simpa
-/
@[simp] lemma maxNilpotentSubmodule_eq_top_of_isNilpotent [LieModule.IsNilpotent L M] :
    maxNilpotentSubmodule R L M = ⊤ := by
  rw [eq_top_iff]
  apply le_sSup
  simpa

end LieModule

end NilpotentModules

instance (priority := 100) LieAlgebra.isSolvable_of_isNilpotent (L : Type v)
    [LieRing L] [hL : LieModule.IsNilpotent L L] :
    LieAlgebra.IsSolvable L := by
  obtain ⟨k, h⟩ : exists k, LieModule.lowerCentralSeries Int L L k = ⊥ := hL.nilpotent_int
  use k; rw [← le_bot_iff] at h ⊢
  exact le_trans (LieModule.derivedSeries_le_lowerCentralSeries Int L k) h

section NilpotentAlgebras

variable (R : Type u) (L : Type v) (L' : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']

/--
Definition of `LieRing.IsNilpotent` / `LieRing.IsNilpotent` 的定义

English:
abbreviation LieRing.IsNilpotent
  signature: (L : Type v) [LieRing L]
  body: LieModule.IsNilpotent L L

中文:
缩写 LieRing.IsNilpotent
  签名: (L : 类型v) [LieRing L]
  定义体: LieModule.IsNilpotent L L

Depends on / 依赖: IsNilpotent, LieModule, LieModule.IsNilpotent
-/
abbrev LieRing.IsNilpotent (L : Type v) [LieRing L] : Prop :=
  LieModule.IsNilpotent L L

open LieRing

/--
theorem `LieAlgebra.nilpotent_ad_of_nilpotent_algebra` / 定理 `LieAlgebra.nilpotent_ad_of_nilpotent_algebra`

English:
theorem LieAlgebra.nilpotent_ad_of_nilpotent_algebra
  given: [IsNilpotent L]
  proof: LieModule.exists_forall_pow_toEnd_eq_zero R L L

中文:
定理 LieAlgebra.nilpotent_ad_of_nilpotent_algebra
  条件: [IsNilpotent L]
  证明: LieModule.exists_forall_pow_toEnd_eq_zero R L L

Depends on / 依赖: LieModule, LieModule.exists_forall_pow_toEnd_eq_zero, exists_forall_pow_toEnd_eq_zero
-/
theorem LieAlgebra.nilpotent_ad_of_nilpotent_algebra [IsNilpotent L] :
    exists k : Nat, forall x : L, ad R L x ^ k = 0 :=
  LieModule.exists_forall_pow_toEnd_eq_zero R L L

-- TODO Generalise the below to Lie modules if / when we define morphisms, equivs of Lie modules
-- covering a Lie algebra morphism of (possibly different) Lie algebras.
variable {R L L'}

open LieModule (lowerCentralSeries)

-- Porting note: added `LieSubmodule.toSubmodule` in the statement
/--
theorem `coe_lowerCentralSeries_ideal_quot_eq` / 定理 `coe_lowerCentralSeries_ideal_quot_eq`

English:
theorem coe_lowerCentralSeries_ideal_quot_eq
  given: {I : LieIdeal R L} (k : Nat)
  proof: by
  induction k with
  | zero =>
    simp only [LieModule.lowerCentralSeries_zero, LieSubmodule.top_toSubmodule]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    congr
    ext x
    constructor
    · rintro ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y,

中文:
定理 coe_lowerCentralSeries_ideal_quot_eq
  条件: {I : LieIdeal R L} (k : 自然数)
  证明: by
  induction k with
  | zero =>
    simp only [LieModule.lowerCentralSeries_zero, LieSubmodule.top_toSubmodule]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    congr
    ext x
    constructor
    · rintro ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y,

Depends on / 依赖: LieModule, LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero, LieSubm, LieSubmodule, LieSubmodule.Quotient.mk, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top, LieSubmodule.top_toSubmodule, Quotient, lieIdeal_oper_eq_linear_span, lowerCentralSeries_succ, lowerCentralSeries_zero, mem_toSubmodule, mem_top, top_toSubmodule
-/
theorem coe_lowerCentralSeries_ideal_quot_eq {I : LieIdeal R L} (k : Nat) :
    LieSubmodule.toSubmodule (lowerCentralSeries R L (L ⧸ I) k) =
      LieSubmodule.toSubmodule (lowerCentralSeries R (L ⧸ I) (L ⧸ I) k) := by
  induction k with
  | zero =>
    simp only [LieModule.lowerCentralSeries_zero, LieSubmodule.top_toSubmodule]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    congr
    ext x
    constructor
    · rintro ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      rw [← LieSubmodule.mem_toSubmodule]; rw [ih]; rw [LieSubmodule.mem_toSubmodule] at hz
      exact ⟨⟨LieSubmodule.Quotient.mk y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩
    · rintro ⟨⟨⟨y⟩, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
      rw [← LieSubmodule.mem_toSubmodule]; rw [← ih]; rw [LieSubmodule.mem_toSubmodule] at hz
      exact ⟨⟨y, LieSubmodule.mem_top _⟩, ⟨z, hz⟩, rfl⟩

-- Porting note: added `LieSubmodule.toSubmodule` in the statement
/--
theorem `LieModule.coe_lowerCentralSeries_ideal_le` / 定理 `LieModule.coe_lowerCentralSeries_ideal_le`

English:
theorem LieModule.coe_lowerCentralSeries_ideal_le
  given: {I : LieIdeal R L} (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_mono
    rintro x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
    exact ⟨⟨y.val, LieSubmodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩

中文:
定理 LieModule.coe_lowerCentralSeries_ideal_le
  条件: {I : LieIdeal R L} (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_mono
    rintro x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
    exact ⟨⟨y.val, LieSubmodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩

Depends on / 依赖: LieModule, LieModule.lowerCentralSeries_succ, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_top, Submodule, Submodule.span_mono, lieIdeal_oper_eq_linear_span, lowerCentralSeries_succ, mem_top, span_mono, y.val
-/
theorem LieModule.coe_lowerCentralSeries_ideal_le {I : LieIdeal R L} (k : Nat) :
    LieSubmodule.toSubmodule (lowerCentralSeries R I I k) <= lowerCentralSeries R L I k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ, LieSubmodule.lieIdeal_oper_eq_linear_span]
    apply Submodule.span_mono
    rintro x ⟨⟨y, -⟩, ⟨z, hz⟩, rfl : ⁅y, z⁆ = x⟩
    exact ⟨⟨y.val, LieSubmodule.mem_top _⟩, ⟨z, ih hz⟩, rfl⟩

/--
theorem `LieAlgebra.nilpotent_of_nilpotent_quotient` / 定理 `LieAlgebra.nilpotent_of_nilpotent_quotient`

English:
theorem LieAlgebra.nilpotent_of_nilpotent_quotient
  statement: {I : LieIdeal R L} (h₁ : I <= center R L)
  proof: by
  suffices LieModule.IsNilpotent L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  simp only [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₂ ⊢
  peel h₂ with k hk
  simp [← LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, hk]

中文:
定理 LieAlgebra.nilpotent_of_nilpotent_quotient
  结论: {I : LieIdeal R L} (h₁ : I <= center R L)
  证明: by
  suffices LieModule.IsNilpotent L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  simp only [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₂ ⊢
  peel h₂ with k hk
  simp [← LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, hk]

Depends on / 依赖: IsNilpotent, LieModule, LieModule.IsNilpotent, LieModule.isNilpotent_iff, LieModule.nilpotentOfNilpotentQuotient, LieRing, LieRing.IsNilpotent, LieSubmodule, LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, isNilpotent_iff, nilpotentOfNilpotentQuotient, toSubmodule_inj
-/
theorem LieAlgebra.nilpotent_of_nilpotent_quotient {I : LieIdeal R L} (h₁ : I <= center R L)
    (h₂ : IsNilpotent (L ⧸ I)) : IsNilpotent L := by
  suffices LieModule.IsNilpotent L (L ⧸ I) by
    exact LieModule.nilpotentOfNilpotentQuotient R L L h₁ this
  simp only [LieRing.IsNilpotent, LieModule.isNilpotent_iff R] at h₂ ⊢
  peel h₂ with k hk
  simp [← LieSubmodule.toSubmodule_inj, coe_lowerCentralSeries_ideal_quot_eq, hk]

/--
theorem `LieAlgebra.non_trivial_center_of_isNilpotent` / 定理 `LieAlgebra.non_trivial_center_of_isNilpotent`

English:
theorem LieAlgebra.non_trivial_center_of_isNilpotent
  given: [Nontrivial L] [IsNilpotent L]
  proof: LieModule.nontrivial_max_triv_of_isNilpotent R L L

中文:
定理 LieAlgebra.non_trivial_center_of_isNilpotent
  条件: [Nontrivial L] [IsNilpotent L]
  证明: LieModule.nontrivial_max_triv_of_isNilpotent R L L

Depends on / 依赖: LieModule, LieModule.nontrivial_max_triv_of_isNilpotent, nontrivial_max_triv_of_isNilpotent
-/
theorem LieAlgebra.non_trivial_center_of_isNilpotent [Nontrivial L] [IsNilpotent L] :
Nontrivial center R L :=
  LieModule.nontrivial_max_triv_of_isNilpotent R L L

/--
theorem `LieIdeal.map_lowerCentralSeries_le` / 定理 `LieIdeal.map_lowerCentralSeries_le`

English:
theorem LieIdeal.map_lowerCentralSeries_le
  given: (k : Nat) {f : L ->ₗ⁅R⁆ L'}
  proof: by
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ]
    exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie le_top ih)

中文:
定理 LieIdeal.map_lowerCentralSeries_le
  条件: (k : 自然数) {f : L ->ₗ⁅R⁆ L'}
  证明: by
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ]
    exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie le_top ih)

Depends on / 依赖: LieIdeal, LieIdeal.map_bracket_le, LieModule, LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero, LieSubmodule, LieSubmodule.mono_lie, le_top, le_trans, lowerCentralSeries_succ, lowerCentralSeries_zero, map_bracket_le, mono_lie
-/
theorem LieIdeal.map_lowerCentralSeries_le (k : Nat) {f : L ->ₗ⁅R⁆ L'} :
    LieIdeal.map f (lowerCentralSeries R L L k) <= lowerCentralSeries R L' L' k := by
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero, le_top]
  | succ k ih =>
    simp only [LieModule.lowerCentralSeries_succ]
    exact le_trans (LieIdeal.map_bracket_le f) (LieSubmodule.mono_lie le_top ih)

/--
theorem `LieIdeal.lowerCentralSeries_map_eq` / 定理 `LieIdeal.lowerCentralSeries_map_eq`

English:
theorem LieIdeal.lowerCentralSeries_map_eq
  given: (k : Nat) {f : L ->ₗ⁅R⁆ L'} (h : Function.Surjective f)
  proof: by
  have h' : (⊤ : LieIdeal R L).map f = ⊤ := by
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero]; exact h'
  | succ k ih => simp only [LieModule.lowerCentralSeries_succ, LieIdeal.map_bracket_eq

中文:
定理 LieIdeal.lowerCentralSeries_map_eq
  条件: (k : 自然数) {f : L ->ₗ⁅R⁆ L'} (h : Function.Surjective f)
  证明: by
  have h' : (⊤ : LieIdeal R L).map f = ⊤ := by
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero]; exact h'
  | succ k ih => simp only [LieModule.lowerCentralSeries_succ, LieIdeal.map_bracket_eq

Depends on / 依赖: LieIdeal, LieIdeal.map_bracket_eq, LieModule, LieModule.lowerCentralSeries_succ, LieModule.lowerCentralSeries_zero, f.idealRange_eq_map, f.idealRange_eq_top_of_surjective, idealRange_eq_map, idealRange_eq_top_of_surjective, lowerCentralSeries_succ, lowerCentralSeries_zero, map_bracket_eq
-/
theorem LieIdeal.lowerCentralSeries_map_eq (k : Nat) {f : L ->ₗ⁅R⁆ L'} (h : Function.Surjective f) :
    LieIdeal.map f (lowerCentralSeries R L L k) = lowerCentralSeries R L' L' k := by
  have h' : (⊤ : LieIdeal R L).map f = ⊤ := by
    rw [← f.idealRange_eq_map]
    exact f.idealRange_eq_top_of_surjective h
  induction k with
  | zero => simp only [LieModule.lowerCentralSeries_zero]; exact h'
  | succ k ih => simp only [LieModule.lowerCentralSeries_succ, LieIdeal.map_bracket_eq f h, ih, h']

/--
theorem `Function.Injective.lieAlgebra_isNilpotent` / 定理 `Function.Injective.lieAlgebra_isNilpotent`

English:
theorem Function.Injective.lieAlgebra_isNilpotent
  statement: [h₁ : IsNilpotent L'] {f : L ->ₗ⁅R⁆ L'}
  proof: by
  rw [LieRing.IsNilpotent]; rw [LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.map_lowerCentralSeries_le

中文:
定理 Function.Injective.lieAlgebra_isNilpotent
  结论: [h₁ : IsNilpotent L'] {f : L ->ₗ⁅R⁆ L'}
  证明: by
  rw [LieRing.IsNilpotent]; rw [LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.map_lowerCentralSeries_le

Depends on / 依赖: IsNilpotent, LieIdeal, LieIdeal.bot_of_map_eq_bot, LieIdeal.map_lowerCentralSeries_le, LieModule, LieModule.isNilpotent_iff, LieRing, LieRing.IsNilpotent, bot_of_map_eq_bot, eq_bot_iff, isNilpotent_iff, map_lowerCentralSeries_le
-/
theorem Function.Injective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L'] {f : L ->ₗ⁅R⁆ L'}
    (h₂ : Function.Injective f) : IsNilpotent L := by
  rw [LieRing.IsNilpotent]; rw [LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  apply LieIdeal.bot_of_map_eq_bot h₂; rw [eq_bot_iff, ← hk]
  apply LieIdeal.map_lowerCentralSeries_le

/--
theorem `Function.Surjective.lieAlgebra_isNilpotent` / 定理 `Function.Surjective.lieAlgebra_isNilpotent`

English:
theorem Function.Surjective.lieAlgebra_isNilpotent
  statement: [h₁ : IsNilpotent L] {f : L ->ₗ⁅R⁆ L'}
  proof: by
  rw [LieRing.IsNilpotent]; rw [LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  rw [← LieIdeal.lowerCentralSeries_map_eq k h₂]; rw [hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

中文:
定理 Function.Surjective.lieAlgebra_isNilpotent
  结论: [h₁ : IsNilpotent L] {f : L ->ₗ⁅R⁆ L'}
  证明: by
  rw [LieRing.IsNilpotent]; rw [LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  rw [← LieIdeal.lowerCentralSeries_map_eq k h₂]; rw [hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

Depends on / 依赖: IsNilpotent, LieIdeal, LieIdeal.lowerCentralSeries_map_eq, LieIdeal.map_eq_bot_iff, LieModule, LieModule.isNilpotent_iff, LieRing, LieRing.IsNilpotent, bot_le, isNilpotent_iff, lowerCentralSeries_map_eq, map_eq_bot_iff
-/
theorem Function.Surjective.lieAlgebra_isNilpotent [h₁ : IsNilpotent L] {f : L ->ₗ⁅R⁆ L'}
    (h₂ : Function.Surjective f) : IsNilpotent L' := by
  rw [LieRing.IsNilpotent]; rw [LieModule.isNilpotent_iff R] at h₁ ⊢
  peel h₁ with k hk
  rw [← LieIdeal.lowerCentralSeries_map_eq k h₂]; rw [hk]
  simp only [LieIdeal.map_eq_bot_iff, bot_le]

/--
theorem `LieEquiv.nilpotent_iff_equiv_nilpotent` / 定理 `LieEquiv.nilpotent_iff_equiv_nilpotent`

English:
theorem LieEquiv.nilpotent_iff_equiv_nilpotent
  given: (e : L ≃ₗ⁅R⁆ L')
  proof: by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isNilpotent
  · exact e.injective.lieAlgebra_isNilpotent

中文:
定理 LieEquiv.nilpotent_iff_equiv_nilpotent
  条件: (e : L ≃ₗ⁅R⁆ L')
  证明: by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isNilpotent
  · exact e.injective.lieAlgebra_isNilpotent

Depends on / 依赖: e.injective.lieAlgebra_isNilpotent, e.symm.injective.lieAlgebra_isNilpotent, injective, lieAlgebra_isNilpotent
-/
theorem LieEquiv.nilpotent_iff_equiv_nilpotent (e : L ≃ₗ⁅R⁆ L') :
    IsNilpotent L ↔ IsNilpotent L' := by
  constructor <;> intro h
  · exact e.symm.injective.lieAlgebra_isNilpotent
  · exact e.injective.lieAlgebra_isNilpotent

/--
theorem `LieHom.isNilpotent_range` / 定理 `LieHom.isNilpotent_range`

English:
theorem LieHom.isNilpotent_range
  given: [IsNilpotent L] (f : L ->ₗ⁅R⁆ L')
  statement: IsNilpotent f.range
  proof: f.surjective_rangeRestrict.lieAlgebra_isNilpotent

中文:
定理 LieHom.isNilpotent_range
  条件: [IsNilpotent L] (f : L ->ₗ⁅R⁆ L')
  结论: IsNilpotent f.range
  证明: f.surjective_rangeRestrict.lieAlgebra_isNilpotent

Depends on / 依赖: f.surjective_rangeRestrict.lieAlgebra_isNilpotent, lieAlgebra_isNilpotent, surjective_rangeRestrict
-/
theorem LieHom.isNilpotent_range [IsNilpotent L] (f : L ->ₗ⁅R⁆ L') : IsNilpotent f.range :=
  f.surjective_rangeRestrict.lieAlgebra_isNilpotent

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Note that this result is not quite a special case of
`LieModule.isNilpotent_range_toEnd_iff` which concerns nilpotency of the
`(ad R L).range`-module `L`, whereas this result concerns nilpotency of the `(ad R L).range`-module
`(ad R L).range`. -/
@[simp]
/--
theorem `LieAlgebra.isNilpotent_range_ad_iff` / 定理 `LieAlgebra.isNilpotent_range_ad_iff`

English:
theorem LieAlgebra.isNilpotent_range_ad_iff
  statement: IsNilpotent (ad R L).range ↔ IsNilpotent L
  proof: by
  refine ⟨fun h => ?_, ?_⟩
  · have : (ad R L).ker = center R L := by simp
    exact
      LieAlgebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
        ((ad R L).quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr h)
  · intro h
    exact (ad R L).isNilpotent_range

中文:
定理 LieAlgebra.isNilpotent_range_ad_iff
  结论: IsNilpotent (ad R L).range ↔ IsNilpotent L
  证明: by
  refine ⟨fun h => ?_, ?_⟩
  · have : (ad R L).ker = center R L := by simp
    exact
      LieAlgebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
        ((ad R L).quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr h)
  · intro h
    exact (ad R L).isNilpotent_range

Depends on / 依赖: LieAlgebra, LieAlgebra.nilpotent_of_nilpotent_quotient, center, isNilpotent_range, le_of_eq, nilpotent_iff_equiv_nilpotent, nilpotent_of_nilpotent_quotient, quotKerEquivRange, quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr
-/
theorem LieAlgebra.isNilpotent_range_ad_iff : IsNilpotent (ad R L).range ↔ IsNilpotent L := by
  refine ⟨fun h => ?_, ?_⟩
  · have : (ad R L).ker = center R L := by simp
    exact
      LieAlgebra.nilpotent_of_nilpotent_quotient (le_of_eq this)
        ((ad R L).quotKerEquivRange.nilpotent_iff_equiv_nilpotent.mpr h)
  · intro h
    exact (ad R L).isNilpotent_range

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [h
  signature: : LieRing.IsNilpotent L] : LieRing.IsNilpotent (⊤ : LieSubalgebra R L)
  body: LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr h

中文:
实例 [h
  签名: : LieRing.IsNilpotent L] : LieRing.IsNilpotent (⊤ : LieSubalgebra R L)
  定义体: LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr h

Depends on / 依赖: LieSubalgebra, LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr, nilpotent_iff_equiv_nilpotent, topEquiv
-/
instance [h : LieRing.IsNilpotent L] : LieRing.IsNilpotent (⊤ : LieSubalgebra R L) :=
  LieSubalgebra.topEquiv.nilpotent_iff_equiv_nilpotent.mpr h

end NilpotentAlgebras

namespace LieIdeal

open LieModule

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (I : LieIdeal R L)
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
variable (k : Nat)

/--
Definition of `lcs` / `lcs` 的定义

English:
definition lcs
  signature: : LieSubmodule R L M
  body: (fun N => ⁅I, N⁆)^[k] ⊤

@[simp]

中文:
定义 lcs
  签名: : LieSubmodule R L M
  定义体: (fun N => ⁅I, N⁆)^[k] ⊤

@[simp]
-/
def lcs : LieSubmodule R L M :=
  (fun N => ⁅I, N⁆)^[k] ⊤

@[simp]
/--
theorem `lcs_zero` / 定理 `lcs_zero`

English:
theorem lcs_zero
  statement: I.lcs M 0 = ⊤
  proof: rfl

@[simp]

中文:
定理 lcs_zero
  结论: I.lcs M 0 = ⊤
  证明: rfl

@[simp]
-/
theorem lcs_zero : I.lcs M 0 = ⊤ :=
  rfl

@[simp]
/--
theorem `lcs_succ` / 定理 `lcs_succ`

English:
theorem lcs_succ
  statement: I.lcs M (k + 1) = ⁅I, I.lcs M k⁆
  proof: Function.iterate_succ_apply' (fun N => ⁅I, N⁆) k ⊤

中文:
定理 lcs_succ
  结论: I.lcs M (k + 1) = ⁅I, I.lcs M k⁆
  证明: Function.iterate_succ_apply' (fun N => ⁅I, N⁆) k ⊤

Depends on / 依赖: Function, Function.iterate_succ_apply, iterate_succ_apply
-/
theorem lcs_succ : I.lcs M (k + 1) = ⁅I, I.lcs M k⁆ :=
  Function.iterate_succ_apply' (fun N => ⁅I, N⁆) k ⊤

/--
theorem `lcs_top` / 定理 `lcs_top`

English:
theorem lcs_top
  statement: (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k
  proof: rfl

中文:
定理 lcs_top
  结论: (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k
  证明: rfl
-/
theorem lcs_top : (⊤ : LieIdeal R L).lcs M k = lowerCentralSeries R L M k :=
  rfl

set_option backward.isDefEq.respectTransparency false in
-- Porting note: added `LieSubmodule.toSubmodule` in the statement
/--
theorem `coe_lcs_eq` / 定理 `coe_lcs_eq`

English:
theorem coe_lcs_eq
  given: [LieModule R L M]
  proof: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [lowerCentralSeries_succ, lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_modu

中文:
定理 coe_lcs_eq
  条件: [LieModule R L M]
  证明: by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [lowerCentralSeries_succ, lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_modu

Depends on / 依赖: I.lcs, LieSubalgebra, LieSubmodule, LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top, coe_bracket_of_module, lcs_succ, lieIdeal_oper_eq_linear_span, lowerCentralSeries_succ, mem_toSubmodule, mem_top, simp_rw, true_and
-/
theorem coe_lcs_eq [LieModule R L M] :
    LieSubmodule.toSubmodule (I.lcs M k) = lowerCentralSeries R I M k := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp_rw [lowerCentralSeries_succ, lcs_succ, LieSubmodule.lieIdeal_oper_eq_linear_span', ←
      (I.lcs M k).mem_toSubmodule, ih, LieSubmodule.mem_toSubmodule, LieSubmodule.mem_top,
      true_and, (I : LieSubalgebra R L).coe_bracket_of_module]
    simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsNilpotent
  signature: L I] : LieRing.IsNilpotent I
  body: by
  let f : I ->ₗ⁅R⁆ L := I.incl
  let g : I ->ₗ⁅R⁆ I := LieHom.id
  have hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact Function.injective_id.lieModuleIsNilpotent hfg

中文:
实例 [IsNilpotent
  签名: L I] : LieRing.IsNilpotent I
  定义体: by
  let f : I ->ₗ⁅R⁆ L := I.incl
  let g : I ->ₗ⁅R⁆ I := LieHom.id
  have hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact Function.injective_id.lieModuleIsNilpotent hfg

Depends on / 依赖: Function, Function.injective_id.lieModuleIsNilpotent, I.incl, LieHom, LieHom.id, injective_id, lieModuleIsNilpotent
-/
instance [IsNilpotent L I] : LieRing.IsNilpotent I := by
  let f : I ->ₗ⁅R⁆ L := I.incl
  let g : I ->ₗ⁅R⁆ I := LieHom.id
  have hfg : forall x m, ⁅f x, g m⁆ = g ⁅x, m⁆ := by aesop
  exact Function.injective_id.lieModuleIsNilpotent hfg

end LieIdeal

section ExtendScalars

open LieModule TensorProduct

variable (R A L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
  [CommRing A] [Algebra R A]

@[simp]
/--
lemma `LieSubmodule.lowerCentralSeries_tensor_eq_baseChange` / 引理 `LieSubmodule.lowerCentralSeries_tensor_eq_baseChange`

English:
lemma LieSubmodule.lowerCentralSeries_tensor_eq_baseChange
  given: (k : Nat)
  proof: by
  induction k with
  | zero => simp
  | succ k ih => simp only [lowerCentralSeries_succ, ih, ← baseChange_top, lie_baseChange]

中文:
引理 LieSubmodule.lowerCentralSeries_tensor_eq_baseChange
  条件: (k : 自然数)
  证明: by
  induction k with
  | zero => simp
  | succ k ih => simp only [lowerCentralSeries_succ, ih, ← baseChange_top, lie_baseChange]

Depends on / 依赖: baseChange_top, lie_baseChange, lowerCentralSeries_succ
-/
lemma LieSubmodule.lowerCentralSeries_tensor_eq_baseChange (k : Nat) :
    lowerCentralSeries A (A otimes[R] L) (A otimes[R] M) k =
    (lowerCentralSeries R L M k).baseChange A := by
  induction k with
  | zero => simp
  | succ k ih => simp only [lowerCentralSeries_succ, ih, ← baseChange_top, lie_baseChange]

/--
Instance `LieModule.instIsNilpotentTensor` / 实例 `LieModule.instIsNilpotentTensor`

English:
instance LieModule.instIsNilpotentTensor
  signature: [IsNilpotent L M]
  body: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff A]
  exact ⟨k, by simp [hk]⟩

中文:
实例 LieModule.instIsNilpotentTensor
  签名: [IsNilpotent L M]
  定义体: by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff A]
  exact ⟨k, by simp [hk]⟩

Depends on / 依赖: IsNilpotent, IsNilpotent.nilpotent, isNilpotent_iff, nilpotent
-/
instance LieModule.instIsNilpotentTensor [IsNilpotent L M] :
    IsNilpotent (A otimes[R] L) (A otimes[R] M) := by
  obtain ⟨k, hk⟩ := IsNilpotent.nilpotent R L M
  rw [isNilpotent_iff A]
  exact ⟨k, by simp [hk]⟩

end ExtendScalars

namespace LieAlgebra

open LieModule

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L] [LieAlgebra R L]

/--
Definition of `maxNilpotentIdeal` / `maxNilpotentIdeal` 的定义

English:
definition maxNilpotentIdeal
  body: maxNilpotentSubmodule R L L

中文:
定义 maxNilpotentIdeal
  定义体: maxNilpotentSubmodule R L L

Depends on / 依赖: maxNilpotentSubmodule
-/
def maxNilpotentIdeal := maxNilpotentSubmodule R L L

/--
Instance `maxNilpotentIdealIsNilpotent` / 实例 `maxNilpotentIdealIsNilpotent`

English:
instance maxNilpotentIdealIsNilpotent
  signature: [IsNoetherian R L]
  body: instMaxNilpotentSubmoduleIsNilpotent R L L

中文:
实例 maxNilpotentIdealIsNilpotent
  签名: [IsNoetherian R L]
  定义体: instMaxNilpotentSubmoduleIsNilpotent R L L

Depends on / 依赖: instMaxNilpotentSubmoduleIsNilpotent
-/
instance maxNilpotentIdealIsNilpotent [IsNoetherian R L] :
    IsNilpotent L (maxNilpotentIdeal R L) :=
  instMaxNilpotentSubmoduleIsNilpotent R L L

/--
theorem `LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal` / 定理 `LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal`

English:
theorem LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal
  given: [IsNoetherian R L] (I : LieIdeal R L)
  proof: isNilpotent_iff_le_maxNilpotentSubmodule R L L I

中文:
定理 LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal
  条件: [IsNoetherian R L] (I : LieIdeal R L)
  证明: isNilpotent_iff_le_maxNilpotentSubmodule R L L I

Depends on / 依赖: isNilpotent_iff_le_maxNilpotentSubmodule
-/
theorem LieIdeal.isNilpotent_iff_le_maxNilpotentIdeal [IsNoetherian R L] (I : LieIdeal R L) :
    IsNilpotent L I ↔ I <= maxNilpotentIdeal R L :=
  isNilpotent_iff_le_maxNilpotentSubmodule R L L I

/--
theorem `center_le_maxNilpotentIdeal` / 定理 `center_le_maxNilpotentIdeal`

English:
theorem center_le_maxNilpotentIdeal
  statement: center R L <= maxNilpotentIdeal R L
  proof: le_sSup (trivialIsNilpotent L (center R L))

中文:
定理 center_le_maxNilpotentIdeal
  结论: center R L <= maxNilpotentIdeal R L
  证明: le_sSup (trivialIsNilpotent L (center R L))

Depends on / 依赖: center, le_sSup, trivialIsNilpotent
-/
theorem center_le_maxNilpotentIdeal : center R L <= maxNilpotentIdeal R L :=
  le_sSup (trivialIsNilpotent L (center R L))

/--
theorem `maxNilpotentIdeal_le_radical` / 定理 `maxNilpotentIdeal_le_radical`

English:
theorem maxNilpotentIdeal_le_radical
  statement: maxNilpotentIdeal R L <= radical R L
  proof: sSup_le_sSup fun I (_ : IsNilpotent L I) => isSolvable_of_isNilpotent I

中文:
定理 maxNilpotentIdeal_le_radical
  结论: maxNilpotentIdeal R L <= radical R L
  证明: sSup_le_sSup fun I (_ : IsNilpotent L I) => isSolvable_of_isNilpotent I

Depends on / 依赖: IsNilpotent, isSolvable_of_isNilpotent, sSup_le_sSup
-/
theorem maxNilpotentIdeal_le_radical : maxNilpotentIdeal R L <= radical R L :=
  sSup_le_sSup fun I (_ : IsNilpotent L I) => isSolvable_of_isNilpotent I

/--
lemma `maxNilpotentIdeal_eq_top_of_isNilpotent` / 引理 `maxNilpotentIdeal_eq_top_of_isNilpotent`

English:
lemma maxNilpotentIdeal_eq_top_of_isNilpotent
  given: [LieRing.IsNilpotent L]
  proof: maxNilpotentSubmodule_eq_top_of_isNilpotent R L L

中文:
引理 maxNilpotentIdeal_eq_top_of_isNilpotent
  条件: [LieRing.IsNilpotent L]
  证明: maxNilpotentSubmodule_eq_top_of_isNilpotent R L L
-/
@[simp] lemma maxNilpotentIdeal_eq_top_of_isNilpotent [LieRing.IsNilpotent L] :
    maxNilpotentIdeal R L = ⊤ :=
  maxNilpotentSubmodule_eq_top_of_isNilpotent R L L

end LieAlgebra
