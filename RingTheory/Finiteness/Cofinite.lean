/-
Copyright (c) 2026 Martin Winter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Martin Winter
-/
module

public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Co-finitely generated submodules

This files defines the notion of a co-finitely generated submodule. A submodule `S` of a module
`M` is co-finitely generated (or CoFG for short) if the quotient of `M` by `S` is finitely
generated (i.e. FG).

## Main declarations

- `Submodule.CoFG` expresses that a submodule is co-finitely generated.

-/

public section

namespace Submodule

section Ring

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/--
Definition of `CoFG` / `CoFG` 的定义

English:
abbreviation CoFG
  signature: (S : Submodule R M)
  body: Module.Finite R (M ⧸ S)

中文:
缩写 CoFG
  签名: (S : Submodule R M)
  定义体: Module.Finite R (M ⧸ S)

Depends on / 依赖: Finite, Module, Module.Finite
-/
abbrev CoFG (S : Submodule R M) : Prop := Module.Finite R (M ⧸ S)

/--
theorem `CoFG.of_finite` / 定理 `CoFG.of_finite`

English:
theorem CoFG.of_finite
  given: [Module.Finite R M] {S : Submodule R M}
  statement: S.CoFG
  proof: Module.Finite.quotient R S

中文:
定理 CoFG.of_finite
  条件: [Module.Finite R M] {S : Submodule R M}
  结论: S.CoFG
  证明: Module.Finite.quotient R S
-/
@[simp] theorem CoFG.of_finite [Module.Finite R M] {S : Submodule R M} : S.CoFG :=
  Module.Finite.quotient R S

/--
theorem `CoFG.top` / 定理 `CoFG.top`

English:
theorem CoFG.top
  statement: (⊤ : Submodule R M).CoFG
  proof: inferInstance

中文:
定理 CoFG.top
  结论: (⊤ : Submodule R M).CoFG
  证明: inferInstance
-/
@[simp] theorem CoFG.top : (⊤ : Submodule R M).CoFG := inferInstance

variable (R M) in
/--
theorem `_root_.Module.Finite.iff_cofg_bot` / 定理 `_root_.Module.Finite.iff_cofg_bot`

English:
theorem _root_.Module.Finite.iff_cofg_bot
  statement: (⊥ : Submodule R M).CoFG ↔ Module.Finite R M
  proof: ⟨fun _ => Module.Finite.equiv (quotEquivOfEqBot ⊥ rfl), fun _ => CoFG.of_finite⟩

中文:
定理 _root_.Module.Finite.iff_cofg_bot
  结论: (⊥ : Submodule R M).CoFG ↔ Module.Finite R M
  证明: ⟨fun _ => Module.Finite.equiv (quotEquivOfEqBot ⊥ rfl), fun _ => CoFG.of_finite⟩

Depends on / 依赖: CoFG.of_finite, Finite, Module, Module.Finite.equiv, of_finite, quotEquivOfEqBot
-/
theorem _root_.Module.Finite.iff_cofg_bot : (⊥ : Submodule R M).CoFG ↔ Module.Finite R M :=
  ⟨fun _ => Module.Finite.equiv (quotEquivOfEqBot ⊥ rfl), fun _ => CoFG.of_finite⟩

/--
theorem `CoFG.fg_of_isCompl` / 定理 `CoFG.fg_of_isCompl`

English:
theorem CoFG.fg_of_isCompl
  given: {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG)
  statement: T.FG
  proof: Module.Finite.iff_fg.mp Module.Finite.equiv quotientEquivOfIsCompl S T hST

中文:
定理 CoFG.fg_of_isCompl
  条件: {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG)
  结论: T.FG
  证明: Module.Finite.iff_fg.mp Module.Finite.equiv quotientEquivOfIsCompl S T hST

Depends on / 依赖: Finite, Module, Module.Finite.equiv, Module.Finite.iff_fg.mp, iff_fg, quotientEquivOfIsCompl
-/
theorem CoFG.fg_of_isCompl {S T : Submodule R M} (hST : IsCompl S T) (hS : S.CoFG) : T.FG :=
Module.Finite.iff_fg.mp Module.Finite.equiv quotientEquivOfIsCompl S T hST

/--
theorem `CoFG.fg_of_disjoint` / 定理 `CoFG.fg_of_disjoint`

English:
theorem CoFG.fg_of_disjoint
  statement: [IsNoetherianRing R] {S T : Submodule R M} (hST : Disjoint S T)
  proof: .of_disjoint_of_isNoetherian_quotient hST

中文:
定理 CoFG.fg_of_disjoint
  结论: [IsNoetherianRing R] {S T : Submodule R M} (hST : Disjoint S T)
  证明: .of_disjoint_of_isNoetherian_quotient hST

Depends on / 依赖: of_disjoint_of_isNoetherian_quotient
-/
theorem CoFG.fg_of_disjoint [IsNoetherianRing R] {S T : Submodule R M} (hST : Disjoint S T)
    (hT : T.CoFG) : S.FG :=
  .of_disjoint_of_isNoetherian_quotient hST

/--
theorem `FG.cofg_of_codisjoint` / 定理 `FG.cofg_of_codisjoint`

English:
theorem FG.cofg_of_codisjoint
  given: {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG)
  proof: have := Module.Finite.iff_fg.mpr hS
  .of_surjective (T.mkQ.domRestrict S) (by simp [← LinearMap.range_eq_top, hST.symm.eq_top])

中文:
定理 FG.cofg_of_codisjoint
  条件: {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG)
  证明: have := Module.Finite.iff_fg.mpr hS
  .of_surjective (T.mkQ.domRestrict S) (by simp [← LinearMap.range_eq_top, hST.symm.eq_top])

Depends on / 依赖: Finite, LinearMap, LinearMap.range_eq_top, Module, Module.Finite.iff_fg.mpr, T.mkQ.domRestrict, domRestrict, eq_top, hST.symm.eq_top, iff_fg, of_surjective, range_eq_top
-/
theorem FG.cofg_of_codisjoint {S T : Submodule R M} (hST : Codisjoint S T) (hS : S.FG) :
    T.CoFG :=
  have := Module.Finite.iff_fg.mpr hS
  .of_surjective (T.mkQ.domRestrict S) (by simp [← LinearMap.range_eq_top, hST.symm.eq_top])

/--
theorem `FG.cofg_of_isCompl` / 定理 `FG.cofg_of_isCompl`

English:
theorem FG.cofg_of_isCompl
  given: {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG)
  statement: T.CoFG
  proof: hS.cofg_of_codisjoint hST.codisjoint

中文:
定理 FG.cofg_of_isCompl
  条件: {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG)
  结论: T.CoFG
  证明: hS.cofg_of_codisjoint hST.codisjoint

Depends on / 依赖: codisjoint, cofg_of_codisjoint, hS.cofg_of_codisjoint, hST.codisjoint
-/
theorem FG.cofg_of_isCompl {S T : Submodule R M} (hST : IsCompl S T) (hS : S.FG) : T.CoFG :=
  hS.cofg_of_codisjoint hST.codisjoint

/--
theorem `CoFG.of_le` / 定理 `CoFG.of_le`

English:
theorem CoFG.of_le
  given: {S T : Submodule R M} (hT : S <= T) (hS : S.CoFG)
  statement: T.CoFG
  proof: by
  rw [← sup_eq_right.mpr hT]
  exact Module.Finite.equiv (quotientQuotientEquivQuotientSup S T)

@[deprecated (since := "2026-05-13")]
alias CoFG.cofg_of_le := CoFG.of_le

中文:
定理 CoFG.of_le
  条件: {S T : Submodule R M} (hT : S <= T) (hS : S.CoFG)
  结论: T.CoFG
  证明: by
  rw [← sup_eq_right.mpr hT]
  exact Module.Finite.equiv (quotientQuotientEquivQuotientSup S T)

@[deprecated (since := "2026-05-13")]
alias CoFG.cofg_of_le := CoFG.of_le

Depends on / 依赖: Finite, Module, Module.Finite.equiv, quotientQuotientEquivQuotientSup, sup_eq_right, sup_eq_right.mpr
-/
theorem CoFG.of_le {S T : Submodule R M} (hT : S <= T) (hS : S.CoFG) : T.CoFG := by
  rw [← sup_eq_right.mpr hT]
  exact Module.Finite.equiv (quotientQuotientEquivQuotientSup S T)

@[deprecated (since := "2026-05-13")]
alias CoFG.cofg_of_le := CoFG.of_le

section LinearMap

open LinearMap

variable {N : Type*} [AddCommGroup N] [Module R N]

/--
theorem `range_fg_iff_ker_cofg` / 定理 `range_fg_iff_ker_cofg`

English:
theorem range_fg_iff_ker_cofg
  given: {f : M ->ₗ[R] N}
  statement: (range f).FG ↔ (ker f).CoFG
  proof: by
  rw [← Module.Finite.iff_fg]
exact Module.Finite.equiv_iff f.quotKerEquivRange.symm

中文:
定理 range_fg_iff_ker_cofg
  条件: {f : M ->ₗ[R] N}
  结论: (range f).FG ↔ (ker f).CoFG
  证明: by
  rw [← Module.Finite.iff_fg]
exact Module.Finite.equiv_iff f.quotKerEquivRange.symm

Depends on / 依赖: Finite, Module, Module.Finite.equiv_iff, Module.Finite.iff_fg, equiv_iff, f.quotKerEquivRange.symm, iff_fg, quotKerEquivRange
-/
theorem range_fg_iff_ker_cofg {f : M ->ₗ[R] N} : (range f).FG ↔ (ker f).CoFG := by
  rw [← Module.Finite.iff_fg]
exact Module.Finite.equiv_iff f.quotKerEquivRange.symm

/--
theorem `CoFG.ker` / 定理 `CoFG.ker`

English:
theorem CoFG.ker
  given: [IsNoetherian R N] (f : M ->ₗ[R] N)
  statement: (ker f).CoFG
  proof: range_fg_iff_ker_cofg.mp IsNoetherian.noetherian _

中文:
定理 CoFG.ker
  条件: [IsNoetherian R N] (f : M ->ₗ[R] N)
  结论: (ker f).CoFG
  证明: range_fg_iff_ker_cofg.mp IsNoetherian.noetherian _
-/
protected theorem CoFG.ker [IsNoetherian R N] (f : M ->ₗ[R] N) : (ker f).CoFG :=
range_fg_iff_ker_cofg.mp IsNoetherian.noetherian _

end LinearMap

section IsNoetherianRing

variable [IsNoetherianRing R]

/--
theorem `CoFG.inf` / 定理 `CoFG.inf`

English:
theorem CoFG.inf
  given: {S T : Submodule R M} (hS : S.CoFG) (hT : T.CoFG)
  proof: by
  rw [← Submodule.ker_mkQ S]; rw [← Submodule.ker_mkQ T]; rw [← LinearMap.ker_prod]
  exact CoFG.ker _

中文:
定理 CoFG.inf
  条件: {S T : Submodule R M} (hS : S.CoFG) (hT : T.CoFG)
  证明: by
  rw [← Submodule.ker_mkQ S]; rw [← Submodule.ker_mkQ T]; rw [← LinearMap.ker_prod]
  exact CoFG.ker _

Depends on / 依赖: CoFG.ker, LinearMap, LinearMap.ker_prod, Submodule, Submodule.ker_mkQ, ker_mkQ, ker_prod
-/
theorem CoFG.inf {S T : Submodule R M} (hS : S.CoFG) (hT : T.CoFG) :
      (S ⊓ T).CoFG := by
  rw [← Submodule.ker_mkQ S]; rw [← Submodule.ker_mkQ T]; rw [← LinearMap.ker_prod]
  exact CoFG.ker _

/--
theorem `CoFG.sInf` / 定理 `CoFG.sInf`

English:
theorem CoFG.sInf
  given: {s : Finset (Submodule R M)} (hs : forall S in s, S.CoFG)
  proof: by
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact hs.1.inf (hs' hs.2)

中文:
定理 CoFG.sInf
  条件: {s : Finset (Submodule R M)} (hs : 对任意 S in s, S.CoFG)
  证明: by
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact hs.1.inf (hs' hs.2)
-/
protected theorem CoFG.sInf {s : Finset (Submodule R M)} (hs : forall S in s, S.CoFG) :
    (sInf (s : Set (Submodule R M))).CoFG := by
  induction s using Finset.induction with
  | empty => simp
  | insert w s hws hs' =>
    simp only [Finset.mem_insert, forall_eq_or_imp, Finset.coe_insert, sInf_insert] at *
    exact hs.1.inf (hs' hs.2)

/--
theorem `CoFG.sInf_of_finite` / 定理 `CoFG.sInf_of_finite`

English:
theorem CoFG.sInf_of_finite
  statement: {s : Set (Submodule R M)} (hs : s.Finite)
  proof: by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact CoFG.sInf hcofg

中文:
定理 CoFG.sInf_of_finite
  结论: {s : Set (Submodule R M)} (hs : s.Finite)
  证明: by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact CoFG.sInf hcofg

Depends on / 依赖: CoFG.sInf, coe_toFinset, hs.coe_toFinset
-/
theorem CoFG.sInf_of_finite {s : Set (Submodule R M)} (hs : s.Finite)
    (hcofg : forall S in s, S.CoFG) : (sInf s).CoFG := by
  rw [← hs.coe_toFinset] at hcofg ⊢; exact CoFG.sInf hcofg

end IsNoetherianRing

end Ring

end Submodule
