/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/
module

public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.SetTheory.Ordinal.Exponential
public import Mathlib.SetTheory.Ordinal.Family

import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finsupp.AList

/-!
# Cantor Normal Form

The Cantor normal form of an ordinal is generally defined as its base `ω` expansion, with its
non-zero exponents in decreasing order. Here, we more generally define a base `b` expansion
`Ordinal.CNF` in this manner, which is well-behaved for any `b ≥ 2`.

## Implementation notes

We implement `Ordinal.CNF` as an association list, where keys are exponents and values are
coefficients. This is because this structure intrinsically reflects two key properties of the Cantor
normal form:

- It is ordered.
- It has finitely many entries.

## Todo

- Prove the basic results relating the CNF to the arithmetic operations on ordinals.
-/

public noncomputable section

universe u

open List

namespace Ordinal.CNF

/-! ### Cantor normal form as a list -/

/-- Inducts on the base `b` expansion of an ordinal. -/
@[elab_as_elim]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: (b : Ordinal) {C : Ordinal -> Sort*} (H0 : C 0)
  body: if h : o = 0 then h ▸ H0 else H o h (CNF.rec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]

中文:
定义 rec
  签名: (b : Ordinal) {C : Ordinal -> Sort*} (H0 : C 0)
  定义体: if h : o = 0 then h ▸ H0 else H o h (CNF.rec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]
-/
protected def rec (b : Ordinal) {C : Ordinal -> Sort*} (H0 : C 0)
    (H : forall o, o != 0 -> C (o % b ^ log b o) -> C o) (o : Ordinal) : C o :=
  if h : o = 0 then h ▸ H0 else H o h (CNF.rec b H0 H (o % b ^ log b o))
termination_by o
decreasing_by exact mod_opow_log_lt_self b h

@[simp]
/--
theorem `rec_zero` / 定理 `rec_zero`

English:
theorem rec_zero
  statement: {C : Ordinal -> Sort*} (b : Ordinal) (H0 : C 0)
  proof: by
  rw [CNF.rec]; rw [dif_pos rfl]

中文:
定理 rec_zero
  结论: {C : Ordinal -> Sort*} (b : Ordinal) (H0 : C 0)
  证明: by
  rw [CNF.rec]; rw [dif_pos rfl]

Depends on / 依赖: CNF.rec, dif_pos
-/
theorem rec_zero {C : Ordinal -> Sort*} (b : Ordinal) (H0 : C 0)
    (H : forall o, o != 0 -> C (o % b ^ log b o) -> C o) : CNF.rec b H0 H 0 = H0 := by
  rw [CNF.rec]; rw [dif_pos rfl]

/--
theorem `rec_pos` / 定理 `rec_pos`

English:
theorem rec_pos
  statement: (b : Ordinal) {o : Ordinal} {C : Ordinal -> Sort*} (ho : o != 0) (H0 : C 0)
  proof: by
  rw [CNF.rec]; rw [dif_neg]

中文:
定理 rec_pos
  结论: (b : Ordinal) {o : Ordinal} {C : Ordinal -> Sort*} (ho : o != 0) (H0 : C 0)
  证明: by
  rw [CNF.rec]; rw [dif_neg]

Depends on / 依赖: CNF.rec, dif_neg
-/
theorem rec_pos (b : Ordinal) {o : Ordinal} {C : Ordinal -> Sort*} (ho : o != 0) (H0 : C 0)
    (H : forall o, o != 0 -> C (o % b ^ log b o) -> C o) :
    CNF.rec b H0 H o = H o ho (@CNF.rec b C H0 H _) := by
  rw [CNF.rec]; rw [dif_neg]

/-- The Cantor normal form of an ordinal `o` is the list of coefficients and exponents in the
base-`b` expansion of `o`.

We special-case `CNF 0 o = CNF 1 o = [(0, o)]` for `o ≠ 0`.

`CNF b (b ^ u₁ * v₁ + b ^ u₂ * v₂) = [(u₁, v₁), (u₂, v₂)]` -/
@[pp_nodot]
/--
Definition of `_root_.Ordinal.CNF` / `_root_.Ordinal.CNF` 的定义

English:
definition _root_.Ordinal.CNF
  signature: (b o : Ordinal)
  body: CNF.rec b [] (fun o _ IH => (log b o, o / b ^ log b o)::IH) o

@[simp]

中文:
定义 _root_.Ordinal.CNF
  签名: (b o : Ordinal)
  定义体: CNF.rec b [] (fun o _ IH => (log b o, o / b ^ log b o)::IH) o

@[simp]

Depends on / 依赖: CNF.rec
-/
def _root_.Ordinal.CNF (b o : Ordinal) : List (Ordinal × Ordinal) :=
  CNF.rec b [] (fun o _ IH => (log b o, o / b ^ log b o)::IH) o

@[simp]
/--
theorem `zero_right` / 定理 `zero_right`

English:
theorem zero_right
  given: (b : Ordinal)
  statement: CNF b 0 = []
  proof: rec_zero b _ _

中文:
定理 zero_right
  条件: (b : Ordinal)
  结论: CNF b 0 = []
  证明: rec_zero b _ _

Depends on / 依赖: rec_zero
-/
theorem zero_right (b : Ordinal) : CNF b 0 = [] :=
  rec_zero b _ _

/--
theorem `ne_zero` / 定理 `ne_zero`

English:
theorem ne_zero
  given: {b o : Ordinal} (ho : o != 0)
  proof: rec_pos b ho _ _

中文:
定理 ne_zero
  条件: {b o : Ordinal} (ho : o != 0)
  证明: rec_pos b ho _ _
-/
protected theorem ne_zero {b o : Ordinal} (ho : o != 0) :
    CNF b o = (log b o, o / b ^ log b o)::CNF b (o % b ^ log b o) :=
  rec_pos b ho _ _

/--
theorem `opow_mul_add` / 定理 `opow_mul_add`

English:
theorem opow_mul_add
  statement: {b e x y : Ordinal}
  proof: by
  have hb' := hb.ne_bot
  rw [CNF.ne_zero]
  · rw [log_opow_mul_add hb hx hy, log_eq_zero hxb, add_zero,
      mul_add_div _ (opow_ne_zero _ hb'), Ordinal.div_eq_zero_of_lt hy, add_zero,
      mul_add_mod_self, mod_eq_of_lt hy]
  · simp_all

中文:
定理 opow_mul_add
  结论: {b e x y : Ordinal}
  证明: by
  have hb' := hb.ne_bot
  rw [CNF.ne_zero]
  · rw [log_opow_mul_add hb hx hy, log_eq_zero hxb, add_zero,
      mul_add_div _ (opow_ne_zero _ hb'), Ordinal.div_eq_zero_of_lt hy, add_zero,
      mul_add_mod_self, mod_eq_of_lt hy]
  · simp_all
-/
protected theorem opow_mul_add {b e x y : Ordinal}
    (hb : 1 < b) (hx : x != 0) (hxb : x < b) (hy : y < b ^ e) :
    CNF b (b ^ e * x + y) = (e, x) :: CNF b y := by
  have hb' := hb.ne_bot
  rw [CNF.ne_zero]
  · rw [log_opow_mul_add hb hx hy, log_eq_zero hxb, add_zero,
      mul_add_div _ (opow_ne_zero _ hb'), Ordinal.div_eq_zero_of_lt hy, add_zero,
      mul_add_mod_self, mod_eq_of_lt hy]
  · simp_all

/--
theorem `zero_left` / 定理 `zero_left`

English:
theorem zero_left
  given: {o : Ordinal} (ho : o != 0)
  statement: CNF 0 o = [(0, o)]
  proof: by
  simp [CNF.ne_zero ho]

中文:
定理 zero_left
  条件: {o : Ordinal} (ho : o != 0)
  结论: CNF 0 o = [(0, o)]
  证明: by
  simp [CNF.ne_zero ho]
-/
protected theorem zero_left {o : Ordinal} (ho : o != 0) : CNF 0 o = [(0, o)] := by
  simp [CNF.ne_zero ho]

/--
theorem `one_left` / 定理 `one_left`

English:
theorem one_left
  given: {o : Ordinal} (ho : o != 0)
  statement: CNF 1 o = [(0, o)]
  proof: by
  simp [CNF.ne_zero ho]

中文:
定理 one_left
  条件: {o : Ordinal} (ho : o != 0)
  结论: CNF 1 o = [(0, o)]
  证明: by
  simp [CNF.ne_zero ho]
-/
protected theorem one_left {o : Ordinal} (ho : o != 0) : CNF 1 o = [(0, o)] := by
  simp [CNF.ne_zero ho]

/--
theorem `of_le_one` / 定理 `of_le_one`

English:
theorem of_le_one
  given: {b o : Ordinal} (hb : b <= 1) (ho : o != 0)
  statement: CNF b o = [(0, o)]
  proof: by
  rcases Order.le_one_iff.1 hb with (rfl | rfl)
  exacts [CNF.zero_left ho, CNF.one_left ho]

中文:
定理 of_le_one
  条件: {b o : Ordinal} (hb : b <= 1) (ho : o != 0)
  结论: CNF b o = [(0, o)]
  证明: by
  rcases Order.le_one_iff.1 hb with (rfl | rfl)
  exacts [CNF.zero_left ho, CNF.one_left ho]
-/
protected theorem of_le_one {b o : Ordinal} (hb : b <= 1) (ho : o != 0) : CNF b o = [(0, o)] := by
  rcases Order.le_one_iff.1 hb with (rfl | rfl)
  exacts [CNF.zero_left ho, CNF.one_left ho]

/--
theorem `of_lt` / 定理 `of_lt`

English:
theorem of_lt
  given: {b o : Ordinal} (ho : o != 0) (hb : o < b)
  statement: CNF b o = [(0, o)]
  proof: by
  rw [CNF.ne_zero ho]; rw [log_eq_zero hb]; rw [opow_zero]; rw [div_one]; rw [mod_one]; rw [zero_right]

中文:
定理 of_lt
  条件: {b o : Ordinal} (ho : o != 0) (hb : o < b)
  结论: CNF b o = [(0, o)]
  证明: by
  rw [CNF.ne_zero ho]; rw [log_eq_zero hb]; rw [opow_zero]; rw [div_one]; rw [mod_one]; rw [zero_right]
-/
protected theorem of_lt {b o : Ordinal} (ho : o != 0) (hb : o < b) : CNF b o = [(0, o)] := by
  rw [CNF.ne_zero ho]; rw [log_eq_zero hb]; rw [opow_zero]; rw [div_one]; rw [mod_one]; rw [zero_right]

/--
theorem `foldr` / 定理 `foldr`

English:
theorem foldr
  given: (b o : Ordinal)
  statement: (CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o
  proof: by
  refine CNF.rec b ?_ ?_ o
  · rw [zero_right, foldr_nil]
  · intro o ho IH
    rw [CNF.ne_zero ho]; rw [foldr_cons]; rw [IH]; rw [div_add_mod]

中文:
定理 foldr
  条件: (b o : Ordinal)
  结论: (CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o
  证明: by
  refine CNF.rec b ?_ ?_ o
  · rw [zero_right, foldr_nil]
  · intro o ho IH
    rw [CNF.ne_zero ho]; rw [foldr_cons]; rw [IH]; rw [div_add_mod]
-/
protected theorem foldr (b o : Ordinal) : (CNF b o).foldr (fun p r => b ^ p.1 * p.2 + r) 0 = o := by
  refine CNF.rec b ?_ ?_ o
  · rw [zero_right, foldr_nil]
  · intro o ho IH
    rw [CNF.ne_zero ho]; rw [foldr_cons]; rw [IH]; rw [div_add_mod]

/--
theorem `fst_le_log` / 定理 `fst_le_log`

English:
theorem fst_le_log
  given: {b o : Ordinal.{u}} {x : Ordinal × Ordinal}
  statement: x in CNF b o -> x.1 <= log b o
  proof: by
  refine CNF.rec b ?_ (fun o ho H => ?_) o
  · simp
  · rw [CNF.ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

中文:
定理 fst_le_log
  条件: {b o : Ordinal.{u}} {x : Ordinal × Ordinal}
  结论: x in CNF b o -> x.1 <= log b o
  证明: by
  refine CNF.rec b ?_ (fun o ho H => ?_) o
  · simp
  · rw [CNF.ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

Depends on / 依赖: CNF.ne_zero, CNF.rec, log_mono_right, mem_cons, mod_opow_log_lt_self, ne_zero
-/
theorem fst_le_log {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x in CNF b o -> x.1 <= log b o := by
  refine CNF.rec b ?_ (fun o ho H => ?_) o
  · simp
  · rw [CNF.ne_zero ho, mem_cons]
    rintro (rfl | h)
    · rfl
    · exact (H h).trans (log_mono_right _ (mod_opow_log_lt_self b ho).le)

/--
theorem `snd_pos` / 定理 `snd_pos`

English:
theorem snd_pos
  given: {b o : Ordinal.{u}} {x : Ordinal × Ordinal}
  statement: x in CNF b o -> 0 < x.2
  proof: by
  refine CNF.rec b (by simp) (fun o ho IH => ?_) o
  rw [CNF.ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

@[deprecated (since := "2026-01-11")]
alias lt_snd := snd_pos

中文:
定理 snd_pos
  条件: {b o : Ordinal.{u}} {x : Ordinal × Ordinal}
  结论: x in CNF b o -> 0 < x.2
  证明: by
  refine CNF.rec b (by simp) (fun o ho IH => ?_) o
  rw [CNF.ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

@[deprecated (since := "2026-01-11")]
alias lt_snd := snd_pos

Depends on / 依赖: CNF.ne_zero, CNF.rec, div_opow_log_pos, ne_zero
-/
theorem snd_pos {b o : Ordinal.{u}} {x : Ordinal × Ordinal} : x in CNF b o -> 0 < x.2 := by
  refine CNF.rec b (by simp) (fun o ho IH => ?_) o
  rw [CNF.ne_zero ho]
  rintro (h | ⟨_, h⟩)
  · exact div_opow_log_pos b ho
  · exact IH h

@[deprecated (since := "2026-01-11")]
alias lt_snd := snd_pos

/--
theorem `snd_lt` / 定理 `snd_lt`

English:
theorem snd_lt
  given: {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal}
  proof: by
  refine CNF.rec b ?_ (fun o ho IH => ?_) o
  · simp
  · rw [CNF.ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

中文:
定理 snd_lt
  条件: {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal}
  证明: by
  refine CNF.rec b ?_ (fun o ho IH => ?_) o
  · simp
  · rw [CNF.ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

Depends on / 依赖: CNF.ne_zero, CNF.rec, div_opow_log_lt, mem_cons, mem_cons.mp, ne_zero
-/
theorem snd_lt {b o : Ordinal.{u}} (hb : 1 < b) {x : Ordinal × Ordinal} :
    x in CNF b o -> x.2 < b := by
  refine CNF.rec b ?_ (fun o ho IH => ?_) o
  · simp
  · rw [CNF.ne_zero ho]
    intro h
    obtain rfl | h := mem_cons.mp h
    · exact div_opow_log_lt o hb
    · exact IH h

/--
theorem `sortedGT` / 定理 `sortedGT`

English:
theorem sortedGT
  given: (b o : Ordinal)
  statement: ((CNF b o).map Prod.fst).SortedGT
  proof: by
  simp_rw [sortedGT_iff_pairwise]
  refine CNF.rec b ?_ (fun o ho IH => ?_) o
  · rw [zero_right]
    exact .nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF.of_le_one hb ho]
      exact pairwise_singleton _ _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF.of_lt ho hob]
        exac

中文:
定理 sortedGT
  条件: (b o : Ordinal)
  结论: ((CNF b o).map Prod.fst).SortedGT
  证明: by
  simp_rw [sortedGT_iff_pairwise]
  refine CNF.rec b ?_ (fun o ho IH => ?_) o
  · rw [zero_right]
    exact .nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF.of_le_one hb ho]
      exact pairwise_singleton _ _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF.of_lt ho hob]
        exac
-/
protected theorem sortedGT (b o : Ordinal) : ((CNF b o).map Prod.fst).SortedGT := by
  simp_rw [sortedGT_iff_pairwise]
  refine CNF.rec b ?_ (fun o ho IH => ?_) o
  · rw [zero_right]
    exact .nil
  · rcases le_or_gt b 1 with hb | hb
    · rw [CNF.of_le_one hb ho]
      exact pairwise_singleton _ _
    · obtain hob | hbo := lt_or_ge o b
      · rw [CNF.of_lt ho hob]
        exact pairwise_singleton _ _
      · rw [CNF.ne_zero ho, map_cons, pairwise_cons]
        refine ⟨fun a H => ?_, IH⟩
        rw [mem_map] at H
        rcases H with ⟨⟨a, a'⟩, H, rfl⟩
        exact (fst_le_log H).trans_lt (log_mod_opow_log_lt_log_self hb hbo)

@[deprecated (since := "2026-01-11")]
alias sorted := CNF.sortedGT

/--
theorem `nodupKeys` / 定理 `nodupKeys`

English:
theorem nodupKeys
  given: (b o : Ordinal)
  statement: (map Prod.toSigma (CNF b o)).NodupKeys
  proof: by
  rw [NodupKeys]; rw [List.keys]; rw [map_map]; rw [Prod.fst_comp_toSigma]
  exact (CNF.sortedGT ..).nodup

中文:
定理 nodupKeys
  条件: (b o : Ordinal)
  结论: (map Prod.toSigma (CNF b o)).NodupKeys
  证明: by
  rw [NodupKeys]; rw [List.keys]; rw [map_map]; rw [Prod.fst_comp_toSigma]
  exact (CNF.sortedGT ..).nodup
-/
private theorem nodupKeys (b o : Ordinal) : (map Prod.toSigma (CNF b o)).NodupKeys := by
  rw [NodupKeys]; rw [List.keys]; rw [map_map]; rw [Prod.fst_comp_toSigma]
  exact (CNF.sortedGT ..).nodup

/-! ### Cantor normal form as a finsupp -/

open AList Finsupp

/-- `CNF.coeff b o` is the finitely supported function returning the coefficient of `b ^ e` in the
Cantor Normal Form (`CNF`) of `o`, for each `e`. -/
@[pp_nodot]
/--
Definition of `coeff` / `coeff` 的定义

English:
definition coeff
  signature: (b o : Ordinal)
  body: lookupFinsupp ⟨_, nodupKeys b o⟩

中文:
定义 coeff
  签名: (b o : Ordinal)
  定义体: lookupFinsupp ⟨_, nodupKeys b o⟩

Depends on / 依赖: lookupFinsupp, nodupKeys
-/
def coeff (b o : Ordinal) : Ordinal ->₀ Ordinal :=
  lookupFinsupp ⟨_, nodupKeys b o⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `support_coeff` / 定理 `support_coeff`

English:
theorem support_coeff
  given: (b o : Ordinal)
  proof: by
  rw [coeff]; rw [lookupFinsupp_support]; rw [filter_eq_self.2]
  · simp [List.keys]
  · simp_rw [mem_map]
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    simpa using (snd_pos ha).ne'

中文:
定理 support_coeff
  条件: (b o : Ordinal)
  证明: by
  rw [coeff]; rw [lookupFinsupp_support]; rw [filter_eq_self.2]
  · simp [List.keys]
  · simp_rw [mem_map]
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    simpa using (snd_pos ha).ne'

Depends on / 依赖: List.keys, filter_eq_self, lookupFinsupp_support, mem_map, simp_rw, snd_pos
-/
theorem support_coeff (b o : Ordinal) :
    (coeff b o).support = ((CNF b o).map Prod.fst).toFinset := by
  rw [coeff]; rw [lookupFinsupp_support]; rw [filter_eq_self.2]
  · simp [List.keys]
  · simp_rw [mem_map]
    rintro _ ⟨a, ⟨ha, rfl⟩⟩
    simpa using (snd_pos ha).ne'

/--
theorem `coeff_of_mem_CNF` / 定理 `coeff_of_mem_CNF`

English:
theorem coeff_of_mem_CNF
  given: {b o e c : Ordinal} (h : ⟨e, c⟩ in CNF b o)
  proof: by
  rw [coeff]; rw [lookupFinsupp_apply]; rw [mem_lookup_iff.2]; rw [Option.getD_some]
  simpa

中文:
定理 coeff_of_mem_CNF
  条件: {b o e c : Ordinal} (h : ⟨e, c⟩ in CNF b o)
  证明: by
  rw [coeff]; rw [lookupFinsupp_apply]; rw [mem_lookup_iff.2]; rw [Option.getD_some]
  simpa

Depends on / 依赖: Option.getD_some, getD_some, lookupFinsupp_apply, mem_lookup_iff
-/
theorem coeff_of_mem_CNF {b o e c : Ordinal} (h : ⟨e, c⟩ in CNF b o) :
    coeff b o e = c := by
  rw [coeff]; rw [lookupFinsupp_apply]; rw [mem_lookup_iff.2]; rw [Option.getD_some]
  simpa

/--
theorem `coeff_of_notMem_CNF` / 定理 `coeff_of_notMem_CNF`

English:
theorem coeff_of_notMem_CNF
  given: {b o e : Ordinal} (h : e ∉ (CNF b o).map Prod.fst)
  proof: by
  rwa [← notMem_support_iff, support_coeff, mem_toFinset]

@[deprecated (since := "2026-01-11")]
alias coeff_of_not_mem_CNF := coeff_of_notMem_CNF

中文:
定理 coeff_of_notMem_CNF
  条件: {b o e : Ordinal} (h : e ∉ (CNF b o).map Prod.fst)
  证明: by
  rwa [← notMem_support_iff, support_coeff, mem_toFinset]

@[deprecated (since := "2026-01-11")]
alias coeff_of_not_mem_CNF := coeff_of_notMem_CNF

Depends on / 依赖: mem_toFinset, notMem_support_iff, support_coeff
-/
theorem coeff_of_notMem_CNF {b o e : Ordinal} (h : e ∉ (CNF b o).map Prod.fst) :
    coeff b o e = 0 := by
  rwa [← notMem_support_iff, support_coeff, mem_toFinset]

@[deprecated (since := "2026-01-11")]
alias coeff_of_not_mem_CNF := coeff_of_notMem_CNF

/--
theorem `coeff_eq_zero_of_lt` / 定理 `coeff_eq_zero_of_lt`

English:
theorem coeff_eq_zero_of_lt
  given: {b o e : Ordinal} (h : o < b ^ e)
  statement: coeff b o e = 0
  proof: by
  apply coeff_of_notMem_CNF
  intro he
  rw [mem_map] at he
  obtain ⟨⟨e, c⟩, he, rfl⟩ := he
  obtain rfl | he' := eq_or_ne e 0
  · simp_all
  · exact (opow_le_of_le_log he' (fst_le_log he)).not_gt h

中文:
定理 coeff_eq_zero_of_lt
  条件: {b o e : Ordinal} (h : o < b ^ e)
  结论: coeff b o e = 0
  证明: by
  apply coeff_of_notMem_CNF
  intro he
  rw [mem_map] at he
  obtain ⟨⟨e, c⟩, he, rfl⟩ := he
  obtain rfl | he' := eq_or_ne e 0
  · simp_all
  · exact (opow_le_of_le_log he' (fst_le_log he)).not_gt h

Depends on / 依赖: coeff_of_notMem_CNF, eq_or_ne, fst_le_log, mem_map, not_gt, opow_le_of_le_log
-/
theorem coeff_eq_zero_of_lt {b o e : Ordinal} (h : o < b ^ e) : coeff b o e = 0 := by
  apply coeff_of_notMem_CNF
  intro he
  rw [mem_map] at he
  obtain ⟨⟨e, c⟩, he, rfl⟩ := he
  obtain rfl | he' := eq_or_ne e 0
  · simp_all
  · exact (opow_le_of_le_log he' (fst_le_log he)).not_gt h

/--
theorem `coeff_zero_apply` / 定理 `coeff_zero_apply`

English:
theorem coeff_zero_apply
  given: (b e : Ordinal)
  statement: coeff b 0 e = 0
  proof: by
  apply coeff_of_notMem_CNF
  simp

@[simp]

中文:
定理 coeff_zero_apply
  条件: (b e : Ordinal)
  结论: coeff b 0 e = 0
  证明: by
  apply coeff_of_notMem_CNF
  simp

@[simp]

Depends on / 依赖: coeff_of_notMem_CNF
-/
theorem coeff_zero_apply (b e : Ordinal) : coeff b 0 e = 0 := by
  apply coeff_of_notMem_CNF
  simp

@[simp]
/--
theorem `coeff_zero_right` / 定理 `coeff_zero_right`

English:
theorem coeff_zero_right
  given: (b : Ordinal)
  statement: coeff b 0 = 0
  proof: by
  ext e
  exact coeff_zero_apply b e

中文:
定理 coeff_zero_right
  条件: (b : Ordinal)
  结论: coeff b 0 = 0
  证明: by
  ext e
  exact coeff_zero_apply b e

Depends on / 依赖: coeff_zero_apply
-/
theorem coeff_zero_right (b : Ordinal) : coeff b 0 = 0 := by
  ext e
  exact coeff_zero_apply b e

/--
theorem `coeff_of_le_one` / 定理 `coeff_of_le_one`

English:
theorem coeff_of_le_one
  given: {b : Ordinal} (hb : b <= 1) (o : Ordinal)
  statement: coeff b o = single 0 o
  proof: by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply coeff_of_mem_CNF
      rw [CNF.of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha]
      apply coeff_of_notMem_CNF
      rw [CNF.of_le_one hb ho]
      simpa using ha

@[simp]

中文:
定理 coeff_of_le_one
  条件: {b : Ordinal} (hb : b <= 1) (o : Ordinal)
  结论: coeff b o = single 0 o
  证明: by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply coeff_of_mem_CNF
      rw [CNF.of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha]
      apply coeff_of_notMem_CNF
      rw [CNF.of_le_one hb ho]
      simpa using ha

@[simp]

Depends on / 依赖: CNF.of_le_one, coeff_of_mem_CNF, coeff_of_notMem_CNF, eq_or_ne, of_le_one, single_eq_of_ne
-/
theorem coeff_of_le_one {b : Ordinal} (hb : b <= 1) (o : Ordinal) : coeff b o = single 0 o := by
  ext a
  obtain rfl | ho := eq_or_ne o 0
  · simp
  · obtain rfl | ha := eq_or_ne a 0
    · apply coeff_of_mem_CNF
      rw [CNF.of_le_one hb ho]
      simp
    · rw [single_eq_of_ne ha]
      apply coeff_of_notMem_CNF
      rw [CNF.of_le_one hb ho]
      simpa using ha

@[simp]
/--
theorem `coeff_zero_left` / 定理 `coeff_zero_left`

English:
theorem coeff_zero_left
  given: (o : Ordinal)
  statement: coeff 0 o = single 0 o
  proof: coeff_of_le_one zero_le_one o

@[simp]

中文:
定理 coeff_zero_left
  条件: (o : Ordinal)
  结论: coeff 0 o = single 0 o
  证明: coeff_of_le_one zero_le_one o

@[simp]

Depends on / 依赖: coeff_of_le_one, zero_le_one
-/
theorem coeff_zero_left (o : Ordinal) : coeff 0 o = single 0 o :=
  coeff_of_le_one zero_le_one o

@[simp]
/--
theorem `coeff_one_left` / 定理 `coeff_one_left`

English:
theorem coeff_one_left
  given: (o : Ordinal)
  statement: coeff 1 o = single 0 o
  proof: coeff_of_le_one le_rfl o

中文:
定理 coeff_one_left
  条件: (o : Ordinal)
  结论: coeff 1 o = single 0 o
  证明: coeff_of_le_one le_rfl o

Depends on / 依赖: coeff_of_le_one, le_rfl
-/
theorem coeff_one_left (o : Ordinal) : coeff 1 o = single 0 o :=
  coeff_of_le_one le_rfl o

/--
theorem `coeff_opow_mul_add` / 定理 `coeff_opow_mul_add`

English:
theorem coeff_opow_mul_add
  statement: {b e x y : Ordinal}
  proof: by
  ext e'
  rw [add_apply]
  obtain rfl | he := eq_or_ne e e'
  · rw [single_eq_same, coeff_eq_zero_of_lt hy, add_zero]
    apply coeff_of_mem_CNF
    rw [CNF.opow_mul_add hb hx hxb hy]
    exact mem_cons_self
  · rw [single_eq_of_ne' he, zero_add]
    by_cases h : e' in (CNF b y).map Prod.fst
   

中文:
定理 coeff_opow_mul_add
  结论: {b e x y : Ordinal}
  证明: by
  ext e'
  rw [add_apply]
  obtain rfl | he := eq_or_ne e e'
  · rw [single_eq_same, coeff_eq_zero_of_lt hy, add_zero]
    apply coeff_of_mem_CNF
    rw [CNF.opow_mul_add hb hx hxb hy]
    exact mem_cons_self
  · rw [single_eq_of_ne' he, zero_add]
    by_cases h : e' in (CNF b y).map Prod.fst
   

Depends on / 依赖: CNF.opow_mul_add, Prod.fst, add_apply, add_zero, coeff_eq_zero_of_lt, coeff_of_mem_CNF, coeff_of_notMem_CNF, eq_or_ne, mem_cons_of_mem, mem_cons_self, mem_map, opow_mul_add, single_eq_of_ne, single_eq_same, zero_add
-/
theorem coeff_opow_mul_add {b e x y : Ordinal}
    (hb : 1 < b) (hx : x != 0) (hxb : x < b) (hy : y < b ^ e) :
    coeff b (b ^ e * x + y) = single e x + coeff b y := by
  ext e'
  rw [add_apply]
  obtain rfl | he := eq_or_ne e e'
  · rw [single_eq_same, coeff_eq_zero_of_lt hy, add_zero]
    apply coeff_of_mem_CNF
    rw [CNF.opow_mul_add hb hx hxb hy]
    exact mem_cons_self
  · rw [single_eq_of_ne' he, zero_add]
    by_cases h : e' in (CNF b y).map Prod.fst
    · rw [mem_map] at h
      obtain ⟨⟨f, c⟩, hf, rfl⟩ := h
      rw [coeff_of_mem_CNF hf]
      apply coeff_of_mem_CNF
      rw [CNF.opow_mul_add hb hx hxb hy]
      exact mem_cons_of_mem _ hf
    · rw [coeff_of_notMem_CNF h, coeff_of_notMem_CNF]
      rw [mem_map] at h ⊢
      rw [CNF.opow_mul_add hb hx hxb hy]
      simp_all

/-! ### Evaluate a Cantor normal form -/

/--
Definition of `eval` / `eval` 的定义

English:
definition eval
  signature: (b : Ordinal) (f : Ordinal ->₀ Ordinal)
  body: (f.support.sort (· >= ·)).foldr (fun p r => b ^ p * f p + r) 0

@[simp]

中文:
定义 eval
  签名: (b : Ordinal) (f : Ordinal ->₀ Ordinal)
  定义体: (f.support.sort (· >= ·)).foldr (fun p r => b ^ p * f p + r) 0

@[simp]

Depends on / 依赖: f.support.sort, support
-/
def eval (b : Ordinal) (f : Ordinal ->₀ Ordinal) : Ordinal :=
  (f.support.sort (· >= ·)).foldr (fun p r => b ^ p * f p + r) 0

@[simp]
/--
theorem `eval_zero_right` / 定理 `eval_zero_right`

English:
theorem eval_zero_right
  given: (b : Ordinal)
  statement: eval b 0 = 0
  proof: by
  simp [eval]

中文:
定理 eval_zero_right
  条件: (b : Ordinal)
  结论: eval b 0 = 0
  证明: by
  simp [eval]
-/
theorem eval_zero_right (b : Ordinal) : eval b 0 = 0 := by
  simp [eval]

/--
theorem `eval_single_add'` / 定理 `eval_single_add'`

English:
theorem eval_single_add'
  statement: (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal}
  proof: by
  obtain rfl | hx := eq_or_ne x 0; · simp
  have hf : f e = 0 := by
    rw [← notMem_support_iff]
    exact fun he => (h e he).false
  rw [eval]; rw [support_single_add (by simpa) hx]; rw [Finset.sort_cons]
  · simp only [add_apply, foldr_cons, single_eq_same, hf, add_zero, add_right_inj]
    app

中文:
定理 eval_single_add'
  结论: (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal}
  证明: by
  obtain rfl | hx := eq_or_ne x 0; · simp
  have hf : f e = 0 := by
    rw [← notMem_support_iff]
    exact fun he => (h e he).false
  rw [eval]; rw [support_single_add (by simpa) hx]; rw [Finset.sort_cons]
  · simp only [add_apply, foldr_cons, single_eq_same, hf, add_zero, add_right_inj]
    app

Depends on / 依赖: Finset, Finset.sort_cons, add_apply, add_right_inj, add_zero, eq_or_ne, foldr_cons, foldr_ext, notMem_support_iff, single_eq_of_ne, single_eq_same, sort_cons, support_single_add, zero_add
-/
theorem eval_single_add' (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal}
    (h : forall e' in f.support, e' < e) : eval b (.single e x + f) = b ^ e * x + eval b f := by
  obtain rfl | hx := eq_or_ne x 0; · simp
  have hf : f e = 0 := by
    rw [← notMem_support_iff]
    exact fun he => (h e he).false
  rw [eval]; rw [support_single_add (by simpa) hx]; rw [Finset.sort_cons]
  · simp only [add_apply, foldr_cons, single_eq_same, hf, add_zero, add_right_inj]
    apply foldr_ext
    intro e' he' _
    congr
    rw [single_eq_of_ne]; rw [zero_add]
    aesop
  · exact fun e' he' => (h e' he').le

@[simp]
/--
theorem `eval_single` / 定理 `eval_single`

English:
theorem eval_single
  given: (b e x : Ordinal)
  statement: eval b (.single e x) = b ^ e * x
  proof: by
  simpa using eval_single_add' b (f := 0)

中文:
定理 eval_single
  条件: (b e x : Ordinal)
  结论: eval b (.single e x) = b ^ e * x
  证明: by
  simpa using eval_single_add' b (f := 0)

Depends on / 依赖: eval_single_add
-/
theorem eval_single (b e x : Ordinal) : eval b (.single e x) = b ^ e * x := by
  simpa using eval_single_add' b (f := 0)

/--
theorem `eval_single_add` / 定理 `eval_single_add`

English:
theorem eval_single_add
  statement: (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal}
  proof: by
  cases f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e' y f hf hy =>
    obtain rfl | he' := (h e' (by simp [hy])).eq_or_lt
    · simp only [← add_assoc, ← single_add, eval_single_add' _ hf, mul_add]
    · rw [eval_single_add']
      refine fun a ha => (h a ha).lt_of_ne ?

中文:
定理 eval_single_add
  结论: (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal}
  证明: by
  cases f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e' y f hf hy =>
    obtain rfl | he' := (h e' (by simp [hy])).eq_or_lt
    · simp only [← add_assoc, ← single_add, eval_single_add' _ hf, mul_add]
    · rw [eval_single_add']
      refine fun a ha => (h a ha).lt_of_ne ?

Depends on / 依赖: Finsupp, Finsupp.induction_on_max, add_assoc, eq_or_lt, eval_single_add, induction_on_max, lt_of_ne, mul_add, not_gt, single_add
-/
theorem eval_single_add (b : Ordinal) {e x : Ordinal} {f : Ordinal ->₀ Ordinal}
    (h : forall e' in f.support, e' <= e) : eval b (.single e x + f) = b ^ e * x + eval b f := by
  cases f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e' y f hf hy =>
    obtain rfl | he' := (h e' (by simp [hy])).eq_or_lt
    · simp only [← add_assoc, ← single_add, eval_single_add' _ hf, mul_add]
    · rw [eval_single_add']
      refine fun a ha => (h a ha).lt_of_ne ?_
      rintro rfl
      apply (hf a _).not_gt he'
      simpa [he'.ne'] using ha

/--
theorem `eval_add` / 定理 `eval_add`

English:
theorem eval_add
  statement: (b : Ordinal) {f₁ f₂ : Ordinal ->₀ Ordinal}
  proof: by
  induction f₁ using Finsupp.induction_on_max with
  | zero => simp
  | single_add e₁ x f₁ hf₁ hx IH =>
    rw [add_assoc]; rw [eval_single_add]; rw [eval_single_add' _ hf₁]; rw [IH]; rw [add_assoc]
    · simp_all
    · intro e₂ he₂
obtain he₂ | he₂ := Finset.mem_union.1 support_add he₂
      · e

中文:
定理 eval_add
  结论: (b : Ordinal) {f₁ f₂ : Ordinal ->₀ Ordinal}
  证明: by
  induction f₁ using Finsupp.induction_on_max with
  | zero => simp
  | single_add e₁ x f₁ hf₁ hx IH =>
    rw [add_assoc]; rw [eval_single_add]; rw [eval_single_add' _ hf₁]; rw [IH]; rw [add_assoc]
    · simp_all
    · intro e₂ he₂
obtain he₂ | he₂ := Finset.mem_union.1 support_add he₂
      · e

Depends on / 依赖: Finset, Finset.mem_union, Finsupp, Finsupp.induction_on_max, add_assoc, eval_single_add, induction_on_max, mem_union, single_add, support_add
-/
theorem eval_add (b : Ordinal) {f₁ f₂ : Ordinal ->₀ Ordinal}
    (h : forall e₁ in f₁.support, forall e₂ in f₂.support, e₂ <= e₁) :
    eval b (f₁ + f₂) = eval b f₁ + eval b f₂ := by
  induction f₁ using Finsupp.induction_on_max with
  | zero => simp
  | single_add e₁ x f₁ hf₁ hx IH =>
    rw [add_assoc]; rw [eval_single_add]; rw [eval_single_add' _ hf₁]; rw [IH]; rw [add_assoc]
    · simp_all
    · intro e₂ he₂
obtain he₂ | he₂ := Finset.mem_union.1 support_add he₂
      · exact (hf₁ _ he₂).le
      · apply h _ _ _ he₂
        simp_all

/--
theorem `eval_lt` / 定理 `eval_lt`

English:
theorem eval_lt
  statement: {b e : Ordinal} {f : Ordinal ->₀ Ordinal}
  proof: by
  induction f using Finsupp.induction_on_max generalizing e with
  | zero =>
    rw [eval_zero_right]
    exact opow_pos _ (hb 0)
  | single_add e' x f hf hx IH =>
    have he' : e' ∉ f.support := fun h => (hf _ h).false
    rw [eval_single_add' _ hf]
    apply opow_mul_add_lt_opow _ (IH _ hf)
  

中文:
定理 eval_lt
  结论: {b e : Ordinal} {f : Ordinal ->₀ Ordinal}
  证明: by
  induction f using Finsupp.induction_on_max generalizing e with
  | zero =>
    rw [eval_zero_right]
    exact opow_pos _ (hb 0)
  | single_add e' x f hf hx IH =>
    have he' : e' ∉ f.support := fun h => (hf _ h).false
    rw [eval_single_add' _ hf]
    apply opow_mul_add_lt_opow _ (IH _ hf)
  

Depends on / 依赖: Finsupp, Finsupp.induction_on_max, add_apply, add_zero, eval_single_add, eval_zero_right, f.support, generalizing, induction_on_max, notMem_support_iff, opow_mul_add_lt_opow, opow_pos, single_add, single_eq_same, support, trans_eq
-/
theorem eval_lt {b e : Ordinal} {f : Ordinal ->₀ Ordinal}
    (hb : forall e', f e' < b) (he : forall e' in f.support, e' < e) : eval b f < b ^ e := by
  induction f using Finsupp.induction_on_max generalizing e with
  | zero =>
    rw [eval_zero_right]
    exact opow_pos _ (hb 0)
  | single_add e' x f hf hx IH =>
    have he' : e' ∉ f.support := fun h => (hf _ h).false
    rw [eval_single_add' _ hf]
    apply opow_mul_add_lt_opow _ (IH _ hf)
    · apply he e' _
      simp [hx]
    · apply (hb e').trans_eq'
      rw [add_apply]; rw [single_eq_same]; rw [notMem_support_iff.1]; rw [add_zero]
      exact fun h => (hf _ h).false
    · intro a
      by_cases ha : a in f.support
      · apply (hb a).trans_eq'
        rw [add_apply]; rw [single_eq_of_ne]; rw [zero_add]
        rintro rfl
        contradiction
      · rw [notMem_support_iff.1 ha]
        exact (hb 0).pos

@[simp]
/--
theorem `eval_coeff` / 定理 `eval_coeff`

English:
theorem eval_coeff
  given: (b o : Ordinal)
  statement: eval b (coeff b o) = o
  proof: by
  conv_rhs => rw [← CNF.foldr b o]
  rw [eval]; rw [support_coeff]; rw [(toFinset_sort _ _).2]; rw [foldr_map]
  · apply foldr_ext
    intro a ha x
    rw [coeff_of_mem_CNF ha]
  · exact (CNF.sortedGT b o).sortedGE.pairwise
  · exact (CNF.sortedGT b o).nodup

中文:
定理 eval_coeff
  条件: (b o : Ordinal)
  结论: eval b (coeff b o) = o
  证明: by
  conv_rhs => rw [← CNF.foldr b o]
  rw [eval]; rw [support_coeff]; rw [(toFinset_sort _ _).2]; rw [foldr_map]
  · apply foldr_ext
    intro a ha x
    rw [coeff_of_mem_CNF ha]
  · exact (CNF.sortedGT b o).sortedGE.pairwise
  · exact (CNF.sortedGT b o).nodup

Depends on / 依赖: CNF.foldr, CNF.sortedGT, coeff_of_mem_CNF, conv_rhs, foldr_ext, foldr_map, pairwise, sortedGE, sortedGE.pairwise, sortedGT, support_coeff, toFinset_sort
-/
theorem eval_coeff (b o : Ordinal) : eval b (coeff b o) = o := by
  conv_rhs => rw [← CNF.foldr b o]
  rw [eval]; rw [support_coeff]; rw [(toFinset_sort _ _).2]; rw [foldr_map]
  · apply foldr_ext
    intro a ha x
    rw [coeff_of_mem_CNF ha]
  · exact (CNF.sortedGT b o).sortedGE.pairwise
  · exact (CNF.sortedGT b o).nodup

/--
theorem `coeff_eval` / 定理 `coeff_eval`

English:
theorem coeff_eval
  given: {b : Ordinal} (hb : 1 < b) {f : Ordinal ->₀ Ordinal} (hf : forall e, f e < b)
  proof: by
  induction f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e x f hf' hx IH =>
    have IH' (e') : f e' < b := by
      by_cases he' : e' in f.support
      · apply (hf e').trans_eq'
        rw [add_apply]; rw [single_eq_of_ne]; rw [zero_add]
        exact (hf' _ he').ne
   

中文:
定理 coeff_eval
  条件: {b : Ordinal} (hb : 1 < b) {f : Ordinal ->₀ Ordinal} (hf : 对任意 e, f e < b)
  证明: by
  induction f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e x f hf' hx IH =>
    have IH' (e') : f e' < b := by
      by_cases he' : e' in f.support
      · apply (hf e').trans_eq'
        rw [add_apply]; rw [single_eq_of_ne]; rw [zero_add]
        exact (hf' _ he').ne
   

Depends on / 依赖: Finsupp, Finsupp.induction_on_max, add_apply, add_zero, coeff_opow_mul_add, eval_single_add, f.support, hb.pos, induction_on_max, notMem_support_iff, single_add, single_eq_of_ne, single_eq_same, support, trans_eq, zero_add
-/
theorem coeff_eval {b : Ordinal} (hb : 1 < b) {f : Ordinal ->₀ Ordinal} (hf : forall e, f e < b) :
    coeff b (eval b f) = f := by
  induction f using Finsupp.induction_on_max with
  | zero => simp
  | single_add e x f hf' hx IH =>
    have IH' (e') : f e' < b := by
      by_cases he' : e' in f.support
      · apply (hf e').trans_eq'
        rw [add_apply]; rw [single_eq_of_ne]; rw [zero_add]
        exact (hf' _ he').ne
      · rw [notMem_support_iff.1 he']
        exact hb.pos
    rw [eval_single_add' _ hf']; rw [coeff_opow_mul_add hb hx]; rw [IH IH']
    · apply (hf e).trans_eq'
      rw [add_apply]; rw [single_eq_same]; rw [notMem_support_iff.1]; rw [add_zero]
      exact fun h => (hf' _ h).false
    · exact eval_lt IH' hf'

/--
theorem `coeff_injective` / 定理 `coeff_injective`

English:
theorem coeff_injective
  given: (b : Ordinal)
  statement: Function.Injective (coeff b)
  proof: Function.LeftInverse.injective fun _ => eval_coeff ..

@[simp]

中文:
定理 coeff_injective
  条件: (b : Ordinal)
  结论: Function.Injective (coeff b)
  证明: Function.LeftInverse.injective fun _ => eval_coeff ..

@[simp]

Depends on / 依赖: Function, Function.LeftInverse.injective, LeftInverse, eval_coeff, injective
-/
theorem coeff_injective (b : Ordinal) : Function.Injective (coeff b) :=
  Function.LeftInverse.injective fun _ => eval_coeff ..

@[simp]
/--
theorem `coeff_inj` / 定理 `coeff_inj`

English:
theorem coeff_inj
  given: {b x y : Ordinal}
  statement: coeff b x = coeff b y ↔ x = y
  proof: (coeff_injective b).eq_iff

中文:
定理 coeff_inj
  条件: {b x y : Ordinal}
  结论: coeff b x = coeff b y ↔ x = y
  证明: (coeff_injective b).eq_iff

Depends on / 依赖: coeff_injective, eq_iff
-/
theorem coeff_inj {b x y : Ordinal} : coeff b x = coeff b y ↔ x = y :=
  (coeff_injective b).eq_iff

end Ordinal.CNF
