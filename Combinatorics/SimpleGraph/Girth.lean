/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.ENat.Lattice

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle, they give `0` or `∞` respectively if the graph is acyclic.

## TODO

- Prove that `G.egirth ≤ 2 * G.ediam + 1` when `G` is not acyclic
- Prove that `G.girth ≤ 2 * G.diam + 1` when the diameter is non-zero

-/

@[expose] public section

namespace SimpleGraph
variable {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}

section egirth


/--
Definition of `egirth` / `egirth` 的定义

English:
definition egirth
  signature: (G : SimpleGraph α)
  body: ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp]

中文:
定义 egirth
  签名: (G : SimpleGraph α)
  定义体: ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp]

Depends on / 依赖: G.Walk, IsCycle, length, w.IsCycle, w.length
-/
noncomputable def egirth (G : SimpleGraph α) : Nat∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp]
/--
lemma `le_egirth` / 引理 `le_egirth`

English:
lemma le_egirth
  given: {n : Nat∞}
  statement: n <= G.egirth ↔ forall a (w : G.Walk a a), w.IsCycle -> n <= w.length
  proof: by
  simp [egirth]

中文:
引理 le_egirth
  条件: {n : 自然数∞}
  结论: n <= G.egirth ↔ 对任意 a (w : G.Walk a a), w.IsCycle -> n <= w.length
  证明: by
  simp [egirth]

Depends on / 依赖: egirth
-/
lemma le_egirth {n : Nat∞} : n <= G.egirth ↔ forall a (w : G.Walk a a), w.IsCycle -> n <= w.length := by
  simp [egirth]

/--
lemma `egirth_le_length` / 引理 `egirth_le_length`

English:
lemma egirth_le_length
  given: {a} {w : G.Walk a a} (h : w.IsCycle)
  statement: G.egirth <= w.length
  proof: le_egirth.mp le_rfl a w h

中文:
引理 egirth_le_length
  条件: {a} {w : G.Walk a a} (h : w.IsCycle)
  结论: G.egirth <= w.length
  证明: le_egirth.mp le_rfl a w h

Depends on / 依赖: le_egirth, le_egirth.mp, le_rfl
-/
lemma egirth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.egirth <= w.length :=
  le_egirth.mp le_rfl a w h

/--
lemma `Walk.IsCircuit.egirth_le_length` / 引理 `Walk.IsCircuit.egirth_le_length`

English:
lemma Walk.IsCircuit.egirth_le_length
  given: {a} {w : G.Walk a a} (hwc : w.IsCircuit)
  proof: by
  classical
  by_contra! hlg
  let w' : G.Walk a a := w.cycleBypass
  have hwc' : w'.IsCycle := hwc.isCycle_cycleBypass
  have hwlg' : w'.length < G.egirth := by
    grw [w.length_cycleBypass_le_length]
    exact hlg
  exact not_le_of_gt hwlg' (SimpleGraph.egirth_le_length hwc')

@[simp]

中文:
引理 Walk.IsCircuit.egirth_le_length
  条件: {a} {w : G.Walk a a} (hwc : w.IsCircuit)
  证明: by
  classical
  by_contra! hlg
  let w' : G.Walk a a := w.cycleBypass
  have hwc' : w'.IsCycle := hwc.isCycle_cycleBypass
  have hwlg' : w'.length < G.egirth := by
    grw [w.length_cycleBypass_le_length]
    exact hlg
  exact not_le_of_gt hwlg' (SimpleGraph.egirth_le_length hwc')

@[simp]

Depends on / 依赖: G.Walk, G.egirth, IsCycle, SimpleGraph, SimpleGraph.egirth_le_length, classical, cycleBypass, egirth, egirth_le_length, hwc.isCycle_cycleBypass, isCycle_cycleBypass, length, length_cycleBypass_le_length, not_le_of_gt, w.cycleBypass, w.length_cycleBypass_le_length
-/
lemma Walk.IsCircuit.egirth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.egirth <= w.length := by
  classical
  by_contra! hlg
  let w' : G.Walk a a := w.cycleBypass
  have hwc' : w'.IsCycle := hwc.isCycle_cycleBypass
  have hwlg' : w'.length < G.egirth := by
    grw [w.length_cycleBypass_le_length]
    exact hlg
  exact not_le_of_gt hwlg' (SimpleGraph.egirth_le_length hwc')

@[simp]
/--
lemma `egirth_eq_top` / 引理 `egirth_eq_top`

English:
lemma egirth_eq_top
  statement: G.egirth = ⊤ ↔ G.IsAcyclic
  proof: by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.egirth_eq_top⟩ := egirth_eq_top

中文:
引理 egirth_eq_top
  结论: G.egirth = ⊤ ↔ G.IsAcyclic
  证明: by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.egirth_eq_top⟩ := egirth_eq_top

Depends on / 依赖: IsAcyclic, egirth
-/
lemma egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic := by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.egirth_eq_top⟩ := egirth_eq_top

set_option backward.isDefEq.respectTransparency false in
/--
lemma `egirth_anti` / 引理 `egirth_anti`

English:
lemma egirth_anti
  statement: Antitone (egirth : SimpleGraph α -> Nat∞)
  proof: fun G H h => iInf_mono fun a => iInf₂_mono' fun w hw => ⟨w.mapLe h, hw.mapLe _, by simp⟩

中文:
引理 egirth_anti
  结论: Antitone (egirth : SimpleGraph α -> 自然数∞)
  证明: fun G H h => iInf_mono fun a => iInf₂_mono' fun w hw => ⟨w.mapLe h, hw.mapLe _, by simp⟩

Depends on / 依赖: hw.mapLe, iInf_mono, w.mapLe
-/
lemma egirth_anti : Antitone (egirth : SimpleGraph α -> Nat∞) :=
  fun G H h => iInf_mono fun a => iInf₂_mono' fun w hw => ⟨w.mapLe h, hw.mapLe _, by simp⟩

/--
lemma `exists_egirth_eq_length` / 引理 `exists_egirth_eq_length`

English:
lemma exists_egirth_eq_length
  proof: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma',
      ENat.iInf_natCast_ne_top, ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

中文:
引理 exists_egirth_eq_length
  证明: by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma',
      ENat.iInf_natCast_ne_top, ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

Depends on / 依赖: ENat.iInf_natCast_ne_top, Ne.eq_def, Sigma.exists, Subtype, Subtype.exists, ciInf_mem, egirth, egirth_eq_top, eq_comm, eq_def, exists_prop, iInf_natCast_ne_top, iInf_sigma, iInf_subtype, simp_rw
-/
lemma exists_egirth_eq_length :
    (exists (a : α) (w : G.Walk a a), w.IsCycle ∧ G.egirth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma',
      ENat.iInf_natCast_ne_top, ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

/--
lemma `three_le_egirth` / 引理 `three_le_egirth`

English:
lemma three_le_egirth
  statement: 3 <= G.egirth
  proof: by
  simpa using fun _ _ h => h.three_le_length

中文:
引理 three_le_egirth
  结论: 3 <= G.egirth
  证明: by
  simpa using fun _ _ h => h.three_le_length

Depends on / 依赖: h.three_le_length, three_le_length
-/
lemma three_le_egirth : 3 <= G.egirth := by
  simpa using fun _ _ h => h.three_le_length

/--
lemma `egirth_bot` / 引理 `egirth_bot`

English:
lemma egirth_bot
  statement: egirth (⊥ : SimpleGraph α) = ⊤
  proof: by simp

中文:
引理 egirth_bot
  结论: egirth (⊥ : SimpleGraph α) = ⊤
  证明: by simp
-/
@[simp] lemma egirth_bot : egirth (⊥ : SimpleGraph α) = ⊤ := by simp

/--
theorem `egirth_top` / 定理 `egirth_top`

English:
theorem egirth_top
  given: (h : 3 <= ENat.card α)
  statement: egirth (⊤ : SimpleGraph α) = 3
  proof: by
  classical
  refine le_antisymm ?_ three_le_egirth
obtain ⟨s, hcard⟩ := Cardinal.exists_finset_eq_card Cardinal.ofNat_le_toENat.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := s.card_eq_three.mp hcard.symm
set w : Walk ⊤ x x := .cons hxy .cons hyz .cons hxz.symm .nil with hw
  have : w.IsCycle :=
 

中文:
定理 egirth_top
  条件: (h : 3 <= E自然数.card α)
  结论: egirth (⊤ : SimpleGraph α) = 3
  证明: by
  classical
  refine le_antisymm ?_ three_le_egirth
obtain ⟨s, hcard⟩ := Cardinal.exists_finset_eq_card Cardinal.ofNat_le_toENat.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := s.card_eq_three.mp hcard.symm
set w : Walk ⊤ x x := .cons hxy .cons hyz .cons hxz.symm .nil with hw
  have : w.IsCycle :=
 

Depends on / 依赖: Cardinal, Cardinal.exists_finset_eq_card, Cardinal.ofNat_le_toENat.mp, IsCycle, card_eq_three, classical, edges_nodup, egirth_le_length, exists_finset_eq_card, hcard.symm, hxz.symm, le_antisymm, ne_nil, ofNat_le_toENat, s.card_eq_three.mp, support_nodup, three_le_egirth, w.IsCycle
-/
theorem egirth_top (h : 3 <= ENat.card α) : egirth (⊤ : SimpleGraph α) = 3 := by
  classical
  refine le_antisymm ?_ three_le_egirth
obtain ⟨s, hcard⟩ := Cardinal.exists_finset_eq_card Cardinal.ofNat_le_toENat.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := s.card_eq_three.mp hcard.symm
set w : Walk ⊤ x x := .cons hxy .cons hyz .cons hxz.symm .nil with hw
  have : w.IsCycle :=
    { edges_nodup := by aesop
      ne_nil := by aesop
      support_nodup := by aesop }
  grw [egirth_le_length this]
  simp [hw]

@[gcongr only]
/--
lemma `IsContained.egirth_le` / 引理 `IsContained.egirth_le`

English:
lemma IsContained.egirth_le
  given: (h : G ⊑ G')
  statement: G'.egirth <= G.egirth
  proof: by
  by_cases hacyc : G.IsAcyclic
  · simp [hacyc.egirth_eq_top]
  obtain ⟨a, w, hw, hwl⟩ := exists_egirth_eq_length.mpr hacyc
  rw [hwl]; rw [← w.length_map h.some.toHom]
exact egirth_le_length hw.map h.some.injective

@[gcongr only]

中文:
引理 IsContained.egirth_le
  条件: (h : G ⊑ G')
  结论: G'.egirth <= G.egirth
  证明: by
  by_cases hacyc : G.IsAcyclic
  · simp [hacyc.egirth_eq_top]
  obtain ⟨a, w, hw, hwl⟩ := exists_egirth_eq_length.mpr hacyc
  rw [hwl]; rw [← w.length_map h.some.toHom]
exact egirth_le_length hw.map h.some.injective

@[gcongr only]

Depends on / 依赖: G.IsAcyclic, IsAcyclic, egirth_eq_top, egirth_le_length, exists_egirth_eq_length, exists_egirth_eq_length.mpr, h.some.injective, h.some.toHom, hacyc.egirth_eq_top, hw.map, injective, length_map, w.length_map
-/
lemma IsContained.egirth_le (h : G ⊑ G') : G'.egirth <= G.egirth := by
  by_cases hacyc : G.IsAcyclic
  · simp [hacyc.egirth_eq_top]
  obtain ⟨a, w, hw, hwl⟩ := exists_egirth_eq_length.mpr hacyc
  rw [hwl]; rw [← w.length_map h.some.toHom]
exact egirth_le_length hw.map h.some.injective

@[gcongr only]
/--
lemma `Iso.egirth_eq` / 引理 `Iso.egirth_eq`

English:
lemma Iso.egirth_eq
  given: (f : G ≃g G')
  statement: G.egirth = G'.egirth
  proof: le_antisymm f.isContained'.egirth_le f.isContained.egirth_le

中文:
引理 Iso.egirth_eq
  条件: (f : G ≃g G')
  结论: G.egirth = G'.egirth
  证明: le_antisymm f.isContained'.egirth_le f.isContained.egirth_le

Depends on / 依赖: egirth_le, f.isContained, f.isContained.egirth_le, isContained, le_antisymm
-/
lemma Iso.egirth_eq (f : G ≃g G') : G.egirth = G'.egirth :=
  le_antisymm f.isContained'.egirth_le f.isContained.egirth_le

end egirth

section girth


/--
Definition of `girth` / `girth` 的定义

English:
definition girth
  signature: (G : SimpleGraph α)
  body: G.egirth.toNat

中文:
定义 girth
  签名: (G : SimpleGraph α)
  定义体: G.egirth.toNat

Depends on / 依赖: G.egirth.toNat, egirth
-/
noncomputable def girth (G : SimpleGraph α) : Nat :=
  G.egirth.toNat

/--
lemma `girth_le_length` / 引理 `girth_le_length`

English:
lemma girth_le_length
  given: {a} {w : G.Walk a a} (h : w.IsCycle)
  statement: G.girth <= w.length
  proof: ENat.natCast_le_natCast.mp G.egirth.natCast_toNat_le_self.trans egirth_le_length h

中文:
引理 girth_le_length
  条件: {a} {w : G.Walk a a} (h : w.IsCycle)
  结论: G.girth <= w.length
  证明: ENat.natCast_le_natCast.mp G.egirth.natCast_toNat_le_self.trans egirth_le_length h

Depends on / 依赖: ENat.natCast_le_natCast.mp, G.egirth.natCast_toNat_le_self.trans, egirth, egirth_le_length, natCast_le_natCast, natCast_toNat_le_self
-/
lemma girth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.girth <= w.length :=
ENat.natCast_le_natCast.mp G.egirth.natCast_toNat_le_self.trans egirth_le_length h

/--
lemma `three_le_girth` / 引理 `three_le_girth`

English:
lemma three_le_girth
  given: (hG : ¬ G.IsAcyclic)
  statement: 3 <= G.girth
  proof: ENat.toNat_le_toNat three_le_egirth egirth_eq_top.not.mpr hG

中文:
引理 three_le_girth
  条件: (hG : ¬ G.IsAcyclic)
  结论: 3 <= G.girth
  证明: ENat.toNat_le_toNat three_le_egirth egirth_eq_top.not.mpr hG

Depends on / 依赖: ENat.toNat_le_toNat, egirth_eq_top, egirth_eq_top.not.mpr, three_le_egirth, toNat_le_toNat
-/
lemma three_le_girth (hG : ¬ G.IsAcyclic) : 3 <= G.girth :=
ENat.toNat_le_toNat three_le_egirth egirth_eq_top.not.mpr hG

/--
lemma `girth_eq_zero` / 引理 `girth_eq_zero`

English:
lemma girth_eq_zero
  statement: G.girth = 0 ↔ G.IsAcyclic
  proof: ⟨fun h => not_not.mp three_le_girth.mt by lia, fun h => by simp [girth, h]⟩

protected alias ⟨_, IsAcyclic.girth_eq_zero⟩ := girth_eq_zero

中文:
引理 girth_eq_zero
  结论: G.girth = 0 ↔ G.IsAcyclic
  证明: ⟨fun h => not_not.mp three_le_girth.mt by lia, fun h => by simp [girth, h]⟩

protected alias ⟨_, IsAcyclic.girth_eq_zero⟩ := girth_eq_zero

Depends on / 依赖: not_not, not_not.mp, three_le_girth, three_le_girth.mt
-/
lemma girth_eq_zero : G.girth = 0 ↔ G.IsAcyclic :=
⟨fun h => not_not.mp three_le_girth.mt by lia, fun h => by simp [girth, h]⟩

protected alias ⟨_, IsAcyclic.girth_eq_zero⟩ := girth_eq_zero

/--
lemma `girth_anti` / 引理 `girth_anti`

English:
lemma girth_anti
  given: {G' : SimpleGraph α} (hab : G <= G') (h : ¬ G.IsAcyclic)
  statement: G'.girth <= G.girth
  proof: ENat.toNat_le_toNat (egirth_anti hab) egirth_eq_top.not.mpr h

中文:
引理 girth_anti
  条件: {G' : SimpleGraph α} (hab : G <= G') (h : ¬ G.IsAcyclic)
  结论: G'.girth <= G.girth
  证明: ENat.toNat_le_toNat (egirth_anti hab) egirth_eq_top.not.mpr h

Depends on / 依赖: ENat.toNat_le_toNat, egirth_anti, egirth_eq_top, egirth_eq_top.not.mpr, toNat_le_toNat
-/
lemma girth_anti {G' : SimpleGraph α} (hab : G <= G') (h : ¬ G.IsAcyclic) : G'.girth <= G.girth :=
ENat.toNat_le_toNat (egirth_anti hab) egirth_eq_top.not.mpr h

/--
lemma `Walk.IsCircuit.girth_le_length` / 引理 `Walk.IsCircuit.girth_le_length`

English:
lemma Walk.IsCircuit.girth_le_length
  given: {a} {w : G.Walk a a} (hwc : w.IsCircuit)
  proof: ENat.natCast_le_natCast.mp G.egirth.natCast_toNat_le_self.trans hwc.egirth_le_length

中文:
引理 Walk.IsCircuit.girth_le_length
  条件: {a} {w : G.Walk a a} (hwc : w.IsCircuit)
  证明: ENat.natCast_le_natCast.mp G.egirth.natCast_toNat_le_self.trans hwc.egirth_le_length

Depends on / 依赖: ENat.natCast_le_natCast.mp, G.egirth.natCast_toNat_le_self.trans, egirth, egirth_le_length, hwc.egirth_le_length, natCast_le_natCast, natCast_toNat_le_self
-/
lemma Walk.IsCircuit.girth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.girth <= w.length :=
ENat.natCast_le_natCast.mp G.egirth.natCast_toNat_le_self.trans hwc.egirth_le_length

/--
lemma `exists_girth_eq_length` / 引理 `exists_girth_eq_length`

English:
lemma exists_girth_eq_length
  proof: by
  refine ⟨by tauto, fun h => ?_⟩
  obtain ⟨_, _, _⟩ := exists_egirth_eq_length.mpr h
  simp_all only [girth, ENat.toNat_natCast]
  tauto

中文:
引理 exists_girth_eq_length
  证明: by
  refine ⟨by tauto, fun h => ?_⟩
  obtain ⟨_, _, _⟩ := exists_egirth_eq_length.mpr h
  simp_all only [girth, ENat.toNat_natCast]
  tauto

Depends on / 依赖: ENat.toNat_natCast, exists_egirth_eq_length, exists_egirth_eq_length.mpr, toNat_natCast
-/
lemma exists_girth_eq_length :
    (exists (a : α) (w : G.Walk a a), w.IsCycle ∧ G.girth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨by tauto, fun h => ?_⟩
  obtain ⟨_, _, _⟩ := exists_egirth_eq_length.mpr h
  simp_all only [girth, ENat.toNat_natCast]
  tauto

/--
lemma `girth_bot` / 引理 `girth_bot`

English:
lemma girth_bot
  statement: girth (⊥ : SimpleGraph α) = 0
  proof: by
  simp [girth]

中文:
引理 girth_bot
  结论: girth (⊥ : SimpleGraph α) = 0
  证明: by
  simp [girth]
-/
@[simp] lemma girth_bot : girth (⊥ : SimpleGraph α) = 0 := by
  simp [girth]

/--
theorem `girth_top` / 定理 `girth_top`

English:
theorem girth_top
  given: (h : 3 <= ENat.card α)
  statement: girth (⊤ : SimpleGraph α) = 3
  proof: by
  simp [girth, egirth_top h]

中文:
定理 girth_top
  条件: (h : 3 <= E自然数.card α)
  结论: girth (⊤ : SimpleGraph α) = 3
  证明: by
  simp [girth, egirth_top h]

Depends on / 依赖: egirth_top
-/
theorem girth_top (h : 3 <= ENat.card α) : girth (⊤ : SimpleGraph α) = 3 := by
  simp [girth, egirth_top h]

/--
lemma `IsContained.girth_le` / 引理 `IsContained.girth_le`

English:
lemma IsContained.girth_le
  given: (h : G ⊑ G') (hG : ¬G.IsAcyclic)
  statement: G'.girth <= G.girth
  proof: ENat.toNat_le_toNat h.egirth_le egirth_eq_top.not.mpr hG

中文:
引理 IsContained.girth_le
  条件: (h : G ⊑ G') (hG : ¬G.IsAcyclic)
  结论: G'.girth <= G.girth
  证明: ENat.toNat_le_toNat h.egirth_le egirth_eq_top.not.mpr hG

Depends on / 依赖: ENat.toNat_le_toNat, egirth_eq_top, egirth_eq_top.not.mpr, egirth_le, h.egirth_le, toNat_le_toNat
-/
lemma IsContained.girth_le (h : G ⊑ G') (hG : ¬G.IsAcyclic) : G'.girth <= G.girth :=
ENat.toNat_le_toNat h.egirth_le egirth_eq_top.not.mpr hG

/--
lemma `Iso.girth_eq` / 引理 `Iso.girth_eq`

English:
lemma Iso.girth_eq
  given: (f : G ≃g G')
  statement: G.girth = G'.girth
  proof: by
  simp [girth, f.egirth_eq]

中文:
引理 Iso.girth_eq
  条件: (f : G ≃g G')
  结论: G.girth = G'.girth
  证明: by
  simp [girth, f.egirth_eq]

Depends on / 依赖: egirth_eq, f.egirth_eq
-/
lemma Iso.girth_eq (f : G ≃g G') : G.girth = G'.girth := by
  simp [girth, f.egirth_eq]

end girth

end SimpleGraph
