/-
Copyright (c) 2026 Jack McKoen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack McKoen
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.Basic

/-!
# Inner fibrations

Inner fibrations of simplicial sets are the morphisms in `SSet` which have the right lifting
property with respect to all inner horn inclusions.

Basic consequences of inner fibrations with respect to the definition of quasi-categories are
formalized.

-/

public section

open CategoryTheory MorphismProperty Simplicial Limits

universe u

namespace SSet

/--
Inductive type `innerHornInclusions` / 归纳类型 `innerHornInclusions`

English:
inductive innerHornInclusions
  parameters: : MorphismProperty SSet.{u} where
  constructors (1):
    - intro: {n : Nat} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) : innerHornInclusions Λ[n + 2, i].ι

中文:
归纳类型 innerHornInclusions
  参数: : MorphismProperty SSet.{u} where
  构造子 (1 个):
    - intro: {n : 自然数} (i : 有限集 (n + 3)) (h0 : 0 < i) (hn : i < 有限集.last (n + 2)) : innerHornInclusions Λ[n + 2, i].ι
-/
inductive innerHornInclusions : MorphismProperty SSet.{u} where
  | intro {n : Nat} (i : Fin (n + 3)) (h0 : 0 < i) (hn : i < Fin.last (n + 2)) :
    innerHornInclusions Λ[n + 2, i].ι

/--
lemma `horn_ι_mem_innerHornInclusions` / 引理 `horn_ι_mem_innerHornInclusions`

English:
lemma horn_ι_mem_innerHornInclusions
  statement: {n : Nat} {i : Fin (n + 1)}
  proof: by
  obtain _ | _ | k := n
  · grind
  · grind
  · exact ⟨i, h0, hn⟩

中文:
引理 horn_ι_mem_innerHornInclusions
  结论: {n : 自然数} {i : 有限集 (n + 1)}
  证明: by
  obtain _ | _ | k := n
  · grind
  · grind
  · exact ⟨i, h0, hn⟩
-/
lemma horn_ι_mem_innerHornInclusions {n : Nat} {i : Fin (n + 1)}
    (h0 : 0 < i) (hn : i < Fin.last n) : innerHornInclusions (horn.{u} n i).ι := by
  obtain _ | _ | k := n
  · grind
  · grind
  · exact ⟨i, h0, hn⟩

/--
lemma `innerHornInclusions_eq_iSup` / 引理 `innerHornInclusions_eq_iSup`

English:
lemma innerHornInclusions_eq_iSup
  proof: by
  ext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain @⟨n, i, h0, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, h0, hn⟩, _, _⟩ := h
    exact horn_ι_mem_innerHornInclusions h0 hn

中文:
引理 innerHornInclusions_eq_iSup
  证明: by
  ext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain @⟨n, i, h0, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, h0, hn⟩, _, _⟩ := h
    exact horn_ι_mem_innerHornInclusions h0 hn

Depends on / 依赖: Subtype, Subtype.exists, exists_prop, iSup_iff, ofHoms_iff
-/
lemma innerHornInclusions_eq_iSup :
    innerHornInclusions.{u} =
    ⨆ n, .ofHoms (fun p : {p : Fin (n + 3) // 0 < p ∧ p < Fin.last (n + 2)} => Λ[n + 2, p].ι) := by
  ext
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain @⟨n, i, h0, hn⟩ := h
    simp only [iSup_iff, ofHoms_iff, Subtype.exists, exists_prop]
    use n, i
  · simp only [iSup_iff, ofHoms_iff] at h
    obtain ⟨n, ⟨i, h0, hn⟩, _, _⟩ := h
    exact horn_ι_mem_innerHornInclusions h0 hn

/--
lemma `innerHornInclusions_le_J` / 引理 `innerHornInclusions_le_J`

English:
lemma innerHornInclusions_le_J
  statement: innerHornInclusions.{u} <= modelCategoryQuillen.J
  proof: fun _ _ _ ⟨_, _, _⟩ => modelCategoryQuillen.horn_ι_mem_J ..

中文:
引理 innerHornInclusions_le_J
  结论: innerHornInclusions.{u} <= modelCategoryQuillen.J
  证明: fun _ _ _ ⟨_, _, _⟩ => modelCategoryQuillen.horn_ι_mem_J ..

Depends on / 依赖: modelCategoryQuillen, modelCategoryQuillen.horn_
-/
lemma innerHornInclusions_le_J : innerHornInclusions.{u} <= modelCategoryQuillen.J :=
  fun _ _ _ ⟨_, _, _⟩ => modelCategoryQuillen.horn_ι_mem_J ..

/--
lemma `innerHornInclusions_le_monomorphisms` / 引理 `innerHornInclusions_le_monomorphisms`

English:
lemma innerHornInclusions_le_monomorphisms
  proof: innerHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

中文:
引理 innerHornInclusions_le_monomorphisms
  证明: innerHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

Depends on / 依赖: J_le_monomorphisms, innerHornInclusions_le_J, innerHornInclusions_le_J.trans, modelCategoryQuillen, modelCategoryQuillen.J_le_monomorphisms
-/
lemma innerHornInclusions_le_monomorphisms :
    innerHornInclusions.{u} <= monomorphisms SSet :=
  innerHornInclusions_le_J.trans modelCategoryQuillen.J_le_monomorphisms

/-- The inner fibrations are the morphisms which have the right lifting property
with respect to inner horn inclusions. -/
@[expose, kerodon 01BA]
/--
Definition of `innerFibrations` / `innerFibrations` 的定义

English:
definition innerFibrations
  signature: : MorphismProperty SSet.{u}
  body: innerHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

中文:
定义 innerFibrations
  签名: : MorphismProperty SSet.{u}
  定义体: innerHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

Depends on / 依赖: innerHornInclusions, innerHornInclusions.rlp
-/
def innerFibrations : MorphismProperty SSet.{u} := innerHornInclusions.rlp
deriving IsMultiplicative, RespectsIso, IsStableUnderBaseChange,
  IsStableUnderRetracts

/-- A morphism `q` satisfies `[InnerFibration q]` if it belongs to `innerFibrations`. -/
@[mk_iff]
/--
Definition of `InnerFibration` / `InnerFibration` 的定义

English:
class InnerFibration
  parameters: {X Y : SSet} (q : X ⟶ Y)
  axioms and operations (1):
    - mem : innerFibrations q

中文:
类 内纤维化
  参数: {X Y : SSet} (q : X ⟶ Y)
  公理与运算 (1 个):
    - mem : innerFibrations q
-/
class InnerFibration {X Y : SSet} (q : X ⟶ Y) : Prop where
  mem : innerFibrations q

/--
lemma `mem_innerFibrations` / 引理 `mem_innerFibrations`

English:
lemma mem_innerFibrations
  given: {X Y : SSet} (q : X ⟶ Y) [InnerFibration q]
  statement: innerFibrations q
  proof: InnerFibration.mem

中文:
引理 mem_innerFibrations
  条件: {X Y : SSet} (q : X ⟶ Y) [内纤维化 q]
  结论: innerFibrations q
  证明: InnerFibration.mem

Depends on / 依赖: InnerFibration, InnerFibration.mem
-/
lemma mem_innerFibrations {X Y : SSet} (q : X ⟶ Y) [InnerFibration q] : innerFibrations q :=
  InnerFibration.mem

/--
lemma `quasicategory_iff_innerFibration` / 引理 `quasicategory_iff_innerFibration`

English:
lemma quasicategory_iff_innerFibration
  given: (X : SSet.{u})
  proof: by
  rw [quasicategory_iff_hasLiftingProperty.{u} _ terminalIsTerminal]; rw [innerFibration_iff]
  exact ⟨fun h _ _ _ ⟨i, h0, hn⟩ => h h0 hn,
    fun h _ _ h0 hn => h _ (horn_ι_mem_innerHornInclusions h0 hn)⟩

@[kerodon 01BB]

中文:
引理 quasicategory_iff_innerFibration
  条件: (X : SSet.{u})
  证明: by
  rw [quasicategory_iff_hasLiftingProperty.{u} _ terminalIsTerminal]; rw [innerFibration_iff]
  exact ⟨fun h _ _ _ ⟨i, h0, hn⟩ => h h0 hn,
    fun h _ _ h0 hn => h _ (horn_ι_mem_innerHornInclusions h0 hn)⟩

@[kerodon 01BB]

Depends on / 依赖: innerFibration_iff, quasicategory_iff_hasLiftingProperty, terminalIsTerminal
-/
lemma quasicategory_iff_innerFibration (X : SSet.{u}) :
    Quasicategory X ↔ InnerFibration (terminal.from X) := by
  rw [quasicategory_iff_hasLiftingProperty.{u} _ terminalIsTerminal]; rw [innerFibration_iff]
  exact ⟨fun h _ _ _ ⟨i, h0, hn⟩ => h h0 hn,
    fun h _ _ h0 hn => h _ (horn_ι_mem_innerHornInclusions h0 hn)⟩

@[kerodon 01BB]
/--
lemma `quasicategory_iff_of_isTerminal` / 引理 `quasicategory_iff_of_isTerminal`

English:
lemma quasicategory_iff_of_isTerminal
  proof: by
  simp only [quasicategory_iff_innerFibration, innerFibration_iff]
  symm
  apply innerFibrations.arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (Limits.IsTerminal.uniqueUpToIso hY Limits.terminalIsTerminal)

@[kerodon 01BJ]

中文:
引理 quasicategory_iff_of_isTerminal
  证明: by
  simp only [quasicategory_iff_innerFibration, innerFibration_iff]
  symm
  apply innerFibrations.arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (Limits.IsTerminal.uniqueUpToIso hY Limits.terminalIsTerminal)

@[kerodon 01BJ]

Depends on / 依赖: Arrow.isoMk, IsTerminal, Iso.refl, Limits, Limits.IsTerminal.uniqueUpToIso, Limits.terminalIsTerminal, arrow_mk_iso_iff, innerFibration_iff, innerFibrations, innerFibrations.arrow_mk_iso_iff, quasicategory_iff_innerFibration, terminalIsTerminal, uniqueUpToIso
-/
lemma quasicategory_iff_of_isTerminal
    {X Y : SSet} (p : X ⟶ Y) (hY : IsTerminal Y) :
    Quasicategory X ↔ InnerFibration p := by
  simp only [quasicategory_iff_innerFibration, innerFibration_iff]
  symm
  apply innerFibrations.arrow_mk_iso_iff
  exact Arrow.isoMk (Iso.refl _) (Limits.IsTerminal.uniqueUpToIso hY Limits.terminalIsTerminal)

@[kerodon 01BJ]
/--
lemma `quasicategory_of_innerFibration` / 引理 `quasicategory_of_innerFibration`

English:
lemma quasicategory_of_innerFibration
  proof: by
  rw [quasicategory_iff_innerFibration] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]; rw [innerFibration_iff]
  refine innerFibrations.comp_mem _ _ InnerFibration.mem hY.mem

中文:
引理 quasicategory_of_innerFibration
  证明: by
  rw [quasicategory_iff_innerFibration] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]; rw [innerFibration_iff]
  refine innerFibrations.comp_mem _ _ InnerFibration.mem hY.mem

Depends on / 依赖: InnerFibration, InnerFibration.mem, Subsingleton, Subsingleton.elim, comp_mem, hY.mem, innerFibration_iff, innerFibrations, innerFibrations.comp_mem, quasicategory_iff_innerFibration, terminal, terminal.from
-/
lemma quasicategory_of_innerFibration
    {X Y : SSet} (p : X ⟶ Y) [InnerFibration p] [hY : Quasicategory Y] :
    Quasicategory X := by
  rw [quasicategory_iff_innerFibration] at hY ⊢
  rw [Subsingleton.elim (terminal.from X) (p ≫ terminal.from Y)]; rw [innerFibration_iff]
  refine innerFibrations.comp_mem _ _ InnerFibration.mem hY.mem

instance {X : SSet} [Quasicategory X] : InnerFibration (terminal.from X) := by
  rwa [← quasicategory_iff_innerFibration]

@[deprecated quasicategory_iff_of_isTerminal (since := "2026-06-08")]
/--
lemma `quasicategory_of_from_innerFibrations` / 引理 `quasicategory_of_from_innerFibrations`

English:
lemma quasicategory_of_from_innerFibrations
  statement: (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
  proof: quasicategory_of_hasLiftingProperty S t (fun h0 hn => h _ (horn_ι_mem_innerHornInclusions h0 hn))

@[deprecated quasicategory_iff_of_isTerminal (since := "2026-06-08")]

中文:
引理 quasicategory_of_from_innerFibrations
  结论: (S : SSet) {X : SSet} (t : Limits.是终止 X)
  证明: quasicategory_of_hasLiftingProperty S t (fun h0 hn => h _ (horn_ι_mem_innerHornInclusions h0 hn))

@[deprecated quasicategory_iff_of_isTerminal (since := "2026-06-08")]

Depends on / 依赖: quasicategory_of_hasLiftingProperty
-/
lemma quasicategory_of_from_innerFibrations (S : SSet) {X : SSet} (t : Limits.IsTerminal X)
    (h : innerFibrations (t.from S)) : Quasicategory S :=
  quasicategory_of_hasLiftingProperty S t (fun h0 hn => h _ (horn_ι_mem_innerHornInclusions h0 hn))

@[deprecated quasicategory_iff_of_isTerminal (since := "2026-06-08")]
/--
lemma `Quasicategory.from_innerFibrations` / 引理 `Quasicategory.from_innerFibrations`

English:
lemma Quasicategory.from_innerFibrations
  statement: (S : SSet) [Quasicategory S]
  proof: fun _ _ _ ⟨_, h0, hn⟩ => hasLiftingProperty S t h0 hn

@[deprecated (since := "2026-06-08")]
alias quasicategory_iff_from_innerFibration := quasicategory_iff_innerFibration

@[deprecated (since := "2026-06-08")]
alias quasicategory_of_innerFibration_quasicategory := quasicategory_of_innerFibration

中文:
引理 拟范畴.from_innerFibrations
  结论: (S : SSet) [拟范畴 S]
  证明: fun _ _ _ ⟨_, h0, hn⟩ => hasLiftingProperty S t h0 hn

@[deprecated (since := "2026-06-08")]
alias quasicategory_iff_from_innerFibration := quasicategory_iff_innerFibration

@[deprecated (since := "2026-06-08")]
alias quasicategory_of_innerFibration_quasicategory := quasicategory_of_innerFibration

Depends on / 依赖: hasLiftingProperty
-/
lemma Quasicategory.from_innerFibrations (S : SSet) [Quasicategory S]
    {X : SSet} (t : Limits.IsTerminal X) : innerFibrations (t.from S) :=
  fun _ _ _ ⟨_, h0, hn⟩ => hasLiftingProperty S t h0 hn

@[deprecated (since := "2026-06-08")]
alias quasicategory_iff_from_innerFibration := quasicategory_iff_innerFibration

@[deprecated (since := "2026-06-08")]
alias quasicategory_of_innerFibration_quasicategory := quasicategory_of_innerFibration

end SSet
