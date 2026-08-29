/-
Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Qi Ge, Christian Merten
-/
module

public import Mathlib.RingTheory.RingHomProperties

/-! # Meta properties of injective ring homomorphisms -/

public section

/--
lemma `_root_.RingHom.injective_stableUnderComposition` / 引理 `_root_.RingHom.injective_stableUnderComposition`

English:
lemma _root_.RingHom.injective_stableUnderComposition
  proof: by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf

中文:
引理 _root_.环态射.injective_stableUnderComposition
  证明: by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf

Depends on / 依赖: Function, Function.Injective.comp, Injective, RingHom, RingHom.coe_comp, coe_comp
-/
lemma _root_.RingHom.injective_stableUnderComposition :
    RingHom.StableUnderComposition (fun f => Function.Injective f) := by
  intro R S T _ _ _ f g hf hg
  simp only [RingHom.coe_comp]
  exact Function.Injective.comp hg hf

/--
lemma `_root_.RingHom.injective_respectsIso` / 引理 `_root_.RingHom.injective_respectsIso`

English:
lemma _root_.RingHom.injective_respectsIso
  proof: by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective

中文:
引理 _root_.环态射.injective_respectsIso
  证明: by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective

Depends on / 依赖: RingHom, RingHom.injective_stableUnderComposition.respectsIso, bijective, e.bijective.injective, injective, injective_stableUnderComposition, respectsIso
-/
lemma _root_.RingHom.injective_respectsIso :
    RingHom.RespectsIso (fun f => Function.Injective f) := by
  apply RingHom.injective_stableUnderComposition.respectsIso
  intro R S _ _ e
  exact e.bijective.injective
