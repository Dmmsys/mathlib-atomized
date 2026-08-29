/-
Copyright (c) 2025 Yaël Dillies, Michał Mrugała. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Michał Mrugała
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Maps

/-!
# Submonoid of pairs with quotient in a submonoid

This file defines the submonoid of pairs whose quotient lies in a submonoid of the localization.
-/

@[expose] public section

variable {M G H : Type*} [CommMonoid M] [CommGroup G] [CommGroup H]
  {f : (⊤ : Submonoid M).LocalizationMap G} {g : (⊤ : Submonoid M).LocalizationMap H}
  {s : Submonoid G} {x : M × M}

namespace Submonoid

variable (f s) in
/-- Given a commutative monoid `M`, a localization map `f` to its Grothendieck group `G` and
a submonoid `s` of `G`, `s.divPairs f` is the submonoid of pairs `(a, b)`
such that `f a / f b ∈ s`. -/
@[to_additive
/-- Given an additive commutative monoid `M`, a localization map `f` to its Grothendieck group `G`
and a submonoid `s` of `G`, `s.subPairs f` is the submonoid of pairs `(a, b)`
such that `f a - f b ∈ s`. -/]
/--
Definition of `divPairs` / `divPairs` 的定义

English:
definition divPairs
  signature: : Submonoid (M × M)
  body: s.comap divMonoidHom.comp .prodMap f f

中文:
定义 divPairs
  签名: : 子幺半群 (M × M)
  定义体: s.comap divMonoidHom.comp .prodMap f f

Depends on / 依赖: divMonoidHom, divMonoidHom.comp, prodMap, s.comap
-/
def divPairs : Submonoid (M × M) := s.comap divMonoidHom.comp .prodMap f f

/--
lemma `mem_divPairs` / 引理 `mem_divPairs`

English:
lemma mem_divPairs
  statement: x in divPairs f s ↔ f x.1 / f x.2 in s
  proof: .rfl

中文:
引理 mem_divPairs
  结论: x in divPairs f s ↔ f x.1 / f x.2 in s
  证明: .rfl
-/
@[to_additive (attr := simp)] lemma mem_divPairs : x in divPairs f s ↔ f x.1 / f x.2 in s := .rfl

--TODO(Yaël): make simp once `LocalizationMap.toMonoidHom` is simp nf
variable (f g s) in
@[to_additive]
/--
lemma `divPairs_comap` / 引理 `divPairs_comap`

English:
lemma divPairs_comap
  proof: by
  ext; simp

中文:
引理 divPairs_comap
  证明: by
  ext; simp
-/
lemma divPairs_comap :
    divPairs g (.comap (g.mulEquivOfLocalizations f).toMonoidHom s) = divPairs f s := by
  ext; simp

end Submonoid
