/-
Copyright (c) 2022 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Sara Rousta
-/
module

public import Mathlib.Data.Set.Lattice.Image
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.UpperLower.Basic

/-!
# The complete lattice structure on `UpperSet`/`LowerSet`

This file defines a completely distributive lattice structure on `UpperSet` and `LowerSet`,
pulled back across the canonical injection (`UpperSet.carrier`, `LowerSet.carrier`) into `Set α`.

## Notes

Upper sets are ordered by **reverse** inclusion. This convention is motivated by the fact that this
makes them order-isomorphic to lower sets and antichains, and matches the convention on `Filter`.
-/

@[expose] public section

open OrderDual Set

variable {α β γ : Type*} {ι : Sort*} {κ : ι -> Sort*}

namespace UpperSet

section LE

variable [LE α]

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SetLike (UpperSet α) α
  body: UpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

中文:
实例 :
  签名: SetLike (UpperSet α) α
  定义体: UpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

Depends on / 依赖: UpperSet, UpperSet.carrier, carrier
-/
instance : SetLike (UpperSet α) α where
  coe := UpperSet.carrier
  coe_injective s t h := by cases s; cases t; congr

/-- See Note [custom simps projection]. -/
@[to_dual /-- See Note [custom simps projection]. -/]
/--
Definition of `Simps.coe` / `Simps.coe` 的定义

English:
definition Simps.coe
  signature: (s : UpperSet α)
  body: s

initialize_simps_projections UpperSet (carrier -> coe, as_prefix coe)
initialize_simps_projections LowerSet (carrier -> coe, as_prefix coe)

@[to_dual (attr := ext)]

中文:
定义 Simps.coe
  签名: (s : UpperSet α)
  定义体: s

initialize_simps_projections UpperSet (carrier -> coe, as_prefix coe)
initialize_simps_projections LowerSet (carrier -> coe, as_prefix coe)

@[to_dual (attr := ext)]
-/
def Simps.coe (s : UpperSet α) : Set α := s

initialize_simps_projections UpperSet (carrier -> coe, as_prefix coe)
initialize_simps_projections LowerSet (carrier -> coe, as_prefix coe)

@[to_dual (attr := ext)]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {s t : UpperSet α}
  statement: (s : Set α) = t -> s = t
  proof: SetLike.ext'

@[to_dual (attr := simp)]

中文:
定理 ext
  条件: {s t : UpperSet α}
  结论: (s : Set α) = t -> s = t
  证明: SetLike.ext'

@[to_dual (attr := simp)]

Depends on / 依赖: SetLike, SetLike.ext
-/
theorem ext {s t : UpperSet α} : (s : Set α) = t -> s = t :=
  SetLike.ext'

@[to_dual (attr := simp)]
/--
theorem `carrier_eq_coe` / 定理 `carrier_eq_coe`

English:
theorem carrier_eq_coe
  given: (s : UpperSet α)
  statement: s.carrier = s
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 carrier_eq_coe
  条件: (s : UpperSet α)
  结论: s.carrier = s
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem carrier_eq_coe (s : UpperSet α) : s.carrier = s :=
  rfl

@[to_dual (attr := simp)]
/--
lemma `upper` / 引理 `upper`

English:
lemma upper
  given: (s : UpperSet α)
  statement: IsUpperSet (s : Set α)
  proof: s.upper'

@[to_dual (attr := simp, norm_cast)]

中文:
引理 upper
  条件: (s : UpperSet α)
  结论: IsUpperSet (s : Set α)
  证明: s.upper'

@[to_dual (attr := simp, norm_cast)]
-/
protected lemma upper (s : UpperSet α) : IsUpperSet (s : Set α) := s.upper'

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (s : Set α) (hs)
  statement: mk s hs = s
  proof: rfl

@[to_dual (attr := simp)]

中文:
引理 coe_mk
  条件: (s : Set α) (hs)
  结论: mk s hs = s
  证明: rfl

@[to_dual (attr := simp)]
-/
lemma coe_mk (s : Set α) (hs) : mk s hs = s := rfl

@[to_dual (attr := simp)]
/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {s : Set α} (hs) {a : α}
  statement: a in mk s hs ↔ a in s
  proof: Iff.rfl

中文:
引理 mem_mk
  条件: {s : Set α} (hs) {a : α}
  结论: a in mk s hs ↔ a in s
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma mem_mk {s : Set α} (hs) {a : α} : a in mk s hs ↔ a in s := Iff.rfl

variable {S : Set (UpperSet α)} {s t : UpperSet α} {a : α}

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Max (UpperSet α)
  body: ⟨fun s t => ⟨s inter t, s.upper.inter t.upper⟩⟩

@[to_dual]

中文:
实例 :
  签名: Max (UpperSet α)
  定义体: ⟨fun s t => ⟨s inter t, s.upper.inter t.upper⟩⟩

@[to_dual]

Depends on / 依赖: s.upper.inter, t.upper
-/
instance : Max (UpperSet α) :=
  ⟨fun s t => ⟨s inter t, s.upper.inter t.upper⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Min (UpperSet α)
  body: ⟨fun s t => ⟨s union t, s.upper.union t.upper⟩⟩

@[to_dual]

中文:
实例 :
  签名: Min (UpperSet α)
  定义体: ⟨fun s t => ⟨s union t, s.upper.union t.upper⟩⟩

@[to_dual]

Depends on / 依赖: s.upper.union, t.upper
-/
instance : Min (UpperSet α) :=
  ⟨fun s t => ⟨s union t, s.upper.union t.upper⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Top (UpperSet α)
  body: ⟨⟨∅, isUpperSet_empty⟩⟩

@[to_dual]

中文:
实例 :
  签名: Top (UpperSet α)
  定义体: ⟨⟨∅, isUpperSet_empty⟩⟩

@[to_dual]

Depends on / 依赖: isUpperSet_empty
-/
instance : Top (UpperSet α) :=
  ⟨⟨∅, isUpperSet_empty⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Bot (UpperSet α)
  body: ⟨⟨univ, isUpperSet_univ⟩⟩

@[to_dual]

中文:
实例 :
  签名: Bot (UpperSet α)
  定义体: ⟨⟨univ, isUpperSet_univ⟩⟩

@[to_dual]

Depends on / 依赖: isUpperSet_univ
-/
instance : Bot (UpperSet α) :=
  ⟨⟨univ, isUpperSet_univ⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SupSet (UpperSet α)
  body: ⟨fun S => ⟨⋂ s in S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

@[to_dual]

中文:
实例 :
  签名: SupSet (UpperSet α)
  定义体: ⟨fun S => ⟨⋂ s in S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

@[to_dual]

Depends on / 依赖: _expand, _trunc, expand_eq_expand, s.upper
-/
instance : SupSet (UpperSet α) :=
  ⟨fun S => ⟨⋂ s in S, ↑s, isUpperSet_iInter₂ fun s _ => s.upper⟩⟩

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (UpperSet α)
  body: ⟨fun S => ⟨⋃ s in S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

中文:
实例 :
  签名: InfSet (UpperSet α)
  定义体: ⟨fun S => ⟨⋃ s in S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

Depends on / 依赖: s.upper
-/
instance : InfSet (UpperSet α) :=
  ⟨fun S => ⟨⋃ s in S, ↑s, isUpperSet_iUnion₂ fun s _ => s.upper⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (UpperSet α)
  body: PartialOrder.lift _ (toDual.injective.comp SetLike.coe_injective)

中文:
实例 :
  签名: PartialOrder (UpperSet α)
  定义体: PartialOrder.lift _ (toDual.injective.comp SetLike.coe_injective)

Depends on / 依赖: PartialOrder, PartialOrder.lift, SetLike, SetLike.coe_injective, coe_injective, injective, toDual, toDual.injective.comp
-/
instance : PartialOrder (UpperSet α) :=
  PartialOrder.lift _ (toDual.injective.comp SetLike.coe_injective)

/--
Instance `completeLattice` / 实例 `completeLattice`

English:
instance completeLattice
  signature: : CompleteLattice (UpperSet α)
  body: (toDual.injective.comp SetLike.coe_injective).completeLattice _
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

中文:
实例 completeLattice
  签名: : CompleteLattice (UpperSet α)
  定义体: (toDual.injective.comp SetLike.coe_injective).completeLattice _
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, completeLattice, injective, toDual, toDual.injective.comp
-/
instance completeLattice : CompleteLattice (UpperSet α) :=
  (toDual.injective.comp SetLike.coe_injective).completeLattice _
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

/--
Instance `completelyDistribLattice` / 实例 `completelyDistribLattice`

English:
instance completelyDistribLattice
  signature: : CompletelyDistribLattice (UpperSet α)
  body: .ofMinimalAxioms
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      (fun _ => rfl) (fun _ => rfl)

@[to_dual existing]

中文:
实例 completelyDistribLattice
  签名: : CompletelyDistribLattice (UpperSet α)
  定义体: .ofMinimalAxioms
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      (fun _ => rfl) (fun _ => rfl)

@[to_dual existing]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, completelyDistribLatticeMinimalAxioms, injective, ofMinimalAxioms, toDual, toDual.injective.comp
-/
instance completelyDistribLattice : CompletelyDistribLattice (UpperSet α) :=
.ofMinimalAxioms
    (toDual.injective.comp SetLike.coe_injective).completelyDistribLatticeMinimalAxioms .of _
      (fun _ => rfl) (fun _ => rfl)

@[to_dual existing]
/--
Instance `_root_.LowerSet.instPartialOrder` / 实例 `_root_.LowerSet.instPartialOrder`

English:
instance _root_.LowerSet.instPartialOrder
  signature: : PartialOrder (LowerSet α)
  body: PartialOrder.lift _ SetLike.coe_injective

@[to_dual existing]

中文:
实例 _root_.LowerSet.instPartialOrder
  签名: : PartialOrder (LowerSet α)
  定义体: PartialOrder.lift _ SetLike.coe_injective

@[to_dual existing]

Depends on / 依赖: PartialOrder, PartialOrder.lift, SetLike, SetLike.coe_injective, coe_injective
-/
instance _root_.LowerSet.instPartialOrder : PartialOrder (LowerSet α) :=
  PartialOrder.lift _ SetLike.coe_injective

@[to_dual existing]
/--
Instance `_root_.LowerSet.completeLattice` / 实例 `_root_.LowerSet.completeLattice`

English:
instance _root_.LowerSet.completeLattice
  signature: : CompleteLattice (LowerSet α)
  body: SetLike.coe_injective.completeLattice _
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

@[to_dual existing]

中文:
实例 _root_.LowerSet.completeLattice
  签名: : CompleteLattice (LowerSet α)
  定义体: SetLike.coe_injective.completeLattice _
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

@[to_dual existing]

Depends on / 依赖: SetLike, SetLike.coe_injective.completeLattice, coe_injective, completeLattice
-/
instance _root_.LowerSet.completeLattice : CompleteLattice (LowerSet α) :=
  SetLike.coe_injective.completeLattice _
    .rfl .rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl rfl

@[to_dual existing]
/--
Instance `_root_.LowerSet.completelyDistribLattice` / 实例 `_root_.LowerSet.completelyDistribLattice`

English:
instance _root_.LowerSet.completelyDistribLattice
  signature: : CompletelyDistribLattice (LowerSet α)
  body: .ofMinimalAxioms SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    (fun _ => rfl) (fun _ => rfl)

@[to_dual]

中文:
实例 _root_.LowerSet.completelyDistribLattice
  签名: : CompletelyDistribLattice (LowerSet α)
  定义体: .ofMinimalAxioms SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    (fun _ => rfl) (fun _ => rfl)

@[to_dual]

Depends on / 依赖: SetLike, SetLike.coe_injective.completelyDistribLatticeMinimalAxioms, coe_injective, completelyDistribLatticeMinimalAxioms, ofMinimalAxioms
-/
instance _root_.LowerSet.completelyDistribLattice : CompletelyDistribLattice (LowerSet α) :=
.ofMinimalAxioms SetLike.coe_injective.completelyDistribLatticeMinimalAxioms .of _
    (fun _ => rfl) (fun _ => rfl)

@[to_dual]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (UpperSet α)
  body: ⟨⊥⟩

@[to_dual (attr := simp 1100, norm_cast)]

中文:
实例 :
  签名: Inhabited (UpperSet α)
  定义体: ⟨⊥⟩

@[to_dual (attr := simp 1100, norm_cast)]
-/
instance : Inhabited (UpperSet α) :=
  ⟨⊥⟩

@[to_dual (attr := simp 1100, norm_cast)]
/--
theorem `coe_subset_coe` / 定理 `coe_subset_coe`

English:
theorem coe_subset_coe
  statement: (s : Set α) subseteq t ↔ t <= s
  proof: Iff.rfl

@[to_dual (attr := simp 1100, norm_cast)]

中文:
定理 coe_subset_coe
  结论: (s : Set α) subseteq t ↔ t <= s
  证明: Iff.rfl

@[to_dual (attr := simp 1100, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
theorem coe_subset_coe : (s : Set α) subseteq t ↔ t <= s :=
  Iff.rfl

@[to_dual (attr := simp 1100, norm_cast)]
/--
lemma `coe_ssubset_coe` / 引理 `coe_ssubset_coe`

English:
lemma coe_ssubset_coe
  statement: (s : Set α) ⊂ t ↔ t < s
  proof: Iff.rfl

@[to_dual (attr := simp, norm_cast)]

中文:
引理 coe_ssubset_coe
  结论: (s : Set α) ⊂ t ↔ t < s
  证明: Iff.rfl

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: Iff.rfl
-/
lemma coe_ssubset_coe : (s : Set α) ⊂ t ↔ t < s := Iff.rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_top` / 定理 `coe_top`

English:
theorem coe_top
  statement: ((⊤ : UpperSet α) : Set α) = ∅
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_top
  结论: ((⊤ : UpperSet α) : Set α) = ∅
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_top : ((⊤ : UpperSet α) : Set α) = ∅ :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_bot` / 定理 `coe_bot`

English:
theorem coe_bot
  statement: ((⊥ : UpperSet α) : Set α) = univ
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_bot
  结论: ((⊥ : UpperSet α) : Set α) = univ
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_bot : ((⊥ : UpperSet α) : Set α) = univ :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_eq_univ` / 定理 `coe_eq_univ`

English:
theorem coe_eq_univ
  statement: (s : Set α) = univ ↔ s = ⊥
  proof: by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_eq_univ
  结论: (s : Set α) = univ ↔ s = ⊥
  证明: by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: SetLike, SetLike.ext, _iff
-/
theorem coe_eq_univ : (s : Set α) = univ ↔ s = ⊥ := by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_eq_empty` / 定理 `coe_eq_empty`

English:
theorem coe_eq_empty
  statement: (s : Set α) = ∅ ↔ s = ⊤
  proof: by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_eq_empty
  结论: (s : Set α) = ∅ ↔ s = ⊤
  证明: by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: SetLike, SetLike.ext, _iff
-/
theorem coe_eq_empty : (s : Set α) = ∅ ↔ s = ⊤ := by simp [SetLike.ext'_iff]

@[to_dual (attr := simp, norm_cast)]
/--
lemma `coe_nonempty` / 引理 `coe_nonempty`

English:
lemma coe_nonempty
  statement: (s : Set α).Nonempty ↔ s != ⊤
  proof: nonempty_iff_ne_empty.trans coe_eq_empty.not

@[to_dual (attr := simp, norm_cast)]

中文:
引理 coe_nonempty
  结论: (s : Set α).Nonempty ↔ s != ⊤
  证明: nonempty_iff_ne_empty.trans coe_eq_empty.not

@[to_dual (attr := simp, norm_cast)]

Depends on / 依赖: coe_eq_empty, coe_eq_empty.not, nonempty_iff_ne_empty, nonempty_iff_ne_empty.trans
-/
lemma coe_nonempty : (s : Set α).Nonempty ↔ s != ⊤ :=
  nonempty_iff_ne_empty.trans coe_eq_empty.not

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_sup` / 定理 `coe_sup`

English:
theorem coe_sup
  given: (s t : UpperSet α)
  statement: (↑(s ⊔ t) : Set α) = (s : Set α) inter t
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_sup
  条件: (s t : UpperSet α)
  结论: (↑(s ⊔ t) : Set α) = (s : Set α) inter t
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_sup (s t : UpperSet α) : (↑(s ⊔ t) : Set α) = (s : Set α) inter t :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: (s t : UpperSet α)
  statement: (↑(s ⊓ t) : Set α) = (s : Set α) union t
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_inf
  条件: (s t : UpperSet α)
  结论: (↑(s ⊓ t) : Set α) = (s : Set α) union t
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_inf (s t : UpperSet α) : (↑(s ⊓ t) : Set α) = (s : Set α) union t :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_sSup` / 定理 `coe_sSup`

English:
theorem coe_sSup
  given: (S : Set (UpperSet α))
  statement: (↑(sSup S) : Set α) = ⋂ s in S, ↑s
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_sSup
  条件: (S : Set (UpperSet α))
  结论: (↑(sSup S) : Set α) = ⋂ s in S, ↑s
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_sSup (S : Set (UpperSet α)) : (↑(sSup S) : Set α) = ⋂ s in S, ↑s :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (UpperSet α))
  statement: (↑(sInf S) : Set α) = ⋃ s in S, ↑s
  proof: rfl

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_sInf
  条件: (S : Set (UpperSet α))
  结论: (↑(sInf S) : Set α) = ⋃ s in S, ↑s
  证明: rfl

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_sInf (S : Set (UpperSet α)) : (↑(sInf S) : Set α) = ⋃ s in S, ↑s :=
  rfl

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_iSup` / 定理 `coe_iSup`

English:
theorem coe_iSup
  given: (f : ι -> UpperSet α)
  statement: (↑(⨆ i, f i) : Set α) = ⋂ i, f i
  proof: by simp [iSup]

@[to_dual (attr := simp, norm_cast)]

中文:
定理 coe_iSup
  条件: (f : ι -> UpperSet α)
  结论: (↑(⨆ i, f i) : Set α) = ⋂ i, f i
  证明: by simp [iSup]

@[to_dual (attr := simp, norm_cast)]
-/
theorem coe_iSup (f : ι -> UpperSet α) : (↑(⨆ i, f i) : Set α) = ⋂ i, f i := by simp [iSup]

@[to_dual (attr := simp, norm_cast)]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: (f : ι -> UpperSet α)
  statement: (↑(⨅ i, f i) : Set α) = ⋃ i, f i
  proof: by simp [iInf]

@[to_dual (attr := norm_cast)]

中文:
定理 coe_iInf
  条件: (f : ι -> UpperSet α)
  结论: (↑(⨅ i, f i) : Set α) = ⋃ i, f i
  证明: by simp [iInf]

@[to_dual (attr := norm_cast)]
-/
theorem coe_iInf (f : ι -> UpperSet α) : (↑(⨅ i, f i) : Set α) = ⋃ i, f i := by simp [iInf]

@[to_dual (attr := norm_cast)]
/--
theorem `coe_iSup₂` / 定理 `coe_iSup₂`

English:
theorem coe_iSup₂
  given: (f : forall i, κ i -> UpperSet α)
  proof: by simp

@[to_dual (attr := norm_cast)]

中文:
定理 coe_iSup₂
  条件: (f : 对任意 i, κ i -> UpperSet α)
  证明: by simp

@[to_dual (attr := norm_cast)]
-/
theorem coe_iSup₂ (f : forall i, κ i -> UpperSet α) :
    (↑(⨆ (i) (j), f i j) : Set α) = ⋂ (i) (j), f i j := by simp

@[to_dual (attr := norm_cast)]
/--
theorem `coe_iInf₂` / 定理 `coe_iInf₂`

English:
theorem coe_iInf₂
  given: (f : forall i, κ i -> UpperSet α)
  proof: by simp

@[to_dual (attr := simp)]

中文:
定理 coe_iInf₂
  条件: (f : 对任意 i, κ i -> UpperSet α)
  证明: by simp

@[to_dual (attr := simp)]
-/
theorem coe_iInf₂ (f : forall i, κ i -> UpperSet α) :
    (↑(⨅ (i) (j), f i j) : Set α) = ⋃ (i) (j), f i j := by simp

@[to_dual (attr := simp)]
/--
theorem `notMem_top` / 定理 `notMem_top`

English:
theorem notMem_top
  statement: a ∉ (⊤ : UpperSet α)
  proof: id

@[to_dual (attr := simp)]

中文:
定理 notMem_top
  结论: a ∉ (⊤ : UpperSet α)
  证明: id

@[to_dual (attr := simp)]
-/
theorem notMem_top : a ∉ (⊤ : UpperSet α) :=
  id

@[to_dual (attr := simp)]
/--
theorem `mem_bot` / 定理 `mem_bot`

English:
theorem mem_bot
  statement: a in (⊥ : UpperSet α)
  proof: trivial

@[to_dual (attr := simp)]

中文:
定理 mem_bot
  结论: a in (⊥ : UpperSet α)
  证明: trivial

@[to_dual (attr := simp)]
-/
theorem mem_bot : a in (⊥ : UpperSet α) :=
  trivial

@[to_dual (attr := simp)]
/--
theorem `mem_sup_iff` / 定理 `mem_sup_iff`

English:
theorem mem_sup_iff
  statement: a in s ⊔ t ↔ a in s ∧ a in t
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 mem_sup_iff
  结论: a in s ⊔ t ↔ a in s ∧ a in t
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_sup_iff : a in s ⊔ t ↔ a in s ∧ a in t :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `mem_inf_iff` / 定理 `mem_inf_iff`

English:
theorem mem_inf_iff
  statement: a in s ⊓ t ↔ a in s ∨ a in t
  proof: Iff.rfl

@[to_dual (attr := simp)]

中文:
定理 mem_inf_iff
  结论: a in s ⊓ t ↔ a in s ∨ a in t
  证明: Iff.rfl

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_inf_iff : a in s ⊓ t ↔ a in s ∨ a in t :=
  Iff.rfl

@[to_dual (attr := simp)]
/--
theorem `mem_sSup_iff` / 定理 `mem_sSup_iff`

English:
theorem mem_sSup_iff
  statement: a in sSup S ↔ forall s in S, a in s
  proof: mem_iInter₂

@[to_dual (attr := simp)]

中文:
定理 mem_sSup_iff
  结论: a in sSup S ↔ 对任意 s in S, a in s
  证明: mem_iInter₂

@[to_dual (attr := simp)]
-/
theorem mem_sSup_iff : a in sSup S ↔ forall s in S, a in s :=
  mem_iInter₂

@[to_dual (attr := simp)]
/--
theorem `mem_sInf_iff` / 定理 `mem_sInf_iff`

English:
theorem mem_sInf_iff
  statement: a in sInf S ↔ exists s in S, a in s
  proof: mem_iUnion₂.trans by simp only [exists_prop, SetLike.mem_coe]

@[to_dual (attr := simp)]

中文:
定理 mem_sInf_iff
  结论: a in sInf S ↔ 存在 s in S, a in s
  证明: mem_iUnion₂.trans by simp only [exists_prop, SetLike.mem_coe]

@[to_dual (attr := simp)]

Depends on / 依赖: SetLike, SetLike.mem_coe, exists_prop, mem_coe
-/
theorem mem_sInf_iff : a in sInf S ↔ exists s in S, a in s :=
mem_iUnion₂.trans by simp only [exists_prop, SetLike.mem_coe]

@[to_dual (attr := simp)]
/--
theorem `mem_iSup_iff` / 定理 `mem_iSup_iff`

English:
theorem mem_iSup_iff
  given: {f : ι -> UpperSet α}
  statement: (a in ⨆ i, f i) ↔ forall i, a in f i
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_iSup]
  exact mem_iInter

@[to_dual (attr := simp)]

中文:
定理 mem_iSup_iff
  条件: {f : ι -> UpperSet α}
  结论: (a in ⨆ i, f i) ↔ 对任意 i, a in f i
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_iSup]
  exact mem_iInter

@[to_dual (attr := simp)]

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_iSup, mem_coe, mem_iInter
-/
theorem mem_iSup_iff {f : ι -> UpperSet α} : (a in ⨆ i, f i) ↔ forall i, a in f i := by
  rw [← SetLike.mem_coe]; rw [coe_iSup]
  exact mem_iInter

@[to_dual (attr := simp)]
/--
theorem `mem_iInf_iff` / 定理 `mem_iInf_iff`

English:
theorem mem_iInf_iff
  given: {f : ι -> UpperSet α}
  statement: (a in ⨅ i, f i) ↔ exists i, a in f i
  proof: by
  rw [← SetLike.mem_coe]; rw [coe_iInf]
  exact mem_iUnion

@[to_dual]

中文:
定理 mem_iInf_iff
  条件: {f : ι -> UpperSet α}
  结论: (a in ⨅ i, f i) ↔ 存在 i, a in f i
  证明: by
  rw [← SetLike.mem_coe]; rw [coe_iInf]
  exact mem_iUnion

@[to_dual]

Depends on / 依赖: SetLike, SetLike.mem_coe, coe_iInf, mem_coe, mem_iUnion
-/
theorem mem_iInf_iff {f : ι -> UpperSet α} : (a in ⨅ i, f i) ↔ exists i, a in f i := by
  rw [← SetLike.mem_coe]; rw [coe_iInf]
  exact mem_iUnion

@[to_dual]
/--
theorem `mem_iSup₂_iff` / 定理 `mem_iSup₂_iff`

English:
theorem mem_iSup₂_iff
  given: {f : forall i, κ i -> UpperSet α}
  statement: (a in ⨆ (i) (j), f i j) ↔ forall i j, a in f i j
  proof: by
  simp

@[to_dual]

中文:
定理 mem_iSup₂_iff
  条件: {f : 对任意 i, κ i -> UpperSet α}
  结论: (a in ⨆ (i) (j), f i j) ↔ 对任意 i j, a in f i j
  证明: by
  simp

@[to_dual]
-/
theorem mem_iSup₂_iff {f : forall i, κ i -> UpperSet α} : (a in ⨆ (i) (j), f i j) ↔ forall i j, a in f i j := by
  simp

@[to_dual]
/--
theorem `mem_iInf₂_iff` / 定理 `mem_iInf₂_iff`

English:
theorem mem_iInf₂_iff
  given: {f : forall i, κ i -> UpperSet α}
  statement: (a in ⨅ (i) (j), f i j) ↔ exists i j, a in f i j
  proof: by
  simp

@[to_dual (attr := simp, norm_cast)]

中文:
定理 mem_iInf₂_iff
  条件: {f : 对任意 i, κ i -> UpperSet α}
  结论: (a in ⨅ (i) (j), f i j) ↔ 存在 i j, a in f i j
  证明: by
  simp

@[to_dual (attr := simp, norm_cast)]
-/
theorem mem_iInf₂_iff {f : forall i, κ i -> UpperSet α} : (a in ⨅ (i) (j), f i j) ↔ exists i j, a in f i j := by
  simp

@[to_dual (attr := simp, norm_cast)]
/--
theorem `codisjoint_coe` / 定理 `codisjoint_coe`

English:
theorem codisjoint_coe
  statement: Codisjoint (s : Set α) t ↔ Disjoint s t
  proof: by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

中文:
定理 codisjoint_coe
  结论: Codisjoint (s : Set α) t ↔ Disjoint s t
  证明: by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

Depends on / 依赖: SetLike, SetLike.ext, _iff, codisjoint_iff, disjoint_iff
-/
theorem codisjoint_coe : Codisjoint (s : Set α) t ↔ Disjoint s t := by
  simp [disjoint_iff, codisjoint_iff, SetLike.ext'_iff]

/-! ### Complement -/

/-- The complement of an upper set as a lower set. -/
@[to_dual /-- The complement of a lower set as an upper set. -/]
/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: (s : UpperSet α)
  body: ⟨sᶜ, s.upper.compl⟩

@[to_dual (attr := simp)]

中文:
定义 compl
  签名: (s : UpperSet α)
  定义体: ⟨sᶜ, s.upper.compl⟩

@[to_dual (attr := simp)]

Depends on / 依赖: s.upper.compl
-/
def compl (s : UpperSet α) : LowerSet α :=
  ⟨sᶜ, s.upper.compl⟩

@[to_dual (attr := simp)]
/--
theorem `coe_compl` / 定理 `coe_compl`

English:
theorem coe_compl
  given: (s : UpperSet α)
  statement: (s.compl : Set α) = (↑s)ᶜ
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_compl
  条件: (s : UpperSet α)
  结论: (s.compl : Set α) = (↑s)ᶜ
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_compl (s : UpperSet α) : (s.compl : Set α) = (↑s)ᶜ :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `mem_compl_iff` / 定理 `mem_compl_iff`

English:
theorem mem_compl_iff
  statement: a in s.compl ↔ a ∉ s
  proof: Iff.rfl

@[to_dual (attr := simp)]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
UpperSet.ext compl_compl _

@[to_dual (attr := simp)]

中文:
定理 mem_compl_iff
  结论: a in s.compl ↔ a ∉ s
  证明: Iff.rfl

@[to_dual (attr := simp)]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
UpperSet.ext compl_compl _

@[to_dual (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem mem_compl_iff : a in s.compl ↔ a ∉ s :=
  Iff.rfl

@[to_dual (attr := simp)]
nonrec theorem compl_compl (s : UpperSet α) : s.compl.compl = s :=
UpperSet.ext compl_compl _

@[to_dual (attr := simp)]
/--
theorem `compl_le_compl` / 定理 `compl_le_compl`

English:
theorem compl_le_compl
  statement: s.compl <= t.compl ↔ s <= t
  proof: compl_subset_compl

@[to_dual (attr := simp)]

中文:
定理 compl_le_compl
  结论: s.compl <= t.compl ↔ s <= t
  证明: compl_subset_compl

@[to_dual (attr := simp)]

Depends on / 依赖: compl_subset_compl
-/
theorem compl_le_compl : s.compl <= t.compl ↔ s <= t :=
  compl_subset_compl

@[to_dual (attr := simp)]
/--
theorem `compl_sup` / 定理 `compl_sup`

English:
theorem compl_sup
  given: (s t : UpperSet α)
  statement: (s ⊔ t).compl = s.compl ⊔ t.compl
  proof: LowerSet.ext compl_inf

@[to_dual (attr := simp)]

中文:
定理 compl_sup
  条件: (s t : UpperSet α)
  结论: (s ⊔ t).compl = s.compl ⊔ t.compl
  证明: LowerSet.ext compl_inf

@[to_dual (attr := simp)]
-/
protected theorem compl_sup (s t : UpperSet α) : (s ⊔ t).compl = s.compl ⊔ t.compl :=
  LowerSet.ext compl_inf

@[to_dual (attr := simp)]
/--
theorem `compl_inf` / 定理 `compl_inf`

English:
theorem compl_inf
  given: (s t : UpperSet α)
  statement: (s ⊓ t).compl = s.compl ⊓ t.compl
  proof: LowerSet.ext compl_sup

@[to_dual (attr := simp)]

中文:
定理 compl_inf
  条件: (s t : UpperSet α)
  结论: (s ⊓ t).compl = s.compl ⊓ t.compl
  证明: LowerSet.ext compl_sup

@[to_dual (attr := simp)]
-/
protected theorem compl_inf (s t : UpperSet α) : (s ⊓ t).compl = s.compl ⊓ t.compl :=
  LowerSet.ext compl_sup

@[to_dual (attr := simp)]
/--
theorem `compl_top` / 定理 `compl_top`

English:
theorem compl_top
  statement: (⊤ : UpperSet α).compl = ⊤
  proof: LowerSet.ext compl_empty

@[to_dual (attr := simp)]

中文:
定理 compl_top
  结论: (⊤ : UpperSet α).compl = ⊤
  证明: LowerSet.ext compl_empty

@[to_dual (attr := simp)]
-/
protected theorem compl_top : (⊤ : UpperSet α).compl = ⊤ :=
  LowerSet.ext compl_empty

@[to_dual (attr := simp)]
/--
theorem `compl_bot` / 定理 `compl_bot`

English:
theorem compl_bot
  statement: (⊥ : UpperSet α).compl = ⊥
  proof: LowerSet.ext compl_univ

@[to_dual (attr := simp)]

中文:
定理 compl_bot
  结论: (⊥ : UpperSet α).compl = ⊥
  证明: LowerSet.ext compl_univ

@[to_dual (attr := simp)]
-/
protected theorem compl_bot : (⊥ : UpperSet α).compl = ⊥ :=
  LowerSet.ext compl_univ

@[to_dual (attr := simp)]
/--
theorem `compl_sSup` / 定理 `compl_sSup`

English:
theorem compl_sSup
  given: (S : Set (UpperSet α))
  statement: (sSup S).compl = ⨆ s in S, UpperSet.compl s
  proof: LowerSet.ext by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[to_dual (attr := simp)]

中文:
定理 compl_sSup
  条件: (S : Set (UpperSet α))
  结论: (sSup S).compl = ⨆ s in S, UpperSet.compl s
  证明: LowerSet.ext by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[to_dual (attr := simp)]
-/
protected theorem compl_sSup (S : Set (UpperSet α)) : (sSup S).compl = ⨆ s in S, UpperSet.compl s :=
LowerSet.ext by simp only [coe_compl, coe_sSup, compl_iInter₂, LowerSet.coe_iSup₂]

@[to_dual (attr := simp)]
/--
theorem `compl_sInf` / 定理 `compl_sInf`

English:
theorem compl_sInf
  given: (S : Set (UpperSet α))
  statement: (sInf S).compl = ⨅ s in S, UpperSet.compl s
  proof: LowerSet.ext by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[to_dual (attr := simp)]

中文:
定理 compl_sInf
  条件: (S : Set (UpperSet α))
  结论: (sInf S).compl = ⨅ s in S, UpperSet.compl s
  证明: LowerSet.ext by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[to_dual (attr := simp)]
-/
protected theorem compl_sInf (S : Set (UpperSet α)) : (sInf S).compl = ⨅ s in S, UpperSet.compl s :=
LowerSet.ext by simp only [coe_compl, coe_sInf, compl_iUnion₂, LowerSet.coe_iInf₂]

@[to_dual (attr := simp)]
/--
theorem `compl_iSup` / 定理 `compl_iSup`

English:
theorem compl_iSup
  given: (f : ι -> UpperSet α)
  statement: (⨆ i, f i).compl = ⨆ i, (f i).compl
  proof: LowerSet.ext by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[to_dual (attr := simp)]

中文:
定理 compl_iSup
  条件: (f : ι -> UpperSet α)
  结论: (⨆ i, f i).compl = ⨆ i, (f i).compl
  证明: LowerSet.ext by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[to_dual (attr := simp)]
-/
protected theorem compl_iSup (f : ι -> UpperSet α) : (⨆ i, f i).compl = ⨆ i, (f i).compl :=
LowerSet.ext by simp only [coe_compl, coe_iSup, compl_iInter, LowerSet.coe_iSup]

@[to_dual (attr := simp)]
/--
theorem `compl_iInf` / 定理 `compl_iInf`

English:
theorem compl_iInf
  given: (f : ι -> UpperSet α)
  statement: (⨅ i, f i).compl = ⨅ i, (f i).compl
  proof: LowerSet.ext by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

@[to_dual]

中文:
定理 compl_iInf
  条件: (f : ι -> UpperSet α)
  结论: (⨅ i, f i).compl = ⨅ i, (f i).compl
  证明: LowerSet.ext by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

@[to_dual]
-/
protected theorem compl_iInf (f : ι -> UpperSet α) : (⨅ i, f i).compl = ⨅ i, (f i).compl :=
LowerSet.ext by simp only [coe_compl, coe_iInf, compl_iUnion, LowerSet.coe_iInf]

@[to_dual]
/--
theorem `compl_iSup₂` / 定理 `compl_iSup₂`

English:
theorem compl_iSup₂
  given: (f : forall i, κ i -> UpperSet α)
  proof: by simp

@[to_dual]

中文:
定理 compl_iSup₂
  条件: (f : 对任意 i, κ i -> UpperSet α)
  证明: by simp

@[to_dual]
-/
theorem compl_iSup₂ (f : forall i, κ i -> UpperSet α) :
    (⨆ (i) (j), f i j).compl = ⨆ (i) (j), (f i j).compl := by simp

@[to_dual]
/--
theorem `compl_iInf₂` / 定理 `compl_iInf₂`

English:
theorem compl_iInf₂
  given: (f : forall i, κ i -> UpperSet α)
  proof: by simp

中文:
定理 compl_iInf₂
  条件: (f : 对任意 i, κ i -> UpperSet α)
  证明: by simp
-/
theorem compl_iInf₂ (f : forall i, κ i -> UpperSet α) :
    (⨅ (i) (j), f i j).compl = ⨅ (i) (j), (f i j).compl := by simp

/-- Upper sets are order-isomorphic to lower sets under complementation. -/
@[simps]
/--
Definition of `_root_.upperSetIsoLowerSet` / `_root_.upperSetIsoLowerSet` 的定义

English:
definition _root_.upperSetIsoLowerSet
  signature: : UpperSet α ≃o LowerSet α where
  body: UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

中文:
定义 _root_.upperSetIsoLowerSet
  签名: : UpperSet α ≃o LowerSet α where
  定义体: UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

Depends on / 依赖: UpperSet, UpperSet.compl
-/
def _root_.upperSetIsoLowerSet : UpperSet α ≃o LowerSet α where
  toFun := UpperSet.compl
  invFun := LowerSet.compl
  left_inv := UpperSet.compl_compl
  right_inv := LowerSet.compl_compl
  map_rel_iff' := UpperSet.compl_le_compl

end LE

section LinearOrder
variable [LinearOrder α]

@[to_dual none]
/--
Instance `total_le` / 实例 `total_le`

English:
instance total_le
  signature: : @Std.Total (UpperSet α) (· <= ·)
  body: ⟨fun s t => t.upper.total s.upper⟩

中文:
实例 total_le
  签名: : @Std.Total (UpperSet α) (· <= ·)
  定义体: ⟨fun s t => t.upper.total s.upper⟩

Depends on / 依赖: s.upper, t.upper.total
-/
instance total_le : @Std.Total (UpperSet α) (· <= ·) := ⟨fun s t => t.upper.total s.upper⟩

/--
Instance `instLinearOrder` / 实例 `instLinearOrder`

English:
instance instLinearOrder
  signature: : LinearOrder (UpperSet α)
  body: by
  classical exact Lattice.toLinearOrder _

中文:
实例 instLinearOrder
  签名: : LinearOrder (UpperSet α)
  定义体: by
  classical exact Lattice.toLinearOrder _

Depends on / 依赖: Lattice, Lattice.toLinearOrder, classical, toLinearOrder
-/
noncomputable instance instLinearOrder : LinearOrder (UpperSet α) := by
  classical exact Lattice.toLinearOrder _

/--
Instance `instCompleteLinearOrder` / 实例 `instCompleteLinearOrder`

English:
instance instCompleteLinearOrder
  signature: : CompleteLinearOrder (UpperSet α)
  body: { completelyDistribLattice, instLinearOrder with }

@[to_dual none]

中文:
实例 instCompleteLinearOrder
  签名: : CompleteLinearOrder (UpperSet α)
  定义体: { completelyDistribLattice, instLinearOrder with }

@[to_dual none]

Depends on / 依赖: completelyDistribLattice, instLinearOrder
-/
noncomputable instance instCompleteLinearOrder : CompleteLinearOrder (UpperSet α) :=
  { completelyDistribLattice, instLinearOrder with }

@[to_dual none]
/--
Instance `_root_.LowerSet.total_le` / 实例 `_root_.LowerSet.total_le`

English:
instance _root_.LowerSet.total_le
  signature: : @Std.Total (LowerSet α) (· <= ·)
  body: ⟨fun s t => s.lower.total t.lower⟩

@[to_dual existing]

中文:
实例 _root_.LowerSet.total_le
  签名: : @Std.Total (LowerSet α) (· <= ·)
  定义体: ⟨fun s t => s.lower.total t.lower⟩

@[to_dual existing]

Depends on / 依赖: s.lower.total, t.lower
-/
instance _root_.LowerSet.total_le : @Std.Total (LowerSet α) (· <= ·) :=
  ⟨fun s t => s.lower.total t.lower⟩

@[to_dual existing]
/--
Instance `_root_.LowerSet.instLinearOrder` / 实例 `_root_.LowerSet.instLinearOrder`

English:
instance _root_.LowerSet.instLinearOrder
  signature: : LinearOrder (LowerSet α)
  body: by
  classical exact Lattice.toLinearOrder _

@[to_dual existing]

中文:
实例 _root_.LowerSet.instLinearOrder
  签名: : LinearOrder (LowerSet α)
  定义体: by
  classical exact Lattice.toLinearOrder _

@[to_dual existing]

Depends on / 依赖: Lattice, Lattice.toLinearOrder, classical, toLinearOrder
-/
noncomputable instance _root_.LowerSet.instLinearOrder : LinearOrder (LowerSet α) := by
  classical exact Lattice.toLinearOrder _

@[to_dual existing]
/--
Instance `_root_.LowerSet.instCompleteLinearOrder` / 实例 `_root_.LowerSet.instCompleteLinearOrder`

English:
instance _root_.LowerSet.instCompleteLinearOrder
  signature: : CompleteLinearOrder (LowerSet α)
  body: { LowerSet.completelyDistribLattice, LowerSet.instLinearOrder with }

中文:
实例 _root_.LowerSet.instCompleteLinearOrder
  签名: : CompleteLinearOrder (LowerSet α)
  定义体: { LowerSet.completelyDistribLattice, LowerSet.instLinearOrder with }

Depends on / 依赖: LowerSet, LowerSet.completelyDistribLattice, LowerSet.instLinearOrder, completelyDistribLattice, instLinearOrder
-/
noncomputable instance _root_.LowerSet.instCompleteLinearOrder : CompleteLinearOrder (LowerSet α) :=
  { LowerSet.completelyDistribLattice, LowerSet.instLinearOrder with }

end LinearOrder

section Map

variable [Preorder α] [Preorder β] [Preorder γ]

variable {f : α ≃o β} {s t : UpperSet α} {a : α} {b : β}

/-- An order isomorphism of Preorders induces an order isomorphism of their upper sets. -/
@[to_dual
/-- An order isomorphism of Preorders induces an order isomorphism of their lower sets. -/]
/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α ≃o β)
  body: ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
left_inv _ := ext f.preimage_image _
right_inv _ := ext f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

中文:
定义 map
  签名: (f : α ≃o β)
  定义体: ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
left_inv _ := ext f.preimage_image _
right_inv _ := ext f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

Depends on / 依赖: s.upper.image
-/
def map (f : α ≃o β) : UpperSet α ≃o UpperSet β where
  toFun s := ⟨f '' s, s.upper.image f⟩
  invFun t := ⟨f ⁻¹' t, t.upper.preimage f.monotone⟩
left_inv _ := ext f.preimage_image _
right_inv _ := ext f.image_preimage _
  map_rel_iff' := image_subset_image_iff f.injective

-- `simps` could generate these theorems, but `to_dual` is not happy with those versions.
@[to_dual (attr := simp)]
/--
theorem `coe_map_apply` / 定理 `coe_map_apply`

English:
theorem coe_map_apply
  given: (f : α ≃o β) (s : UpperSet α)
  statement: map f s = f '' s
  proof: rfl
@[to_dual (attr := simp)]

中文:
定理 coe_map_apply
  条件: (f : α ≃o β) (s : UpperSet α)
  结论: map f s = f '' s
  证明: rfl
@[to_dual (attr := simp)]
-/
theorem coe_map_apply (f : α ≃o β) (s : UpperSet α) : map f s = f '' s := rfl
@[to_dual (attr := simp)]
/--
theorem `coe_map_symm_apply` / 定理 `coe_map_symm_apply`

English:
theorem coe_map_symm_apply
  given: (f : α ≃o β) (s : UpperSet β)
  statement: (map f).symm s = f ⁻¹' s
  proof: rfl

中文:
定理 coe_map_symm_apply
  条件: (f : α ≃o β) (s : UpperSet β)
  结论: (map f).symm s = f ⁻¹' s
  证明: rfl
-/
theorem coe_map_symm_apply (f : α ≃o β) (s : UpperSet β) : (map f).symm s = f ⁻¹' s := rfl

set_option backward.isDefEq.respectTransparency false in
@[to_dual (attr := simp)]
/--
theorem `symm_map` / 定理 `symm_map`

English:
theorem symm_map
  given: (f : α ≃o β)
  statement: (map f).symm = map f.symm
  proof: by
  ext; simp [map, OrderIso.symm_apply_eq]

@[to_dual (attr := simp)]

中文:
定理 symm_map
  条件: (f : α ≃o β)
  结论: (map f).symm = map f.symm
  证明: by
  ext; simp [map, OrderIso.symm_apply_eq]

@[to_dual (attr := simp)]

Depends on / 依赖: OrderIso, OrderIso.symm_apply_eq, symm_apply_eq
-/
theorem symm_map (f : α ≃o β) : (map f).symm = map f.symm := by
  ext; simp [map, OrderIso.symm_apply_eq]

@[to_dual (attr := simp)]
/--
theorem `mem_map` / 定理 `mem_map`

English:
theorem mem_map
  statement: b in map f s ↔ f.symm b in s
  proof: by
  rw [← f.symm_symm]; rw [← symm_map]; rw [f.symm_symm]
  rfl

@[to_dual (attr := simp)]

中文:
定理 mem_map
  结论: b in map f s ↔ f.symm b in s
  证明: by
  rw [← f.symm_symm]; rw [← symm_map]; rw [f.symm_symm]
  rfl

@[to_dual (attr := simp)]

Depends on / 依赖: f.symm_symm, symm_map, symm_symm
-/
theorem mem_map : b in map f s ↔ f.symm b in s := by
  rw [← f.symm_symm]; rw [← symm_map]; rw [f.symm_symm]
  rfl

@[to_dual (attr := simp)]
/--
theorem `map_refl` / 定理 `map_refl`

English:
theorem map_refl
  statement: map (OrderIso.refl α) = OrderIso.refl _
  proof: by
  ext
  simp

@[to_dual (attr := simp)]

中文:
定理 map_refl
  结论: map (OrderIso.refl α) = OrderIso.refl _
  证明: by
  ext
  simp

@[to_dual (attr := simp)]
-/
theorem map_refl : map (OrderIso.refl α) = OrderIso.refl _ := by
  ext
  simp

@[to_dual (attr := simp)]
/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (g : β ≃o γ) (f : α ≃o β)
  statement: map g (map f s) = map (f.trans g) s
  proof: by
  ext
  simp

中文:
定理 map_map
  条件: (g : β ≃o γ) (f : α ≃o β)
  结论: map g (map f s) = map (f.trans g) s
  证明: by
  ext
  simp
-/
theorem map_map (g : β ≃o γ) (f : α ≃o β) : map g (map f s) = map (f.trans g) s := by
  ext
  simp

variable (f s t)

@[to_dual (attr := norm_cast)]
/--
theorem `coe_map` / 定理 `coe_map`

English:
theorem coe_map
  statement: (map f s : Set β) = f '' s
  proof: rfl

@[to_dual (attr := simp)]

中文:
定理 coe_map
  结论: (map f s : Set β) = f '' s
  证明: rfl

@[to_dual (attr := simp)]
-/
theorem coe_map : (map f s : Set β) = f '' s :=
  rfl

@[to_dual (attr := simp)]
/--
theorem `compl_map` / 定理 `compl_map`

English:
theorem compl_map
  statement: (map f s).compl = LowerSet.map f s.compl
  proof: SetLike.coe_injective (Set.image_compl_eq f.bijective).symm

中文:
定理 compl_map
  结论: (map f s).compl = LowerSet.map f s.compl
  证明: SetLike.coe_injective (Set.image_compl_eq f.bijective).symm

Depends on / 依赖: Set.image_compl_eq, SetLike, SetLike.coe_injective, bijective, coe_injective, f.bijective, image_compl_eq
-/
theorem compl_map : (map f s).compl = LowerSet.map f s.compl :=
  SetLike.coe_injective (Set.image_compl_eq f.bijective).symm


end Map

end UpperSet
