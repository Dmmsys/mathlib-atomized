/-
Copyright (c) 2018 Kevin Buzzard, Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Buzzard, Patrick Massot
-/
-- This file is to a certain extent based on `quotient_module.lean` by Johannes Hölzl.
module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Data.Finite.Prod
public import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
# Deducing finiteness of a group.
-/

@[expose] public section

open Function QuotientGroup Subgroup
open scoped Pointwise


variable {F G H : Type*} [Group F] [Group G] [Group H] [Fintype F] [Fintype H]
variable (f : F ->* G) (g : G ->* H)

namespace Group

open scoped Classical in
/-- If `F` and `H` are finite such that `ker(G →* H) ≤ im(F →* G)`, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
/-- If `F` and `H` are finite such that `ker(G →+ H) ≤ im(F →+ G)`, then `G` is finite. -/]
/--
Definition of `fintypeOfKerLeRange` / `fintypeOfKerLeRange` 的定义

English:
definition fintypeOfKerLeRange
  signature: (h : g.ker <= f.range)
  body: @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
Fintype.ofInjective _ inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm

中文:
定义 fintypeOfKerLeRange
  签名: (h : g.ker <= f.range)
  定义体: @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
Fintype.ofInjective _ inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, Fintype.ofInjective, groupEquivQuotientProdSubgroup, groupEquivQuotientProdSubgroup.symm, inclusion_injective, instFintypeProd, kerLift_injective, ofEquiv, ofInjective
-/
noncomputable def fintypeOfKerLeRange (h : g.ker <= f.range) : Fintype G :=
  @Fintype.ofEquiv _ _
    (@instFintypeProd _ _ (Fintype.ofInjective _ <| kerLift_injective g) <|
Fintype.ofInjective _ inclusion_injective h)
    groupEquivQuotientProdSubgroup.symm

/-- If `F` and `H` are finite such that `ker(G →* H) = im(F →* G)`, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
/-- If `F` and `H` are finite such that `ker(G →+ H) = im(F →+ G)`, then `G` is finite. -/]
/--
Definition of `fintypeOfKerEqRange` / `fintypeOfKerEqRange` 的定义

English:
definition fintypeOfKerEqRange
  signature: (h : g.ker = f.range)
  body: fintypeOfKerLeRange _ _ h.le

中文:
定义 fintypeOfKerEqRange
  签名: (h : g.ker = f.range)
  定义体: fintypeOfKerLeRange _ _ h.le

Depends on / 依赖: fintypeOfKerLeRange, h.le
-/
noncomputable def fintypeOfKerEqRange (h : g.ker = f.range) : Fintype G :=
  fintypeOfKerLeRange _ _ h.le

/-- If `ker(G →* H)` and `H` are finite, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
  /-- If `ker(G →+ H)` and `H` are finite, then `G` is finite. -/]
/--
Definition of `fintypeOfKerOfCodom` / `fintypeOfKerOfCodom` 的定义

English:
definition fintypeOfKerOfCodom
  signature: [Fintype g.ker]
  body: fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩

中文:
定义 fintypeOfKerOfCodom
  签名: [有限类型 g.ker]
  定义体: fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩

Depends on / 依赖: fintypeOfKerLeRange, inclusion, le_top, toMonoidHom, toMonoidHom.comp, topEquiv
-/
noncomputable def fintypeOfKerOfCodom [Fintype g.ker] : Fintype G :=
  fintypeOfKerLeRange ((topEquiv : _ ≃* G).toMonoidHom.comp <| inclusion le_top) g fun x hx =>
    ⟨⟨x, hx⟩, rfl⟩

/-- If `F` and `coker(F →* G)` are finite, then `G` is finite. -/
@[to_additive (attr := instance_reducible)
  /-- If `F` and `coker(F →+ G)` are finite, then `G` is finite. -/]
/--
Definition of `fintypeOfDomOfCoker` / `fintypeOfDomOfCoker` 的定义

English:
definition fintypeOfDomOfCoker
  signature: [Normal f.range] [Fintype <| G ⧸ f.range]
  body: fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp

中文:
定义 fintypeOfDomOfCoker
  签名: [正规 f.range] [有限类型 <| G ⧸ f.range]
  定义体: fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp

Depends on / 依赖: eq_one_iff, f.range, fintypeOfKerLeRange
-/
noncomputable def fintypeOfDomOfCoker [Normal f.range] [Fintype <| G ⧸ f.range] : Fintype G :=
  fintypeOfKerLeRange _ (mk' f.range) fun x => (eq_one_iff x).mp

end Group

@[to_additive]
/--
lemma `finite_iff_subgroup_quotient` / 引理 `finite_iff_subgroup_quotient`

English:
lemma finite_iff_subgroup_quotient
  given: (H : Subgroup G)
  statement: Finite G ↔ Finite H ∧ Finite (G ⧸ H)
  proof: by
  rw [(groupEquivQuotientProdSubgroup (s := H)).finite_iff]; rw [Prod.finite_iff]; rw [and_comm]

@[to_additive]

中文:
引理 finite_iff_subgroup_quotient
  条件: (H : 子群 G)
  结论: 有限 G ↔ 有限 H ∧ 有限 (G ⧸ H)
  证明: by
  rw [(groupEquivQuotientProdSubgroup (s := H)).finite_iff]; rw [Prod.finite_iff]; rw [and_comm]

@[to_additive]

Depends on / 依赖: Prod.finite_iff, and_comm, finite_iff, groupEquivQuotientProdSubgroup
-/
lemma finite_iff_subgroup_quotient (H : Subgroup G) : Finite G ↔ Finite H ∧ Finite (G ⧸ H) := by
  rw [(groupEquivQuotientProdSubgroup (s := H)).finite_iff]; rw [Prod.finite_iff]; rw [and_comm]

@[to_additive]
/--
lemma `Finite.of_subgroup_quotient` / 引理 `Finite.of_subgroup_quotient`

English:
lemma Finite.of_subgroup_quotient
  given: (H : Subgroup G) [Finite H] [Finite (G ⧸ H)]
  statement: Finite G
  proof: by
  rw [finite_iff_subgroup_quotient]; constructor <;> assumption

中文:
引理 有限.of_subgroup_quotient
  条件: (H : 子群 G) [有限 H] [有限 (G ⧸ H)]
  结论: 有限 G
  证明: by
  rw [finite_iff_subgroup_quotient]; constructor <;> assumption

Depends on / 依赖: finite_iff_subgroup_quotient
-/
lemma Finite.of_subgroup_quotient (H : Subgroup G) [Finite H] [Finite (G ⧸ H)] : Finite G := by
  rw [finite_iff_subgroup_quotient]; constructor <;> assumption
