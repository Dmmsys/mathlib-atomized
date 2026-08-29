/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Aaron Anderson
-/
module

public import Mathlib.Data.Finsupp.Defs

/-!
# Pointwise order on finitely supported functions

This file lifts order structures on `M` to `ι →₀ M`.
-/

@[expose] public section

assert_not_exists CompleteLattice

noncomputable section

open Finset

namespace Finsupp
variable {ι M : Type*} [Zero M]

section LE
variable [LE M] {f g : ι ->₀ M}

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: : LE (ι ->₀ M) where le f g
  body: forall i, f i <= g i

中文:
实例 instLE
  签名: : LE (ι ->₀ M) where le f g
  定义体: forall i, f i <= g i
-/
instance instLE : LE (ι ->₀ M) where le f g := forall i, f i <= g i

/--
lemma `le_def` / 引理 `le_def`

English:
lemma le_def
  statement: f <= g ↔ forall i, f i <= g i
  proof: .rfl

中文:
引理 le_def
  结论: f <= g ↔ 对任意 i, f i <= g i
  证明: .rfl
-/
lemma le_def : f <= g ↔ forall i, f i <= g i := .rfl

/--
lemma `coe_le_coe` / 引理 `coe_le_coe`

English:
lemma coe_le_coe
  statement: ⇑f <= g ↔ f <= g
  proof: .rfl

中文:
引理 coe_le_coe
  结论: ⇑f <= g ↔ f <= g
  证明: .rfl
-/
@[simp, norm_cast] lemma coe_le_coe : ⇑f <= g ↔ f <= g := .rfl

/-- The order on `Finsupp`s over a partial order embeds into the order on functions -/
@[simps]
/--
Definition of `orderEmbeddingToFun` / `orderEmbeddingToFun` 的定义

English:
definition orderEmbeddingToFun
  signature: : (ι ->₀ M) ↪o (ι -> M) where
  body: f
  inj' := DFunLike.coe_injective
  map_rel_iff' := coe_le_coe

中文:
定义 orderEmbeddingToFun
  签名: : (ι ->₀ M) ↪o (ι -> M) where
  定义体: f
  inj' := DFunLike.coe_injective
  map_rel_iff' := coe_le_coe
-/
def orderEmbeddingToFun : (ι ->₀ M) ↪o (ι -> M) where
  toFun f := f
  inj' := DFunLike.coe_injective
  map_rel_iff' := coe_le_coe

/--
Definition of `orderIsoFunOnFinite` / `orderIsoFunOnFinite` 的定义

English:
definition orderIsoFunOnFinite
  signature: [Finite ι]
  body: equivFunOnFinite
  map_rel_iff' := Iff.rfl

中文:
定义 orderIsoFunOnFinite
  签名: [有限 ι]
  定义体: equivFunOnFinite
  map_rel_iff' := Iff.rfl

Depends on / 依赖: equivFunOnFinite
-/
def orderIsoFunOnFinite [Finite ι] : (ι ->₀ M) ≃o (ι -> M) where
  toEquiv := equivFunOnFinite
  map_rel_iff' := Iff.rfl

end LE

section Preorder
variable [Preorder M] {f g : ι ->₀ M} {i : ι} {a b : M}

/--
Instance `preorder` / 实例 `preorder`

English:
instance preorder
  signature: : Preorder (ι ->₀ M) where
  body: le_rfl
  le_trans _ _ _ hfg hgh i := (hfg i).trans (hgh i)

中文:
实例 preorder
  签名: : 预序 (ι ->₀ M) where
  定义体: le_rfl
  le_trans _ _ _ hfg hgh i := (hfg i).trans (hgh i)

Depends on / 依赖: le_rfl
-/
instance preorder : Preorder (ι ->₀ M) where
  le_refl _ _ := le_rfl
  le_trans _ _ _ hfg hgh i := (hfg i).trans (hgh i)

/--
lemma `lt_def` / 引理 `lt_def`

English:
lemma lt_def
  statement: f < g ↔ f <= g ∧ exists i, f i < g i
  proof: Pi.lt_def

中文:
引理 lt_def
  结论: f < g ↔ f <= g ∧ 存在 i, f i < g i
  证明: Pi.lt_def

Depends on / 依赖: Pi.lt_def, lt_def
-/
lemma lt_def : f < g ↔ f <= g ∧ exists i, f i < g i := Pi.lt_def
/--
lemma `coe_lt_coe` / 引理 `coe_lt_coe`

English:
lemma coe_lt_coe
  statement: ⇑f < g ↔ f < g
  proof: .rfl

中文:
引理 coe_lt_coe
  结论: ⇑f < g ↔ f < g
  证明: .rfl
-/
@[simp, norm_cast] lemma coe_lt_coe : ⇑f < g ↔ f < g := .rfl

/--
lemma `coe_mono` / 引理 `coe_mono`

English:
lemma coe_mono
  statement: Monotone (Finsupp.toFun : (ι ->₀ M) -> ι -> M)
  proof: fun _ _ => id

中文:
引理 coe_mono
  结论: 递增 (有限支撑.toFun : (ι ->₀ M) -> ι -> M)
  证明: fun _ _ => id
-/
lemma coe_mono : Monotone (Finsupp.toFun : (ι ->₀ M) -> ι -> M) := fun _ _ => id

/--
lemma `coe_strictMono` / 引理 `coe_strictMono`

English:
lemma coe_strictMono
  statement: Monotone (Finsupp.toFun : (ι ->₀ M) -> ι -> M)
  proof: fun _ _ => id

中文:
引理 coe_strictMono
  结论: 递增 (有限支撑.toFun : (ι ->₀ M) -> ι -> M)
  证明: fun _ _ => id
-/
lemma coe_strictMono : Monotone (Finsupp.toFun : (ι ->₀ M) -> ι -> M) := fun _ _ => id

end Preorder

/--
Instance `partialorder` / 实例 `partialorder`

English:
instance partialorder
  signature: [PartialOrder M]
  body: ext fun i => (hfg i).antisymm (hgf i)

中文:
实例 partialorder
  签名: [偏序 M]
  定义体: ext fun i => (hfg i).antisymm (hgf i)

Depends on / 依赖: antisymm
-/
instance partialorder [PartialOrder M] : PartialOrder (ι ->₀ M) where
  le_antisymm _f _g hfg hgf := ext fun i => (hfg i).antisymm (hgf i)

section SemilatticeInf
variable [SemilatticeInf M]

/--
Instance `semilatticeInf` / 实例 `semilatticeInf`

English:
instance semilatticeInf
  signature: : SemilatticeInf (ι ->₀ M) where
  body: zipWith (· ⊓ ·) (inf_idem _)
  inf_le_left _f _g _i := inf_le_left
  inf_le_right _f _g _i := inf_le_right
  le_inf _f _g _i h1 h2 s := le_inf (h1 s) (h2 s)

中文:
实例 semilatticeInf
  签名: : SemilatticeInf (ι ->₀ M) where
  定义体: zipWith (· ⊓ ·) (inf_idem _)
  inf_le_left _f _g _i := inf_le_left
  inf_le_right _f _g _i := inf_le_right
  le_inf _f _g _i h1 h2 s := le_inf (h1 s) (h2 s)

Depends on / 依赖: inf_idem, zipWith
-/
instance semilatticeInf : SemilatticeInf (ι ->₀ M) where
  inf := zipWith (· ⊓ ·) (inf_idem _)
  inf_le_left _f _g _i := inf_le_left
  inf_le_right _f _g _i := inf_le_right
  le_inf _f _g _i h1 h2 s := le_inf (h1 s) (h2 s)

/--
lemma `inf_apply` / 引理 `inf_apply`

English:
lemma inf_apply
  given: (f g : ι ->₀ M) (i : ι)
  statement: (f ⊓ g) i = f i ⊓ g i
  proof: rfl

中文:
引理 inf_apply
  条件: (f g : ι ->₀ M) (i : ι)
  结论: (f ⊓ g) i = f i ⊓ g i
  证明: rfl
-/
@[simp] lemma inf_apply (f g : ι ->₀ M) (i : ι) : (f ⊓ g) i = f i ⊓ g i := rfl

end SemilatticeInf

section SemilatticeSup
variable [SemilatticeSup M]

/--
Instance `semilatticeSup` / 实例 `semilatticeSup`

English:
instance semilatticeSup
  signature: : SemilatticeSup (ι ->₀ M) where
  body: zipWith (· ⊔ ·) (sup_idem _)
  le_sup_left _f _g _i := le_sup_left
  le_sup_right _f _g _i := le_sup_right
  sup_le _f _g _h hf hg i := sup_le (hf i) (hg i)

@[simp]

中文:
实例 semilatticeSup
  签名: : SemilatticeSup (ι ->₀ M) where
  定义体: zipWith (· ⊔ ·) (sup_idem _)
  le_sup_left _f _g _i := le_sup_left
  le_sup_right _f _g _i := le_sup_right
  sup_le _f _g _h hf hg i := sup_le (hf i) (hg i)

@[simp]

Depends on / 依赖: sup_idem, zipWith
-/
instance semilatticeSup : SemilatticeSup (ι ->₀ M) where
  sup := zipWith (· ⊔ ·) (sup_idem _)
  le_sup_left _f _g _i := le_sup_left
  le_sup_right _f _g _i := le_sup_right
  sup_le _f _g _h hf hg i := sup_le (hf i) (hg i)

@[simp]
/--
lemma `sup_apply` / 引理 `sup_apply`

English:
lemma sup_apply
  given: (f g : ι ->₀ M) (i : ι)
  statement: (f ⊔ g) i = f i ⊔ g i
  proof: rfl

中文:
引理 sup_apply
  条件: (f g : ι ->₀ M) (i : ι)
  结论: (f ⊔ g) i = f i ⊔ g i
  证明: rfl
-/
lemma sup_apply (f g : ι ->₀ M) (i : ι) : (f ⊔ g) i = f i ⊔ g i := rfl

end SemilatticeSup

section Lattice
variable [Lattice M] (f g : ι ->₀ M)

/--
Instance `lattice` / 实例 `lattice`

English:
instance lattice
  signature: : Lattice (ι ->₀ M) where
  body: Finsupp.semilatticeInf
  __ := Finsupp.semilatticeSup

中文:
实例 lattice
  签名: : 格 (ι ->₀ M) where
  定义体: Finsupp.semilatticeInf
  __ := Finsupp.semilatticeSup

Depends on / 依赖: Finsupp, Finsupp.semilatticeInf, semilatticeInf, toLocalizationMap
-/
instance lattice : Lattice (ι ->₀ M) where
  __ := Finsupp.semilatticeInf
  __ := Finsupp.semilatticeSup

variable [DecidableEq ι]

/--
lemma `support_inf_union_support_sup` / 引理 `support_inf_union_support_sup`

English:
lemma support_inf_union_support_sup
  statement: (f ⊓ g).support union (f ⊔ g).support = f.support union g.support
  proof: coe_injective compl_injective by ext; simp [inf_eq_and_sup_eq_iff]

中文:
引理 support_inf_union_support_sup
  结论: (f ⊓ g).support union (f ⊔ g).support = f.support union g.support
  证明: coe_injective compl_injective by ext; simp [inf_eq_and_sup_eq_iff]

Depends on / 依赖: _sec, coe_injective, compl_injective, inf_eq_and_sup_eq_iff, toLocalizationMap
-/
lemma support_inf_union_support_sup : (f ⊓ g).support union (f ⊔ g).support = f.support union g.support :=
coe_injective compl_injective by ext; simp [inf_eq_and_sup_eq_iff]

/--
lemma `support_sup_union_support_inf` / 引理 `support_sup_union_support_inf`

English:
lemma support_sup_union_support_inf
  statement: (f ⊔ g).support union (f ⊓ g).support = f.support union g.support
  proof: (union_comm _ _).trans support_inf_union_support_sup _ _

中文:
引理 support_sup_union_support_inf
  结论: (f ⊔ g).support union (f ⊓ g).support = f.support union g.support
  证明: (union_comm _ _).trans support_inf_union_support_sup _ _

Depends on / 依赖: _mul, support_inf_union_support_sup, toLocalizationMap, union_comm
-/
lemma support_sup_union_support_inf : (f ⊔ g).support union (f ⊓ g).support = f.support union g.support :=
(union_comm _ _).trans support_inf_union_support_sup _ _

end Lattice
end Finsupp
