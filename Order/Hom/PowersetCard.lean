/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.Data.Set.PowersetCard
public import Mathlib.Data.Finset.Sort
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Finite sets of an ordered type

This file defines the isomorphism between ordered embeddings into a linearly ordered type and
the finite sets of that type.

## Definitions

* `ofFinEmbEquiv` is the equivalence between `Fin n ↪o I` and `Set.powersetCard I n` when `I` is
  a linearly ordered type.

-/

@[expose] public section

open Finset Function Set

namespace Set.powersetCard

section order

variable {n : Nat} {I : Type*} [LinearOrder I]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `ofFinEmbEquiv` / `ofFinEmbEquiv` 的定义

English:
definition ofFinEmbEquiv
  signature: : (Fin n ↪o I) ≃ powersetCard I n where
  body: ofFinEmb n I f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by symm; apply Finset.orderEmbOfFin_unique'; simp
  right_inv s := by ext; simp

中文:
定义 ofFinEmbEquiv
  签名: : (Fin n ↪o I) ≃ powersetCard I n where
  定义体: ofFinEmb n I f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by symm; apply Finset.orderEmbOfFin_unique'; simp
  right_inv s := by ext; simp

Depends on / 依赖: f.toEmbedding, ofFinEmb, toEmbedding
-/
def ofFinEmbEquiv : (Fin n ↪o I) ≃ powersetCard I n where
  toFun f := ofFinEmb n I f.toEmbedding
  invFun s := Finset.orderEmbOfFin s.val s.prop
  left_inv f := by symm; apply Finset.orderEmbOfFin_unique'; simp
  right_inv s := by ext; simp

/--
lemma `ofFinEmbEquiv_apply` / 引理 `ofFinEmbEquiv_apply`

English:
lemma ofFinEmbEquiv_apply
  given: (f : Fin n ↪o I)
  proof: rfl

中文:
引理 ofFinEmbEquiv_apply
  条件: (f : Fin n ↪o I)
  证明: rfl
-/
lemma ofFinEmbEquiv_apply (f : Fin n ↪o I) :
    ofFinEmbEquiv f = ofFinEmb n I f.toEmbedding :=
  rfl

/--
lemma `ofFinEmbEquiv_symm_apply` / 引理 `ofFinEmbEquiv_symm_apply`

English:
lemma ofFinEmbEquiv_symm_apply
  given: (s : powersetCard I n)
  proof: rfl

@[simp]

中文:
引理 ofFinEmbEquiv_symm_apply
  条件: (s : powersetCard I n)
  证明: rfl

@[simp]
-/
lemma ofFinEmbEquiv_symm_apply (s : powersetCard I n) :
    ofFinEmbEquiv.symm s = Finset.orderEmbOfFin s.val s.prop := rfl

@[simp]
/--
lemma `mem_ofFinEmbEquiv_iff_mem_range` / 引理 `mem_ofFinEmbEquiv_iff_mem_range`

English:
lemma mem_ofFinEmbEquiv_iff_mem_range
  given: (f : Fin n ↪o I) (i : I)
  proof: by
  simp [ofFinEmbEquiv_apply]

中文:
引理 mem_ofFinEmbEquiv_iff_mem_range
  条件: (f : Fin n ↪o I) (i : I)
  证明: by
  simp [ofFinEmbEquiv_apply]

Depends on / 依赖: ofFinEmbEquiv_apply
-/
lemma mem_ofFinEmbEquiv_iff_mem_range (f : Fin n ↪o I) (i : I) :
    i in ofFinEmbEquiv f ↔ i in range f := by
  simp [ofFinEmbEquiv_apply]

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mem_range_ofFinEmbEquiv_symm_iff_mem` / 引理 `mem_range_ofFinEmbEquiv_symm_iff_mem`

English:
lemma mem_range_ofFinEmbEquiv_symm_iff_mem
  given: (s : powersetCard I n) (i : I)
  proof: by
  simp [ofFinEmbEquiv_symm_apply]

中文:
引理 mem_range_ofFinEmbEquiv_symm_iff_mem
  条件: (s : powersetCard I n) (i : I)
  证明: by
  simp [ofFinEmbEquiv_symm_apply]

Depends on / 依赖: ofFinEmbEquiv_symm_apply
-/
lemma mem_range_ofFinEmbEquiv_symm_iff_mem (s : powersetCard I n) (i : I) :
    i in range (ofFinEmbEquiv.symm s) ↔ i in s := by
  simp [ofFinEmbEquiv_symm_apply]

/--
Definition of `orderIsoOfFin` / `orderIsoOfFin` 的定义

English:
definition orderIsoOfFin
  signature: {n : Nat} {I : Type*} [LinearOrder I] (s : powersetCard I n)
  body: s.val.orderIsoOfFin s.prop

中文:
定义 orderIsoOfFin
  签名: {n : 自然数} {I : 类型} [LinearOrder I] (s : powersetCard I n)
  定义体: s.val.orderIsoOfFin s.prop
-/
@[simps!] def orderIsoOfFin {n : Nat} {I : Type*} [LinearOrder I] (s : powersetCard I n) :
    Fin n ≃o s.val :=
  s.val.orderIsoOfFin s.prop

/--
Definition of `permOfDisjoint` / `permOfDisjoint` 的定义

English:
definition permOfDisjoint
  signature: {m n : Nat} {I : Type*} [LinearOrder I]
  body: letI e₁ : Fin (m + n) ≃ Fin m oplus Fin n := finSumFinEquiv.symm
  letI e₂ : Fin m oplus Fin n ≃ s.val oplus t.val := (orderIsoOfFin s).sumCongr (orderIsoOfFin t)
  letI e₃ : s.val oplus t.val ≃ disjUnion h := Equiv.Finset.disjUnionEquiv _ _ h
  letI e₄ : disjUnion h ≃o Fin (m + n) := (orderIsoOfFin

中文:
定义 permOfDisjoint
  签名: {m n : 自然数} {I : 类型} [LinearOrder I]
  定义体: letI e₁ : Fin (m + n) ≃ Fin m oplus Fin n := finSumFinEquiv.symm
  letI e₂ : Fin m oplus Fin n ≃ s.val oplus t.val := (orderIsoOfFin s).sumCongr (orderIsoOfFin t)
  letI e₃ : s.val oplus t.val ≃ disjUnion h := Equiv.Finset.disjUnionEquiv _ _ h
  letI e₄ : disjUnion h ≃o Fin (m + n) := (orderIsoOfFin

Depends on / 依赖: Equiv.Finset.disjUnionEquiv, Finset, disjUnion, disjUnionEquiv, finSumFinEquiv, finSumFinEquiv.symm, orderIsoOfFin, s.val, sumCongr, t.val
-/
def permOfDisjoint {m n : Nat} {I : Type*} [LinearOrder I]
    {s : powersetCard I m} {t : powersetCard I n} (h : Disjoint s.val t.val) :
    Equiv.Perm (Fin (m + n)) :=
  letI e₁ : Fin (m + n) ≃ Fin m oplus Fin n := finSumFinEquiv.symm
  letI e₂ : Fin m oplus Fin n ≃ s.val oplus t.val := (orderIsoOfFin s).sumCongr (orderIsoOfFin t)
  letI e₃ : s.val oplus t.val ≃ disjUnion h := Equiv.Finset.disjUnionEquiv _ _ h
  letI e₄ : disjUnion h ≃o Fin (m + n) := (orderIsoOfFin (disjUnion h)).symm
e₁.trans e₂.trans e₃.trans e₄

end order

end Set.powersetCard
