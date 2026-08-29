/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.Embedding.Restriction

/-!
# Opposite categories of cochain complexes

We construct an equivalence of categories `CochainComplex.opEquivalence C`
between `(CochainComplex C ℤ)ᵒᵖ` and `CochainComplex Cᵒᵖ ℤ`, and we show
that two morphisms in `CochainComplex C ℤ` are homotopic iff they are
homotopic as morphisms in `CochainComplex Cᵒᵖ ℤ`.

-/

@[expose] public section

noncomputable section

open Opposite CategoryTheory Limits

variable (C : Type*) [Category* C]

namespace ComplexShape

/-- The embedding of the complex shape `up ℤ` in `down ℤ` given by `n ↦ -n`. -/
@[simps]
/--
Definition of `embeddingUpIntDownInt` / `embeddingUpIntDownInt` 的定义

English:
definition embeddingUpIntDownInt
  signature: : (up Int).Embedding (down Int) where
  body: -n
  injective_f _ _ := by simp
  rel := by simp

中文:
定义 embeddingUp整数Down整数
  签名: : (up 整数).嵌入 (down 整数) where
  定义体: -n
  injective_f _ _ := by simp
  rel := by simp
-/
def embeddingUpIntDownInt : (up Int).Embedding (down Int) where
  f n := -n
  injective_f _ _ := by simp
  rel := by simp

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: embeddingUpIntDownInt.IsRelIff
  body: by dsimp; lia

中文:
实例 :
  签名: embeddingUp整数Down整数.是RelIff
  定义体: by dsimp; lia
-/
instance : embeddingUpIntDownInt.IsRelIff where
  rel' := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/-- The embedding of the complex shape `down ℤ` in `up ℤ` given by `n ↦ -n`. -/
@[simps]
/--
Definition of `embeddingDownIntUpInt` / `embeddingDownIntUpInt` 的定义

English:
definition embeddingDownIntUpInt
  signature: : (down Int).Embedding (up Int) where
  body: -n
  injective_f _ _ := by simp
  rel := by dsimp; lia

中文:
定义 embeddingDown整数Up整数
  签名: : (down 整数).嵌入 (up 整数) where
  定义体: -n
  injective_f _ _ := by simp
  rel := by dsimp; lia
-/
def embeddingDownIntUpInt : (down Int).Embedding (up Int) where
  f n := -n
  injective_f _ _ := by simp
  rel := by dsimp; lia

set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: embeddingDownIntUpInt.IsRelIff
  body: by dsimp; lia

中文:
实例 :
  签名: embeddingDown整数Up整数.是RelIff
  定义体: by dsimp; lia
-/
instance : embeddingDownIntUpInt.IsRelIff where
  rel' := by dsimp; lia

end ComplexShape

namespace ChainComplex

variable [HasZeroMorphisms C]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
attribute [local simp] HomologicalComplex.XIsoOfEq in
/--
Definition of `cochainComplexEquivalence` / `cochainComplexEquivalence` 的定义

English:
definition cochainComplexEquivalence
  signature: :
  body: ComplexShape.embeddingUpIntDownInt.restrictionFunctor C
  inverse := ComplexShape.embeddingDownIntUpInt.restrictionFunctor C
  unitIso :=
    NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents
      (fun n => K.XIsoOfEq (by simp)))
  counitIso :=
    NatIso.ofComponents (fun K => H

中文:
定义 cochainComplexEquivalence
  签名: :
  定义体: ComplexShape.embeddingUpIntDownInt.restrictionFunctor C
  inverse := ComplexShape.embeddingDownIntUpInt.restrictionFunctor C
  unitIso :=
    NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents
      (fun n => K.XIsoOfEq (by simp)))
  counitIso :=
    NatIso.ofComponents (fun K => H

Depends on / 依赖: ComplexShape, ComplexShape.embeddingUpIntDownInt.restrictionFunctor, embeddingUpIntDownInt, restrictionFunctor
-/
def cochainComplexEquivalence :
    ChainComplex C Int ≌ CochainComplex C Int where
  functor := ComplexShape.embeddingUpIntDownInt.restrictionFunctor C
  inverse := ComplexShape.embeddingDownIntUpInt.restrictionFunctor C
  unitIso :=
    NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents
      (fun n => K.XIsoOfEq (by simp)))
  counitIso :=
    NatIso.ofComponents (fun K => HomologicalComplex.Hom.isoOfComponents
      (fun n => K.XIsoOfEq (by simp)))

end ChainComplex

namespace CochainComplex

/--
Definition of `opEquivalence` / `opEquivalence` 的定义

English:
definition opEquivalence
  signature: [HasZeroMorphisms C]
  body: (HomologicalComplex.opEquivalence C (.up Int)).trans
    (ChainComplex.cochainComplexEquivalence _)

中文:
定义 opEquivalence
  签名: [有ZeroMorphisms C]
  定义体: (HomologicalComplex.opEquivalence C (.up Int)).trans
    (ChainComplex.cochainComplexEquivalence _)

Depends on / 依赖: ChainComplex, ChainComplex.cochainComplexEquivalence, HomologicalComplex, HomologicalComplex.opEquivalence, cochainComplexEquivalence, opEquivalence
-/
def opEquivalence [HasZeroMorphisms C] :
    (CochainComplex C Int)ᵒᵖ ≌ CochainComplex Cᵒᵖ Int :=
  (HomologicalComplex.opEquivalence C (.up Int)).trans
    (ChainComplex.cochainComplexEquivalence _)

variable {C} [Preadditive C]

attribute [local simp] opEquivalence ChainComplex.cochainComplexEquivalence

section

variable {K L : CochainComplex C Int} {f g : K ⟶ L}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homotopyOp` / `homotopyOp` 的定义

English:
definition homotopyOp
  signature: (h : Homotopy f g)
  body: (h.hom (-q) (-p)).op
  zero p q hpq := by
    rw [h.zero]; rw [op_zero]
    dsimp at hpq ⊢
    lia
  comm n := by
    dsimp
    simp only [h.comm, op_add, add_left_inj]
    rw [add_comm]
    congr 1
    · rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      symm
      exact dNext_eq _ (i' := n + 1) (by

中文:
定义 homotopyOp
  签名: (h : 同伦 f g)
  定义体: (h.hom (-q) (-p)).op
  zero p q hpq := by
    rw [h.zero]; rw [op_zero]
    dsimp at hpq ⊢
    lia
  comm n := by
    dsimp
    simp only [h.comm, op_add, add_left_inj]
    rw [add_comm]
    congr 1
    · rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      symm
      exact dNext_eq _ (i' := n + 1) (by

Depends on / 依赖: h.hom
-/
def homotopyOp (h : Homotopy f g) :
    Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op) where
  hom p q := (h.hom (-q) (-p)).op
  zero p q hpq := by
    rw [h.zero]; rw [op_zero]
    dsimp at hpq ⊢
    lia
  comm n := by
    dsimp
    simp only [h.comm, op_add, add_left_inj]
    rw [add_comm]
    congr 1
    · rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      symm
      exact dNext_eq _ (i' := n + 1) (by simp)
    · rw [dNext_eq _ (i' := - (n - 1)) (by dsimp; lia)]
      symm
      exact prevD_eq _ (j' := n - 1) (by simp)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `homotopyOp_hom_eq` / 引理 `homotopyOp_hom_eq`

English:
lemma homotopyOp_hom_eq
  statement: (h : Homotopy f g)
  proof: by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyOp]

中文:
引理 homotopyOp_hom_eq
  结论: (h : 同伦 f g)
  证明: by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyOp]

Depends on / 依赖: K.XIsoOfEq, L.XIsoOfEq, XIsoOfEq, h.hom, hom.op, homotopyOp
-/
lemma homotopyOp_hom_eq (h : Homotopy f g)
    (p q p' q' : Int) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (homotopyOp h).hom p q =
      (L.XIsoOfEq (by dsimp; lia)).hom.op ≫ (h.hom q' p').op ≫
        (K.XIsoOfEq (by dsimp; lia)).hom.op := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyOp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Definition of `homotopyUnop` / `homotopyUnop` 的定义

English:
definition homotopyUnop
  signature: (h : Homotopy ((opEquivalence C).functor.map f.op)
  body: (K.XIsoOfEq (by simp)).hom ≫ (h.hom (-q) (-p)).unop ≫ (L.XIsoOfEq (by simp)).hom
  zero p q hpq := by
    rw [h.zero]; rw [unop_zero]; rw [zero_comp]; rw [comp_zero]
    dsimp at hpq ⊢
    lia
  comm n := Quiver.Hom.op_inj (by
    have H (p q p' q' : Int) (hp : p = p') (hq : q = q') :
      h.hom p 

中文:
定义 homotopyUnop
  签名: (h : 同伦 ((opEquivalence C).functor.map f.op)
  定义体: (K.XIsoOfEq (by simp)).hom ≫ (h.hom (-q) (-p)).unop ≫ (L.XIsoOfEq (by simp)).hom
  zero p q hpq := by
    rw [h.zero]; rw [unop_zero]; rw [zero_comp]; rw [comp_zero]
    dsimp at hpq ⊢
    lia
  comm n := Quiver.Hom.op_inj (by
    have H (p q p' q' : Int) (hp : p = p') (hq : q = q') :
      h.hom p 

Depends on / 依赖: K.XIsoOfEq, L.XIsoOfEq, XIsoOfEq, h.hom
-/
def homotopyUnop (h : Homotopy ((opEquivalence C).functor.map f.op)
    ((opEquivalence C).functor.map g.op)) :
    Homotopy f g where
  hom p q := (K.XIsoOfEq (by simp)).hom ≫ (h.hom (-q) (-p)).unop ≫ (L.XIsoOfEq (by simp)).hom
  zero p q hpq := by
    rw [h.zero]; rw [unop_zero]; rw [zero_comp]; rw [comp_zero]
    dsimp at hpq ⊢
    lia
  comm n := Quiver.Hom.op_inj (by
    have H (p q p' q' : Int) (hp : p = p') (hq : q = q') :
      h.hom p q = (L.XIsoOfEq (by simpa using hp.symm)).hom.op ≫ h.hom p' q' ≫
        (K.XIsoOfEq (by simpa)).hom.op := by
      subst hp hq
      simp
    obtain ⟨n, rfl⟩ : exists (m : Int), n = -m := ⟨-n , by simp⟩
    have := h.comm n
    dsimp at this
    rw [op_add]; rw [op_add]; rw [this]; rw [add_left_inj]; rw [add_comm]
    congr 1
    · refine (prevD_eq _ (j' := n - 1) (by dsimp; lia)).trans ?_
      rw [dNext_eq _ (i' := - (n - 1)) (by dsimp; lia)]
      dsimp
      simp [H (- -n) (- -(n - 1)) n (n - 1) (by lia) (by lia), ← op_comp_assoc]
    · refine (dNext_eq _ (i' := n + 1) (by dsimp)).trans ?_
      rw [prevD_eq _ (j' := - (n + 1)) (by simp)]
      dsimp
      simp [H (- -(n + 1)) (- -n) (n + 1) n (by simp) (by simp), ← op_comp_assoc, ← op_comp])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `homotopyUnop_hom_eq` / 引理 `homotopyUnop_hom_eq`

English:
lemma homotopyUnop_hom_eq
  proof: by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyUnop]

中文:
引理 homotopyUnop_hom_eq
  证明: by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyUnop]

Depends on / 依赖: K.XIsoOfEq, L.XIsoOfEq, XIsoOfEq, h.hom, homotopyUnop
-/
lemma homotopyUnop_hom_eq
    (h : Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op))
    (p q p' q' : Int) (hp : p + p' = 0 := by lia) (hq : q + q' = 0 := by lia) :
    (homotopyUnop h).hom p q =
      (K.XIsoOfEq (by dsimp; lia)).hom ≫ (h.hom q' p').unop ≫
        (L.XIsoOfEq (by dsimp; lia)).hom := by
  obtain rfl : p' = -p := by lia
  obtain rfl : q' = -q := by lia
  simp [homotopyUnop]

end

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Definition of `homotopyOpEquiv` / `homotopyOpEquiv` 的定义

English:
definition homotopyOpEquiv
  signature: {K L : CochainComplex C Int} {f g : K ⟶ L}
  body: homotopyOp h
  invFun h := homotopyUnop h
  left_inv h := by
    ext p q
    simp [homotopyUnop_hom_eq _ p q (-p) (-q),
      homotopyOp_hom_eq _ (-q) (-p) q p]
  right_inv h := by
    ext p q
    simp [homotopyOp_hom_eq _ p q (-p) (-q),
      homotopyUnop_hom_eq _ (-q) (-p) q p]

中文:
定义 homotopyOpEquiv
  签名: {K L : 上链复形 C 整数} {f g : K ⟶ L}
  定义体: homotopyOp h
  invFun h := homotopyUnop h
  left_inv h := by
    ext p q
    simp [homotopyUnop_hom_eq _ p q (-p) (-q),
      homotopyOp_hom_eq _ (-q) (-p) q p]
  right_inv h := by
    ext p q
    simp [homotopyOp_hom_eq _ p q (-p) (-q),
      homotopyUnop_hom_eq _ (-q) (-p) q p]

Depends on / 依赖: homotopyOp
-/
def homotopyOpEquiv {K L : CochainComplex C Int} {f g : K ⟶ L} :
    Homotopy f g ≃ Homotopy ((opEquivalence C).functor.map f.op)
      ((opEquivalence C).functor.map g.op) where
  toFun h := homotopyOp h
  invFun h := homotopyUnop h
  left_inv h := by
    ext p q
    simp [homotopyUnop_hom_eq _ p q (-p) (-q),
      homotopyOp_hom_eq _ (-q) (-p) q p]
  right_inv h := by
    ext p q
    simp [homotopyOp_hom_eq _ p q (-p) (-q),
      homotopyUnop_hom_eq _ (-q) (-p) q p]

set_option backward.isDefEq.respectTransparency.types false in
/--
lemma `exactAt_op` / 引理 `exactAt_op`

English:
lemma exactAt_op
  statement: {K : CochainComplex C Int} {n : Int} (hK : K.ExactAt n)
  proof: by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp)]; rw [← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK

中文:
引理 exactAt_op
  结论: {K : 上链复形 C 整数} {n : 整数} (hK : K.ExactAt n)
  证明: by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp)]; rw [← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK

Depends on / 依赖: ExactAt, HomologicalComplex, HomologicalComplex.exactAt_iff, ShortComplex, ShortComplex.exact_unop_iff, exactAt_iff, exact_unop_iff, functor, functor.obj, opEquivalence
-/
lemma exactAt_op {K : CochainComplex C Int} {n : Int} (hK : K.ExactAt n)
    (m : Int) (hm : n + m = 0 := by lia) :
    ((opEquivalence C).functor.obj (op K)).ExactAt m := by
  obtain rfl : n = -m := by lia
  rw [HomologicalComplex.exactAt_iff' _ (m - 1) m (m + 1) (by simp) (by simp)]; rw [← ShortComplex.exact_unop_iff]
  rwa [HomologicalComplex.exactAt_iff' _ (-(m + 1)) (-m) (-(m - 1)) (by grind [prev])
    (by grind [next])] at hK

/--
lemma `acyclic_op` / 引理 `acyclic_op`

English:
lemma acyclic_op
  given: {K : CochainComplex C Int} (hK : K.Acyclic)
  proof: fun n => exactAt_op (hK (-n)) n

中文:
引理 acyclic_op
  条件: {K : 上链复形 C 整数} (hK : K.非循环)
  证明: fun n => exactAt_op (hK (-n)) n

Depends on / 依赖: exactAt_op
-/
lemma acyclic_op {K : CochainComplex C Int} (hK : K.Acyclic) :
    ((opEquivalence C).functor.obj (op K)).Acyclic :=
  fun n => exactAt_op (hK (-n)) n

end CochainComplex
