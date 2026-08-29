/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.Polynomial.GroupRingAction
public import Mathlib.Algebra.Ring.Action.Field
public import Mathlib.Algebra.Ring.Action.Invariant
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.RingTheory.Polynomial.Subring

/-!
# Fixed field under a group action.

This is the basis of the Fundamental Theorem of Galois Theory.
Given a (finite) group `G` that acts on a field `F`, we define `FixedPoints.subfield G F`,
the subfield consisting of elements of `F` fixed by every element of `G`.

This subfield is then normal and separable, and in addition if `G` acts faithfully on `F`
then `finrank (FixedPoints.subfield G F) F = Fintype.card G`.

## Main Definitions

- `FixedPoints.subfield G F`, the subfield consisting of elements of `F` fixed by every
  element of `G`, where `G` is a group that acts on `F`.
-/

@[expose] public section


noncomputable section

open MulAction Finset Module

universe u v w

variable {M : Type u} [Monoid M]
variable (G : Type u) [Group G]
variable (K : Type*) (F : Type v) [Field F] [MulSemiringAction M F] [MulSemiringAction G F] (m : M)

/--
Definition of `FixedBy.subfield` / `FixedBy.subfield` 的定义

English:
definition FixedBy.subfield
  signature: : Subfield F where
  body: fixedBy F m
  zero_mem' := smul_zero m
add_mem' hx hy := (smul_add m _ _).trans congr_arg₂ _ hx hy
neg_mem' hx := (smul_neg m _).trans congr_arg _ hx
  one_mem' := smul_one m
mul_mem' hx hy := (smul_mul' m _ _).trans congr_arg₂ _ hx hy
inv_mem' x hx := (smul_inv'' m x).trans congr_arg _ hx

@[simp]

中文:
定义 FixedBy.subfield
  签名: : 子域 F where
  定义体: fixedBy F m
  zero_mem' := smul_zero m
add_mem' hx hy := (smul_add m _ _).trans congr_arg₂ _ hx hy
neg_mem' hx := (smul_neg m _).trans congr_arg _ hx
  one_mem' := smul_one m
mul_mem' hx hy := (smul_mul' m _ _).trans congr_arg₂ _ hx hy
inv_mem' x hx := (smul_inv'' m x).trans congr_arg _ hx

@[simp]

Depends on / 依赖: fixedBy
-/
def FixedBy.subfield : Subfield F where
  carrier := fixedBy F m
  zero_mem' := smul_zero m
add_mem' hx hy := (smul_add m _ _).trans congr_arg₂ _ hx hy
neg_mem' hx := (smul_neg m _).trans congr_arg _ hx
  one_mem' := smul_one m
mul_mem' hx hy := (smul_mul' m _ _).trans congr_arg₂ _ hx hy
inv_mem' x hx := (smul_inv'' m x).trans congr_arg _ hx

@[simp]
/--
theorem `FixedBy.subfield_mem_iff` / 定理 `FixedBy.subfield_mem_iff`

English:
theorem FixedBy.subfield_mem_iff
  given: (x : F)
  proof: Iff.rfl

中文:
定理 FixedBy.subfield_mem_iff
  条件: (x : F)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem FixedBy.subfield_mem_iff (x : F) :
    x in FixedBy.subfield F m ↔ m • x = x := Iff.rfl

variable [Field K] [Algebra K F] [SMulCommClass M K F]

/--
Definition of `FixedBy.intermediateField` / `FixedBy.intermediateField` 的定义

English:
definition FixedBy.intermediateField
  signature: : IntermediateField K F where
  body: FixedBy.subfield F m
  algebraMap_mem' x := smul_algebraMap m x

@[simp]

中文:
定义 FixedBy.intermediateField
  签名: : 中间域 K F where
  定义体: FixedBy.subfield F m
  algebraMap_mem' x := smul_algebraMap m x

@[simp]

Depends on / 依赖: FixedBy, FixedBy.subfield, subfield
-/
def FixedBy.intermediateField : IntermediateField K F where
  __ := FixedBy.subfield F m
  algebraMap_mem' x := smul_algebraMap m x

@[simp]
/--
theorem `FixedBy.intermediateField_mem_iff` / 定理 `FixedBy.intermediateField_mem_iff`

English:
theorem FixedBy.intermediateField_mem_iff
  given: (x : F)
  proof: Iff.rfl

中文:
定理 FixedBy.intermediateField_mem_iff
  条件: (x : F)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem FixedBy.intermediateField_mem_iff (x : F) :
    x in FixedBy.intermediateField K F m ↔ m • x = x := Iff.rfl

section InvariantSubfields

variable (M) {F}

/--
Definition of `IsInvariantSubfield` / `IsInvariantSubfield` 的定义

English:
class IsInvariantSubfield
  parameters: (S : Subfield F)
  axioms and operations (1):
    - smul_mem : forall (m : M) {x : F}, x in S -> m • x in S

中文:
类 是InvariantSubfield
  参数: (S : 子域 F)
  公理与运算 (1 个):
    - smul_mem : 对任意 (m : M) {x : F}, x in S -> m • x in S
-/
class IsInvariantSubfield (S : Subfield F) : Prop where
  smul_mem : forall (m : M) {x : F}, x in S -> m • x in S

variable (S : Subfield F)

/--
Instance `IsInvariantSubfield.toMulSemiringAction` / 实例 `IsInvariantSubfield.toMulSemiringAction`

English:
instance IsInvariantSubfield.toMulSemiringAction
  signature: [IsInvariantSubfield M S]
  body: ⟨m • x.1, IsInvariantSubfield.smul_mem m x.2⟩
one_smul s := Subtype.ext one_smul M s.1
mul_smul m₁ m₂ s := Subtype.ext mul_smul m₁ m₂ s.1
smul_add m s₁ s₂ := Subtype.ext smul_add m s₁.1 s₂.1
smul_zero m := Subtype.ext smul_zero m
smul_one m := Subtype.ext smul_one m
smul_mul m s₁ s₂ := Subtype.ext s

中文:
实例 是InvariantSubfield.toMulSemiringAction
  签名: [是InvariantSubfield M S]
  定义体: ⟨m • x.1, IsInvariantSubfield.smul_mem m x.2⟩
one_smul s := Subtype.ext one_smul M s.1
mul_smul m₁ m₂ s := Subtype.ext mul_smul m₁ m₂ s.1
smul_add m s₁ s₂ := Subtype.ext smul_add m s₁.1 s₂.1
smul_zero m := Subtype.ext smul_zero m
smul_one m := Subtype.ext smul_one m
smul_mul m s₁ s₂ := Subtype.ext s

Depends on / 依赖: IsInvariantSubfield, IsInvariantSubfield.smul_mem, smul_mem
-/
instance IsInvariantSubfield.toMulSemiringAction [IsInvariantSubfield M S] :
    MulSemiringAction M S where
  smul m x := ⟨m • x.1, IsInvariantSubfield.smul_mem m x.2⟩
one_smul s := Subtype.ext one_smul M s.1
mul_smul m₁ m₂ s := Subtype.ext mul_smul m₁ m₂ s.1
smul_add m s₁ s₂ := Subtype.ext smul_add m s₁.1 s₂.1
smul_zero m := Subtype.ext smul_zero m
smul_one m := Subtype.ext smul_one m
smul_mul m s₁ s₂ := Subtype.ext smul_mul' m s₁.1 s₂.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsInvariantSubfield
  signature: M S] : IsInvariantSubring M S.toSubring where
  body: IsInvariantSubfield.smul_mem

中文:
实例 [是InvariantSubfield
  签名: M S] : 是不变子环 M S.toSubring where
  定义体: IsInvariantSubfield.smul_mem

Depends on / 依赖: IsInvariantSubfield, IsInvariantSubfield.smul_mem, smul_mem
-/
instance [IsInvariantSubfield M S] : IsInvariantSubring M S.toSubring where
  smul_mem := IsInvariantSubfield.smul_mem

end InvariantSubfields

namespace FixedPoints

variable (M)

set_option backward.isDefEq.respectTransparency.types false in
-- we use `Subfield.copy` so that the underlying set is `fixedPoints M F`
/--
Definition of `subfield` / `subfield` 的定义

English:
definition subfield
  signature: : Subfield F
  body: Subfield.copy (⨅ m : M, FixedBy.subfield F m) (fixedPoints M F)
    (by ext; simp [FixedBy.subfield])

中文:
定义 subfield
  签名: : 子域 F
  定义体: Subfield.copy (⨅ m : M, FixedBy.subfield F m) (fixedPoints M F)
    (by ext; simp [FixedBy.subfield])

Depends on / 依赖: FixedBy, FixedBy.subfield, Subfield, Subfield.copy, fixedPoints, subfield
-/
def subfield : Subfield F :=
  Subfield.copy (⨅ m : M, FixedBy.subfield F m) (fixedPoints M F)
    (by ext; simp [FixedBy.subfield])

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsInvariantSubfield M (FixedPoints.subfield M F)
  body: by rw [hx, hx]

中文:
实例 :
  签名: 是InvariantSubfield M (FixedPoints.subfield M F)
  定义体: by rw [hx, hx]
-/
instance : IsInvariantSubfield M (FixedPoints.subfield M F) where
  smul_mem g x hx g' := by rw [hx, hx]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMulCommClass M (FixedPoints.subfield M F) F
  body: show m • (↑f * f') = f * m • f' by rw [smul_mul', f.prop m]

中文:
实例 :
  签名: 标量交换类 M (FixedPoints.subfield M F) F
  定义体: show m • (↑f * f') = f * m • f' by rw [smul_mul', f.prop m]

Depends on / 依赖: f.prop, smul_mul
-/
instance : SMulCommClass M (FixedPoints.subfield M F) F where
  smul_comm m f f' := show m • (↑f * f') = f * m • f' by rw [smul_mul', f.prop m]

/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: : SMulCommClass (FixedPoints.subfield M F) M F
  body: SMulCommClass.symm _ _ _

@[simp]

中文:
实例 smulCommClass'
  签名: : 标量交换类 (FixedPoints.subfield M F) M F
  定义体: SMulCommClass.symm _ _ _

@[simp]

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass' : SMulCommClass (FixedPoints.subfield M F) M F :=
  SMulCommClass.symm _ _ _

@[simp]
/--
theorem `smul` / 定理 `smul`

English:
theorem smul
  given: (m : M) (x : FixedPoints.subfield M F)
  statement: m • x = x
  proof: Subtype.ext x.2 m

中文:
定理 smul
  条件: (m : M) (x : FixedPoints.subfield M F)
  结论: m • x = x
  证明: Subtype.ext x.2 m

Depends on / 依赖: Subtype, Subtype.ext
-/
theorem smul (m : M) (x : FixedPoints.subfield M F) : m • x = x :=
Subtype.ext x.2 m

-- Why is this so slow?
@[simp]
/--
theorem `smul_polynomial` / 定理 `smul_polynomial`

English:
theorem smul_polynomial
  given: (m : M) (p : Polynomial (FixedPoints.subfield M F))
  statement: m • p = p
  proof: Polynomial.induction_on p (fun x => by rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by rw [smul_add, ihp, ihq]) fun n x _ => by
    rw [smul_mul']; rw [Polynomial.smul_C]; rw [smul]; rw [smul_pow']; rw [Polynomial.smul_X]

中文:
定理 smul_polynomial
  条件: (m : M) (p : 多项式 (FixedPoints.subfield M F))
  结论: m • p = p
  证明: Polynomial.induction_on p (fun x => by rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by rw [smul_add, ihp, ihq]) fun n x _ => by
    rw [smul_mul']; rw [Polynomial.smul_C]; rw [smul]; rw [smul_pow']; rw [Polynomial.smul_X]

Depends on / 依赖: Polynomial, Polynomial.induction_on, Polynomial.smul_C, Polynomial.smul_X, induction_on, smul_C, smul_X, smul_add, smul_mul, smul_pow
-/
theorem smul_polynomial (m : M) (p : Polynomial (FixedPoints.subfield M F)) : m • p = p :=
  Polynomial.induction_on p (fun x => by rw [Polynomial.smul_C, smul])
    (fun p q ihp ihq => by rw [smul_add, ihp, ihq]) fun n x _ => by
    rw [smul_mul']; rw [Polynomial.smul_C]; rw [smul]; rw [smul_pow']; rw [Polynomial.smul_X]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Algebra (FixedPoints.subfield M F) F
  body: by infer_instance

中文:
实例 :
  签名: 代数 (FixedPoints.subfield M F) F
  定义体: by infer_instance

Depends on / 依赖: infer_instance
-/
instance : Algebra (FixedPoints.subfield M F) F := by infer_instance

/--
theorem `coe_algebraMap` / 定理 `coe_algebraMap`

English:
theorem coe_algebraMap
  proof: rfl

中文:
定理 coe_algebraMap
  证明: rfl
-/
theorem coe_algebraMap :
    algebraMap (FixedPoints.subfield M F) F = Subfield.subtype (FixedPoints.subfield M F) :=
  rfl

/--
theorem `linearIndependent_smul_of_linearIndependent` / 定理 `linearIndependent_smul_of_linearIndependent`

English:
theorem linearIndependent_smul_of_linearIndependent
  given: {s : Finset F}
  proof: by
  classical
  have : IsEmpty ((∅ : Finset F) : Set F) := by simp
  refine Finset.induction_on s (fun _ => linearIndependent_empty_type) fun a s has ih hs => ?_
  rw [coe_insert] at hs ⊢
  rw [linearIndepOn_insert (mt mem_coe.1 has)] at hs
  rw [linearIndepOn_insert (mt mem_coe.1 has)]; refine ⟨ih

中文:
定理 linearIndependent_smul_of_linearIndependent
  条件: {s : 有限集 F}
  证明: by
  classical
  have : IsEmpty ((∅ : Finset F) : Set F) := by simp
  refine Finset.induction_on s (fun _ => linearIndependent_empty_type) fun a s has ih hs => ?_
  rw [coe_insert] at hs ⊢
  rw [linearIndepOn_insert (mt mem_coe.1 has)] at hs
  rw [linearIndepOn_insert (mt mem_coe.1 has)]; refine ⟨ih

Depends on / 依赖: Finset, Finset.induction_on, Finsupp, Finsupp.linearCombination_apply_of_mem_supported, Finsupp.mem_span_image_iff_linearCombination, FixedPoin, IsEmpty, classical, coe_insert, induction_on, linearCombination_apply_of_mem_supported, linearIndepOn_insert, linearIndependent_empty_type, mem_coe, mem_span_image_iff_linearCombination
-/
theorem linearIndependent_smul_of_linearIndependent {s : Finset F} :
    (LinearIndepOn (FixedPoints.subfield G F) id (s : Set F)) ->
      LinearIndepOn F (MulAction.toFun G F) s := by
  classical
  have : IsEmpty ((∅ : Finset F) : Set F) := by simp
  refine Finset.induction_on s (fun _ => linearIndependent_empty_type) fun a s has ih hs => ?_
  rw [coe_insert] at hs ⊢
  rw [linearIndepOn_insert (mt mem_coe.1 has)] at hs
  rw [linearIndepOn_insert (mt mem_coe.1 has)]; refine ⟨ih hs.1, fun ha => ?_⟩
  rw [Finsupp.mem_span_image_iff_linearCombination] at ha; rcases ha with ⟨l, hl, hla⟩
  rw [Finsupp.linearCombination_apply_of_mem_supported F hl] at hla
  suffices forall i in s, l i in FixedPoints.subfield G F by
    replace hla := (sum_apply _ _ fun i => l i • toFun G F i).symm.trans (congr_fun hla 1)
    simp_rw [Pi.smul_apply, toFun_apply, one_smul] at hla
    refine hs.2 (hla ▸ Submodule.sum_mem _ fun c hcs => ?_)
    change (⟨l c, this c hcs⟩ : FixedPoints.subfield G F) • c in _
exact Submodule.smul_mem _ _ Submodule.subset_span by simpa
  intro i his g
  refine
    eq_of_sub_eq_zero
      (linearIndependent_iff'.1 (ih hs.1) s.attach (fun i => g • l i - l i) ?_ ⟨i, his⟩
          (mem_attach _ _) :
        _)
  refine (sum_attach s fun i => (g • l i - l i) • MulAction.toFun G F i).trans ?_
  ext g'
  conv_lhs =>
    rw [Finset.sum_apply]
    congr
    · skip
    · ext
      rw [Pi.smul_apply]; rw [sub_smul]; rw [smul_eq_mul]
  rw [sum_sub_distrib]; rw [Pi.zero_apply]; rw [sub_eq_zero]
  conv_lhs =>
    congr
    · skip
    · ext x
      rw [toFun_apply]; rw [← mul_inv_cancel_left g g']; rw [mul_smul]; rw [← smul_mul']; rw [← toFun_apply _ x]
  change
    (∑ x in s, g • (fun y => l y • MulAction.toFun G F y) x (g⁻¹ * g')) =
      ∑ x in s, (fun y => l y • MulAction.toFun G F y) x g'
  rw [← smul_sum]; rw [← sum_apply _ _ fun y => l y • toFun G F y]; rw [←
    sum_apply _ _ fun y => l y • toFun G F y]
  rw [hla]; rw [toFun_apply]; rw [toFun_apply]; rw [smul_smul]; rw [mul_inv_cancel_left]

section Fintype

variable [Fintype G] (x : F)

/--
Definition of `minpoly` / `minpoly` 的定义

English:
definition minpoly
  signature: : Polynomial (FixedPoints.subfield G F)
  body: (prodXSubSMul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
    hn.symm ▸ prodXSubSMul.coeff G F x g n

中文:
定义 minpoly
  签名: : 多项式 (FixedPoints.subfield G F)
  定义体: (prodXSubSMul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
    hn.symm ▸ prodXSubSMul.coeff G F x g n

Depends on / 依赖: FixedPoints, FixedPoints.subfield, Polynomial, Polynomial.mem_coeffs_iff, hn.symm, mem_coeffs_iff, prodXSubSMul, prodXSubSMul.coeff, subfield, toSubring
-/
def minpoly : Polynomial (FixedPoints.subfield G F) :=
  (prodXSubSMul G F x).toSubring (FixedPoints.subfield G F).toSubring fun _ hc g =>
    let ⟨n, _, hn⟩ := Polynomial.mem_coeffs_iff.1 hc
    hn.symm ▸ prodXSubSMul.coeff G F x g n

namespace minpoly

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `monic` / 定理 `monic`

English:
theorem monic
  statement: (minpoly G F x).Monic
  proof: by
  simp only [minpoly]
  rw [Polynomial.monic_toSubring]
  exact prodXSubSMul.monic G F x

中文:
定理 monic
  结论: (minpoly G F x).Monic
  证明: by
  simp only [minpoly]
  rw [Polynomial.monic_toSubring]
  exact prodXSubSMul.monic G F x

Depends on / 依赖: Polynomial, Polynomial.monic_toSubring, minpoly, monic_toSubring, prodXSubSMul, prodXSubSMul.monic
-/
theorem monic : (minpoly G F x).Monic := by
  simp only [minpoly]
  rw [Polynomial.monic_toSubring]
  exact prodXSubSMul.monic G F x

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `eval₂` / 定理 `eval₂`

English:
theorem eval₂
  proof: by
  rw [← prodXSubSMul.eval G F x]; rw [Polynomial.eval₂_eq_eval_map]
  simp only [minpoly, Polynomial.map_toSubring]

中文:
定理 eval₂
  证明: by
  rw [← prodXSubSMul.eval G F x]; rw [Polynomial.eval₂_eq_eval_map]
  simp only [minpoly, Polynomial.map_toSubring]

Depends on / 依赖: Polynomial, Polynomial.eval, Polynomial.map_toSubring, map_toSubring, minpoly, prodXSubSMul, prodXSubSMul.eval
-/
theorem eval₂ :
    Polynomial.eval₂ (Subring.subtype <| (FixedPoints.subfield G F).toSubring) x (minpoly G F x) =
      0 := by
  rw [← prodXSubSMul.eval G F x]; rw [Polynomial.eval₂_eq_eval_map]
  simp only [minpoly, Polynomial.map_toSubring]

/--
theorem `eval₂'` / 定理 `eval₂'`

English:
theorem eval₂'
  proof: eval₂ G F x

中文:
定理 eval₂'
  证明: eval₂ G F x
-/
theorem eval₂' :
    Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x (minpoly G F x) = 0 :=
  eval₂ G F x

/--
theorem `ne_one` / 定理 `ne_one`

English:
theorem ne_one
  statement: minpoly G F x != (1 : Polynomial (FixedPoints.subfield G F))
  proof: fun H =>
  have := eval₂ G F x
(one_ne_zero : (1 : F) != 0) by rwa [H, Polynomial.eval₂_one] at this

中文:
定理 ne_one
  结论: minpoly G F x != (1 : 多项式 (FixedPoints.subfield G F))
  证明: fun H =>
  have := eval₂ G F x
(one_ne_zero : (1 : F) != 0) by rwa [H, Polynomial.eval₂_one] at this
-/
theorem ne_one : minpoly G F x != (1 : Polynomial (FixedPoints.subfield G F)) := fun H =>
  have := eval₂ G F x
(one_ne_zero : (1 : F) != 0) by rwa [H, Polynomial.eval₂_one] at this

set_option backward.isDefEq.respectTransparency.types false in
/--
theorem `of_eval₂` / 定理 `of_eval₂`

English:
theorem of_eval₂
  statement: (f : Polynomial (FixedPoints.subfield G F))
  proof: by
  classical
  rw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F)]; rw [minpoly]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ _]; rw [prodXSubSMul]
  refine
    Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C <| MulA

中文:
定理 of_eval₂
  结论: (f : 多项式 (FixedPoints.subfield G F))
  证明: by
  classical
  rw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F)]; rw [minpoly]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ _]; rw [prodXSubSMul]
  refine
    Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C <| MulA

Depends on / 依赖: Fintype, Fintype.prod_dvd_of_coprime, FixedPoints, FixedPoints.subfield, IsRoot, MulAction, MulAction.injective_ofQuotientStabilizer, MulAction.ofQuotientStabilizer_mk, Polynomial, Polynomial.IsRoot.def, Polynomial.dvd_iff_isRoot, Polynomial.eval_smul, Polynomial.map_dvd_map, Polynomial.map_toSubring, Polynomial.pairwise_coprime_X_sub_C, QuotientGroup, QuotientGroup.induction_on, Subfield, Subfield.subtype, Subfield.toSubring_subtype_eq_subtype
-/
theorem of_eval₂ (f : Polynomial (FixedPoints.subfield G F))
    (hf : Polynomial.eval₂ (Subfield.subtype <| FixedPoints.subfield G F) x f = 0) :
    minpoly G F x ∣ f := by
  classical
  rw [← Polynomial.map_dvd_map' (Subfield.subtype <| FixedPoints.subfield G F)]; rw [minpoly]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ _]; rw [prodXSubSMul]
  refine
    Fintype.prod_dvd_of_coprime
      (Polynomial.pairwise_coprime_X_sub_C <| MulAction.injective_ofQuotientStabilizer G x) fun y =>
      QuotientGroup.induction_on y fun g => ?_
  rw [Polynomial.dvd_iff_isRoot]; rw [Polynomial.IsRoot.def]; rw [MulAction.ofQuotientStabilizer_mk]; rw [Polynomial.eval_smul']; rw [← IsInvariantSubring.coe_subtypeHom' G (FixedPoints.subfield G F).toSubring]; rw [← MulSemiringActionHom.coe_polynomial]; rw [← map_smul]; rw [smul_polynomial]; rw [MulSemiringActionHom.coe_polynomial]; rw [IsInvariantSubring.coe_subtypeHom']; rw [Polynomial.eval_map]; rw [Subfield.toSubring_subtype_eq_subtype]; rw [hf]; rw [smul_zero]

-- Why is this so slow?
/--
theorem `irreducible_aux` / 定理 `irreducible_aux`

English:
theorem irreducible_aux
  statement: (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
  proof: by
  have hf2 : f ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg]; rw [Polynomial.eval₂_mul]; rw [mul_eq_zero] at this
  rcases this with this | this
  · right
    have hf3 : f = minp

中文:
定理 irreducible_aux
  结论: (f g : 多项式 (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
  证明: by
  have hf2 : f ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg]; rw [Polynomial.eval₂_mul]; rw [mul_eq_zero] at this
  rcases this with this | this
  · right
    have hf3 : f = minp

Depends on / 依赖: Polynomial, Polynomial.eq_of_monic_of_associated, Polynomial.eval, associated_of_dvd_dvd, dvd_mul_left, dvd_mul_right, eq_of_monic_of_associated, minpoly, mul_eq_zero, mul_one, mul_right_inj, ne_zero
-/
theorem irreducible_aux (f g : Polynomial (FixedPoints.subfield G F)) (hf : f.Monic) (hg : g.Monic)
    (hfg : f * g = minpoly G F x) : f = 1 ∨ g = 1 := by
  have hf2 : f ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_right _ _
  have hg2 : g ∣ minpoly G F x := by rw [← hfg]; exact dvd_mul_left _ _
  have := eval₂ G F x
  rw [← hfg]; rw [Polynomial.eval₂_mul]; rw [mul_eq_zero] at this
  rcases this with this | this
  · right
    have hf3 : f = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hf (monic G F x)
        (associated_of_dvd_dvd hf2 <| @of_eval₂ G _ F _ _ _ x f this)
    rwa [← mul_one (minpoly G F x), hf3, mul_right_inj' (monic G F x).ne_zero] at hfg
  · left
    have hg3 : g = minpoly G F x :=
      Polynomial.eq_of_monic_of_associated hg (monic G F x)
        (associated_of_dvd_dvd hg2 <| @of_eval₂ G _ F _ _ _ x g this)
    rwa [← one_mul (minpoly G F x), hg3, mul_left_inj' (monic G F x).ne_zero] at hfg

/--
theorem `irreducible` / 定理 `irreducible`

English:
theorem irreducible
  statement: Irreducible (minpoly G F x)
  proof: (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

中文:
定理 irreducible
  结论: 不可约 (minpoly G F x)
  证明: (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

Depends on / 依赖: Polynomial, Polynomial.irreducible_of_monic, irreducible_aux, irreducible_of_monic, ne_one
-/
theorem irreducible : Irreducible (minpoly G F x) :=
  (Polynomial.irreducible_of_monic (monic G F x) (ne_one G F x)).2 (irreducible_aux G F x)

end minpoly

end Fintype

/--
theorem `isIntegral` / 定理 `isIntegral`

English:
theorem isIntegral
  given: [Finite G] (x : F)
  statement: IsIntegral (FixedPoints.subfield G F) x
  proof: by
  cases nonempty_fintype G; exact ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

中文:
定理 is整数egral
  条件: [有限 G] (x : F)
  结论: 是整 (FixedPoints.subfield G F) x
  证明: by
  cases nonempty_fintype G; exact ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

Depends on / 依赖: minpoly, minpoly.eval, minpoly.monic, nonempty_fintype
-/
theorem isIntegral [Finite G] (x : F) : IsIntegral (FixedPoints.subfield G F) x := by
  cases nonempty_fintype G; exact ⟨minpoly G F x, minpoly.monic G F x, minpoly.eval₂ G F x⟩

section Fintype

variable [Fintype G] (x : F)

/--
theorem `minpoly_eq_minpoly` / 定理 `minpoly_eq_minpoly`

English:
theorem minpoly_eq_minpoly
  statement: minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x
  proof: minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x)
    (minpoly.monic G F x)

中文:
定理 minpoly_eq_minpoly
  结论: minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x
  证明: minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x)
    (minpoly.monic G F x)

Depends on / 依赖: eq_of_irreducible_of_monic, irreducible, minpoly, minpoly.eq_of_irreducible_of_monic, minpoly.eval, minpoly.irreducible, minpoly.monic
-/
theorem minpoly_eq_minpoly : minpoly G F x = _root_.minpoly (FixedPoints.subfield G F) x :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible G F x) (minpoly.eval₂ G F x)
    (minpoly.monic G F x)

/--
theorem `rank_le_card` / 定理 `rank_le_card`

English:
theorem rank_le_card
  statement: Module.rank (FixedPoints.subfield G F) F <= Fintype.card G
  proof: rank_le fun s hs => by
    simpa only [rank_fun', Cardinal.mk_coe_finset, Finset.coe_sort_coe, Cardinal.lift_natCast,
      Nat.cast_le] using
      (linearIndependent_smul_of_linearIndependent G F hs).cardinal_lift_le_rank

中文:
定理 rank_le_card
  结论: 模.rank (FixedPoints.subfield G F) F <= 有限类型.card G
  证明: rank_le fun s hs => by
    simpa only [rank_fun', Cardinal.mk_coe_finset, Finset.coe_sort_coe, Cardinal.lift_natCast,
      Nat.cast_le] using
      (linearIndependent_smul_of_linearIndependent G F hs).cardinal_lift_le_rank

Depends on / 依赖: Cardinal, Cardinal.lift_natCast, Cardinal.mk_coe_finset, Finset, Finset.coe_sort_coe, Nat.cast_le, cardinal_lift_le_rank, cast_le, coe_sort_coe, lift_natCast, linearIndependent_smul_of_linearIndependent, mk_coe_finset, rank_fun, rank_le
-/
theorem rank_le_card : Module.rank (FixedPoints.subfield G F) F <= Fintype.card G :=
  rank_le fun s hs => by
    simpa only [rank_fun', Cardinal.mk_coe_finset, Finset.coe_sort_coe, Cardinal.lift_natCast,
      Nat.cast_le] using
      (linearIndependent_smul_of_linearIndependent G F hs).cardinal_lift_le_rank

end Fintype

section Finite

variable [Finite G]

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `normal` / 实例 `normal`

English:
instance normal
  signature: : Normal (FixedPoints.subfield G F) F where
  body: (isIntegral G F x).isAlgebraic
  splits' x := by
    cases nonempty_fintype G
    rw [← minpoly_eq_minpoly]; rw [minpoly]; rw [coe_algebraMap]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ (subfield G F).toSubring]; rw [prodXSubSMul]
    exact Polynomial.Splits.prod f

中文:
实例 normal
  签名: : 正规 (FixedPoints.subfield G F) F where
  定义体: (isIntegral G F x).isAlgebraic
  splits' x := by
    cases nonempty_fintype G
    rw [← minpoly_eq_minpoly]; rw [minpoly]; rw [coe_algebraMap]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ (subfield G F).toSubring]; rw [prodXSubSMul]
    exact Polynomial.Splits.prod f

Depends on / 依赖: isAlgebraic, isIntegral
-/
instance normal : Normal (FixedPoints.subfield G F) F where
  isAlgebraic x := (isIntegral G F x).isAlgebraic
  splits' x := by
    cases nonempty_fintype G
    rw [← minpoly_eq_minpoly]; rw [minpoly]; rw [coe_algebraMap]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ (subfield G F).toSubring]; rw [prodXSubSMul]
    exact Polynomial.Splits.prod fun _ _ => Polynomial.Splits.X_sub_C _

set_option backward.isDefEq.respectTransparency.types false in
/--
Instance `isSeparable` / 实例 `isSeparable`

English:
instance isSeparable
  signature: : Algebra.IsSeparable (FixedPoints.subfield G F) F
  body: by
  classical
  exact ⟨fun x => by
    cases nonempty_fintype G
    rw [IsSeparable]; rw [← minpoly_eq_minpoly]; rw [← Polynomial.separable_map (FixedPoints.subfield G F).subtype]; rw [minpoly]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ (subfield G F).toSubring]
 

中文:
实例 isSeparable
  签名: : 代数.是可分 (FixedPoints.subfield G F) F
  定义体: by
  classical
  exact ⟨fun x => by
    cases nonempty_fintype G
    rw [IsSeparable]; rw [← minpoly_eq_minpoly]; rw [← Polynomial.separable_map (FixedPoints.subfield G F).subtype]; rw [minpoly]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ (subfield G F).toSubring]
 

Depends on / 依赖: FixedPoints, FixedPoints.subfield, IsSeparable, Polynomial, Polynomial.map_toSubring, Polynomial.separable_map, Polynomial.separable_prod_X_sub_C_iff, Subfield, Subfield.toSubring_subtype_eq_subtype, classical, injective_ofQuotientStabilizer, map_toSubring, minpoly, minpoly_eq_minpoly, nonempty_fintype, separable_map, separable_prod_X_sub_C_iff, subfield, subtype, toSubring
-/
instance isSeparable : Algebra.IsSeparable (FixedPoints.subfield G F) F := by
  classical
  exact ⟨fun x => by
    cases nonempty_fintype G
    rw [IsSeparable]; rw [← minpoly_eq_minpoly]; rw [← Polynomial.separable_map (FixedPoints.subfield G F).subtype]; rw [minpoly]; rw [← Subfield.toSubring_subtype_eq_subtype]; rw [Polynomial.map_toSubring _ (subfield G F).toSubring]
    exact Polynomial.separable_prod_X_sub_C_iff.2 (injective_ofQuotientStabilizer G x)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FiniteDimensional (subfield G F) F
  body: by
  cases nonempty_fintype G
  exact IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 <| (rank_le_card G F).trans_lt Cardinal.natCast_lt_aleph0)

中文:
实例 :
  签名: 有限维 (subfield G F) F
  定义体: by
  cases nonempty_fintype G
  exact IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 <| (rank_le_card G F).trans_lt Cardinal.natCast_lt_aleph0)

Depends on / 依赖: Cardinal, Cardinal.natCast_lt_aleph0, IsNoetherian, IsNoetherian.iff_fg, IsNoetherian.iff_rank_lt_aleph0, iff_fg, iff_rank_lt_aleph0, natCast_lt_aleph0, nonempty_fintype, rank_le_card, trans_lt
-/
instance : FiniteDimensional (subfield G F) F := by
  cases nonempty_fintype G
  exact IsNoetherian.iff_fg.1
    (IsNoetherian.iff_rank_lt_aleph0.2 <| (rank_le_card G F).trans_lt Cardinal.natCast_lt_aleph0)

end Finite

/--
theorem `finrank_le_card` / 定理 `finrank_le_card`

English:
theorem finrank_le_card
  given: [Fintype G]
  statement: finrank (subfield G F) F <= Fintype.card G
  proof: by
  rw [← @Nat.cast_le Cardinal]; rw [finrank_eq_rank]
  apply rank_le_card

中文:
定理 finrank_le_card
  条件: [有限类型 G]
  结论: finrank (subfield G F) F <= 有限类型.card G
  证明: by
  rw [← @Nat.cast_le Cardinal]; rw [finrank_eq_rank]
  apply rank_le_card

Depends on / 依赖: Cardinal, Nat.cast_le, cast_le, finrank_eq_rank, rank_le_card
-/
theorem finrank_le_card [Fintype G] : finrank (subfield G F) F <= Fintype.card G := by
  rw [← @Nat.cast_le Cardinal]; rw [finrank_eq_rank]
  apply rank_le_card

end FixedPoints

/--
theorem `linearIndependent_toLinearMap` / 定理 `linearIndependent_toLinearMap`

English:
theorem linearIndependent_toLinearMap
  statement: (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
  proof: have : LinearIndependent B (LinearMap.ltoFun R A B B ∘ AlgHom.toLinearMap) :=
    ((linearIndependent_monoidHom A B).comp ((↑) : (A ->ₐ[R] B) -> A ->* B) fun _ _ hfg =>
        AlgHom.ext fun _ => DFunLike.ext_iff.1 hfg _ :
      _)
  this.of_comp _

中文:
定理 linearIndependent_toLinearMap
  结论: (R : 类型u) (A : 类型v) (B : 类型 w) [交换半环 R]
  证明: have : LinearIndependent B (LinearMap.ltoFun R A B B ∘ AlgHom.toLinearMap) :=
    ((linearIndependent_monoidHom A B).comp ((↑) : (A ->ₐ[R] B) -> A ->* B) fun _ _ hfg =>
        AlgHom.ext fun _ => DFunLike.ext_iff.1 hfg _ :
      _)
  this.of_comp _

Depends on / 依赖: AlgHom, AlgHom.ext, AlgHom.toLinearMap, DFunLike, DFunLike.ext_iff, LinearIndependent, LinearMap, LinearMap.ltoFun, ext_iff, linearIndependent_monoidHom, ltoFun, of_comp, this.of_comp, toLinearMap
-/
theorem linearIndependent_toLinearMap (R : Type u) (A : Type v) (B : Type w) [CommSemiring R]
    [Semiring A] [Algebra R A] [CommRing B] [IsDomain B] [Algebra R B] :
    LinearIndependent B (AlgHom.toLinearMap : (A ->ₐ[R] B) -> A ->ₗ[R] B) :=
  have : LinearIndependent B (LinearMap.ltoFun R A B B ∘ AlgHom.toLinearMap) :=
    ((linearIndependent_monoidHom A B).comp ((↑) : (A ->ₐ[R] B) -> A ->* B) fun _ _ hfg =>
        AlgHom.ext fun _ => DFunLike.ext_iff.1 hfg _ :
      _)
  this.of_comp _

/--
theorem `cardinalMk_algHom` / 定理 `cardinalMk_algHom`

English:
theorem cardinalMk_algHom
  statement: (K : Type u) (V : Type v) (W : Type w) [Field K] [Ring V] [Algebra K V]
  proof: (linearIndependent_toLinearMap K V W).cardinalMk_le_finrank

中文:
定理 cardinalMk_algHom
  结论: (K : 类型u) (V : 类型v) (W : 类型 w) [域 K] [环 V] [代数 K V]
  证明: (linearIndependent_toLinearMap K V W).cardinalMk_le_finrank

Depends on / 依赖: cardinalMk_le_finrank, linearIndependent_toLinearMap
-/
theorem cardinalMk_algHom (K : Type u) (V : Type v) (W : Type w) [Field K] [Ring V] [Algebra K V]
    [FiniteDimensional K V] [Field W] [Algebra K W] :
    Cardinal.mk (V ->ₐ[K] W) <= finrank W (V ->ₗ[K] W) :=
  (linearIndependent_toLinearMap K V W).cardinalMk_le_finrank

/--
Instance `AlgEquiv.fintype` / 实例 `AlgEquiv.fintype`

English:
instance AlgEquiv.fintype
  signature: (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
  body: Fintype.ofEquiv (V ->ₐ[K] V) (algEquivEquivAlgHom K V).symm

中文:
实例 代数等价.fintype
  签名: (K : 类型u) (V : 类型v) [域 K] [域 V] [代数 K V]
  定义体: Fintype.ofEquiv (V ->ₐ[K] V) (algEquivEquivAlgHom K V).symm

Depends on / 依赖: Fintype, Fintype.ofEquiv, algEquivEquivAlgHom, ofEquiv
-/
noncomputable instance AlgEquiv.fintype (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype (V ≃ₐ[K] V) :=
  Fintype.ofEquiv (V ->ₐ[K] V) (algEquivEquivAlgHom K V).symm

/--
theorem `finrank_algHom` / 定理 `finrank_algHom`

English:
theorem finrank_algHom
  statement: (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
  proof: (linearIndependent_toLinearMap K V V).fintype_card_le_finrank

中文:
定理 finrank_algHom
  结论: (K : 类型u) (V : 类型v) [域 K] [域 V] [代数 K V]
  证明: (linearIndependent_toLinearMap K V V).fintype_card_le_finrank

Depends on / 依赖: fintype_card_le_finrank, linearIndependent_toLinearMap
-/
theorem finrank_algHom (K : Type u) (V : Type v) [Field K] [Field V] [Algebra K V]
    [FiniteDimensional K V] : Fintype.card (V ->ₐ[K] V) <= finrank V (V ->ₗ[K] V) :=
  (linearIndependent_toLinearMap K V V).fintype_card_le_finrank

/--
theorem `AlgHom.card_le` / 定理 `AlgHom.card_le`

English:
theorem AlgHom.card_le
  given: {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  proof: Module.finrank_linearMap_self F K K ▸ finrank_algHom F K

中文:
定理 代数态射.card_le
  条件: {F K : 类型} [域 F] [域 K] [代数 F K] [有限维 F K]
  证明: Module.finrank_linearMap_self F K K ▸ finrank_algHom F K

Depends on / 依赖: Module, Module.finrank_linearMap_self, finrank_algHom, finrank_linearMap_self
-/
theorem AlgHom.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card (K ->ₐ[F] K) <= Module.finrank F K :=
  Module.finrank_linearMap_self F K K ▸ finrank_algHom F K

/--
theorem `AlgEquiv.card_le` / 定理 `AlgEquiv.card_le`

English:
theorem AlgEquiv.card_le
  given: {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]
  proof: Fintype.ofEquiv_card (algEquivEquivAlgHom F K).toEquiv.symm ▸ AlgHom.card_le

中文:
定理 代数等价.card_le
  条件: {F K : 类型} [域 F] [域 K] [代数 F K] [有限维 F K]
  证明: Fintype.ofEquiv_card (algEquivEquivAlgHom F K).toEquiv.symm ▸ AlgHom.card_le

Depends on / 依赖: AlgHom, AlgHom.card_le, Fintype, Fintype.ofEquiv_card, algEquivEquivAlgHom, card_le, ofEquiv_card, toEquiv, toEquiv.symm
-/
theorem AlgEquiv.card_le {F K : Type*} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    Fintype.card Gal(K/F) <= Module.finrank F K :=
  Fintype.ofEquiv_card (algEquivEquivAlgHom F K).toEquiv.symm ▸ AlgHom.card_le

namespace FixedPoints

variable (G F : Type*) [Group G] [Field F] [MulSemiringAction G F]

/-- Let $F$ be a field. Let $G$ be a finite group acting faithfully on $F$.
Then $[F : F^G] = |G|$. -/
@[stacks 09I3 "second part"]
/--
theorem `finrank_eq_card` / 定理 `finrank_eq_card`

English:
theorem finrank_eq_card
  given: [Fintype G] [FaithfulSMul G F]
  proof: le_antisymm (FixedPoints.finrank_le_card G F)
    calc
      Fintype.card G <= Fintype.card (F ->ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      _ <= finrank F (F ->ₗ[FixedPoints.subfield G F] F) := finrank_algHom (subfield G 

中文:
定理 finrank_eq_card
  条件: [有限类型 G] [忠实标量乘法 G F]
  证明: le_antisymm (FixedPoints.finrank_le_card G F)
    calc
      Fintype.card G <= Fintype.card (F ->ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      _ <= finrank F (F ->ₗ[FixedPoints.subfield G F] F) := finrank_algHom (subfield G 

Depends on / 依赖: Fintype, Fintype.card, Fintype.card_le_of_injective, FixedPoints, FixedPoints.finrank_le_card, FixedPoints.subfield, MulSemiringAction, MulSemiringAction.toAlgHom_injective, card_le_of_injective, finrank, finrank_algHom, finrank_le_card, finrank_linearMap_self, le_antisymm, subfield, toAlgHom_injective
-/
theorem finrank_eq_card [Fintype G] [FaithfulSMul G F] :
    finrank (FixedPoints.subfield G F) F = Fintype.card G :=
le_antisymm (FixedPoints.finrank_le_card G F)
    calc
      Fintype.card G <= Fintype.card (F ->ₐ[FixedPoints.subfield G F] F) :=
        Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
      _ <= finrank F (F ->ₗ[FixedPoints.subfield G F] F) := finrank_algHom (subfield G F) F
      _ = finrank (FixedPoints.subfield G F) F := finrank_linearMap_self _ _ _

/--
theorem `toAlgHom_bijective` / 定理 `toAlgHom_bijective`

English:
theorem toAlgHom_bijective
  given: [Finite G] [FaithfulSMul G F]
  proof: by
  cases nonempty_fintype G
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact MulSemiringAction.toAlgHom_injective _ F
  · apply le_antisymm
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
    · rw [← finrank_eq_card G F]
      exact LE.l

中文:
定理 toAlgHom_bijective
  条件: [有限 G] [忠实标量乘法 G F]
  证明: by
  cases nonempty_fintype G
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact MulSemiringAction.toAlgHom_injective _ F
  · apply le_antisymm
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
    · rw [← finrank_eq_card G F]
      exact LE.l

Depends on / 依赖: Fintype, Fintype.bijective_iff_injective_and_card, Fintype.card_le_of_injective, LE.le.trans_eq, MulSemiringAction, MulSemiringAction.toAlgHom_injective, bijective_iff_injective_and_card, card_le_of_injective, finrank_algHom, finrank_eq_card, finrank_linearMap_self, le_antisymm, nonempty_fintype, toAlgHom_injective, trans_eq
-/
theorem toAlgHom_bijective [Finite G] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgHom _ _ : G -> F ->ₐ[subfield G F] F) := by
  cases nonempty_fintype G
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact MulSemiringAction.toAlgHom_injective _ F
  · apply le_antisymm
    · exact Fintype.card_le_of_injective _ (MulSemiringAction.toAlgHom_injective _ F)
    · rw [← finrank_eq_card G F]
      exact LE.le.trans_eq (finrank_algHom _ F) (finrank_linearMap_self _ _ _)

/--
Definition of `toAlgHomEquiv` / `toAlgHomEquiv` 的定义

English:
definition toAlgHomEquiv
  signature: [Finite G] [FaithfulSMul G F]
  body: Equiv.ofBijective _ (toAlgHom_bijective G F)

中文:
定义 toAlgHomEquiv
  签名: [有限 G] [忠实标量乘法 G F]
  定义体: Equiv.ofBijective _ (toAlgHom_bijective G F)

Depends on / 依赖: Equiv.ofBijective, ofBijective, toAlgHom_bijective
-/
def toAlgHomEquiv [Finite G] [FaithfulSMul G F] : G ≃ (F ->ₐ[FixedPoints.subfield G F] F) :=
  Equiv.ofBijective _ (toAlgHom_bijective G F)

/--
theorem `toAlgAut_bijective` / 定理 `toAlgAut_bijective`

English:
theorem toAlgAut_bijective
  given: [Finite G] [FaithfulSMul G F]
  proof: by
  refine ⟨fun _ _ h => (FixedPoints.toAlgHom_bijective G F).injective ?_,
    fun f => ((FixedPoints.toAlgHom_bijective G F).surjective f).imp (fun _ h => ?_)⟩ <;>
      rwa [DFunLike.ext_iff] at h ⊢

中文:
定理 toAlgAut_bijective
  条件: [有限 G] [忠实标量乘法 G F]
  证明: by
  refine ⟨fun _ _ h => (FixedPoints.toAlgHom_bijective G F).injective ?_,
    fun f => ((FixedPoints.toAlgHom_bijective G F).surjective f).imp (fun _ h => ?_)⟩ <;>
      rwa [DFunLike.ext_iff] at h ⊢

Depends on / 依赖: DFunLike, DFunLike.ext_iff, FixedPoints, FixedPoints.toAlgHom_bijective, ext_iff, injective, surjective, toAlgHom_bijective
-/
theorem toAlgAut_bijective [Finite G] [FaithfulSMul G F] :
    Function.Bijective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F) := by
  refine ⟨fun _ _ h => (FixedPoints.toAlgHom_bijective G F).injective ?_,
    fun f => ((FixedPoints.toAlgHom_bijective G F).surjective f).imp (fun _ h => ?_)⟩ <;>
      rwa [DFunLike.ext_iff] at h ⊢

/--
Definition of `toAlgAutMulEquiv` / `toAlgAutMulEquiv` 的定义

English:
definition toAlgAutMulEquiv
  signature: [Finite G] [FaithfulSMul G F]
  body: MulEquiv.ofBijective _ (toAlgAut_bijective G F)

中文:
定义 toAlgAutMulEquiv
  签名: [有限 G] [忠实标量乘法 G F]
  定义体: MulEquiv.ofBijective _ (toAlgAut_bijective G F)

Depends on / 依赖: MulEquiv, MulEquiv.ofBijective, ofBijective, toAlgAut_bijective
-/
def toAlgAutMulEquiv [Finite G] [FaithfulSMul G F] : G ≃* (F ≃ₐ[FixedPoints.subfield G F] F) :=
  MulEquiv.ofBijective _ (toAlgAut_bijective G F)

/--
theorem `toAlgAut_surjective` / 定理 `toAlgAut_surjective`

English:
theorem toAlgAut_surjective
  given: [Finite G]
  proof: by
  let f : G ->* F ≃ₐ[FixedPoints.subfield G F] F :=
    MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F
  let Q := G ⧸ f.ker
  let _ : MulSemiringAction Q F := MulSemiringAction.compHom _ (QuotientGroup.kerLift f)
  have : FaithfulSMul Q F := ⟨fun {q₁ q₂} => by
    induction q₁, q₂ usin

中文:
定理 toAlgAut_surjective
  条件: [有限 G]
  证明: by
  let f : G ->* F ≃ₐ[FixedPoints.subfield G F] F :=
    MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F
  let Q := G ⧸ f.ker
  let _ : MulSemiringAction Q F := MulSemiringAction.compHom _ (QuotientGroup.kerLift f)
  have : FaithfulSMul Q F := ⟨fun {q₁ q₂} => by
    induction q₁, q₂ usin

Depends on / 依赖: AlgEquiv, AlgEquiv.ext_iff, AlgEquiv.of, FaithfulSMul, FixedPoints, FixedPoints.subfield, MonoidHom, MonoidHom.mem_ker, MulSemiringAction, MulSemiringAction.compHom, MulSemiringAction.toAlgAut, Quotient, Quotient.inductionOn, QuotientGroup, QuotientGroup.eq, QuotientGroup.kerLift, compHom, ext_iff, f.ker, inv_mul_eq_one
-/
theorem toAlgAut_surjective [Finite G] :
    Function.Surjective (MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F) := by
  let f : G ->* F ≃ₐ[FixedPoints.subfield G F] F :=
    MulSemiringAction.toAlgAut G (FixedPoints.subfield G F) F
  let Q := G ⧸ f.ker
  let _ : MulSemiringAction Q F := MulSemiringAction.compHom _ (QuotientGroup.kerLift f)
  have : FaithfulSMul Q F := ⟨fun {q₁ q₂} => by
    induction q₁, q₂ using Quotient.inductionOn₂ with | _ g₁ g₂
    intro h
    rwa [QuotientGroup.eq, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one, AlgEquiv.ext_iff]⟩
  intro f
  obtain ⟨q, hq⟩ := (toAlgAut_bijective Q F).surjective
    (AlgEquiv.ofRingEquiv (f := f) (fun ⟨x, hx⟩ => f.commutes' ⟨x, fun g => hx g⟩))
  revert hq
  refine QuotientGroup.induction_on q (fun g hg => ⟨g, ?_⟩)
  rwa [AlgEquiv.ext_iff] at hg ⊢

end FixedPoints
