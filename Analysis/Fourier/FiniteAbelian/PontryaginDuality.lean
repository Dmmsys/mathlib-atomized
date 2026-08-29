/-
Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Algebra.DirectSum.AddChar
public import Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.Topology.Instances.AddCircle.Real
import Mathlib.Algebra.Field.ModEq

/-!
# Pontryagin duality for finite abelian groups

This file proves the Pontryagin duality in case of finite abelian groups. This states that any
finite abelian group is canonically isomorphic to its double dual (the space of complex-valued
characters of its space of complex-valued characters).

We first prove it for `ZMod n` and then extend to all finite abelian groups using the
Structure Theorem.

## TODO

Reuse the work done in `Mathlib/GroupTheory/FiniteAbelian/Duality.lean`. This requires to write some
more glue.
-/

@[expose] public section

noncomputable section

open Circle Finset Function Module Multiplicative
open Fintype (card)
open Real hiding exp
open scoped BigOperators DirectSum

variable {α : Type*} [AddCommGroup α] {n : Nat} {a b : α}

namespace AddChar
variable (n : Nat) [NeZero n]

/--
Definition of `zmod` / `zmod` 的定义

English:
definition zmod
  signature: (x : ZMod n)
  body: AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩
ZMod.toAddCircle.comp .mulLeft x

中文:
定义 zmod
  签名: (x : ZMod n)
  定义体: AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩
ZMod.toAddCircle.comp .mulLeft x

Depends on / 依赖: AddChar, AddChar.compAddMonoidHom, AddCircle, AddCircle.toCircle, AddCircle.toCircle_add, AddCircle.toCircle_zero, ZMod.toAddCircle.comp, compAddMonoidHom, mulLeft, toAddCircle, toCircle, toCircle_add, toCircle_zero
-/
def zmod (x : ZMod n) : AddChar (ZMod n) Circle :=
AddChar.compAddMonoidHom ⟨AddCircle.toCircle, AddCircle.toCircle_zero, AddCircle.toCircle_add⟩
ZMod.toAddCircle.comp .mulLeft x

/--
lemma `zmod_intCast` / 引理 `zmod_intCast`

English:
lemma zmod_intCast
  given: (x y : Int)
  statement: zmod n x y = exp (2 * π * (x * y / n))
  proof: by
  simp [zmod, ← Int.cast_mul x y, -Int.cast_mul, ZMod.toAddCircle_intCast,
    AddCircle.toCircle_apply_mk]

中文:
引理 zmod_intCast
  条件: (x y : 整数)
  结论: zmod n x y = exp (2 * π * (x * y / n))
  证明: by
  simp [zmod, ← Int.cast_mul x y, -Int.cast_mul, ZMod.toAddCircle_intCast,
    AddCircle.toCircle_apply_mk]
-/
@[simp] lemma zmod_intCast (x y : Int) : zmod n x y = exp (2 * π * (x * y / n)) := by
  simp [zmod, ← Int.cast_mul x y, -Int.cast_mul, ZMod.toAddCircle_intCast,
    AddCircle.toCircle_apply_mk]

/--
lemma `zmod_zero` / 引理 `zmod_zero`

English:
lemma zmod_zero
  statement: zmod n 0 = 1
  proof: DFunLike.ext _ _ by simp [zmod]

中文:
引理 zmod_zero
  结论: zmod n 0 = 1
  证明: DFunLike.ext _ _ by simp [zmod]
-/
@[simp] lemma zmod_zero : zmod n 0 = 1 :=
DFunLike.ext _ _ by simp [zmod]

variable {n}

/--
lemma `zmod_add` / 引理 `zmod_add`

English:
lemma zmod_add
  statement: forall x y : ZMod n, zmod n (x + y) = zmod n x * zmod n y
  proof: by
  simp [DFunLike.ext_iff, zmod, add_mul, map_add_eq_mul]

中文:
引理 zmod_add
  结论: 对任意 x y : ZMod n, zmod n (x + y) = zmod n x * zmod n y
  证明: by
  simp [DFunLike.ext_iff, zmod, add_mul, map_add_eq_mul]
-/
@[simp] lemma zmod_add : forall x y : ZMod n, zmod n (x + y) = zmod n x * zmod n y := by
  simp [DFunLike.ext_iff, zmod, add_mul, map_add_eq_mul]

/--
lemma `zmod_injective` / 引理 `zmod_injective`

English:
lemma zmod_injective
  statement: Injective (zmod n)
  proof: by
  simp_rw [Injective, ZMod.intCast_surjective.forall]
  rintro x y h
  have hn : (n : Real) != 0 := NeZero.ne _
  simpa [pi_ne_zero, exp_inj, hn, CharP.intCast_eq_intCast (ZMod n) n] using
(zmod_intCast ..).symm.trans (DFunLike.congr_fun h ((1 : Int) : ZMod n)).trans
      zmod_intCast ..

中文:
引理 zmod_injective
  结论: 单射 (zmod n)
  证明: by
  simp_rw [Injective, ZMod.intCast_surjective.forall]
  rintro x y h
  have hn : (n : Real) != 0 := NeZero.ne _
  simpa [pi_ne_zero, exp_inj, hn, CharP.intCast_eq_intCast (ZMod n) n] using
(zmod_intCast ..).symm.trans (DFunLike.congr_fun h ((1 : Int) : ZMod n)).trans
      zmod_intCast ..

Depends on / 依赖: CharP.intCast_eq_intCast, DFunLike, DFunLike.congr_fun, Injective, NeZero, NeZero.ne, ZMod.intCast_surjective.forall, congr_fun, exp_inj, intCast_eq_intCast, intCast_surjective, pi_ne_zero, simp_rw, symm.trans, zmod_intCast
-/
lemma zmod_injective : Injective (zmod n) := by
  simp_rw [Injective, ZMod.intCast_surjective.forall]
  rintro x y h
  have hn : (n : Real) != 0 := NeZero.ne _
  simpa [pi_ne_zero, exp_inj, hn, CharP.intCast_eq_intCast (ZMod n) n] using
(zmod_intCast ..).symm.trans (DFunLike.congr_fun h ((1 : Int) : ZMod n)).trans
      zmod_intCast ..

/--
lemma `zmod_inj` / 引理 `zmod_inj`

English:
lemma zmod_inj
  given: {x y : ZMod n}
  statement: zmod n x = zmod n y ↔ x = y
  proof: zmod_injective.eq_iff

中文:
引理 zmod_inj
  条件: {x y : ZMod n}
  结论: zmod n x = zmod n y ↔ x = y
  证明: zmod_injective.eq_iff
-/
@[simp] lemma zmod_inj {x y : ZMod n} : zmod n x = zmod n y ↔ x = y := zmod_injective.eq_iff

/--
Definition of `zmodHom` / `zmodHom` 的定义

English:
definition zmodHom
  signature: : AddChar (ZMod n) (AddChar (ZMod n) Circle) where
  body: zmod n
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

中文:
定义 zmodHom
  签名: : 加法特征 (ZMod n) (加法特征 (ZMod n) Circle) where
  定义体: zmod n
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp
-/
def zmodHom : AddChar (ZMod n) (AddChar (ZMod n) Circle) where
  toFun := zmod n
  map_zero_eq_one' := by simp
  map_add_eq_mul' := by simp

/--
Definition of `mkZModAux` / `mkZModAux` 的定义

English:
definition mkZModAux
  signature: {ι : Type*} [DecidableEq ι] (n : ι -> Nat) [forall i, NeZero (n i)]
  body: AddChar.directSum fun i => zmod (n i) (u i)

中文:
定义 mkZModAux
  签名: {ι : 类型} [DecidableEq ι] (n : ι -> 自然数) [对任意 i, NeZero (n i)]
  定义体: AddChar.directSum fun i => zmod (n i) (u i)
-/
private def mkZModAux {ι : Type*} [DecidableEq ι] (n : ι -> Nat) [forall i, NeZero (n i)]
    (u : forall i, ZMod (n i)) : AddChar (⨁ i, ZMod (n i)) Circle :=
  AddChar.directSum fun i => zmod (n i) (u i)

/--
lemma `mkZModAux_injective` / 引理 `mkZModAux_injective`

English:
lemma mkZModAux_injective
  given: {ι : Type*} [DecidableEq ι] {n : ι -> Nat} [forall i, NeZero (n i)]
  proof: AddChar.directSum_injective.comp fun f g h => by simpa [funext_iff] using h

中文:
引理 mkZModAux_injective
  条件: {ι : 类型} [DecidableEq ι] {n : ι -> 自然数} [对任意 i, NeZero (n i)]
  证明: AddChar.directSum_injective.comp fun f g h => by simpa [funext_iff] using h
-/
private lemma mkZModAux_injective {ι : Type*} [DecidableEq ι] {n : ι -> Nat} [forall i, NeZero (n i)] :
    Injective (mkZModAux n) :=
  AddChar.directSum_injective.comp fun f g h => by simpa [funext_iff] using h

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `circleEquivComplex` / `circleEquivComplex` 的定义

English:
definition circleEquivComplex
  signature: [Finite α]
  body: toMonoidHomEquiv.symm coeHom.comp ψ.toMonoidHom
  invFun ψ :=
    { toFun := fun a => (⟨ψ a, mem_sphere_zero_iff_norm.2 <| ψ.norm_apply _⟩ : Circle)
      map_zero_eq_one' := by simp [Circle]
      map_add_eq_mul' := fun a b => by ext : 1; simp [map_add_eq_mul] }
  left_inv ψ := by ext : 1; simp
  right_inv ψ := by ext : 1; simp
  map_add' ψ χ := rfl

中文:
定义 circleEquivComplex
  签名: [有限 α]
  定义体: toMonoidHomEquiv.symm coeHom.comp ψ.toMonoidHom
  invFun ψ :=
    { toFun := fun a => (⟨ψ a, mem_sphere_zero_iff_norm.2 <| ψ.norm_apply _⟩ : Circle)
      map_zero_eq_one' := by simp [Circle]
      map_add_eq_mul' := fun a b => by ext : 1; simp [map_add_eq_mul] }
  left_inv ψ := by ext : 1; simp
  right_inv ψ := by ext : 1; simp
  map_add' ψ χ := rfl

Depends on / 依赖: coeHom, coeHom.comp, toMonoidHom, toMonoidHomEquiv, toMonoidHomEquiv.symm
-/
def circleEquivComplex [Finite α] : AddChar α Circle ≃+ AddChar α Complex where
toFun ψ := toMonoidHomEquiv.symm coeHom.comp ψ.toMonoidHom
  invFun ψ :=
    { toFun := fun a => (⟨ψ a, mem_sphere_zero_iff_norm.2 <| ψ.norm_apply _⟩ : Circle)
      map_zero_eq_one' := by simp [Circle]
      map_add_eq_mul' := fun a b => by ext : 1; simp [map_add_eq_mul] }
  left_inv ψ := by ext : 1; simp
  right_inv ψ := by ext : 1; simp
  map_add' ψ χ := rfl

/--
lemma `card_eq` / 引理 `card_eq`

English:
lemma card_eq
  given: [Fintype α]
  statement: card (AddChar α Complex) = card α
  proof: by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' i : NeZero (n i) := by have := hn i; exact ⟨by positivity⟩
  let f : α -> AddChar α Complex := fun a => coeHom.compAddChar ((mkZModAux n <| e a).compAddMonoidHom e)
  have hf : Injective f := circleEquivComplex.injective.comp
    ((compAddMonoidHom_injective_left _ e.surjective).comp <| mkZModAux_injective.comp <|
DFunLike.coe_injective.comp e.injective.comp Additive.ofMul.injective)
  exact (card_addChar_le _ _).antisymm (Fintype.card_le_of_injective _ hf)

中文:
引理 card_eq
  条件: [有限类型 α]
  结论: card (加法特征 α 复形) = card α
  证明: by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' i : NeZero (n i) := by have := hn i; exact ⟨by positivity⟩
  let f : α -> AddChar α Complex := fun a => coeHom.compAddChar ((mkZModAux n <| e a).compAddMonoidHom e)
  have hf : Injective f := circleEquivComplex.injective.comp
    ((compAddMonoidHom_injective_left _ e.surjective).comp <| mkZModAux_injective.comp <|
DFunLike.coe_injective.comp e.injective.comp Additive.ofMul.injective)
  exact (card_addChar_le _ _).antisymm (Fintype.card_le_of_injective _ hf)
-/
@[simp] lemma card_eq [Fintype α] : card (AddChar α Complex) = card α := by
  obtain ⟨ι, _, n, hn, ⟨e⟩⟩ := AddCommGroup.equiv_directSum_zmod_of_finite' α
  classical
  have hn' i : NeZero (n i) := by have := hn i; exact ⟨by positivity⟩
  let f : α -> AddChar α Complex := fun a => coeHom.compAddChar ((mkZModAux n <| e a).compAddMonoidHom e)
  have hf : Injective f := circleEquivComplex.injective.comp
    ((compAddMonoidHom_injective_left _ e.surjective).comp <| mkZModAux_injective.comp <|
DFunLike.coe_injective.comp e.injective.comp Additive.ofMul.injective)
  exact (card_addChar_le _ _).antisymm (Fintype.card_le_of_injective _ hf)

/--
Definition of `zmodAddEquiv` / `zmodAddEquiv` 的定义

English:
definition zmodAddEquiv
  signature: : ZMod n ≃+ AddChar (ZMod n) Complex
  body: by
  refine AddEquiv.ofBijective
    (circleEquivComplex.toAddMonoidHom.comp <| AddChar.toAddMonoidHom zmodHom) ?_
  rw [Fintype.bijective_iff_injective_and_card]; rw [card_eq]
  exact ⟨circleEquivComplex.injective.comp zmod_injective, rfl⟩

中文:
定义 zmodAddEquiv
  签名: : ZMod n ≃+ 加法特征 (ZMod n) 复形
  定义体: by
  refine AddEquiv.ofBijective
    (circleEquivComplex.toAddMonoidHom.comp <| AddChar.toAddMonoidHom zmodHom) ?_
  rw [Fintype.bijective_iff_injective_and_card]; rw [card_eq]
  exact ⟨circleEquivComplex.injective.comp zmod_injective, rfl⟩

Depends on / 依赖: AddChar, AddChar.toAddMonoidHom, AddEquiv, AddEquiv.ofBijective, Fintype, Fintype.bijective_iff_injective_and_card, bijective_iff_injective_and_card, card_eq, circleEquivComplex, circleEquivComplex.injective.comp, circleEquivComplex.toAddMonoidHom.comp, injective, ofBijective, toAddMonoidHom, zmodHom, zmod_injective
-/
def zmodAddEquiv : ZMod n ≃+ AddChar (ZMod n) Complex := by
  refine AddEquiv.ofBijective
    (circleEquivComplex.toAddMonoidHom.comp <| AddChar.toAddMonoidHom zmodHom) ?_
  rw [Fintype.bijective_iff_injective_and_card]; rw [card_eq]
  exact ⟨circleEquivComplex.injective.comp zmod_injective, rfl⟩

/--
lemma `zmodAddEquiv_apply` / 引理 `zmodAddEquiv_apply`

English:
lemma zmodAddEquiv_apply
  given: (x : ZMod n)
  proof: rfl

中文:
引理 zmodAddEquiv_apply
  条件: (x : ZMod n)
  证明: rfl
-/
@[simp] lemma zmodAddEquiv_apply (x : ZMod n) :
    zmodAddEquiv x = circleEquivComplex (zmod n x) := rfl

section Finite
variable (α) [Finite α]

/--
Definition of `complexBasis` / `complexBasis` 的定义

English:
definition complexBasis
  signature: : Basis (AddChar α Complex) Complex (α -> Complex)
  body: basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) by
    cases nonempty_fintype α; rw [card_eq, Module.finrank_fintype_fun_eq_card]

@[simp, norm_cast]

中文:
定义 complexBasis
  签名: : 基 (加法特征 α 复形) 复形 (α -> 复形)
  定义体: basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) by
    cases nonempty_fintype α; rw [card_eq, Module.finrank_fintype_fun_eq_card]

@[simp, norm_cast]

Depends on / 依赖: AddChar, AddChar.linearIndependent, Module, Module.finrank_fintype_fun_eq_card, basisOfLinearIndependentOfCardEqFinrank, card_eq, finrank_fintype_fun_eq_card, linearIndependent, nonempty_fintype
-/
def complexBasis : Basis (AddChar α Complex) Complex (α -> Complex) :=
basisOfLinearIndependentOfCardEqFinrank (AddChar.linearIndependent _ _) by
    cases nonempty_fintype α; rw [card_eq, Module.finrank_fintype_fun_eq_card]

@[simp, norm_cast]
/--
lemma `coe_complexBasis` / 引理 `coe_complexBasis`

English:
lemma coe_complexBasis
  statement: ⇑(complexBasis α) = ((⇑) : AddChar α Complex -> α -> Complex)
  proof: by
  rw [complexBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]

中文:
引理 coe_complexBasis
  结论: ⇑(complexBasis α) = ((⇑) : 加法特征 α 复形 -> α -> 复形)
  证明: by
  rw [complexBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]

Depends on / 依赖: coe_basisOfLinearIndependentOfCardEqFinrank, complexBasis
-/
lemma coe_complexBasis : ⇑(complexBasis α) = ((⇑) : AddChar α Complex -> α -> Complex) := by
  rw [complexBasis]; rw [coe_basisOfLinearIndependentOfCardEqFinrank]

variable {α}

@[simp]
/--
lemma `complexBasis_apply` / 引理 `complexBasis_apply`

English:
lemma complexBasis_apply
  given: (ψ : AddChar α Complex)
  statement: complexBasis α ψ = ψ
  proof: by rw [coe_complexBasis]

中文:
引理 complexBasis_apply
  条件: (ψ : 加法特征 α 复形)
  结论: complexBasis α ψ = ψ
  证明: by rw [coe_complexBasis]

Depends on / 依赖: coe_complexBasis
-/
lemma complexBasis_apply (ψ : AddChar α Complex) : complexBasis α ψ = ψ := by rw [coe_complexBasis]

/--
lemma `exists_apply_ne_zero` / 引理 `exists_apply_ne_zero`

English:
lemma exists_apply_ne_zero
  statement: (exists ψ : AddChar α Complex, ψ a != 1) ↔ a != 0
  proof: by
  refine ⟨?_, fun ha => ?_⟩
  · rintro ⟨ψ, hψ⟩ rfl
    exact hψ ψ.map_zero_eq_one
  classical
  by_contra! h
  let f : α -> Complex := fun b => if a = b then 1 else 0
  have h₀ := congr_fun ((complexBasis α).sum_repr f) 0
  have h₁ := congr_fun ((complexBasis α).sum_repr f) a
  simp only [complexBasis_apply, Fintype.sum_apply, Pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_eq_one, if_pos rfl, if_neg ha, f] at h₀ h₁
  exact one_ne_zero (h₁.symm.trans h₀)

中文:
引理 存在_apply_ne_zero
  结论: (存在 ψ : 加法特征 α 复形, ψ a != 1) ↔ a != 0
  证明: by
  refine ⟨?_, fun ha => ?_⟩
  · rintro ⟨ψ, hψ⟩ rfl
    exact hψ ψ.map_zero_eq_one
  classical
  by_contra! h
  let f : α -> Complex := fun b => if a = b then 1 else 0
  have h₀ := congr_fun ((complexBasis α).sum_repr f) 0
  have h₁ := congr_fun ((complexBasis α).sum_repr f) a
  simp only [complexBasis_apply, Fintype.sum_apply, Pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_eq_one, if_pos rfl, if_neg ha, f] at h₀ h₁
  exact one_ne_zero (h₁.symm.trans h₀)

Depends on / 依赖: Fintype, Fintype.sum_apply, Pi.smul_apply, classical, complexBasis, complexBasis_apply, congr_fun, if_neg, if_pos, map_zero_eq_one, mul_one, one_ne_zero, smul_apply, smul_eq_mul, sum_apply, sum_repr, symm.trans
-/
lemma exists_apply_ne_zero : (exists ψ : AddChar α Complex, ψ a != 1) ↔ a != 0 := by
  refine ⟨?_, fun ha => ?_⟩
  · rintro ⟨ψ, hψ⟩ rfl
    exact hψ ψ.map_zero_eq_one
  classical
  by_contra! h
  let f : α -> Complex := fun b => if a = b then 1 else 0
  have h₀ := congr_fun ((complexBasis α).sum_repr f) 0
  have h₁ := congr_fun ((complexBasis α).sum_repr f) a
  simp only [complexBasis_apply, Fintype.sum_apply, Pi.smul_apply, h, smul_eq_mul, mul_one,
    map_zero_eq_one, if_pos rfl, if_neg ha, f] at h₀ h₁
  exact one_ne_zero (h₁.symm.trans h₀)

/--
lemma `forall_apply_eq_zero` / 引理 `forall_apply_eq_zero`

English:
lemma forall_apply_eq_zero
  statement: (forall ψ : AddChar α Complex, ψ a = 1) ↔ a = 0
  proof: by
  simpa using exists_apply_ne_zero.not

中文:
引理 对任意_apply_eq_zero
  结论: (对任意 ψ : 加法特征 α 复形, ψ a = 1) ↔ a = 0
  证明: by
  simpa using exists_apply_ne_zero.not

Depends on / 依赖: exists_apply_ne_zero, exists_apply_ne_zero.not
-/
lemma forall_apply_eq_zero : (forall ψ : AddChar α Complex, ψ a = 1) ↔ a = 0 := by
  simpa using exists_apply_ne_zero.not

/--
lemma `doubleDualEmb_injective` / 引理 `doubleDualEmb_injective`

English:
lemma doubleDualEmb_injective
  statement: Injective (doubleDualEmb : α -> AddChar (AddChar α Complex) Complex)
  proof: doubleDualEmb.ker_eq_bot_iff.1 eq_bot_iff.2 fun a ha =>
    forall_apply_eq_zero.1 fun ψ => by simpa using! DFunLike.congr_fun ha (Additive.ofMul ψ)

中文:
引理 doubleDualEmb_injective
  结论: 单射 (doubleDualEmb : α -> 加法特征 (加法特征 α 复形) 复形)
  证明: doubleDualEmb.ker_eq_bot_iff.1 eq_bot_iff.2 fun a ha =>
    forall_apply_eq_zero.1 fun ψ => by simpa using! DFunLike.congr_fun ha (Additive.ofMul ψ)

Depends on / 依赖: Additive, Additive.ofMul, DFunLike, DFunLike.congr_fun, congr_fun, doubleDualEmb, doubleDualEmb.ker_eq_bot_iff, eq_bot_iff, forall_apply_eq_zero, ker_eq_bot_iff
-/
lemma doubleDualEmb_injective : Injective (doubleDualEmb : α -> AddChar (AddChar α Complex) Complex) :=
doubleDualEmb.ker_eq_bot_iff.1 eq_bot_iff.2 fun a ha =>
    forall_apply_eq_zero.1 fun ψ => by simpa using! DFunLike.congr_fun ha (Additive.ofMul ψ)

/--
lemma `doubleDualEmb_bijective` / 引理 `doubleDualEmb_bijective`

English:
lemma doubleDualEmb_bijective
  statement: Bijective (doubleDualEmb : α -> AddChar (AddChar α Complex) Complex)
  proof: by
  cases nonempty_fintype α
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨doubleDualEmb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]

中文:
引理 doubleDualEmb_bijective
  结论: 双射 (doubleDualEmb : α -> 加法特征 (加法特征 α 复形) 复形)
  证明: by
  cases nonempty_fintype α
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨doubleDualEmb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]

Depends on / 依赖: Fintype, Fintype.bijective_iff_injective_and_card, bijective_iff_injective_and_card, card_eq, card_eq.symm, card_eq.symm.trans, doubleDualEmb_injective, nonempty_fintype
-/
lemma doubleDualEmb_bijective : Bijective (doubleDualEmb : α -> AddChar (AddChar α Complex) Complex) := by
  cases nonempty_fintype α
  exact (Fintype.bijective_iff_injective_and_card _).2
    ⟨doubleDualEmb_injective, card_eq.symm.trans card_eq.symm⟩

@[simp]
/--
lemma `doubleDualEmb_inj` / 引理 `doubleDualEmb_inj`

English:
lemma doubleDualEmb_inj
  statement: (doubleDualEmb a : AddChar (AddChar α Complex) Complex) = doubleDualEmb b ↔ a = b
  proof: doubleDualEmb_injective.eq_iff

中文:
引理 doubleDualEmb_inj
  结论: (doubleDualEmb a : 加法特征 (加法特征 α 复形) 复形) = doubleDualEmb b ↔ a = b
  证明: doubleDualEmb_injective.eq_iff

Depends on / 依赖: doubleDualEmb_injective, doubleDualEmb_injective.eq_iff, eq_iff
-/
lemma doubleDualEmb_inj : (doubleDualEmb a : AddChar (AddChar α Complex) Complex) = doubleDualEmb b ↔ a = b :=
  doubleDualEmb_injective.eq_iff

/--
lemma `doubleDualEmb_eq_zero` / 引理 `doubleDualEmb_eq_zero`

English:
lemma doubleDualEmb_eq_zero
  statement: (doubleDualEmb a : AddChar (AddChar α Complex) Complex) = 0 ↔ a = 0
  proof: by
  rw [← map_zero doubleDualEmb]; rw [doubleDualEmb_inj]

中文:
引理 doubleDualEmb_eq_zero
  结论: (doubleDualEmb a : 加法特征 (加法特征 α 复形) 复形) = 0 ↔ a = 0
  证明: by
  rw [← map_zero doubleDualEmb]; rw [doubleDualEmb_inj]
-/
@[simp] lemma doubleDualEmb_eq_zero : (doubleDualEmb a : AddChar (AddChar α Complex) Complex) = 0 ↔ a = 0 := by
  rw [← map_zero doubleDualEmb]; rw [doubleDualEmb_inj]

/--
lemma `doubleDualEmb_ne_zero` / 引理 `doubleDualEmb_ne_zero`

English:
lemma doubleDualEmb_ne_zero
  statement: (doubleDualEmb a : AddChar (AddChar α Complex) Complex) != 0 ↔ a != 0
  proof: doubleDualEmb_eq_zero.not

中文:
引理 doubleDualEmb_ne_zero
  结论: (doubleDualEmb a : 加法特征 (加法特征 α 复形) 复形) != 0 ↔ a != 0
  证明: doubleDualEmb_eq_zero.not

Depends on / 依赖: doubleDualEmb_eq_zero, doubleDualEmb_eq_zero.not
-/
lemma doubleDualEmb_ne_zero : (doubleDualEmb a : AddChar (AddChar α Complex) Complex) != 0 ↔ a != 0 :=
  doubleDualEmb_eq_zero.not

/--
Definition of `doubleDualEquiv` / `doubleDualEquiv` 的定义

English:
definition doubleDualEquiv
  signature: : α ≃+ AddChar (AddChar α Complex) Complex
  body: .ofBijective _ doubleDualEmb_bijective

@[simp]

中文:
定义 doubleDualEquiv
  签名: : α ≃+ 加法特征 (加法特征 α 复形) 复形
  定义体: .ofBijective _ doubleDualEmb_bijective

@[simp]

Depends on / 依赖: doubleDualEmb_bijective, ofBijective
-/
def doubleDualEquiv : α ≃+ AddChar (AddChar α Complex) Complex := .ofBijective _ doubleDualEmb_bijective

@[simp]
/--
lemma `coe_doubleDualEquiv` / 引理 `coe_doubleDualEquiv`

English:
lemma coe_doubleDualEquiv
  statement: ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α Complex) Complex) = doubleDualEmb
  proof: rfl

中文:
引理 coe_doubleDualEquiv
  结论: ⇑(doubleDualEquiv : α ≃+ 加法特征 (加法特征 α 复形) 复形) = doubleDualEmb
  证明: rfl
-/
lemma coe_doubleDualEquiv : ⇑(doubleDualEquiv : α ≃+ AddChar (AddChar α Complex) Complex) = doubleDualEmb := rfl

/--
lemma `doubleDualEmb_doubleDualEquiv_symm_apply` / 引理 `doubleDualEmb_doubleDualEquiv_symm_apply`

English:
lemma doubleDualEmb_doubleDualEquiv_symm_apply
  given: (a : AddChar (AddChar α Complex) Complex)
  proof: doubleDualEquiv.apply_symm_apply _

中文:
引理 doubleDualEmb_doubleDualEquiv_symm_apply
  条件: (a : 加法特征 (加法特征 α 复形) 复形)
  证明: doubleDualEquiv.apply_symm_apply _
-/
@[simp] lemma doubleDualEmb_doubleDualEquiv_symm_apply (a : AddChar (AddChar α Complex) Complex) :
    doubleDualEmb (doubleDualEquiv.symm a) = a :=
  doubleDualEquiv.apply_symm_apply _

/--
lemma `doubleDualEquiv_symm_doubleDualEmb_apply` / 引理 `doubleDualEquiv_symm_doubleDualEmb_apply`

English:
lemma doubleDualEquiv_symm_doubleDualEmb_apply
  given: (a : AddChar (AddChar α Complex) Complex)
  proof: doubleDualEquiv.symm_apply_apply _

中文:
引理 doubleDualEquiv_symm_doubleDualEmb_apply
  条件: (a : 加法特征 (加法特征 α 复形) 复形)
  证明: doubleDualEquiv.symm_apply_apply _
-/
@[simp] lemma doubleDualEquiv_symm_doubleDualEmb_apply (a : AddChar (AddChar α Complex) Complex) :
    doubleDualEquiv.symm (doubleDualEmb a) = a := doubleDualEquiv.symm_apply_apply _

end Finite

/--
lemma `sum_apply_eq_ite` / 引理 `sum_apply_eq_ite`

English:
lemma sum_apply_eq_ite
  given: [Fintype α] [DecidableEq α] (a : α)
  proof: by
  simpa using sum_eq_ite (doubleDualEmb a : AddChar (AddChar α Complex) Complex)

中文:
引理 sum_apply_eq_ite
  条件: [有限类型 α] [DecidableEq α] (a : α)
  证明: by
  simpa using sum_eq_ite (doubleDualEmb a : AddChar (AddChar α Complex) Complex)

Depends on / 依赖: AddChar, doubleDualEmb, sum_eq_ite
-/
lemma sum_apply_eq_ite [Fintype α] [DecidableEq α] (a : α) :
    ∑ ψ : AddChar α Complex, ψ a = if a = 0 then (Fintype.card α : Complex) else 0 := by
  simpa using sum_eq_ite (doubleDualEmb a : AddChar (AddChar α Complex) Complex)

/--
lemma `expect_apply_eq_ite` / 引理 `expect_apply_eq_ite`

English:
lemma expect_apply_eq_ite
  given: [Finite α] [DecidableEq α] (a : α)
  proof: by
  simpa using expect_eq_ite (doubleDualEmb a : AddChar (AddChar α Complex) Complex)

中文:
引理 expect_apply_eq_ite
  条件: [有限 α] [DecidableEq α] (a : α)
  证明: by
  simpa using expect_eq_ite (doubleDualEmb a : AddChar (AddChar α Complex) Complex)

Depends on / 依赖: AddChar, doubleDualEmb, expect_eq_ite
-/
lemma expect_apply_eq_ite [Finite α] [DecidableEq α] (a : α) :
    𝔼 ψ : AddChar α Complex, ψ a = if a = 0 then 1 else 0 := by
  simpa using expect_eq_ite (doubleDualEmb a : AddChar (AddChar α Complex) Complex)

/--
lemma `sum_apply_eq_zero_iff_ne_zero` / 引理 `sum_apply_eq_zero_iff_ne_zero`

English:
lemma sum_apply_eq_zero_iff_ne_zero
  given: [Finite α]
  statement: ∑ ψ : AddChar α Complex, ψ a = 0 ↔ a != 0
  proof: by
  classical
  cases nonempty_fintype α
  rw [sum_apply_eq_ite]; rw [Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

中文:
引理 sum_apply_eq_zero_iff_ne_zero
  条件: [有限 α]
  结论: ∑ ψ : 加法特征 α 复形, ψ a = 0 ↔ a != 0
  证明: by
  classical
  cases nonempty_fintype α
  rw [sum_apply_eq_ite]; rw [Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

Depends on / 依赖: Fintype, Fintype.card_ne_zero, Nat.cast_ne_zero, Ne.ite_eq_right_iff, card_ne_zero, cast_ne_zero, classical, ite_eq_right_iff, nonempty_fintype, sum_apply_eq_ite
-/
lemma sum_apply_eq_zero_iff_ne_zero [Finite α] : ∑ ψ : AddChar α Complex, ψ a = 0 ↔ a != 0 := by
  classical
  cases nonempty_fintype α
  rw [sum_apply_eq_ite]; rw [Ne.ite_eq_right_iff]
  exact Nat.cast_ne_zero.2 Fintype.card_ne_zero

/--
lemma `sum_apply_ne_zero_iff_eq_zero` / 引理 `sum_apply_ne_zero_iff_eq_zero`

English:
lemma sum_apply_ne_zero_iff_eq_zero
  given: [Finite α]
  statement: ∑ ψ : AddChar α Complex, ψ a != 0 ↔ a = 0
  proof: sum_apply_eq_zero_iff_ne_zero.not_left

中文:
引理 sum_apply_ne_zero_iff_eq_zero
  条件: [有限 α]
  结论: ∑ ψ : 加法特征 α 复形, ψ a != 0 ↔ a = 0
  证明: sum_apply_eq_zero_iff_ne_zero.not_left

Depends on / 依赖: not_left, sum_apply_eq_zero_iff_ne_zero, sum_apply_eq_zero_iff_ne_zero.not_left
-/
lemma sum_apply_ne_zero_iff_eq_zero [Finite α] : ∑ ψ : AddChar α Complex, ψ a != 0 ↔ a = 0 :=
  sum_apply_eq_zero_iff_ne_zero.not_left

/--
lemma `expect_apply_eq_zero_iff_ne_zero` / 引理 `expect_apply_eq_zero_iff_ne_zero`

English:
lemma expect_apply_eq_zero_iff_ne_zero
  given: [Finite α]
  statement: 𝔼 ψ : AddChar α Complex, ψ a = 0 ↔ a != 0
  proof: by
  classical
  cases nonempty_fintype α
  rw [expect_apply_eq_ite]; rw [one_ne_zero.ite_eq_right_iff]

中文:
引理 expect_apply_eq_zero_iff_ne_zero
  条件: [有限 α]
  结论: 𝔼 ψ : 加法特征 α 复形, ψ a = 0 ↔ a != 0
  证明: by
  classical
  cases nonempty_fintype α
  rw [expect_apply_eq_ite]; rw [one_ne_zero.ite_eq_right_iff]

Depends on / 依赖: classical, expect_apply_eq_ite, ite_eq_right_iff, nonempty_fintype, one_ne_zero, one_ne_zero.ite_eq_right_iff
-/
lemma expect_apply_eq_zero_iff_ne_zero [Finite α] : 𝔼 ψ : AddChar α Complex, ψ a = 0 ↔ a != 0 := by
  classical
  cases nonempty_fintype α
  rw [expect_apply_eq_ite]; rw [one_ne_zero.ite_eq_right_iff]

/--
lemma `expect_apply_ne_zero_iff_eq_zero` / 引理 `expect_apply_ne_zero_iff_eq_zero`

English:
lemma expect_apply_ne_zero_iff_eq_zero
  given: [Finite α]
  statement: 𝔼 ψ : AddChar α Complex, ψ a != 0 ↔ a = 0
  proof: expect_apply_eq_zero_iff_ne_zero.not_left

中文:
引理 expect_apply_ne_zero_iff_eq_zero
  条件: [有限 α]
  结论: 𝔼 ψ : 加法特征 α 复形, ψ a != 0 ↔ a = 0
  证明: expect_apply_eq_zero_iff_ne_zero.not_left

Depends on / 依赖: expect_apply_eq_zero_iff_ne_zero, expect_apply_eq_zero_iff_ne_zero.not_left, not_left
-/
lemma expect_apply_ne_zero_iff_eq_zero [Finite α] : 𝔼 ψ : AddChar α Complex, ψ a != 0 ↔ a = 0 :=
  expect_apply_eq_zero_iff_ne_zero.not_left

end AddChar
