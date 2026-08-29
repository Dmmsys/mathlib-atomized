/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Syntax
public import Mathlib.ModelTheory.Semantics
public import Mathlib.ModelTheory.Algebra.Ring.Basic
public import Mathlib.Algebra.Field.MinimalAxioms
public import Mathlib.Data.Nat.Cast.Order.Ring

/-!
# The First-Order Theory of Fields

This file defines the first-order theory of fields as a theory over the language of rings.

## Main definitions

- `FirstOrder.Language.Theory.field` : the theory of fields
- `FirstOrder.Model.fieldOfModelField` : a model of the theory of fields on a type `K` that
  already has ring operations.
- `FirstOrder.Model.compatibleRingOfModelField` : shows that the ring operations on `K` given
  by `fieldOfModelField` are compatible with the ring operations on `K` given by the
  `Language.ring.Structure` instance.
-/

@[expose] public section

variable {K : Type*}

namespace FirstOrder

namespace Field

open Language FirstOrder.Ring Structure BoundedFormula

/--
Inductive type `FieldAxiom` / 归纳类型 `FieldAxiom`

English:
inductive FieldAxiom
  parameters: : Type
  constructors (9):
    - addAssoc: FieldAxiom
    - zeroAdd: FieldAxiom
    - negAddCancel: FieldAxiom
    - mulAssoc: FieldAxiom
    - mulComm: FieldAxiom
    - oneMul: FieldAxiom
    - existsInv: FieldAxiom
    - leftDistrib: FieldAxiom
    - existsPairNE: FieldAxiom

中文:
归纳类型 FieldAxiom
  参数: : Type
  构造子 (9 个):
    - addAssoc: FieldAxiom
    - zeroAdd: FieldAxiom
    - negAddCancel: FieldAxiom
    - mulAssoc: FieldAxiom
    - mulComm: FieldAxiom
    - oneMul: FieldAxiom
    - existsInv: FieldAxiom
    - leftDistrib: FieldAxiom
    - existsPairNE: FieldAxiom
-/
inductive FieldAxiom : Type
  | addAssoc : FieldAxiom
  | zeroAdd : FieldAxiom
  | negAddCancel : FieldAxiom
  | mulAssoc : FieldAxiom
  | mulComm : FieldAxiom
  | oneMul : FieldAxiom
  | existsInv : FieldAxiom
  | leftDistrib : FieldAxiom
  | existsPairNE : FieldAxiom

/-- The first-order sentence corresponding to each field axiom -/
@[simp]
/--
Definition of `FieldAxiom.toSentence` / `FieldAxiom.toSentence` 的定义

English:
definition FieldAxiom.toSentence
  signature: : FieldAxiom -> Language.ring.Sentence

中文:
定义 FieldAxiom.toSentence
  签名: : FieldAxiom -> Language.ring.Sentence
-/
def FieldAxiom.toSentence : FieldAxiom -> Language.ring.Sentence
  | .addAssoc => forall' forall' forall' (((&0 + &1) + &2) =' (&0 + (&1 + &2)))
  | .zeroAdd => forall' (((0 : Language.ring.Term _) + &0) =' &0)
  | .negAddCancel => forall' forall' ((-&0 + &0) =' 0)
  | .mulAssoc => forall' forall' forall' (((&0 * &1) * &2) =' (&0 * (&1 * &2)))
  | .mulComm => forall' forall' ((&0 * &1) =' (&1 * &0))
  | .oneMul => forall' (((1 : Language.ring.Term _) * &0) =' &0)
  | .existsInv => forall' (∼(&0 =' 0) ⟹ exists' ((&0 * &1) =' 1))
  | .leftDistrib => forall' forall' forall' ((&0 * (&1 + &2)) =' ((&0 * &1) + (&0 * &2)))
  | .existsPairNE => exists' exists' (∼(&0 =' &1))

/-- The Proposition corresponding to each field axiom -/
@[simp]
/--
Definition of `FieldAxiom.toProp` / `FieldAxiom.toProp` 的定义

English:
definition FieldAxiom.toProp
  signature: (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K]

中文:
定义 FieldAxiom.toProp
  签名: (K : 类型) [Add K] [Mul K] [Neg K] [Zero K] [One K]
-/
def FieldAxiom.toProp (K : Type*) [Add K] [Mul K] [Neg K] [Zero K] [One K] :
    FieldAxiom -> Prop
  | .addAssoc => forall x y z : K, (x + y) + z = x + (y + z)
  | .zeroAdd => forall x : K, 0 + x = x
  | .negAddCancel => forall x : K, -x + x = 0
  | .mulAssoc => forall x y z : K, (x * y) * z = x * (y * z)
  | .mulComm => forall x y : K, x * y = y * x
  | .oneMul => forall x : K, 1 * x = x
  | .existsInv => forall x : K, x != 0 -> exists y, x * y = 1
  | .leftDistrib => forall x y z : K, x * (y + z) = x * y + x * z
  | .existsPairNE => exists x y : K, x != y

/--
Definition of `_root_.FirstOrder.Language.Theory.field` / `_root_.FirstOrder.Language.Theory.field` 的定义

English:
definition _root_.FirstOrder.Language.Theory.field
  signature: : Language.ring.Theory
  body: Set.range FieldAxiom.toSentence

中文:
定义 _root_.FirstOrder.Language.Theory.field
  签名: : Language.ring.Theory
  定义体: Set.range FieldAxiom.toSentence

Depends on / 依赖: FieldAxiom, FieldAxiom.toSentence, Set.range, toSentence
-/
def _root_.FirstOrder.Language.Theory.field : Language.ring.Theory :=
  Set.range FieldAxiom.toSentence

/--
theorem `FieldAxiom.realize_toSentence_iff_toProp` / 定理 `FieldAxiom.realize_toSentence_iff_toProp`

English:
theorem FieldAxiom.realize_toSentence_iff_toProp
  statement: {K : Type*}
  proof: by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]

中文:
定理 FieldAxiom.realize_toSentence_iff_toProp
  结论: {K : 类型}
  证明: by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]

Depends on / 依赖: Fin.snoc, Formula, Formula.Realize, Realize, Sentence, Sentence.Realize
-/
theorem FieldAxiom.realize_toSentence_iff_toProp {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    (ax : FieldAxiom) :
    (K ⊨ (ax.toSentence : Sentence Language.ring)) ↔ ax.toProp K := by
  cases ax <;>
  simp [Sentence.Realize, Formula.Realize, Fin.snoc]

/--
theorem `FieldAxiom.toProp_of_model` / 定理 `FieldAxiom.toProp_of_model`

English:
theorem FieldAxiom.toProp_of_model
  statement: {K : Type*}
  proof: (FieldAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.field
      (Set.mem_range_self ax))

中文:
定理 FieldAxiom.toProp_of_model
  结论: {K : 类型}
  证明: (FieldAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.field
      (Set.mem_range_self ax))

Depends on / 依赖: FieldAxiom, FieldAxiom.realize_toSentence_iff_toProp, Set.mem_range_self, Theory, Theory.field, Theory.realize_sentence_of_mem, mem_range_self, realize_sentence_of_mem, realize_toSentence_iff_toProp
-/
theorem FieldAxiom.toProp_of_model {K : Type*}
    [Add K] [Mul K] [Neg K] [Zero K] [One K] [CompatibleRing K]
    [Theory.field.Model K] (ax : FieldAxiom) : ax.toProp K :=
  (FieldAxiom.realize_toSentence_iff_toProp ax).1
    (Theory.realize_sentence_of_mem Theory.field
      (Set.mem_range_self ax))

open FieldAxiom

/--
Definition of `fieldOfModelField` / `fieldOfModelField` 的定义

English:
abbreviation fieldOfModelField
  signature: (K : Type*) [Language.ring.Structure K]
  body: letI : DecidableEq K := Classical.decEq K
  letI := addOfRingStructure K
  letI := mulOfRingStructure K
  letI := negOfRingStructure K
  letI := zeroOfRingStructure K
  letI := oneOfRingStructure K
  letI := compatibleRingOfRingStructure K
  have exists_inv : forall x : K, x != 0 -> exists y : K, x 

中文:
缩写 fieldOfModelField
  签名: (K : 类型) [Language.ring.Structure K]
  定义体: letI : DecidableEq K := Classical.decEq K
  letI := addOfRingStructure K
  letI := mulOfRingStructure K
  letI := negOfRingStructure K
  letI := zeroOfRingStructure K
  letI := oneOfRingStructure K
  letI := compatibleRingOfRingStructure K
  have exists_inv : forall x : K, x != 0 -> exists y : K, x 

Depends on / 依赖: Classical, Classical.choose, Classical.decEq, DecidableEq, Field.ofMinimalAxioms, addAssoc, addAssoc.toProp_of_model, addOfRingStructure, compatibleRingOfRingStructure, existsInv, existsInv.toProp_of_model, exists_inv, mulOfRingStructure, negAddCancel, negAddCancel.t, negOfRingStructure, ofMinimalAxioms, oneOfRingStructure, toProp_of_model, zeroAdd
-/
noncomputable abbrev fieldOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : Field K :=
  letI : DecidableEq K := Classical.decEq K
  letI := addOfRingStructure K
  letI := mulOfRingStructure K
  letI := negOfRingStructure K
  letI := zeroOfRingStructure K
  letI := oneOfRingStructure K
  letI := compatibleRingOfRingStructure K
  have exists_inv : forall x : K, x != 0 -> exists y : K, x * y = 1 :=
    existsInv.toProp_of_model
  letI : Inv K := ⟨fun x => if hx0 : x = 0 then 0 else Classical.choose (exists_inv x hx0)⟩
  Field.ofMinimalAxioms K
    addAssoc.toProp_of_model
    zeroAdd.toProp_of_model
    negAddCancel.toProp_of_model
    mulAssoc.toProp_of_model
    mulComm.toProp_of_model
    oneMul.toProp_of_model
    (fun x hx0 => show x * (dite _ _ _) = _ from
        (dif_neg hx0).symm ▸ Classical.choose_spec (existsInv.toProp_of_model x hx0))
    (dif_pos rfl)
    leftDistrib.toProp_of_model
    existsPairNE.toProp_of_model

section

attribute [local instance] fieldOfModelField

/--
Definition of `compatibleRingOfModelField` / `compatibleRingOfModelField` 的定义

English:
abbreviation compatibleRingOfModelField
  signature: (K : Type*) [Language.ring.Structure K]
  body: compatibleRingOfRingStructure K

中文:
缩写 compatibleRingOfModelField
  签名: (K : 类型) [Language.ring.Structure K]
  定义体: compatibleRingOfRingStructure K

Depends on / 依赖: compatibleRingOfRingStructure
-/
noncomputable abbrev compatibleRingOfModelField (K : Type*) [Language.ring.Structure K]
    [Theory.field.Model K] : CompatibleRing K :=
  compatibleRingOfRingStructure K

end

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Field
  signature: K] [CompatibleRing K] : Theory.field.Model K
  body: { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)]
      cases a with
      | existsPairNE => exact exists_pair_ne K
      | existsInv => exact fun x hx0 => ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
      | addAs

中文:
实例 [Field
  签名: K] [CompatibleRing K] : Theory.field.Model K
  定义体: { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)]
      cases a with
      | existsPairNE => exact exists_pair_ne K
      | existsInv => exact fun x hx0 => ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
      | addAs

Depends on / 依赖: Set.mem_range, Theory, Theory.field, a.realize_toSentence_iff_toProp, addAssoc, add_assoc, existsInv, existsPairNE, exists_imp, exists_pair_ne, leftDistrib, mem_range, mulAssoc, mulComm, mul_add, mul_assoc, mul_comm, negAddCancel, neg_add_cancel, oneMul
-/
instance [Field K] [CompatibleRing K] : Theory.field.Model K :=
  { realize_of_mem := by
      simp only [Theory.field, Set.mem_range, exists_imp]
      rintro φ a rfl
      rw [a.realize_toSentence_iff_toProp (K := K)]
      cases a with
      | existsPairNE => exact exists_pair_ne K
      | existsInv => exact fun x hx0 => ⟨x⁻¹, mul_inv_cancel₀ hx0⟩
      | addAssoc => exact add_assoc
      | zeroAdd => exact zero_add
      | negAddCancel => exact neg_add_cancel
      | mulAssoc => exact mul_assoc
      | mulComm => exact mul_comm
      | oneMul => exact one_mul
      | leftDistrib => exact mul_add }

end Field

end FirstOrder
