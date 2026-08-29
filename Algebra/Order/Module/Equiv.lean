/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Order.Group.Equiv
public import Mathlib.Algebra.Order.Module.Synonym

/-!
# Linear equivalence for order type synonyms
-/

@[expose] public section

variable (α β : Type*)
variable [Semiring α] [AddCommMonoid β] [Module α β]

/--
Definition of `toLexLinearEquiv` / `toLexLinearEquiv` 的定义

English:
definition toLexLinearEquiv
  signature: : β ≃ₗ[α] Lex β
  body: (toLexAddEquiv β).toLinearEquiv toLex_smul

中文:
定义 toLexLinearEquiv
  签名: : β ≃ₗ[α] Lex β
  定义体: (toLexAddEquiv β).toLinearEquiv toLex_smul

Depends on / 依赖: toLexAddEquiv, toLex_smul, toLinearEquiv
-/
def toLexLinearEquiv : β ≃ₗ[α] Lex β := (toLexAddEquiv β).toLinearEquiv toLex_smul

/--
Definition of `ofLexLinearEquiv` / `ofLexLinearEquiv` 的定义

English:
definition ofLexLinearEquiv
  signature: : Lex β ≃ₗ[α] β
  body: (ofLexAddEquiv β).toLinearEquiv ofLex_smul

中文:
定义 ofLexLinearEquiv
  签名: : Lex β ≃ₗ[α] β
  定义体: (ofLexAddEquiv β).toLinearEquiv ofLex_smul

Depends on / 依赖: ofLexAddEquiv, ofLex_smul, toLinearEquiv
-/
def ofLexLinearEquiv : Lex β ≃ₗ[α] β := (ofLexAddEquiv β).toLinearEquiv ofLex_smul

/--
lemma `coe_toLexLinearEquiv` / 引理 `coe_toLexLinearEquiv`

English:
lemma coe_toLexLinearEquiv
  statement: ⇑(toLexLinearEquiv α β) = toLex
  proof: rfl

中文:
引理 coe_toLexLinearEquiv
  结论: ⇑(toLexLinearEquiv α β) = toLex
  证明: rfl
-/
@[simp] lemma coe_toLexLinearEquiv : ⇑(toLexLinearEquiv α β) = toLex := rfl
/--
lemma `coe_ofLexLinearEquiv` / 引理 `coe_ofLexLinearEquiv`

English:
lemma coe_ofLexLinearEquiv
  statement: ⇑(ofLexLinearEquiv α β) = ofLex
  proof: rfl

中文:
引理 coe_ofLexLinearEquiv
  结论: ⇑(ofLexLinearEquiv α β) = ofLex
  证明: rfl
-/
@[simp] lemma coe_ofLexLinearEquiv : ⇑(ofLexLinearEquiv α β) = ofLex := rfl

/--
lemma `symm_toLexLinearEquiv` / 引理 `symm_toLexLinearEquiv`

English:
lemma symm_toLexLinearEquiv
  statement: (toLexLinearEquiv α β).symm = ofLexLinearEquiv α β
  proof: rfl

中文:
引理 symm_toLexLinearEquiv
  结论: (toLexLinearEquiv α β).symm = ofLexLinearEquiv α β
  证明: rfl
-/
@[simp] lemma symm_toLexLinearEquiv : (toLexLinearEquiv α β).symm = ofLexLinearEquiv α β := rfl
/--
lemma `symm_ofLexLinearEquiv` / 引理 `symm_ofLexLinearEquiv`

English:
lemma symm_ofLexLinearEquiv
  statement: (ofLexLinearEquiv α β).symm = toLexLinearEquiv α β
  proof: rfl

中文:
引理 symm_ofLexLinearEquiv
  结论: (ofLexLinearEquiv α β).symm = toLexLinearEquiv α β
  证明: rfl
-/
@[simp] lemma symm_ofLexLinearEquiv : (ofLexLinearEquiv α β).symm = toLexLinearEquiv α β := rfl
