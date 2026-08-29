/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Order.Group.End
public import Mathlib.Order.RelIso.Basic

/-!
# Tautological action by relation automorphisms
-/

@[expose] public section

assert_not_exists MonoidWithZero

namespace RelHom
variable {α : Type*} {r : α -> α -> Prop}

/--
Instance `applyMulAction` / 实例 `applyMulAction`

English:
instance applyMulAction
  signature: : MulAction (r ->r r) α where
  body: (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 applyMulAction
  签名: : 乘法作用 (r ->r r) α where
  定义体: (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
-/
instance applyMulAction : MulAction (r ->r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (f : r ->r r) (a : α)
  statement: f • a = f a
  proof: rfl

中文:
引理 smul_def
  条件: (f : r ->r r) (a : α)
  结论: f • a = f a
  证明: rfl
-/
@[simp] lemma smul_def (f : r ->r r) (a : α) : f • a = f a := rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (r ->r r) α where eq_of_smul_eq_smul h
  body: RelHom.ext h

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (r ->r r) α where eq_of_smul_eq_smul h
  定义体: RelHom.ext h

Depends on / 依赖: RelHom, RelHom.ext
-/
instance apply_faithfulSMul : FaithfulSMul (r ->r r) α where eq_of_smul_eq_smul h := RelHom.ext h

end RelHom

namespace RelEmbedding
variable {α : Type*} {r : α -> α -> Prop}

/--
Instance `applyMulAction` / 实例 `applyMulAction`

English:
instance applyMulAction
  signature: : MulAction (r ↪r r) α where
  body: (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 applyMulAction
  签名: : 乘法作用 (r ↪r r) α where
  定义体: (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
-/
instance applyMulAction : MulAction (r ↪r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (f : r ↪r r) (a : α)
  statement: f • a = f a
  proof: rfl

中文:
引理 smul_def
  条件: (f : r ↪r r) (a : α)
  结论: f • a = f a
  证明: rfl
-/
@[simp] lemma smul_def (f : r ↪r r) (a : α) : f • a = f a := rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (r ↪r r) α where eq_of_smul_eq_smul h
  body: ext h

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (r ↪r r) α where eq_of_smul_eq_smul h
  定义体: ext h
-/
instance apply_faithfulSMul : FaithfulSMul (r ↪r r) α where eq_of_smul_eq_smul h := ext h

end RelEmbedding

namespace RelIso
variable {α : Type*} {r : α -> α -> Prop}

/--
Instance `applyMulAction` / 实例 `applyMulAction`

English:
instance applyMulAction
  signature: : MulAction (r ≃r r) α where
  body: (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

中文:
实例 applyMulAction
  签名: : 乘法作用 (r ≃r r) α where
  定义体: (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
-/
instance applyMulAction : MulAction (r ≃r r) α where
  smul := (⇑)
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/--
lemma `smul_def` / 引理 `smul_def`

English:
lemma smul_def
  given: (f : r ≃r r) (a : α)
  statement: f • a = f a
  proof: rfl

中文:
引理 smul_def
  条件: (f : r ≃r r) (a : α)
  结论: f • a = f a
  证明: rfl
-/
@[simp] lemma smul_def (f : r ≃r r) (a : α) : f • a = f a := rfl

/--
Instance `apply_faithfulSMul` / 实例 `apply_faithfulSMul`

English:
instance apply_faithfulSMul
  signature: : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h
  body: RelIso.ext h

中文:
实例 apply_faithfulSMul
  签名: : 忠实标量乘法 (r ≃r r) α where eq_of_smul_eq_smul h
  定义体: RelIso.ext h

Depends on / 依赖: RelIso, RelIso.ext
-/
instance apply_faithfulSMul : FaithfulSMul (r ≃r r) α where eq_of_smul_eq_smul h := RelIso.ext h

end RelIso
