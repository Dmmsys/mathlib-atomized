/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Preadditive.Basic

/-!
# The category of additive commutative groups is preadditive.
-/

@[expose] public section

assert_not_exists Subgroup

open CategoryTheory

universe u

namespace AddCommGrpCat

variable {M N : AddCommGrpCat.{u}}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (M ⟶ N)
  body: ofHom (f.hom + g.hom)

中文:
实例 :
  签名: Add (M ⟶ N)
  定义体: ofHom (f.hom + g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)

/--
lemma `hom_add` / 引理 `hom_add`

English:
lemma hom_add
  given: (f g : M ⟶ N)
  statement: (f + g).hom = f.hom + g.hom
  proof: rfl

中文:
引理 hom_add
  条件: (f g : M ⟶ N)
  结论: (f + g).hom = f.hom + g.hom
  证明: rfl
-/
@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl

/--
lemma `hom_add_apply` / 引理 `hom_add_apply`

English:
lemma hom_add_apply
  given: {P Q : AddCommGrpCat} (f g : P ⟶ Q) (x : P)
  statement: (f + g) x = f x + g x
  proof: rfl

中文:
引理 hom_add_apply
  条件: {P Q : AddCommGrpCat} (f g : P ⟶ Q) (x : P)
  结论: (f + g) x = f x + g x
  证明: rfl
-/
lemma hom_add_apply {P Q : AddCommGrpCat} (f g : P ⟶ Q) (x : P) : (f + g) x = f x + g x := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (M ⟶ N)
  body: ofHom 0

中文:
实例 :
  签名: Zero (M ⟶ N)
  定义体: ofHom 0
-/
instance : Zero (M ⟶ N) where
  zero := ofHom 0

/--
lemma `hom_zero` / 引理 `hom_zero`

English:
lemma hom_zero
  statement: (0 : M ⟶ N).hom = 0
  proof: rfl

中文:
引理 hom_zero
  结论: (0 : M ⟶ N).hom = 0
  证明: rfl
-/
@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Nat (M ⟶ N)
  body: ofHom (n • f.hom)

中文:
实例 :
  签名: SMul 自然数 (M ⟶ N)
  定义体: ofHom (n • f.hom)

Depends on / 依赖: f.hom
-/
instance : SMul Nat (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

/--
lemma `hom_nsmul` / 引理 `hom_nsmul`

English:
lemma hom_nsmul
  given: (n : Nat) (f : M ⟶ N)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 hom_nsmul
  条件: (n : 自然数) (f : M ⟶ N)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
@[simp] lemma hom_nsmul (n : Nat) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (M ⟶ N)
  body: ofHom (-f.hom)

中文:
实例 :
  签名: Neg (M ⟶ N)
  定义体: ofHom (-f.hom)

Depends on / 依赖: f.hom
-/
instance : Neg (M ⟶ N) where
  neg f := ofHom (-f.hom)

/--
lemma `hom_neg` / 引理 `hom_neg`

English:
lemma hom_neg
  given: (f : M ⟶ N)
  statement: (-f).hom = -f.hom
  proof: rfl

中文:
引理 hom_neg
  条件: (f : M ⟶ N)
  结论: (-f).hom = -f.hom
  证明: rfl
-/
@[simp] lemma hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (M ⟶ N)
  body: ofHom (f.hom - g.hom)

中文:
实例 :
  签名: Sub (M ⟶ N)
  定义体: ofHom (f.hom - g.hom)

Depends on / 依赖: f.hom, g.hom
-/
instance : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)

/--
lemma `hom_sub` / 引理 `hom_sub`

English:
lemma hom_sub
  given: (f g : M ⟶ N)
  statement: (f - g).hom = f.hom - g.hom
  proof: rfl

中文:
引理 hom_sub
  条件: (f g : M ⟶ N)
  结论: (f - g).hom = f.hom - g.hom
  证明: rfl
-/
@[simp] lemma hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul Int (M ⟶ N)
  body: ofHom (n • f.hom)

中文:
实例 :
  签名: SMul 整数 (M ⟶ N)
  定义体: ofHom (n • f.hom)

Depends on / 依赖: GrpObj, GrpObj.left_inv, GrpObj.right_inv, f.hom, left_inv, ofAlgHom, right_inv, unop.hom
-/
instance : SMul Int (M ⟶ N) where
  smul n f := ofHom (n • f.hom)

/--
lemma `hom_zsmul` / 引理 `hom_zsmul`

English:
lemma hom_zsmul
  given: (n : Int) (f : M ⟶ N)
  statement: (n • f).hom = n • f.hom
  proof: rfl

中文:
引理 hom_zsmul
  条件: (n : 整数) (f : M ⟶ N)
  结论: (n • f).hom = n • f.hom
  证明: rfl
-/
@[simp] lemma hom_zsmul (n : Int) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl

instance (P Q : AddCommGrpCat) : AddCommGroup (P ⟶ Q) :=
  Function.Injective.addCommGroup (Hom.hom) ConcreteCategory.hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Preadditive AddCommGrpCat

中文:
实例 :
  签名: Preadditive AddCommGrpCat

Depends on / 依赖: CommAlgCat, CommAlgCat.of, IsCommMonObj
-/
instance : Preadditive AddCommGrpCat where

/-- `AddCommGrpCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
/--
Definition of `homAddEquiv` / `homAddEquiv` 的定义

English:
definition homAddEquiv
  signature: : (M ⟶ N) ≃+ (M ->+ N)
  body: { ConcreteCategory.homEquiv (C := AddCommGrpCat) with
    map_add' _ _ := rfl }

中文:
定义 homAddEquiv
  签名: : (M ⟶ N) ≃+ (M ->+ N)
  定义体: { ConcreteCategory.homEquiv (C := AddCommGrpCat) with
    map_add' _ _ := rfl }

Depends on / 依赖: AddCommGrpCat, ConcreteCategory, ConcreteCategory.homEquiv, homEquiv, map_add
-/
def homAddEquiv : (M ⟶ N) ≃+ (M ->+ N) :=
  { ConcreteCategory.homEquiv (C := AddCommGrpCat) with
    map_add' _ _ := rfl }

end AddCommGrpCat
