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

/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (M ⟶ N) where
  add f g := ofHom (f.hom + g.hom)
/-
**AddCommGrpCat.hom_add** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {M N : AddCommGrpCat} (f g : M ⟶ N), AddCommGrpCat.Hom.hom (f + g) = Add
CommGrpCat.Hom.hom f + AddCommGrpCat.Hom.hom g
参数：f g : M ⟶ N；f + g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_add (f g : M ⟶ N) : (f + g).hom = f.hom + g.hom := rfl
/-
**AddCommGrpCat.hom_add_apply** 是 Mathlib 中的一个引理，位于命名空间 `AddCommGrpCat`。
形式化陈述：hom_add_apply {P Q : AddCommGrpCat} (f g : P ⟶ Q) (x : P) : (f + g) x = f 
x + g x
参数：f g : P ⟶ Q；x : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma hom_add_apply {P Q : AddCommGrpCat} (f g : P ⟶ Q) (x : P) : (f + g) x = f x + g x := rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (M ⟶ N) where
  zero := ofHom 0
/-
**AddCommGrpCat.hom_zero** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {M N : AddCommGrpCat}, AddCommGrpCat.Hom.hom 0 = 0
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_zero : (0 : M ⟶ N).hom = 0 := rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℕ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)
/-
**AddCommGrpCat.hom_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {M N : AddCommGrpCat} (n : ℕ) (f : M ⟶ N), AddCommGrpCat.Hom.hom (n • f)
 = n • AddCommGrpCat.Hom.hom f
参数：n : ℕ；f : M ⟶ N；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_nsmul (n : ℕ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (M ⟶ N) where
  neg f := ofHom (-f.hom)
/-
**AddCommGrpCat.hom_neg** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {M N : AddCommGrpCat} (f : M ⟶ N), AddCommGrpCat.Hom.hom (-f) = -AddComm
GrpCat.Hom.hom f
参数：f : M ⟶ N；-f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_neg (f : M ⟶ N) : (-f).hom = -f.hom := rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (M ⟶ N) where
  sub f g := ofHom (f.hom - g.hom)
/-
**AddCommGrpCat.hom_sub** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {M N : AddCommGrpCat} (f g : M ⟶ N), AddCommGrpCat.Hom.hom (f - g) = Add
CommGrpCat.Hom.hom f - AddCommGrpCat.Hom.hom g
参数：f g : M ⟶ N；f - g。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_sub (f g : M ⟶ N) : (f - g).hom = f.hom - g.hom := rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul ℤ (M ⟶ N) where
  smul n f := ofHom (n • f.hom)
/-
**AddCommGrpCat.hom_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `AddCommGrpCat`。
形式化陈述：∀ {M N : AddCommGrpCat} (n : ℤ) (f : M ⟶ N), AddCommGrpCat.Hom.hom (n • f)
 = n • AddCommGrpCat.Hom.hom f
参数：n : ℤ；f : M ⟶ N；n • f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma hom_zsmul (n : ℤ) (f : M ⟶ N) : (n • f).hom = n • f.hom := rfl
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (P Q : AddCommGrpCat) : AddCommGroup (P ⟶ Q) :=
  Function.Injective.addCommGroup (Hom.hom) ConcreteCategory.hom_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
/-
**AddCommGrpCat.** 是 Mathlib 中的一个实例，位于命名空间 `AddCommGrpCat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preadditive AddCommGrpCat where

/-- `AddCommGrpCat.Hom.hom` bundled as an additive equivalence. -/
@[simps!]
/-
**AddCommGrpCat.homAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AddCommGrpCat`。
形式化陈述：homAddEquiv : (M ⟶ N) ≃+ (M ->+ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddCommGrpCat.Hom.hom` bundled as an additive equivalence.
-/
def homAddEquiv : (M ⟶ N) ≃+ (M →+ N) :=
  { ConcreteCategory.homEquiv (C := AddCommGrpCat) with
    map_add' _ _ := rfl }

end AddCommGrpCat

