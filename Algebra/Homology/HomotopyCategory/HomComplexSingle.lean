/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Cochains from or to single complexes

We introduce constructors `Cochain.fromSingleMk` and `Cocycle.fromSingleMk`
for cochains and cocycles from a single complex. We also introduce similar
definitions for cochains and cocycles to a single complex.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

namespace HomComplex

variable {X : C} {K : CochainComplex C ℤ}

namespace Cochain

/-- Constructor for cochains from a single complex. -/
@[nolint unusedArguments]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk** 是 Mathlib 中的一个定义，位于命名空间 `Coch
ainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (_ : p + n = q) : Cocha
in ((singleFunctor C p).obj X) K n
参数：f : X ⟶ K.X q；_ : p + n = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cochains from a single complex.
-/
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (_ : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f) n

set_option backward.isDefEq.respectTransparency false in
variable (X K) in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_zero** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_zero (p q n : Int) (h : p + n = q) : fromSingleMk (X
参数：p q n : Int；h : p + n = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用引理 `CochainComplex.HomComplex.Cochain.single_zero`：single_zero (p q n : Int)
 : (single (p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_v** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_v {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : (fr
omSingleMk f h).v p q h = (HomologicalComplex.singleObjXSelf (.up Int) p X).hom 
≫ f
参数：f : X ⟶ K.X q；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v`：single_v {p q : Int} (f : K.
X p ⟶ L.X q) (n : Int) (hpq : p + n = q) : (single f n).v p q hpq = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_v {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    (fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f := by
  simp [fromSingleMk]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_v_eq_zero** 是 Mathlib 中的一个引理，位于
命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_v_eq_zero {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = 
q) (p' q' : Int) (hpq' : p' + n = q') (hp' : p' != p) : (fromSingleMk f h).v p' 
q' hpq' = 0
参数：f : X ⟶ K.X q；h : p + n = q；p' q' : Int；hpq' : p' + n = q'；hp' : p' != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v_eq_zero`：single_v_eq_zero {p 
q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q') (hp' :
 p' != p) : (single f n).v p' q' hpq' = …
-/
lemma fromSingleMk_v_eq_zero {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (fromSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (n' q' : ℤ) (h' : p + n' = q') :
    δ n n' (fromSingleMk f h) = fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
/-- Cochains of degree `n` from `(singleFunctor C p).obj X` to `K` identify
to `X ⟶ K.X q` when `p + n = q`. -/
/-
**CochainComplex.HomComplex.Cochain.fromSingleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleEquiv {p q n : Int} (h : p + n = q) : Cochain ((singleFunctor C 
p).obj X) K n ≃+ (X ⟶ K.X q) where toFun α
参数：h : p + n = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cochains of degree `n` from `(singleFunctor C p).obj X` to `K` identify
to `X ⟶ K.X q` when `p + n = q`.
-/
noncomputable def fromSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n ≃+ (X ⟶ K.X q) where
  toFun α := (HomologicalComplex.singleObjXSelf (.up ℤ) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk** 是 Mathlib 中的一
个引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleEquiv_fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p 
+ n = q) : fromSingleEquiv h (fromSingleMk f h) = f
参数：f : X ⟶ K.X q；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_v`：fromSingleMk_v {p q : 
Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : (fromSingleMk f h).v p q h = (H
omologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleEquiv_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleEquiv h (fromSingleMk f h) = f := by
  simp [fromSingleEquiv]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_add** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_add {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) :
 fromSingleMk (f + g) h = fromSingleMk f h + fromSingleMk g h
参数：f g : X ⟶ K.X q；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1
 : Add N] (f : M ≃+ N) (x y : M), f (x + y) = f x + f y
-/
lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f + g) h = fromSingleMk f h + fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_add _ _

@[simp]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_sub** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_sub {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) :
 fromSingleMk (f - g) h = fromSingleMk f h - fromSingleMk g h
参数：f g : X ⟶ K.X q；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
-/
lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f - g) h = fromSingleMk f h - fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_sub _ _

@[simp]
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_neg** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_neg {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : f
romSingleMk (-f) h = -fromSingleMk f h
参数：f : X ⟶ K.X q；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_neg`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x : G), h (-x) = -h x
-/
lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (-f) h = -fromSingleMk f h :=
  (fromSingleEquiv h).symm.map_neg _
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_surjective {p n : Int} (α : Cochain ((singleFunctor C p).obj 
X) K n) (q : Int) (h : p + n = q) : exists (f : X ⟶ K.X q), fromSingleMk f h = α
参数：α : Cochain ((singleFunctor C p).obj X) K n；q : Int；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [ins
t_1 : Add N] (e : M ≃+ N), Function.Surjective ⇑e
-/
lemma fromSingleMk_surjective {p n : ℤ} (α : Cochain ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) :
    ∃ (f : X ⟶ K.X q), fromSingleMk f h = α :=
  (fromSingleEquiv h).symm.surjective α

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_precomp** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : Int} (f : X ⟶ K.X q) {n 
: Int} (h : p + n = q) : fromSingleMk (g ≫ f) h = (Cochain.ofHom ((singleFunctor
 C p).map g)).comp (fromSingleMk f h) (zero_add n)
参数：g : X' ⟶ X；f : X ⟶ K.X q；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_v`：fromSingleMk_v {p q : 
Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : (fromSingleMk f h).v p q h = (H
omologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `HomologicalComplex.single_map_f_self`：single_map_f_self (j : ι) {A B : V
} (f : A ⟶ B) : ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫ f ≫ (s
ingleObjXSelf c j B).inv
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_precomp
    {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (g ≫ f) h =
      (Cochain.ofHom ((singleFunctor C p).map g)).comp (fromSingleMk f h) (zero_add n) := by
  apply (fromSingleEquiv h).injective
  simp [fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：fromSingleMk_postcomp {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q
) {L : CochainComplex C Int} (g : K ⟶ L) : fromSingleMk (f ≫ g.f q) h = (fromSin
gleMk f h).comp (.ofHom g) (add_zero n)
参数：f : X ⟶ K.X q；h : p + n = q；g : K ⟶ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_v`：fromSingleMk_v {p q : 
Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : (fromSingleMk f h).v p q h = (H
omologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h =
      (fromSingleMk f h).comp (.ofHom g) (add_zero n) :=
  (fromSingleEquiv h).injective (by simp [fromSingleEquiv, singleFunctor, singleFunctors])

/-- Constructor for cochains to a single complex. -/
@[nolint unusedArguments]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (_ : p + n = q) : Cochain
 K ((singleFunctor C q).obj X) n
参数：f : K.X p ⟶ X；_ : p + n = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cochains to a single complex.
-/
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (_ : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n :=
  Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv) n

set_option backward.isDefEq.respectTransparency false in
variable (X K) in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_zero** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_zero (p q n : Int) (h : p + n = q) : toSingleMk (X
参数：p q n : Int；h : p + n = q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用引理 `CochainComplex.HomComplex.Cochain.single_zero`：single_zero (p q n : Int)
 : (single (p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    toSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [toSingleMk]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_v {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : (toSi
ngleMk f h).v p q h = f ≫ (HomologicalComplex.singleObjXSelf (.up Int) q X).inv
参数：f : K.X p ⟶ X；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v`：single_v {p q : Int} (f : K.
X p ⟶ L.X q) (n : Int) (hpq : p + n = q) : (single f n).v p q hpq = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_v {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    (toSingleMk f h).v p q h =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv := by
  simp [toSingleMk]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_v_eq_zero** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_v_eq_zero {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q)
 (p' q' : Int) (hpq' : p' + n = q') (hp' : p' != p) : (toSingleMk f h).v p' q' h
pq' = 0
参数：f : K.X p ⟶ X；h : p + n = q；p' q' : Int；hpq' : p' + n = q'；hp' : p' != p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.single_v_eq_zero`：single_v_eq_zero {p 
q : Int} (f : K.X p ⟶ L.X q) (n : Int) (p' q' : Int) (hpq' : p' + n = q') (hp' :
 p' != p) : (single f n).v p' q' hpq' = …
-/
lemma toSingleMk_v_eq_zero {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (toSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (n' p' : ℤ) (h' : p' + n' = q) :
    δ n n' (toSingleMk f h) = n'.negOnePow • toSingleMk (K.d p' p ≫ f) h' := by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

set_option backward.isDefEq.respectTransparency false in
/-- Cochains of degree `n` from `(singleFunctor C q).obj X` to `K` identify
to `K.X p ⟶ X` when `p + n = q`. -/
/-
**CochainComplex.HomComplex.Cochain.toSingleEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex.HomComplex.Cochain`。
形式化陈述：toSingleEquiv {p q n : Int} (h : p + n = q) : Cochain K ((singleFunctor C 
q).obj X) n ≃+ (K.X p ⟶ X) where toFun α
参数：h : p + n = q。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Cochains of degree `n` from `(singleFunctor C q).obj X` to `K` identify
to `K.X p ⟶ X` when `p + n = q`.
-/
noncomputable def toSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n ≃+ (K.X p ⟶ X) where
  toFun α := α.v p q h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).hom
  invFun f := toSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hq : q' = q
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  right_inv f := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.toSingleEquiv_toSingleMk** 是 Mathlib 中的一个引理，
位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：toSingleEquiv_toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n 
= q) : toSingleEquiv h (toSingleMk f h) = f
参数：f : K.X p ⟶ X；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_v`：toSingleMk_v {p q : Int}
 (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : (toSingleMk f h).v p q h = f ≫ (Hom
ologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleEquiv_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleEquiv h (toSingleMk f h) = f := by
  simp [toSingleEquiv]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_add** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_add {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) : t
oSingleMk (f + g) h = toSingleMk f h + toSingleMk g h
参数：f g : K.X p ⟶ X；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst_1
 : Add N] (f : M ≃+ N) (x y : M), f (x + y) = f x + f y
-/
lemma toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (f + g) h = toSingleMk f h + toSingleMk g h :=
  (toSingleEquiv h).symm.map_add _ _

@[simp]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_sub** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_sub {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) : t
oSingleMk (f - g) h = toSingleMk f h - toSingleMk g h
参数：f g : K.X p ⟶ X；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_sub`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x y : G),   h (x - y) = h x - h y
-/
lemma toSingleMk_sub {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (f - g) h = toSingleMk f h - toSingleMk g h :=
  (toSingleEquiv h).symm.map_sub _ _

@[simp]
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_neg** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_neg {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : toS
ingleMk (-f) h = -toSingleMk f h
参数：f : K.X p ⟶ X；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.map_neg`：∀ {G : Type u_7} {H : Type u_8} [inst : AddGroup G] [i
nst_1 : SubtractionMonoid H] (h : G ≃+ H) (x : G), h (-x) = -h x
-/
lemma toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (-f) h = -toSingleMk f h :=
  (toSingleEquiv h).symm.map_neg _
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_surjective {q n : Int} (α : Cochain K ((singleFunctor C q).obj 
X) n) (p : Int) (h : p + n = q) : exists (f : K.X p ⟶ X), toSingleMk f h = α
参数：α : Cochain K ((singleFunctor C q).obj X) n；p : Int；h : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.surjective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [ins
t_1 : Add N] (e : M ≃+ N), Function.Surjective ⇑e
-/
lemma toSingleMk_surjective {q n : ℤ} (α : Cochain K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) :
    ∃ (f : K.X p ⟶ X), toSingleMk f h = α :=
  (toSingleEquiv h).symm.surjective α

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_postcomp** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_postcomp {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) 
{X' : C} (g : X ⟶ X') : toSingleMk (f ≫ g) h = (toSingleMk f h).comp (.ofHom ((s
ingleFunctor C q).map g)) (add_zero n)
参数：f : K.X p ⟶ X；h : p + n = q；g : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_v`：toSingleMk_v {p q : Int}
 (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : (toSingleMk f h).v p q h = f ≫ (Hom
ologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `HomologicalComplex.single_map_f_self`：single_map_f_self (j : ι) {A B : V
} (f : A ⟶ B) : ((single V c j).map f).f j = (singleObjXSelf c j A).hom ≫ f ≫ (s
ingleObjXSelf c j B).inv
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_postcomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) {X' : C} (g : X ⟶ X') :
    toSingleMk (f ≫ g) h =
      (toSingleMk f h).comp (.ofHom ((singleFunctor C q).map g)) (add_zero n) := by
  apply (toSingleEquiv h).injective
  simp [toSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.toSingleMk_precomp** 是 Mathlib 中的一个引理，位于命名空间
 `CochainComplex.HomComplex.Cochain`。
形式化陈述：toSingleMk_precomp {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) {
L : CochainComplex C Int} (g : L ⟶ K) : toSingleMk (g.f p ≫ f) h = (Cochain.ofHo
m g).comp (toSingleMk f h) (zero_add n)
参数：f : K.X p ⟶ X；h : p + n = q；g : L ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_v`：toSingleMk_v {p q : Int}
 (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : (toSingleMk f h).v p q h = f ≫ (Hom
ologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_precomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : L ⟶ K) :
    toSingleMk (g.f p ≫ f) h =
      (Cochain.ofHom g).comp (toSingleMk f h) (zero_add n) :=
  (toSingleEquiv h).injective (by simp [toSingleEquiv, singleFunctor, singleFunctors])

end Cochain

namespace Cocycle

/-- Constructor for cocycles from a single complex. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk** 是 Mathlib 中的一个定义，位于命名空间 `Coch
ainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) (q' : I
nt) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) : Cocycle ((singleFunctor C p).ob
j X) K n
参数：f : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d q q' = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cocycles from a single complex.
-/
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    Cocycle ((singleFunctor C p).obj X) K n :=
  Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia), hf]
    simp)
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_precomp** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : Int} (f : X ⟶ K.X q) {n 
: Int} (h : p + n = q) (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) : f
romSingleMk (g ≫ f) h q' hq' (by simp [hf]) = (fromSingleMk f h q' hq' hf).preco
mp ((singleFunctor C p).map g)
参数：g : X' ⟶ X；f : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d
 q q' = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_precomp`：fromSingleMk_pre
comp {X' : C} (g : X' ⟶ X) {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q)
 : fromSingleMk (g ≫ f) h = (Cochain.ofHom (…
· 使用定理 `CochainComplex.HomComplex.Cocycle.precomp_coe`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K
 : CochainComplex C ℤ} {n : ℤ} (z :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (g ≫ f) h q' hq' (by simp [hf]) =
      (fromSingleMk f h q' hq' hf).precomp ((singleFunctor C p).map g) := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_postcomp** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_postcomp {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q
) (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) {L : CochainComplex C In
t} (g : K ⟶ L) : fromSingleMk (f ≫ g.f q) h q' hq' (by simp [reassoc_of% hf]) = 
(fromSingleMk f h q' hq' hf).postcomp g
参数：f : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d q q' = 0；g
 : K ⟶ L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_postcomp`：fromSingleMk_po
stcomp {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) {L : CochainComplex
 C Int} (g : K ⟶ L) : fromSingleMk (f ≫ g.f q…
· 使用定理 `CochainComplex.HomComplex.Cocycle.postcomp_coe`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
K : CochainComplex C ℤ} {n : ℤ} (z :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) {L : CochainComplex C ℤ}
    (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h q' hq' (by simp [reassoc_of% hf]) =
      (fromSingleMk f h q' hq' hf).postcomp g := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_surjective** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_surjective {p n : Int} (α : Cocycle ((singleFunctor C p).obj 
X) K n) (q : Int) (h : p + n = q) (q' : Int) (hq' : q + 1 = q') : exists (f : X 
⟶ K.X q) (hf : f ≫ K.d q q' = 0), fromSingleMk f h q' hq' hf = α
参数：α : Cocycle ((singleFunctor C p).obj X) K n；q : Int；h : p + n = q；q' : Int；hq
' : q + 1 = q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_surjective`：fromSingleMk_
surjective {p n : Int} (α : Cochain ((singleFunctor C p).obj X) K n) (q : Int) (
h : p + n = q) : exists (f : X ⟶ K.X q), fromSi…
· 使用引理 `CochainComplex.HomComplex.Cocycle.δ_eq_zero`：δ_eq_zero {n : Int} (z : Co
cycle F G n) (m : Int) : δ n m (z : Cochain F G n) = 0
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.δ_fromSingleMk`：δ_fromSingleMk {p q : 
Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) (n' q' : Int) (h' : p + n' = q') 
: δ n n' (fromSingleMk f h) = fromSing…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_v`：fromSingleMk_v {p q : 
Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : (fromSingleMk f h).v p q h = (H
omologicalComplex.singleObjXSelf (.up …
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
-/
lemma fromSingleMk_surjective {p n : ℤ} (α : Cocycle ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) (q' : ℤ) (hq' : q + 1 = q') :
    ∃ (f : X ⟶ K.X q) (hf : f ≫ K.d q q' = 0), fromSingleMk f h q' hq' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf, Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_add** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_add {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) (
q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) : f
romSingleMk (f + g) h q' hq' (by simp [hf, hg]) = fromSingleMk f h q' hq' hf + f
romSingleMk g h q' hq' hg
参数：f g : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d q q' = 0
；hg : g ≫ K.d q q' = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_add`：fromSingleMk_add {p 
q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) : fromSingleMk (f + g) h = 
fromSingleMk f h + fromSingleMk g h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f + g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf + fromSingleMk g h q' hq' hg := by
  cat_disch
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_sub** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_sub {p q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) (
q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) : f
romSingleMk (f - g) h q' hq' (by simp [hf, hg]) = fromSingleMk f h q' hq' hf - f
romSingleMk g h q' hq' hg
参数：f g : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d q q' = 0
；hg : g ≫ K.d q q' = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_sub`：fromSingleMk_sub {p 
q : Int} (f g : X ⟶ K.X q) {n : Int} (h : p + n = q) : fromSingleMk (f - g) h = 
fromSingleMk f h - fromSingleMk g h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f - g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf - fromSingleMk g h q' hq' hg := by
  cat_disch
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_neg** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_neg {p q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) (q'
 : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) : fromSingleMk (-f) h q' hq' 
(by simp [hf]) = - fromSingleMk f h q' hq' hf
参数：f : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d q q' = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_neg`：fromSingleMk_neg {p 
q : Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) : fromSingleMk (-f) h = -from
SingleMk f h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (-f) h q' hq' (by simp [hf]) = - fromSingleMk f h q' hq' hf := by
  cat_disch

variable (X K) in
@[simp]
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_zero** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_zero {p q : Int} {n : Int} (h : p + n = q) (q' : Int) (hq' : 
q + 1 = q') : fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0
参数：h : p + n = q；q' : Int；hq' : q + 1 = q'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_zero`：fromSingleMk_zero (
p q n : Int) (h : p + n = q) : fromSingleMk (X
· 使用引理 `CochainComplex.HomComplex.Cocycle.coe_zero`：coe_zero : (↑(0 : Cocycle F 
G n) : Cochain F G n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma fromSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') :
    fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0 := by
  cat_disch
/-
**CochainComplex.HomComplex.Cocycle.fromSingleMk_mem_coboundaries_iff** 是 Mathli
b 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：fromSingleMk_mem_coboundaries_iff {p q : Int} (f : X ⟶ K.X q) {n : Int} (h
 : p + n = q) (q' : Int) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (q'' : Int) 
(hq'' : q'' + 1 = q) : fromSingleMk f h q' hq' hf in coboundaries _ _ _ ↔ exists
 (g : X ⟶ K.X q''), g ≫ K.d q'' q = f
参数：f : X ⟶ K.X q；h : p + n = q；q' : Int；hq' : q + 1 = q'；hf : f ≫ K.d q q' = 0；q
'' : Int；hq'' : q'' + 1 = q。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.mem_coboundaries_iff`：mem_coboundaries_iff (α 
: Cocycle K L n) (m : Int) (hm : m + 1 = n) : α in coboundaries K L n ↔ exists (
β : Cochain K L m), δ m n β = α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cochain.fromSingleMk_surjective`：fromSingleMk_
surjective {p n : Int} (α : Cochain ((singleFunctor C p).obj X) K n) (q : Int) (
h : p + n = q) : exists (f : X ⟶ K.X q), fromSi…
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `CochainComplex.HomComplex.Cochain.δ_fromSingleMk`：δ_fromSingleMk {p q : 
Int} (f : X ⟶ K.X q) {n : Int} (h : p + n = q) (n' q' : Int) (h' : p + n' = q') 
: δ n n' (fromSingleMk f h) = fromSing…
· 使用定理 `CochainComplex.HomComplex.Cocycle.fromSingleMk_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [
inst_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma fromSingleMk_mem_coboundaries_iff {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0)
    (q'' : ℤ) (hq'' : q'' + 1 = q) :
    fromSingleMk f h q' hq' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : X ⟶ K.X q''), g ≫ K.d q'' q = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg, fromSingleMk_coe, Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

/-- Constructor for cocycles to a single complex. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) (p' : Int
) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) : Cocycle K ((singleFunctor C q).ob
j X) n
参数：f : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for cocycles to a single complex.
-/
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    Cocycle K ((singleFunctor C q).obj X) n :=
  Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia), hf]
    simp)
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_postcomp** 是 Mathlib 中的一个引理，位于命名空
间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_postcomp {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) 
(p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {X' : C} (g : X ⟶ X') : to
SingleMk (f ≫ g) h p' hp' (by simp [reassoc_of% hf]) = (toSingleMk f h p' hp' hf
).postcomp ((singleFunctor C q).map g)
参数：f : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0；g
 : X ⟶ X'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_postcomp`：toSingleMk_postco
mp {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) {X' : C} (g : X ⟶ X') :
 toSingleMk (f ≫ g) h = (toSingleMk f h).co…
· 使用定理 `CochainComplex.HomComplex.Cocycle.postcomp_coe`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
K : CochainComplex C ℤ} {n : ℤ} (z :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_postcomp {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {X' : C} (g : X ⟶ X') :
    toSingleMk (f ≫ g) h p' hp' (by simp [reassoc_of% hf]) =
      (toSingleMk f h p' hp' hf).postcomp ((singleFunctor C q).map g) := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_postcomp])
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_precomp** 是 Mathlib 中的一个引理，位于命名空间
 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_precomp {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) (
p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {L : CochainComplex C Int} 
(g : L ⟶ K) : toSingleMk (g.f p ≫ f) h p' hp' (by simp [← g.comm_assoc, hf]) = (
toSingleMk f h p' hp' hf).precomp g
参数：f : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0；g
 : L ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_precomp`：toSingleMk_precomp
 {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) {L : CochainComplex C Int
} (g : L ⟶ K) : toSingleMk (g.f p ≫ f) h =…
· 使用定理 `CochainComplex.HomComplex.Cocycle.precomp_coe`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K
 : CochainComplex C ℤ} {n : ℤ} (z :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_precomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    {L : CochainComplex C ℤ} (g : L ⟶ K) :
    toSingleMk (g.f p ≫ f) h p' hp' (by simp [← g.comm_assoc, hf]) =
      (toSingleMk f h p' hp' hf).precomp g := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_precomp])

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_surjective** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_surjective {q n : Int} (α : Cocycle K ((singleFunctor C q).obj 
X) n) (p : Int) (h : p + n = q) (p' : Int) (hp' : p' + 1 = p) : exists (f : K.X 
p ⟶ X) (hf : K.d p' p ≫ f = 0), toSingleMk f h p' hp' hf = α
参数：α : Cocycle K ((singleFunctor C q).obj X) n；p : Int；h : p + n = q；p' : Int；hp
' : p' + 1 = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_surjective`：toSingleMk_surj
ective {q n : Int} (α : Cochain K ((singleFunctor C q).obj X) n) (p : Int) (h : 
p + n = q) : exists (f : K.X p ⟶ X), toSingle…
· 使用引理 `CochainComplex.HomComplex.Cocycle.δ_eq_zero`：δ_eq_zero {n : Int} (z : Co
cycle F G n) (m : Int) : δ n m (z : Cochain F G n) = 0
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_mono`：∀ {C : Type u} [inst : CategoryTheory.Catego
ry.{v, u} C] {X Y Z : C} (f : Y ⟶ X) [CategoryTheory.Mono f] {g h : Z ⟶ Y},   Ca
tegoryTheory.Cat…
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.instStrongMonoOfIsRegularMono`：∀ {C : Type u₁} [inst : Ca
tegoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsRegula
rMono f],   CategoryTheory.StrongM…
· 使用定理 `CategoryTheory.instIsRegularMonoOfIsSplitMono`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {X Y : C} (f : X ⟶ Y) [CategoryTheory.IsSplit
Mono f],   CategoryTheory.IsRegular…
· 使用定理 `CategoryTheory.IsSplitMono.of_iso`：∀ {C : Type u₁} [inst : CategoryTheor
y.Category.{v₁, u₁} C] {X Y : C} (f : Y ⟶ X) [CategoryTheory.IsIso f],   Categor
yTheory.IsSplitMono f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_v`：toSingleMk_v {p q : Int}
 (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : (toSingleMk f h).v p q h = f ≫ (Hom
ologicalComplex.singleObjXSelf (.up …
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用引理 `CochainComplex.HomComplex.Cochain.δ_toSingleMk`：δ_toSingleMk {p q : Int}
 (f : K.X p ⟶ X) {n : Int} (h : p + n = q) (n' p' : Int) (h' : p' + n' = q) : δ 
n n' (toSingleMk f h) = n'.negOnePow…
· 使用定理 `CochainComplex.HomComplex.δ_units_smul`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {R : Type u_1} 
  [inst_2 : Ring R] [inst_3 …
· 使用引理 `CochainComplex.HomComplex.Cocycle.coe_units_smul`：coe_units_smul (z : Co
cycle F G n) (x : Rˣ) : (↑(x • z) : Cochain F G n) = x • (z : Cochain F G n)
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
-/
lemma toSingleMk_surjective {q n : ℤ} (α : Cocycle K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p) :
    ∃ (f : K.X p ⟶ X) (hf : K.d p' p ≫ f = 0), toSingleMk f h p' hp' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul, δ_units_smul, ← hf, Cochain.δ_toSingleMk _ _ _ p' (by lia),
    smul_smul, Int.units_mul_self, one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv] using!
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_add** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_add {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) (p'
 : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) : toS
ingleMk (f + g) h p' hp' (by simp [hf, hg]) = toSingleMk f h p' hp' hf + toSingl
eMk g h p' hp' hg
参数：f g : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0
；hg : K.d p' p ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_add`：toSingleMk_add {p q : 
Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) : toSingleMk (f + g) h = toSing
leMk f h + toSingleMk g h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f + g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf + toSingleMk g h p' hp' hg := by
  cat_disch
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_sub** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_sub {p q : Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) (p'
 : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) : toS
ingleMk (f - g) h p' hp' (by simp [hf, hg]) = toSingleMk f h p' hp' hf - toSingl
eMk g h p' hp' hg
参数：f g : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0
；hg : K.d p' p ≫ g = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_sub`：toSingleMk_sub {p q : 
Int} (f g : K.X p ⟶ X) {n : Int} (h : p + n = q) : toSingleMk (f - g) h = toSing
leMk f h - toSingleMk g h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_sub {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f - g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf - toSingleMk g h p' hp' hg := by
  cat_disch
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_neg** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_neg {p q : Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) (p' :
 Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) : toSingleMk (-f) h p' hp' (by 
simp [hf]) = - toSingleMk f h p' hp' hf
参数：f : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_neg`：toSingleMk_neg {p q : 
Int} (f : K.X p ⟶ X) {n : Int} (h : p + n = q) : toSingleMk (-f) h = -toSingleMk
 f h
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    toSingleMk (-f) h p' hp' (by simp [hf]) =
      - toSingleMk f h p' hp' hf := by
  cat_disch

variable (X K) in
@[simp]
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_zero** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_zero {p q : Int} {n : Int} (h : p + n = q) (p' : Int) (hp' : p'
 + 1 = p) : toSingleMk (0 : K.X p ⟶ X) h p' hp' (by simp) = 0
参数：h : p + n = q；p' : Int；hp' : p' + 1 = p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cocycle.ext`：ext {z₁ z₂ : Cocycle F G n} (h : 
(z₁ : Cochain F G n) = z₂) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_zero`：toSingleMk_zero (p q 
n : Int) (h : p + n = q) : toSingleMk (X
· 使用引理 `CochainComplex.HomComplex.Cocycle.coe_zero`：coe_zero : (↑(0 : Cocycle F 
G n) : Cochain F G n) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) :
    toSingleMk (0 : K.X p ⟶ X) h p' hp' (by simp) = 0 := by
  cat_disch

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff** 是 Mathlib 
中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：toSingleMk_mem_coboundaries_iff {p q : Int} (f : K.X p ⟶ X) {n : Int} (h :
 p + n = q) (p' : Int) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (p'' : Int) (h
p'' : p + 1 = p'') : toSingleMk f h p' hp' hf in coboundaries _ _ _ ↔ exists (g 
: K.X p'' ⟶ X), K.d p p'' ≫ g = f
参数：f : K.X p ⟶ X；h : p + n = q；p' : Int；hp' : p' + 1 = p；hf : K.d p' p ≫ f = 0；p
'' : Int；hp'' : p + 1 = p''。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.mem_coboundaries_iff`：mem_coboundaries_iff (α 
: Cocycle K L n) (m : Int) (hm : m + 1 = n) : α in coboundaries K L n ↔ exists (
β : Cochain K L m), δ m n β = α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cochain.toSingleMk_surjective`：toSingleMk_surj
ective {q n : Int} (α : Cochain K ((singleFunctor C q).obj X) n) (p : Int) (h : 
p + n = q) : exists (f : K.X p ⟶ X), toSingle…
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用引理 `CategoryTheory.Linear.comp_units_smul`：comp_units_smul {X Y Z : C} (f : 
X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g) = r • f ≫ g
· 使用定理 `map_zsmul_unit`：∀ {F : Type u_16} {M : Type u_17} {N : Type u_18} [inst 
: AddGroup M] [inst_1 : AddGroup N] [inst_2 : FunLike F M N]   [AddMonoidHomClas
s F …
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
· 使用引理 `CochainComplex.HomComplex.Cochain.δ_toSingleMk`：δ_toSingleMk {p q : Int}
 (f : K.X p ⟶ X) {n : Int} (h : p + n = q) (n' p' : Int) (h' : p' + n' = q) : δ 
n n' (toSingleMk f h) = n'.negOnePow…
· 使用定理 `CochainComplex.HomComplex.Cocycle.toSingleMk_coe`：∀ {C : Type u} [inst :
 CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   [in
st_2 : CategoryTheory.Limits.HasZeroOb…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CochainComplex.HomComplex.δ_units_smul`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] {R : Type u_1} 
  [inst_2 : Ring R] [inst_3 …
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma toSingleMk_mem_coboundaries_iff {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (p'' : ℤ) (hp'' : p + 1 = p'') :
    toSingleMk f h p' hp' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : K.X p'' ⟶ X), K.d p p'' ≫ g = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg, toSingleMk_coe, Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

end Cocycle

end HomComplex

end CochainComplex

