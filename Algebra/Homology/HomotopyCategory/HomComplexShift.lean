/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Tactic.Linarith

/-! # Shifting cochains

Let `C` be a preadditive category. Given two cochain complexes (indexed by `ℤ`),
the type of cochains `HomComplex.Cochain K L n` of degree `n` was introduced
in `Mathlib/Algebra/Homology/HomotopyCategory/HomComplex.lean`. In this file, we
study how these cochains behave with respect to the shift on the complexes `K`
and `L`.

When `n`, `a`, `n'` are integers such that `h : n' + a = n`,
we obtain `rightShiftAddEquiv K L n a n' h : Cochain K L n ≃+ Cochain K (L⟦a⟧) n'`.
This definition does not involve signs, but the analogous definition
of `leftShiftAddEquiv K L n a n' h' : Cochain K L n ≃+ Cochain (K⟦a⟧) L n'`
when `h' : n + a = n'` does involve signs, as we follow the conventions
appearing in the introduction of
[Brian Conrad's book *Grothendieck duality and base change*][conrad2000].

## References
* [Brian Conrad, Grothendieck duality and base change][conrad2000]

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] {R : Type*} [Ring R] [Linear R C]
  {K L M : CochainComplex C ℤ} {n : ℤ}

namespace CochainComplex.HomComplex

namespace Cochain

variable (γ γ₁ γ₂ : Cochain K L n)

/-- The map `Cochain K L n → Cochain K (L⟦a⟧) n'` when `n' + a = n`. -/
/-
**CochainComplex.HomComplex.Cochain.rightShift** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：rightShift (a n' : Int) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n'
参数：a n' : Int；hn' : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cochain K L n → Cochain K (L⟦a⟧) n'` when `n' + a = n`.
-/
def rightShift (a n' : ℤ) (hn' : n' + a = n) : Cochain K (L⟦a⟧) n' :=
  Cochain.mk (fun p q hpq => γ.v p (p + n) rfl ≫
    (L.shiftFunctorObjXIso a q (p + n) (by lia)).inv)

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.rightShift_v** 是 Mathlib 中的一个引理，位于命名空间 `Coch
ainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_v (a n' : Int) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q
) (p' : Int) (hp' : p + n = p') : (γ.rightShift a n' hn').v p q hpq = γ.v p p' h
p' ≫ (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv
参数：a n' : Int；hn' : n' + a = n；p q : Int；hpq : p + n' = q；p' : Int；hp' : p + n =
 p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightShift_v (a n' : ℤ) (hn' : n' + a = n) (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p + n = p') :
    (γ.rightShift a n' hn').v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a q p' (by rw [← hp', ← hpq, ← hn', add_assoc])).inv := by
  subst hp'
  dsimp only [rightShift]
  simp only [mk_v]

/-- The map `Cochain K L n → Cochain (K⟦a⟧) L n'` when `n + a = n'`. -/
/-
**CochainComplex.HomComplex.Cochain.leftShift** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：leftShift (a n' : Int) (hn' : n + a = n') : Cochain (K⟦a⟧) L n'
参数：a n' : Int；hn' : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cochain K L n → Cochain (K⟦a⟧) L n'` when `n + a = n'`.
-/
def leftShift (a n' : ℤ) (hn' : n + a = n') : Cochain (K⟦a⟧) L n' :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a p (p + a) rfl).hom ≫ γ.v (p + a) q (by lia))
/-
**CochainComplex.HomComplex.Cochain.leftShift_v** 是 Mathlib 中的一个引理，位于命名空间 `Cocha
inComplex.HomComplex.Cochain`。
形式化陈述：leftShift_v (a n' : Int) (hn' : n + a = n') (p q : Int) (hpq : p + n' = q)
 (p' : Int) (hp' : p' + n = q) : (γ.leftShift a n' hn').v p q hpq = (a * n' + ((
a * (a - 1)) / 2)).negOnePow • (K.shiftFunctorObjXIso a p p' (by rw [← add_left_
inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp'
参数：a n' : Int；hn' : n + a = n'；p q : Int；hpq : p + n' = q；p' : Int；hp' : p' + n 
= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma leftShift_v (a n' : ℤ) (hn' : n + a = n') (p q : ℤ) (hpq : p + n' = q)
    (p' : ℤ) (hp' : p' + n = q) :
    (γ.leftShift a n' hn').v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p p'
        (by rw [← add_left_inj n, hp', add_assoc, add_comm a, hn', hpq])).hom ≫ γ.v p' q hp' := by
  obtain rfl : p' = p + a := by lia
  dsimp only [leftShift]
  simp only [mk_v]

/-- The map `Cochain K (L⟦a⟧) n' → Cochain K L n` when `n' + a = n`. -/
/-
**CochainComplex.HomComplex.Cochain.rightUnshift** 是 Mathlib 中的一个定义，位于命名空间 `Coch
ainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a
 = n) : Cochain K L n
参数：γ : Cochain K (L⟦a⟧) n'；n : Int；hn : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cochain K (L⟦a⟧) n' → Cochain K L n` when `n' + a = n`.
-/
def rightUnshift {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => γ.v p (p + n') rfl ≫
    (L.shiftFunctorObjXIso a (p + n') q (by rw [← hpq, add_assoc, hn])).hom)
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_v** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_v {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' +
 a = n) (p q : Int) (hpq : p + n = q) (p' : Int) (hp' : p + n' = p') : (γ.rightU
nshift n hn).v p q hpq = γ.v p p' hp' ≫ (L.shiftFunctorObjXIso a p' q (by rw [← 
hpq, ← hn, ← add_assoc, hp'])).hom
参数：γ : Cochain K (L⟦a⟧) n'；n : Int；hn : n' + a = n；p q : Int；hpq : p + n = q；p' 
: Int；hp' : p + n' = p'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightUnshift_v {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p + n' = p') :
    (γ.rightUnshift n hn).v p q hpq = γ.v p p' hp' ≫
      (L.shiftFunctorObjXIso a p' q (by rw [← hpq, ← hn, ← add_assoc, hp'])).hom := by
  subst hp'
  dsimp only [rightUnshift]
  simp only [mk_v]

/-- The map `Cochain (K⟦a⟧) L n' → Cochain K L n` when `n + a = n'`. -/
/-
**CochainComplex.HomComplex.Cochain.leftUnshift** 是 Mathlib 中的一个定义，位于命名空间 `Cocha
inComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a =
 n') : Cochain K L n
参数：γ : Cochain (K⟦a⟧) L n'；n : Int；hn : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cochain (K⟦a⟧) L n' → Cochain K L n` when `n + a = n'`.
-/
def leftUnshift {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    Cochain K L n :=
  Cochain.mk (fun p q hpq => (a * n' + ((a * (a - 1)) / 2)).negOnePow •
    (K.shiftFunctorObjXIso a (p - a) p (by lia)).inv ≫ γ.v (p - a) q (by lia))
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_v** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_v {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a
 = n') (p q : Int) (hpq : p + n = q) (p' : Int) (hp' : p' + n' = q) : (γ.leftUns
hift n hn).v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow • (K.shiftFuncto
rObjXIso a p' p (by lia)).inv ≫ γ.v p' q (by lia)
参数：γ : Cochain (K⟦a⟧) L n'；n : Int；hn : n + a = n'；p q : Int；hpq : p + n = q；p' 
: Int；hp' : p' + n' = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma leftUnshift_v {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (p q : ℤ) (hpq : p + n = q) (p' : ℤ) (hp' : p' + n' = q) :
    (γ.leftUnshift n hn).v p q hpq = (a * n' + ((a * (a - 1)) / 2)).negOnePow •
      (K.shiftFunctorObjXIso a p' p (by lia)).inv ≫ γ.v p' q (by lia) := by
  obtain rfl : p' = p - a := by lia
  rfl

/-- The map `Cochain K L n → Cochain (K⟦a⟧) (L⟦a⟧) n`. -/
/-
**CochainComplex.HomComplex.Cochain.shift** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.HomComplex.Cochain`。
形式化陈述：shift (a : Int) : Cochain (K⟦a⟧) (L⟦a⟧) n
参数：a : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cochain K L n → Cochain (K⟦a⟧) (L⟦a⟧) n`.
-/
def shift (a : ℤ) : Cochain (K⟦a⟧) (L⟦a⟧) n :=
  Cochain.mk (fun p q hpq => (K.shiftFunctorObjXIso a p _ rfl).hom ≫
    γ.v (p + a) (q + a) (by lia) ≫ (L.shiftFunctorObjXIso a q _ rfl).inv)
/-
**CochainComplex.HomComplex.Cochain.shift_v** 是 Mathlib 中的一个引理，位于命名空间 `CochainCo
mplex.HomComplex.Cochain`。
形式化陈述：shift_v (a : Int) (p q : Int) (hpq : p + n = q) (p' q' : Int) (hp' : p' = 
p + a) (hq' : q' = q + a) : (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p
' hp').hom ≫ γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc
]) ≫ (L.shiftFunctorObjXIso a q q' hq').inv
参数：a : Int；p q : Int；hpq : p + n = q；p' q' : Int；hp' : p' = p + a；hq' : q' = q +
 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma shift_v (a : ℤ) (p q : ℤ) (hpq : p + n = q) (p' q' : ℤ)
    (hp' : p' = p + a) (hq' : q' = q + a) :
    (γ.shift a).v p q hpq = (K.shiftFunctorObjXIso a p p' hp').hom ≫
      γ.v p' q' (by rw [hp', hq', ← hpq, add_assoc, add_comm a, add_assoc]) ≫
      (L.shiftFunctorObjXIso a q q' hq').inv := by
  subst hp' hq'
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CochainComplex.HomComplex.Cochain.shift_v'** 是 Mathlib 中的一个引理，位于命名空间 `CochainC
omplex.HomComplex.Cochain`。
形式化陈述：shift_v' (a : Int) (p q : Int) (hpq : p + n = q) : (γ.shift a).v p q hpq =
 γ.v (p + a) (q + a) (by lia)
参数：a : Int；p q : Int；hpq : p + n = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.shift_v`：shift_v (a : Int) (p q : Int)
 (hpq : p + n = q) (p' q' : Int) (hp' : p' = p + a) (hq' : q' = q + a) : (γ.shif
t a).v p q hpq = (K.shiftFuncto…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shift_v' (a : ℤ) (p q : ℤ) (hpq : p + n = q) :
    (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia) := by
  simp only [shift_v γ a p q hpq _ _ rfl rfl, shiftFunctor_obj_X, shiftFunctorObjXIso,
    HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom, Iso.refl_inv, comp_id, id_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_rightShift** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_rightShift (a n' : Int) (hn' : n' + a = n) : (γ.rightShift a 
n' hn').rightUnshift n hn' = γ
参数：a n' : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_v`：rightUnshift_v {n' a :
 Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (p q : Int) (hpq : p
 + n = q) (p' : Int) (hp' : p + n' = p…
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
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
lemma rightUnshift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').rightUnshift n hn' = γ := by
  ext p q hpq
  simp only [rightUnshift_v _ n hn' p q hpq (p + n') rfl,
    γ.rightShift_v _ _ hn' p (p + n') rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.inv_hom_id, comp_id]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightShift_rightUnshift** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_rightUnshift {a n' : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (
hn' : n' + a = n) : (γ.rightUnshift n hn').rightShift a n' hn' = γ
参数：γ : Cochain K (L⟦a⟧) n'；n : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_v`：rightUnshift_v {n' a :
 Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (p q : Int) (hpq : p
 + n = q) (p' : Int) (hp' : p + n' = p…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.hom self.inv = …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightShift_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn' : n' + a = n) :
    (γ.rightUnshift n hn').rightShift a n' hn' = γ := by
  ext p q hpq
  simp only [(γ.rightUnshift n hn').rightShift_v a n' hn' p q hpq (p + n) rfl,
    γ.rightUnshift_v n hn' p (p + n) rfl q hpq,
    shiftFunctorObjXIso, assoc, Iso.hom_inv_id, comp_id]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_leftShift** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_leftShift (a n' : Int) (hn' : n + a = n') : (γ.leftShift a n' 
hn').leftUnshift n hn' = γ
参数：a n' : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.leftUnshift_v`：leftUnshift_v {n' a : I
nt} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') (p q : Int) (hpq : p +
 n = q) (p' : Int) (hp' : p' + n' = q…
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用引理 `CategoryTheory.Linear.comp_units_smul`：comp_units_smul {X Y Z : C} (f : 
X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g) = r • f ≫ g
· 使用定理 `CategoryTheory.Iso.inv_hom_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : Y ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma leftUnshift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').leftUnshift n hn' = γ := by
  ext p q hpq
  rw [(γ.leftShift a n' hn').leftUnshift_v n hn' p q hpq (q - n') (by lia),
    γ.leftShift_v a n' hn' (q - n') q (by lia) p hpq, Linear.comp_units_smul,
    Iso.inv_hom_id_assoc, smul_smul, Int.units_mul_self, one_smul]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_leftUnshift** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_leftUnshift {a n' : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn
' : n + a = n') : (γ.leftUnshift n hn').leftShift a n' hn' = γ
参数：γ : Cochain (K⟦a⟧) L n'；n : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用引理 `CochainComplex.HomComplex.Cochain.leftUnshift_v`：leftUnshift_v {n' a : I
nt} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') (p q : Int) (hpq : p +
 n = q) (p' : Int) (hp' : p' + n' = q…
· 使用引理 `CategoryTheory.Linear.comp_units_smul`：comp_units_smul {X Y Z : C} (f : 
X ⟶ Y) (r : Rˣ) (g : Y ⟶ Z) : f ≫ (r • g) = r • f ≫ g
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma leftShift_leftUnshift {a n' : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn' : n + a = n') :
    (γ.leftUnshift n hn').leftShift a n' hn' = γ := by
  ext p q hpq
  rw [(γ.leftUnshift n hn').leftShift_v a n' hn' p q hpq (q - n) (by lia),
    γ.leftUnshift_v n hn' (q - n) q (by lia) p hpq, Linear.comp_units_smul, smul_smul,
    Iso.hom_inv_id_assoc, Int.units_mul_self, one_smul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightShift_add** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_add (a n' : Int) (hn' : n' + a = n) : (γ₁ + γ₂).rightShift a n'
 hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn'
参数：a n' : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Preadditive.add_comp`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C)   (f f' 
: P ⟶ Q) (g : Q ⟶ R),   C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightShift_add (a n' : ℤ) (hn' : n' + a = n) :
    (γ₁ + γ₂).rightShift a n' hn' = γ₁.rightShift a n' hn' + γ₂.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, add_v, add_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_add** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_add (a n' : Int) (hn' : n + a = n') : (γ₁ + γ₂).leftShift a n' h
n' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn'
参数：a n' : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `CategoryTheory.Preadditive.comp_add`：∀ {C : Type u} {inst : CategoryTheo
ry.Category.{v, u} C} [self : CategoryTheory.Preadditive C] (P Q R : C) (f : P ⟶
 Q)   (g g' : Q ⟶ R),   C…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftShift_add (a n' : ℤ) (hn' : n + a = n') :
    (γ₁ + γ₂).leftShift a n' hn' = γ₁.leftShift a n' hn' + γ₂.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), add_v, comp_add, smul_add]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.shift_add** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：shift_add (a : Int) : (γ₁ + γ₂).shift a = γ₁.shift a + γ₂.shift a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.shift_v'`：shift_v' (a : Int) (p q : In
t) (hpq : p + n = q) : (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shift_add (a : ℤ) :
    (γ₁ + γ₂).shift a = γ₁.shift a + γ₂.shift a := by
  ext p q hpq
  dsimp
  simp only [shift_v', add_v]

variable (K L)

/-- The additive equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n`. -/
@[simps]
/-
**CochainComplex.HomComplex.Cochain.rightShiftAddEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightShiftAddEquiv (n a n' : Int) (hn' : n' + a = n) : Cochain K L n ≃+ Co
chain K (L⟦a⟧) n' where toFun γ
参数：n a n' : Int；hn' : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n`.
-/
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain K L n ≃+ Cochain K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by simp only [rightUnshift_rightShift]
  right_inv γ := by simp only [rightShift_rightUnshift]
  map_add' γ γ' := by simp only [rightShift_add]

/-- The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'`. -/
@[simps]
/-
**CochainComplex.HomComplex.Cochain.leftShiftAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShiftAddEquiv (n a n' : Int) (hn' : n + a = n') : Cochain K L n ≃+ Coc
hain (K⟦a⟧) L n' where toFun γ
参数：n a n' : Int；hn' : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'
`.
-/
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cochain K L n ≃+ Cochain (K⟦a⟧) L n' where
  toFun γ := γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by simp only [leftUnshift_leftShift]
  right_inv γ := by simp only [leftShift_leftUnshift]
  map_add' γ γ' := by simp only [leftShift_add]

/-- The additive map `Cochain K L n →+ Cochain (K⟦a⟧) (L⟦a⟧) n`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cochain.shiftAddHom** 是 Mathlib 中的一个定义，位于命名空间 `Cocha
inComplex.HomComplex.Cochain`。
形式化陈述：shiftAddHom (n a : Int) : Cochain K L n ->+ Cochain (K⟦a⟧) (L⟦a⟧) n
参数：n a : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive map `Cochain K L n →+ Cochain (K⟦a⟧) (L⟦a⟧) n`.
-/
def shiftAddHom (n a : ℤ) : Cochain K L n →+ Cochain (K⟦a⟧) (L⟦a⟧) n :=
  AddMonoidHom.mk' (fun γ => γ.shift a) (by intros; simp only [shift_add])

variable (n)

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightShift_zero** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_zero (a n' : Int) (hn' : n' + a = n) : (0 : Cochain K L n).righ
tShift a n' hn' = 0
参数：a n' : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma rightShift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K L n).rightShift a n' hn' = 0 := by
  change rightShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_zero** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_zero (a n' : Int) (hn' : n' + a = n) : (0 : Cochain K (L⟦a⟧) 
n').rightUnshift n hn' = 0
参数：a n' : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma rightUnshift_zero (a n' : ℤ) (hn' : n' + a = n) :
    (0 : Cochain K (L⟦a⟧) n').rightUnshift n hn' = 0 := by
  change (rightShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_zero** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_zero (a n' : Int) (hn' : n + a = n') : (0 : Cochain K L n).leftS
hift a n' hn' = 0
参数：a n' : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma leftShift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain K L n).leftShift a n' hn' = 0 := by
  change leftShiftAddEquiv K L n a n' hn' 0 = 0
  apply map_zero

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_zero** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_zero (a n' : Int) (hn' : n + a = n') : (0 : Cochain (K⟦a⟧) L n
').leftUnshift n hn' = 0
参数：a n' : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma leftUnshift_zero (a n' : ℤ) (hn' : n + a = n') :
    (0 : Cochain (K⟦a⟧) L n').leftUnshift n hn' = 0 := by
  change (leftShiftAddEquiv K L n a n' hn').symm 0 = 0
  apply map_zero

@[simp]
/-
**CochainComplex.HomComplex.Cochain.shift_zero** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：shift_zero (a : Int) : (0 : Cochain K L n).shift a = 0
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma shift_zero (a : ℤ) :
    (0 : Cochain K L n).shift a = 0 := by
  change shiftAddHom K L n a 0 = 0
  apply map_zero

variable {K L n}

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightShift_neg** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_neg (a n' : Int) (hn' : n' + a = n) : (-γ).rightShift a n' hn' 
= -γ.rightShift a n' hn'
参数：a n' : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma rightShift_neg (a n' : ℤ) (hn' : n' + a = n) :
    (-γ).rightShift a n' hn' = -γ.rightShift a n' hn' := by
  change rightShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_neg** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_neg {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n'
 + a = n) : (-γ).rightUnshift n hn = -γ.rightUnshift n hn
参数：γ : Cochain K (L⟦a⟧) n'；n : Int；hn : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma rightUnshift_neg {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    (-γ).rightUnshift n hn = -γ.rightUnshift n hn := by
  change (rightShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_neg** 是 Mathlib 中的一个引理，位于命名空间 `Coc
hainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_neg (a n' : Int) (hn' : n + a = n') : (-γ).leftShift a n' hn' = 
-γ.leftShift a n' hn'
参数：a n' : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma leftShift_neg (a n' : ℤ) (hn' : n + a = n') :
    (-γ).leftShift a n' hn' = -γ.leftShift a n' hn' := by
  change leftShiftAddEquiv K L n a n' hn' (-γ) = _
  apply map_neg

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_neg** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_neg {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n +
 a = n') : (-γ).leftUnshift n hn = -γ.leftUnshift n hn
参数：γ : Cochain (K⟦a⟧) L n'；n : Int；hn : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma leftUnshift_neg {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (-γ).leftUnshift n hn = -γ.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (-γ) = _
  apply map_neg

@[simp]
/-
**CochainComplex.HomComplex.Cochain.shift_neg** 是 Mathlib 中的一个引理，位于命名空间 `Cochain
Complex.HomComplex.Cochain`。
形式化陈述：shift_neg (a : Int) : (-γ).shift a = -γ.shift a
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
lemma shift_neg (a : ℤ) :
    (-γ).shift a = -γ.shift a := by
  change shiftAddHom K L n a (-γ) = _
  apply map_neg

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_add** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_add {n' a : Int} (γ₁ γ₂ : Cochain K (L⟦a⟧) n') (n : Int) (hn 
: n' + a = n) : (γ₁ + γ₂).rightUnshift n hn = γ₁.rightUnshift n hn + γ₂.rightUns
hift n hn
参数：γ₁ γ₂ : Cochain K (L⟦a⟧) n'；n : Int；hn : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma rightUnshift_add {n' a : ℤ} (γ₁ γ₂ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    (γ₁ + γ₂).rightUnshift n hn = γ₁.rightUnshift n hn + γ₂.rightUnshift n hn := by
  change (rightShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_add** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_add {n' a : Int} (γ₁ γ₂ : Cochain (K⟦a⟧) L n') (n : Int) (hn :
 n + a = n') : (γ₁ + γ₂).leftUnshift n hn = γ₁.leftUnshift n hn + γ₂.leftUnshift
 n hn
参数：γ₁ γ₂ : Cochain (K⟦a⟧) L n'；n : Int；hn : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddEquivClass.instAddMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N 
: Type u_5} [inst : EquivLike F M N] [inst_1 : AddZeroClass M]   [inst_2 : AddZe
roClass N] [AddEquivClass…
· 使用定理 `AddEquiv.instAddEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Add 
M] [inst_1 : Add N], AddEquivClass (M ≃+ N) M N
-/
lemma leftUnshift_add {n' a : ℤ} (γ₁ γ₂ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    (γ₁ + γ₂).leftUnshift n hn = γ₁.leftUnshift n hn + γ₂.leftUnshift n hn := by
  change (leftShiftAddEquiv K L n a n' hn).symm (γ₁ + γ₂) = _
  apply map_add

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightShift_smul** 是 Mathlib 中的一个引理，位于命名空间 `C
ochainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_smul (a n' : Int) (hn' : n' + a = n) (x : R) : (x • γ).rightShi
ft a n' hn' = x • γ.rightShift a n' hn'
参数：a n' : Int；hn' : n' + a = n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `CategoryTheory.Linear.smul_comp`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rightShift_smul (a n' : ℤ) (hn' : n' + a = n) (x : R) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [rightShift_v _ a n' hn' p q hpq _ rfl, smul_v, Linear.smul_comp]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_smul** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_smul (a n' : Int) (hn' : n + a = n') (x : R) : (x • γ).leftShift
 a n' hn' = x • γ.leftShift a n' hn'
参数：a n' : Int；hn' : n + a = n'；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `CategoryTheory.Linear.comp_smul`：∀ {R : Type w} {inst : Semiring R} {C :
 Type u} {inst_1 : CategoryTheory.Category.{v, u} C}   {inst_2 : CategoryTheory.
Preadditive C} [self …
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leftShift_smul (a n' : ℤ) (hn' : n + a = n') (x : R) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  ext p q hpq
  dsimp
  simp only [leftShift_v _ a n' hn' p q hpq (p + a) (by lia), smul_v, Linear.comp_smul,
    smul_comm x]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.shift_smul** 是 Mathlib 中的一个引理，位于命名空间 `Cochai
nComplex.HomComplex.Cochain`。
形式化陈述：shift_smul (a : Int) (x : R) : (x • γ).shift a = x • (γ.shift a)
参数：a : Int；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.shift_v'`：shift_v' (a : Int) (p q : In
t) (hpq : p + n = q) : (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shift_smul (a : ℤ) (x : R) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [shift_v', smul_v]

variable (K L R)

set_option backward.defeqAttrib.useBackward true in
/-- The linear equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n` and
the category is `R`-linear. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cochain.rightShiftLinearEquiv** 是 Mathlib 中的一个定义，位于命
名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightShiftLinearEquiv (n a n' : Int) (hn' : n' + a = n) : Cochain K L n ≃ₗ
[R] Cochain K (L⟦a⟧) n'
参数：n a n' : Int；hn' : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear equivalence `Cochain K L n ≃+ Cochain K L⟦a⟧ n'` when `n' + a = n` an
d
the category is `R`-linear.
-/
def rightShiftLinearEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cochain K L n ≃ₗ[R] Cochain K (L⟦a⟧) n' :=
  (rightShiftAddEquiv K L n a n' hn').toLinearEquiv
    (fun x γ => by dsimp; simp only [rightShift_smul])

set_option backward.defeqAttrib.useBackward true in
/-- The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'` and
the category is `R`-linear. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cochain.leftShiftLinearEquiv** 是 Mathlib 中的一个定义，位于命名
空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShiftLinearEquiv (n a n' : Int) (hn : n + a = n') : Cochain K L n ≃ₗ[R
] Cochain (K⟦a⟧) L n'
参数：n a n' : Int；hn : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `Cochain K L n ≃+ Cochain (K⟦a⟧) L n'` when `n + a = n'
` and
the category is `R`-linear.
-/
def leftShiftLinearEquiv (n a n' : ℤ) (hn : n + a = n') :
    Cochain K L n ≃ₗ[R] Cochain (K⟦a⟧) L n' :=
  (leftShiftAddEquiv K L n a n' hn).toLinearEquiv
    (fun x γ => by dsimp; simp only [leftShift_smul])

set_option backward.defeqAttrib.useBackward true in
/-- The linear map `Cochain K L n ≃+ Cochain (K⟦a⟧) (L⟦a⟧) n` when the category is `R`-linear. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cochain.shiftLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：shiftLinearMap (n a : Int) : Cochain K L n ->ₗ[R] Cochain (K⟦a⟧) (L⟦a⟧) n 
where toAddHom
参数：n a : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear map `Cochain K L n ≃+ Cochain (K⟦a⟧) (L⟦a⟧) n` when the category is `
R`-linear.
-/
def shiftLinearMap (n a : ℤ) :
    Cochain K L n →ₗ[R] Cochain (K⟦a⟧) (L⟦a⟧) n where
  toAddHom := shiftAddHom K L n a
  map_smul' _ _ := by dsimp; simp only [shift_smul]

variable {K L R}

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightShift_units_smul** 是 Mathlib 中的一个引理，位于命
名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_units_smul (a n' : Int) (hn' : n' + a = n) (x : Rˣ) : (x • γ).r
ightShift a n' hn' = x • γ.rightShift a n' hn'
参数：a n' : Int；hn' : n' + a = n；x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_smul`：rightShift_smul (a n'
 : Int) (hn' : n' + a = n) (x : R) : (x • γ).rightShift a n' hn' = x • γ.rightSh
ift a n' hn'
-/
lemma rightShift_units_smul (a n' : ℤ) (hn' : n' + a = n) (x : Rˣ) :
    (x • γ).rightShift a n' hn' = x • γ.rightShift a n' hn' := by
  apply rightShift_smul

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_units_smul** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_units_smul (a n' : Int) (hn' : n + a = n') (x : Rˣ) : (x • γ).le
ftShift a n' hn' = x • γ.leftShift a n' hn'
参数：a n' : Int；hn' : n + a = n'；x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_smul`：leftShift_smul (a n' :
 Int) (hn' : n + a = n') (x : R) : (x • γ).leftShift a n' hn' = x • γ.leftShift 
a n' hn'
-/
lemma leftShift_units_smul (a n' : ℤ) (hn' : n + a = n') (x : Rˣ) :
    (x • γ).leftShift a n' hn' = x • γ.leftShift a n' hn' := by
  apply leftShift_smul

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.shift_units_smul** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：shift_units_smul (a : Int) (x : Rˣ) : (x • γ).shift a = x • (γ.shift a)
参数：a : Int；x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.shift_v'`：shift_v' (a : Int) (p q : In
t) (hpq : p + n = q) : (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma shift_units_smul (a : ℤ) (x : Rˣ) :
    (x • γ).shift a = x • (γ.shift a) := by
  ext p q hpq
  dsimp
  simp only [shift_v', units_smul_v]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_smul** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_smul {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n
' + a = n) (x : R) : (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn
参数：γ : Cochain K (L⟦a⟧) n'；n : Int；hn : n' + a = n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma rightUnshift_smul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) (x : R) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  change (rightShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_units_smul** 是 Mathlib 中的一个引理，位
于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_units_smul {n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (
hn : n' + a = n) (x : Rˣ) : (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn
参数：γ : Cochain K (L⟦a⟧) n'；n : Int；hn : n' + a = n；x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_smul`：rightUnshift_smul {
n' a : Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (x : R) : (x •
 γ).rightUnshift n hn = x • γ.rightUnshif…
-/
lemma rightUnshift_units_smul {n' a : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ)
    (hn : n' + a = n) (x : Rˣ) :
    (x • γ).rightUnshift n hn = x • γ.rightUnshift n hn := by
  apply rightUnshift_smul

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_smul** 是 Mathlib 中的一个引理，位于命名空间 `
CochainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_smul {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n 
+ a = n') (x : R) : (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn
参数：γ : Cochain (K⟦a⟧) L n'；n : Int；hn : n + a = n'；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
-/
lemma leftUnshift_smul {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') (x : R) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  change (leftShiftLinearEquiv R K L n a n' hn).symm (x • γ) = _
  apply map_smul

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftUnshift_units_smul** 是 Mathlib 中的一个引理，位于
命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftUnshift_units_smul {n' a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (h
n : n + a = n') (x : Rˣ) : (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn
参数：γ : Cochain (K⟦a⟧) L n'；n : Int；hn : n + a = n'；x : Rˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.leftUnshift_smul`：leftUnshift_smul {n'
 a : Int} (γ : Cochain (K⟦a⟧) L n') (n : Int) (hn : n + a = n') (x : R) : (x • γ
).leftUnshift n hn = x • γ.leftUnshift n…
-/
lemma leftUnshift_units_smul {n' a : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ)
    (hn : n + a = n') (x : Rˣ) :
    (x • γ).leftUnshift n hn = x • γ.leftUnshift n hn := by
  apply leftUnshift_smul
/-
**CochainComplex.HomComplex.Cochain.rightUnshift_comp** 是 Mathlib 中的一个引理，位于命名空间 
`CochainComplex.HomComplex.Cochain`。
形式化陈述：rightUnshift_comp {m : Int} {a : Int} (γ' : Cochain L (M⟦a⟧) m) {nm : Int}
 (hnm : n + m = nm) (nm' : Int) (hnm' : nm + a = nm') (m' : Int) (hm' : m + a = 
m') : (γ.comp γ' hnm).rightUnshift nm' hnm' = γ.comp (γ'.rightUnshift m' hm') (b
y lia)
参数：γ' : Cochain L (M⟦a⟧) m；hnm : n + m = nm；nm' : Int；hnm' : nm + a = nm'；m' : I
nt；hm' : m + a = m'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_v`：rightUnshift_v {n' a :
 Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (p q : Int) (hpq : p
 + n = q) (p' : Int) (hp' : p + n' = p…
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
-/
lemma rightUnshift_comp {m : ℤ} {a : ℤ} (γ' : Cochain L (M⟦a⟧) m) {nm : ℤ} (hnm : n + m = nm)
    (nm' : ℤ) (hnm' : nm + a = nm') (m' : ℤ) (hm' : m + a = m') :
    (γ.comp γ' hnm).rightUnshift nm' hnm' =
      γ.comp (γ'.rightUnshift m' hm') (by lia) := by
  ext p q hpq
  rw [(γ.comp γ' hnm).rightUnshift_v nm' hnm' p q hpq (p + n + m) (by lia),
    γ.comp_v γ' hnm p (p + n) (p + n + m) rfl rfl,
    comp_v _ _ (show n + m' = nm' by lia) p (p + n) q (by lia) (by lia),
    γ'.rightUnshift_v m' hm' (p + n) q (by lia) (p + n + m) rfl, assoc]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.leftShift_comp** 是 Mathlib 中的一个引理，位于命名空间 `Co
chainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_comp (a n' : Int) (hn' : n + a = n') {m t t' : Int} (γ' : Cochai
n L M m) (h : n + m = t) (ht' : t + a = t') : (γ.comp γ' h).leftShift a t' ht' =
 (a * m).negOnePow • (γ.leftShift a n' hn').comp γ' (by rw [← ht', ← h, ← hn', a
dd_assoc, add_comm a, add_assoc])
参数：a n' : Int；hn' : n + a = n'；γ' : Cochain L M m；h : n + m = t；ht' : t + a = t'
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_v`：comp_v {n₁ n₂ n₁₂ : Int} (z₁ :
 Cochain F G n₁) (z₂ : Cochain G K n₂) (h : n₁ + n₂ = n₁₂) (p₁ p₂ p₃ : Int) (h₁ 
: p₁ + n₁ = p₂) (h₂ : p₂ + n₂ …
· 使用引理 `CategoryTheory.Linear.units_smul_comp`：units_smul_comp {X Y Z : C} (r : 
Rˣ) (f : X ⟶ Y) (g : Y ⟶ Z) : (r • f) ≫ g = r • f ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
lemma leftShift_comp (a n' : ℤ) (hn' : n + a = n') {m t t' : ℤ} (γ' : Cochain L M m)
    (h : n + m = t) (ht' : t + a = t') :
    (γ.comp γ' h).leftShift a t' ht' = (a * m).negOnePow • (γ.leftShift a n' hn').comp γ'
      (by rw [← ht', ← h, ← hn', add_assoc, add_comm a, add_assoc]) := by
  ext p q hpq
  have h' : n' + m = t' := by lia
  dsimp
  simp only [Cochain.comp_v _ _ h' p (p + n') q rfl (by lia),
    γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
    (γ.comp γ' h).leftShift_v a t' (by lia) p q hpq (p + a) (by lia),
    smul_smul, Linear.units_smul_comp, assoc, Int.negOnePow_add, ← mul_assoc, ← h',
    comp_v _ _ h (p + a) (p + n') q (by lia) (by lia)]
  congr 2
  rw [add_comm n', mul_add, Int.negOnePow_add]

@[simp]
/-
**CochainComplex.HomComplex.Cochain.leftShift_comp_zero_cochain** 是 Mathlib 中的一个
引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_comp_zero_cochain (a n' : Int) (hn' : n + a = n') (γ' : Cochain 
L M 0) : (γ.comp γ' (add_zero n)).leftShift a n' hn' = (γ.leftShift a n' hn').co
mp γ' (add_zero n')
参数：a n' : Int；hn' : n + a = n'；γ' : Cochain L M 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_comp`：leftShift_comp (a n' :
 Int) (hn' : n + a = n') {m t t' : Int} (γ' : Cochain L M m) (h : n + m = t) (ht
' : t + a = t') : (γ.comp γ' h).leftSh…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用引理 `Int.negOnePow_zero`：negOnePow_zero : negOnePow 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
lemma leftShift_comp_zero_cochain (a n' : ℤ) (hn' : n + a = n') (γ' : Cochain L M 0) :
    (γ.comp γ' (add_zero n)).leftShift a n' hn' =
      (γ.leftShift a n' hn').comp γ' (add_zero n') := by
  rw [leftShift_comp γ a n' hn' γ' (add_zero _) hn', mul_zero, Int.negOnePow_zero, one_smul]

set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_rightShift (a n' m' : ℤ) (hn' : n' + a = n) (m : ℤ) (hm' : m' + a = m) :
    δ n' m' (γ.rightShift a n' hn') = a.negOnePow • (δ n m γ).rightShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).rightShift_v a m' hm' p q hpq _ rfl,
      δ_v n m hnm _ p (p + m) rfl (p + n) (p + 1) (by lia) rfl,
      δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl,
      γ.rightShift_v a n' hn' p (p + n') rfl (p + n) rfl,
      γ.rightShift_v a n' hn' (p + 1) q _ (p + m) (by lia)]
    simp only [shiftFunctorObjXIso, shiftFunctor_obj_d',
      Linear.comp_units_smul, assoc, HomologicalComplex.XIsoOfEq_inv_comp_d,
      add_comp, HomologicalComplex.d_comp_XIsoOfEq_inv, Linear.units_smul_comp, smul_add,
      add_right_inj, smul_smul]
    simp only [← hm', add_comm m', Int.negOnePow_add, ← mul_assoc,
      Int.units_mul_self, one_mul]
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by lia)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, rightShift_zero, smul_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_rightUnshift {a n' : ℤ} (γ : Cochain K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n)
    (m m' : ℤ) (hm' : m' + a = m) :
    δ n m (γ.rightUnshift n hn) = a.negOnePow • (δ n' m' γ).rightUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (rightShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [rightUnshift_rightShift, γ'.δ_rightShift a n' m' hn m hm', rightUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_leftShift (a n' m' : ℤ) (hn' : n + a = n') (m : ℤ) (hm' : m + a = m') :
    δ n' m' (γ.leftShift a n' hn') = a.negOnePow • (δ n m γ).leftShift a m' hm' := by
  by_cases hnm : n + 1 = m
  · have hnm' : n' + 1 = m' := by lia
    ext p q hpq
    dsimp
    rw [(δ n m γ).leftShift_v a m' hm' p q hpq (p + a) (by lia),
      δ_v n m hnm _ (p + a) q (by lia) (p + n') (p + 1 + a) (by lia) (by lia),
      δ_v n' m' hnm' _ p q hpq (p + n') (p + 1) (by lia) rfl,
      γ.leftShift_v a n' hn' p (p + n') rfl (p + a) (by lia),
      γ.leftShift_v a n' hn' (p + 1) q (by lia) (p + 1 + a) (by lia)]
    simp only [shiftFunctor_obj_X, shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
      Iso.refl_hom, id_comp, Linear.units_smul_comp, shiftFunctor_obj_d',
      Linear.comp_units_smul, smul_add, smul_smul]
    congr 2
    · rw [← hnm', add_comm n', mul_add, mul_one]
      simp only [Int.negOnePow_add, ← mul_assoc, Int.units_mul_self, one_mul]
    · simp only [← Int.negOnePow_add, ← hn', ← hm', ← hnm]
      congr 1
      linarith
  · have hnm' : ¬ n' + 1 = m' := fun _ => hnm (by lia)
    rw [δ_shape _ _ hnm', δ_shape _ _ hnm, leftShift_zero, smul_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_leftUnshift {a n' : ℤ} (γ : Cochain (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n')
    (m m' : ℤ) (hm' : m + a = m') :
    δ n m (γ.leftUnshift n hn) = a.negOnePow • (δ n' m' γ).leftUnshift m hm' := by
  obtain ⟨γ', rfl⟩ := (leftShiftAddEquiv K L n a n' hn).surjective γ
  dsimp
  simp only [leftUnshift_leftShift, γ'.δ_leftShift a n' m' hn m hm', leftUnshift_units_smul,
    smul_smul, Int.units_mul_self, one_smul]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**CochainComplex.HomComplex.Cochain.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.H
omComplex.Cochain`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_shift (a m : ℤ) :
    δ n m (γ.shift a) = a.negOnePow • (δ n m γ).shift a := by
  by_cases hnm : n + 1 = m
  · ext p q hpq
    dsimp
    simp only [shift_v', shiftFunctor_obj_d',
      δ_v n m hnm _ p q hpq (q - 1) (p + 1) rfl rfl,
      δ_v n m hnm _ (p + a) (q + a) (by lia) (q - 1 + a) (p + 1 + a)
        (by lia) (by lia),
      smul_add, Linear.units_smul_comp, Linear.comp_units_smul, add_right_inj]
    rw [smul_comm]
  · rw [δ_shape _ _ hnm, δ_shape _ _ hnm, shift_zero, smul_zero]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.leftShift_rightShift** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_rightShift (a n' : Int) (hn' : n' + a = n) : (γ.rightShift a n' 
hn').leftShift a n hn' = (a * n + (a * (a - 1)) / 2).negOnePow • γ.shift a
参数：a n' : Int；hn' : n' + a = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用引理 `CochainComplex.HomComplex.Cochain.shift_v'`：shift_v' (a : Int) (p q : In
t) (hpq : p + n = q) : (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma leftShift_rightShift (a n' : ℤ) (hn' : n' + a = n) :
    (γ.rightShift a n' hn').leftShift a n hn' =
      (a * n + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [leftShift_v _ a n hn' p q hpq (p + a) (by lia),
    rightShift_v _ a n' hn' (p + a) q (by lia) (q + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp, comp_id]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CochainComplex.HomComplex.Cochain.rightShift_leftShift** 是 Mathlib 中的一个引理，位于命名
空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：rightShift_leftShift (a n' : Int) (hn' : n + a = n') : (γ.leftShift a n' h
n').rightShift a n hn' = (a * n' + (a * (a - 1)) / 2).negOnePow • γ.shift a
参数：a n' : Int；hn' : n + a = n'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_v`：rightShift_v (a n' : Int
) (hn' : n' + a = n) (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p + n = p'
) : (γ.rightShift a n' hn').v p q hp…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_v`：leftShift_v (a n' : Int) 
(hn' : n + a = n') (p q : Int) (hpq : p + n' = q) (p' : Int) (hp' : p' + n = q) 
: (γ.leftShift a n' hn').v p q hpq …
· 使用引理 `CochainComplex.HomComplex.Cochain.shift_v'`：shift_v' (a : Int) (p q : In
t) (hpq : p + n = q) : (γ.shift a).v p q hpq = γ.v (p + a) (q + a) (by lia)
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
-/
lemma rightShift_leftShift (a n' : ℤ) (hn' : n + a = n') :
    (γ.leftShift a n' hn').rightShift a n hn' =
      (a * n' + (a * (a - 1)) / 2).negOnePow • γ.shift a := by
  ext p q hpq
  simp only [rightShift_v _ a n hn' p q hpq (q + a) (by lia),
    leftShift_v _ a n' hn' p (q + a) (by lia) (p + a) (by lia), units_smul_v, shift_v']
  dsimp
  rw [id_comp, comp_id]

/-- The left and right shift of cochains commute only up to a sign. -/
/-
**CochainComplex.HomComplex.Cochain.leftShift_rightShift_eq_negOnePow_rightShift
_leftShift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.HomComplex.Cochain`。
形式化陈述：leftShift_rightShift_eq_negOnePow_rightShift_leftShift (a n' n'' : Int) (h
n' : n' + a = n) (hn'' : n + a = n'') : (γ.rightShift a n' hn').leftShift a n hn
' = a.negOnePow • (γ.leftShift a n'' hn'').rightShift a n hn''
参数：a n' n'' : Int；hn' : n' + a = n；hn'' : n + a = n''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CochainComplex.HomComplex.Cochain.leftShift_rightShift`：leftShift_rightS
hift (a n' : Int) (hn' : n' + a = n) : (γ.rightShift a n' hn').leftShift a n hn'
 = (a * n + (a * (a - 1)) / 2).negOnePow • γ…
· 使用引理 `CochainComplex.HomComplex.Cochain.rightShift_leftShift`：rightShift_leftS
hift (a n' : Int) (hn' : n + a = n') : (γ.leftShift a n' hn').rightShift a n hn'
 = (a * n' + (a * (a - 1)) / 2).negOnePow • …
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用引理 `Int.negOnePow_add`：negOnePow_add (n₁ n₂ : Int) : (n₁ + n₂).negOnePow = n
₁.negOnePow * n₂.negOnePow
· 使用引理 `Int.negOnePow_mul_self`：negOnePow_mul_self (n : Int) : (n * n).negOnePow
 = n.negOnePow
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Int.units_mul_self`：units_mul_self (u : Intˣ) : u * u = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a

--- 原说明 ---
The left and right shift of cochains commute only up to a sign.
-/
lemma leftShift_rightShift_eq_negOnePow_rightShift_leftShift
    (a n' n'' : ℤ) (hn' : n' + a = n) (hn'' : n + a = n'') :
    (γ.rightShift a n' hn').leftShift a n hn' =
      a.negOnePow • (γ.leftShift a n'' hn'').rightShift a n hn'' := by
  rw [leftShift_rightShift, rightShift_leftShift, smul_smul, ← hn'', add_comm n a, mul_add,
    Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_add, Int.negOnePow_mul_self,
    ← mul_assoc, ← mul_assoc, Int.units_mul_self, one_mul]

end Cochain

namespace Cocycle

/-- The map `Cocycle K L n → Cocycle K (L⟦a⟧) n'` when `n' + a = n`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.rightShift** 是 Mathlib 中的一个定义，位于命名空间 `Cochai
nComplex.HomComplex.Cocycle`。
形式化陈述：rightShift (γ : Cocycle K L n) (a n' : Int) (hn' : n' + a = n) : Cocycle K
 (L⟦a⟧) n'
参数：γ : Cocycle K L n；a n' : Int；hn' : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cocycle K L n → Cocycle K (L⟦a⟧) n'` when `n' + a = n`.
-/
def rightShift (γ : Cocycle K L n) (a n' : ℤ) (hn' : n' + a = n) :
    Cocycle K (L⟦a⟧) n' :=
  Cocycle.mk (γ.1.rightShift a n' hn') _ rfl (by
    simp only [Cochain.δ_rightShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.rightShift_zero, smul_zero])

/-- The map `Cocycle K (L⟦a⟧) n' → Cocycle K L n` when `n' + a = n`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.rightUnshift** 是 Mathlib 中的一个定义，位于命名空间 `Coch
ainComplex.HomComplex.Cocycle`。
形式化陈述：rightUnshift {n' a : Int} (γ : Cocycle K (L⟦a⟧) n') (n : Int) (hn : n' + a
 = n) : Cocycle K L n
参数：γ : Cocycle K (L⟦a⟧) n'；n : Int；hn : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cocycle K (L⟦a⟧) n' → Cocycle K L n` when `n' + a = n`.
-/
def rightUnshift {n' a : ℤ} (γ : Cocycle K (L⟦a⟧) n') (n : ℤ) (hn : n' + a = n) :
    Cocycle K L n :=
  Cocycle.mk (γ.1.rightUnshift n hn) _ rfl (by
    rw [Cochain.δ_rightUnshift _ n hn (n + 1) (n + 1 - a) (by lia),
      δ_eq_zero, Cochain.rightUnshift_zero, smul_zero])

/-- The map `Cocycle K L n → Cocycle (K⟦a⟧) L n'` when `n + a = n'`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.leftShift** 是 Mathlib 中的一个定义，位于命名空间 `Cochain
Complex.HomComplex.Cocycle`。
形式化陈述：leftShift (γ : Cocycle K L n) (a n' : Int) (hn' : n + a = n') : Cocycle (K
⟦a⟧) L n'
参数：γ : Cocycle K L n；a n' : Int；hn' : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cocycle K L n → Cocycle (K⟦a⟧) L n'` when `n + a = n'`.
-/
def leftShift (γ : Cocycle K L n) (a n' : ℤ) (hn' : n + a = n') :
    Cocycle (K⟦a⟧) L n' :=
  Cocycle.mk (γ.1.leftShift a n' hn') _ rfl (by
    simp only [Cochain.δ_leftShift _ a n' (n' + 1) hn' (n + 1) (by lia),
      δ_eq_zero, Cochain.leftShift_zero, smul_zero])

/-- The map `Cocycle (K⟦a⟧) L n' → Cocycle K L n` when `n + a = n'`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.leftUnshift** 是 Mathlib 中的一个定义，位于命名空间 `Cocha
inComplex.HomComplex.Cocycle`。
形式化陈述：leftUnshift {n' a : Int} (γ : Cocycle (K⟦a⟧) L n') (n : Int) (hn : n + a =
 n') : Cocycle K L n
参数：γ : Cocycle (K⟦a⟧) L n'；n : Int；hn : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cocycle (K⟦a⟧) L n' → Cocycle K L n` when `n + a = n'`.
-/
def leftUnshift {n' a : ℤ} (γ : Cocycle (K⟦a⟧) L n') (n : ℤ) (hn : n + a = n') :
    Cocycle K L n :=
  Cocycle.mk (γ.1.leftUnshift n hn) _ rfl (by
    rw [Cochain.δ_leftUnshift _ n hn (n + 1) (n + 1 + a) rfl,
      δ_eq_zero, Cochain.leftUnshift_zero, smul_zero])

/-- The map `Cocycle K L n → Cocycle (K⟦a⟧) (L⟦a⟧) n`. -/
@[simps!]
/-
**CochainComplex.HomComplex.Cocycle.shift** 是 Mathlib 中的一个定义，位于命名空间 `CochainComp
lex.HomComplex.Cocycle`。
形式化陈述：shift (γ : Cocycle K L n) (a : Int) : Cocycle (K⟦a⟧) (L⟦a⟧) n
参数：γ : Cocycle K L n；a : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `Cocycle K L n → Cocycle (K⟦a⟧) (L⟦a⟧) n`.
-/
def shift (γ : Cocycle K L n) (a : ℤ) :
    Cocycle (K⟦a⟧) (L⟦a⟧) n :=
  Cocycle.mk (γ.1.shift a) _ rfl
    (by simp only [Cochain.δ_shift, δ_eq_zero, Cochain.shift_zero, smul_zero])

/-- The additive equivalence `Cocycle K L n ≃+ Cocycle K L⟦a⟧ n'` when `n' + a = n`. -/
@[simps]
/-
**CochainComplex.HomComplex.Cocycle.rightShiftAddEquiv** 是 Mathlib 中的一个定义，位于命名空间
 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：rightShiftAddEquiv (n a n' : Int) (hn' : n' + a = n) : Cocycle K L n ≃+ Co
cycle K (L⟦a⟧) n' where toFun γ
参数：n a n' : Int；hn' : n' + a = n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `Cocycle K L n ≃+ Cocycle K L⟦a⟧ n'` when `n' + a = n`.
-/
def rightShiftAddEquiv (n a n' : ℤ) (hn' : n' + a = n) :
    Cocycle K L n ≃+ Cocycle K (L⟦a⟧) n' where
  toFun γ := γ.rightShift a n' hn'
  invFun γ := γ.rightUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

/-- The additive equivalence `K ⟶ L⟦n⟧ ≃+ Cocycle K L n`. -/
@[simps! -isSimp apply symm_apply]
/-
**CochainComplex.HomComplex.Cocycle.equivHomShift** 是 Mathlib 中的一个定义，位于命名空间 `Coc
hainComplex.HomComplex.Cocycle`。
形式化陈述：equivHomShift : (K ⟶ L⟦n⟧) ≃+ Cocycle K L n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `K ⟶ L⟦n⟧ ≃+ Cocycle K L n`.
-/
def equivHomShift :
    (K ⟶ L⟦n⟧) ≃+ Cocycle K L n :=
  (equivHom _ _).trans (rightShiftAddEquiv _ _ _ (zero_add n)).symm

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.HomComplex.Cocycle.equivHomShift_comp** 是 Mathlib 中的一个引理，位于命名空间
 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：equivHomShift_comp {K' : CochainComplex C Int} (g : K' ⟶ K) (f : K ⟶ L⟦n⟧)
 : equivHomShift (g ≫ f) = Cocycle.precomp (equivHomShift f) g
参数：g : K' ⟶ K；f : K ⟶ L⟦n⟧。
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
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.equivHomShift_apply`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] 
  {K L : CochainComplex C ℤ} {n : ℤ} (a : K…
· 使用定理 `CochainComplex.HomComplex.Cocycle.rightUnshift_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} {n' a : ℤ}   (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_comp`：ofHom_comp (f : F ⟶ G) (g 
: G ⟶ K) : ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0)
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_v`：rightUnshift_v {n' a :
 Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (p q : Int) (hpq : p
 + n = q) (p' : Int) (hp' : p + n' = p…
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CochainComplex.HomComplex.Cocycle.precomp_coe`：∀ {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G K
 : CochainComplex C ℤ} {n : ℤ} (z :…
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivHomShift_comp {K' : CochainComplex C ℤ}
    (g : K' ⟶ K) (f : K ⟶ L⟦n⟧) :
    equivHomShift (g ≫ f) = Cocycle.precomp (equivHomShift f) g := by
  ext p q hpq
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]
/-
**CochainComplex.HomComplex.Cocycle.equivHomShift_symm_precomp** 是 Mathlib 中的一个引
理，位于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：equivHomShift_symm_precomp (z : Cocycle K L n) {K' : CochainComplex C Int}
 (g : K' ⟶ K) : equivHomShift.symm (z.precomp g) = g ≫ equivHomShift.symm z
参数：z : Cocycle K L n；g : K' ⟶ K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用引理 `CochainComplex.HomComplex.Cocycle.equivHomShift_comp`：equivHomShift_comp
 {K' : CochainComplex C Int} (g : K' ⟶ K) (f : K ⟶ L⟦n⟧) : equivHomShift (g ≫ f)
 = Cocycle.precomp (equivHomShift f) g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivHomShift_symm_precomp
    (z : Cocycle K L n) {K' : CochainComplex C ℤ} (g : K' ⟶ K) :
    equivHomShift.symm (z.precomp g) = g ≫ equivHomShift.symm z :=
  equivHomShift.injective (by simp [equivHomShift_comp])

set_option backward.isDefEq.respectTransparency.types false in
/-
**CochainComplex.HomComplex.Cocycle.equivHomShift_comp_shift** 是 Mathlib 中的一个引理，
位于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：equivHomShift_comp_shift (f : K ⟶ L⟦n⟧) {L' : CochainComplex C Int} (g : L
 ⟶ L') : equivHomShift (f ≫ g⟦n⟧') = Cocycle.postcomp (equivHomShift f) g
参数：f : K ⟶ L⟦n⟧；g : L ⟶ L'。
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
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.Cocycle.equivHomShift_apply`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C] 
  {K L : CochainComplex C ℤ} {n : ℤ} (a : K…
· 使用定理 `CochainComplex.HomComplex.Cocycle.rightUnshift_coe`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {
K L : CochainComplex C ℤ} {n' a : ℤ}   (…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CochainComplex.HomComplex.Cocycle.ofHom_coe`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : C
ochainComplex C ℤ} (φ : F ⟶ G),  …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_comp`：ofHom_comp (f : F ⟶ G) (g 
: G ⟶ K) : ofHom (f ≫ g) = (ofHom f).comp (ofHom g) (zero_add 0)
· 使用引理 `CochainComplex.HomComplex.Cochain.rightUnshift_v`：rightUnshift_v {n' a :
 Int} (γ : Cochain K (L⟦a⟧) n') (n : Int) (hn : n' + a = n) (p q : Int) (hpq : p
 + n = q) (p' : Int) (hp' : p + n' = p…
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CochainComplex.HomComplex.Cocycle.postcomp_coe`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
K : CochainComplex C ℤ} {n : ℤ} (z :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivHomShift_comp_shift (f : K ⟶ L⟦n⟧) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    equivHomShift (f ≫ g⟦n⟧') = Cocycle.postcomp (equivHomShift f) g := by
  ext p q rfl
  simp [equivHomShift_apply, Cochain.rightUnshift_v _ _ _ _ _ _ _ (add_zero p)]
/-
**CochainComplex.HomComplex.Cocycle.equivHomShift_symm_postcomp** 是 Mathlib 中的一个
引理，位于命名空间 `CochainComplex.HomComplex.Cocycle`。
形式化陈述：equivHomShift_symm_postcomp (z : Cocycle K L n) {L' : CochainComplex C Int
} (g : L ⟶ L') : equivHomShift.symm (z.postcomp g) = equivHomShift.symm z ≫ g⟦n⟧
'
参数：z : Cocycle K L n；g : L ⟶ L'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `AddEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M] [inst
_1 : Add N] (e : M ≃+ N), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddEquiv.apply_symm_apply`：∀ {M : Type u_4} {N : Type u_5} [inst : Add M
] [inst_1 : Add N] (e : M ≃+ N) (y : N), e (e.symm y) = y
· 使用引理 `CochainComplex.HomComplex.Cocycle.equivHomShift_comp_shift`：equivHomShif
t_comp_shift (f : K ⟶ L⟦n⟧) {L' : CochainComplex C Int} (g : L ⟶ L') : equivHomS
hift (f ≫ g⟦n⟧') = Cocycle.postcomp (equivHomShi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equivHomShift_symm_postcomp
    (z : Cocycle K L n) {L' : CochainComplex C ℤ} (g : L ⟶ L') :
    equivHomShift.symm (z.postcomp g) = equivHomShift.symm z ≫ g⟦n⟧' :=
  equivHomShift.injective (by simp [equivHomShift_comp_shift])

/-- The additive equivalence `Cocycle K L n ≃+ Cocycle K⟦a⟧ L n'` when `n + a = n'`. -/
@[simps]
/-
**CochainComplex.HomComplex.Cocycle.leftShiftAddEquiv** 是 Mathlib 中的一个定义，位于命名空间 
`CochainComplex.HomComplex.Cocycle`。
形式化陈述：leftShiftAddEquiv (n a n' : Int) (hn' : n + a = n') : Cocycle K L n ≃+ Coc
ycle (K⟦a⟧) L n' where toFun γ
参数：n a n' : Int；hn' : n + a = n'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `Cocycle K L n ≃+ Cocycle K⟦a⟧ L n'` when `n + a = n'`.
-/
def leftShiftAddEquiv (n a n' : ℤ) (hn' : n + a = n') :
    Cocycle K L n ≃+ Cocycle (K⟦a⟧) L n' where
  toFun γ := γ.leftShift a n' hn'
  invFun γ := γ.leftUnshift n hn'
  left_inv γ := by cat_disch
  right_inv γ := by cat_disch
  map_add' γ γ' := by cat_disch

/-- The additive equivalence `(K⟦n⟧) ⟶ L ≃+ Cocycle K L m` when `m + n = 0`. -/
@[simps! -isSimp apply symm_apply]
/-
**CochainComplex.HomComplex.Cocycle.equivHomShift'** 是 Mathlib 中的一个定义，位于命名空间 `Co
chainComplex.HomComplex.Cocycle`。
形式化陈述：equivHomShift' (n m : Int) (h : m + n = 0) : ((K⟦n⟧) ⟶ L) ≃+ Cocycle K L m
参数：n m : Int；h : m + n = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The additive equivalence `(K⟦n⟧) ⟶ L ≃+ Cocycle K L m` when `m + n = 0`.
-/
def equivHomShift' (n m : ℤ) (h : m + n = 0) :
    ((K⟦n⟧) ⟶ L) ≃+ Cocycle K L m :=
  (equivHom _ _).trans (leftShiftAddEquiv _ _ _ h).symm

end Cocycle

end CochainComplex.HomComplex

