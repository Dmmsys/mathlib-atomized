/-
Copyright (c) 2026 Justus Springer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Justus Springer
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.ClosureShift
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-!
# Generators in triangulated categories

We define the notions of strong and classical generators in (pre)triangulated categories.
This is not to be confused with `ObjectProperty.IsStrongGenerator` defined in
`CategoryTheory/Generator`.

## Main definitions

- `ObjectProperty.triangEnvelopeIter P n`: The object property of all objects reachable from `P`
  by shifts, binary products, retracts and at most `n` extensions.
- `ObjectProperty.triangEnvelope P`: The triangulated envelope of `P`, i.e., the object property
  of all objects reachable from `P` by shifts, binary products, retracts and extensions. This is
  the smallest triangulated object property closed under retracts that contains `P`, see
  `ObjectProperty.triangEnvelope_le_iff`.
- `ObjectProperty.IsStrongTriangulatedGenerator P`: `P` is a strong triangulated generator if
  there exists `n` such that every object is in `P.triangEnvelopeIter n`.
- `ObjectProperty.IsClassicalTriangulatedGenerator P`: `P` is a classical triangulated generator
  if every object is in `P.triangEnvelope`.

## Main results

- `ObjectProperty.triangEnvelope_le_iff`: The universal property of `P.triangEnvelope`: it is
  the smallest triangulated object property closed under retracts that contains `P`.
- `ObjectProperty.IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator`: A strong
  triangulated generator is a classical triangulated generator.

## TODO

* Prove that if `C` has a strong generator and `P` is a classical generator, then `P` is a
  strong generator (stacks 0FXA).

## References

* [Bondal and Van den Bergh, *Generators and representability of functors in commutative and
  noncommutative geometry*][bondal_vandenbergh_2003]
* [Stacks 09SJ](https://stacks.math.columbia.edu/tag/09SJ)

-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

open Category Limits Preadditive ZeroObject Pretriangulated Triangulated

variable {C : Type*} [Category* C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] (P : ObjectProperty C)

/-- All objects that can be reached by shifts, binary products, retracts and at most `n`
extensions from objects in `P`. -/
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter** 是 Mathlib 中的一个缩写定义，位于命名空间 `
CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter (n : Nat) : ObjectProperty C
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All objects that can be reached by shifts, binary products, retracts and at most
 `n`
extensions from objects in `P`.
-/
abbrev triangEnvelopeIter (n : ℕ) : ObjectProperty C :=
  ((P.shiftClosure ℤ).binaryProductsClosure.retractClosure.extensionProductIter n).retractClosure

@[simp]
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter_zero** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter_zero : P.triangEnvelopeIter 0 = (P.shiftClosure Int).bi
naryProductsClosure.retractClosure
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.triangEnvelopeIter.eq_1`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_zero`：extensionProduc
tIter_zero : P.extensionProductIter 0 = P
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_eq_self`：retractClosure_eq_
self [IsStableUnderRetracts P] : retractClosure P = P
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderRetractsRetractClosure`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C),   P.retractClosure.IsStableUnderRetracts
-/
lemma triangEnvelopeIter_zero :
    P.triangEnvelopeIter 0 = (P.shiftClosure ℤ).binaryProductsClosure.retractClosure := by
  rw [triangEnvelopeIter, extensionProductIter_zero, retractClosure_eq_self]
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter_succ** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter_succ (n : Nat) : P.triangEnvelopeIter (n + 1) = (extens
ionProduct (P.shiftClosure Int).binaryProductsClosure.retractClosure (P.triangEn
velopeIter n)).retractClosure
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.triangEnvelopeIter.eq_1`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_succ`：extensionProduc
tIter_succ (n : Nat) : P.extensionProductIter (n + 1) = extensionProduct P (P.ex
tensionProductIter n)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClo
sure_retractClosure`：retractClosure_extensionProduct_retractClosure_retractClosu
re : (extensionProduct P.retractClosure Q.retractClosure).retractClosure = (exte
n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_retractClosure`：retractClos
ure_retractClosure : P.retractClosure.retractClosure = P.retractClosure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma triangEnvelopeIter_succ (n : ℕ) :
    P.triangEnvelopeIter (n + 1) =
      (extensionProduct (P.shiftClosure ℤ).binaryProductsClosure.retractClosure
         (P.triangEnvelopeIter n)).retractClosure := by
  rw [triangEnvelopeIter, extensionProductIter_succ,
    ← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter_succ'** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter_succ' [IsTriangulated C] (n : Nat) : P.triangEnvelopeIt
er (n + 1) = (extensionProduct (P.triangEnvelopeIter n) (P.shiftClosure Int).bin
aryProductsClosure.retractClosure).retractClosure
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.triangEnvelopeIter.eq_1`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_succ'`：extensionProdu
ctIter_succ' [IsTriangulated C] (n : Nat) : P.extensionProductIter (n + 1) = ext
ensionProduct (P.extensionProductIter n) P
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClo
sure_retractClosure`：retractClosure_extensionProduct_retractClosure_retractClosu
re : (extensionProduct P.retractClosure Q.retractClosure).retractClosure = (exte
n…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_retractClosure`：retractClos
ure_retractClosure : P.retractClosure.retractClosure = P.retractClosure
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma triangEnvelopeIter_succ' [IsTriangulated C] (n : ℕ) :
    P.triangEnvelopeIter (n + 1) =
      (extensionProduct (P.triangEnvelopeIter n)
        (P.shiftClosure ℤ).binaryProductsClosure.retractClosure).retractClosure := by
  rw [triangEnvelopeIter, extensionProductIter_succ',
    ← retractClosure_extensionProduct_retractClosure_retractClosure]
  simp
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter_add** 是 Mathlib 中的一个引理，位于命名空间
 `CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter_add [IsTriangulated C] {n m n' : Nat} (h : n = n' + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_add`：extensionProduct
Iter_add [IsTriangulated C] {n m n' : Nat} (h : n = n' + 1) : P.extensionProduct
Iter (n + m) = extensionProduct (P.extension…
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClo
sure_retractClosure`：retractClosure_extensionProduct_retractClosure_retractClosu
re : (extensionProduct P.retractClosure Q.retractClosure).retractClosure = (exte
n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma triangEnvelopeIter_add [IsTriangulated C] {n m n' : ℕ} (h : n = n' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n') (P.triangEnvelopeIter m)).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add _ h]
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter_add'** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter_add' [IsTriangulated C] {n m m' : Nat} (h : m = m' + 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_add'`：extensionProduc
tIter_add' [IsTriangulated C] {n m m' : Nat} (h : m = m' + 1) : P.extensionProdu
ctIter (n + m) = extensionProduct (P.extensio…
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_extensionProduct_retractClo
sure_retractClosure`：retractClosure_extensionProduct_retractClosure_retractClosu
re : (extensionProduct P.retractClosure Q.retractClosure).retractClosure = (exte
n…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma triangEnvelopeIter_add' [IsTriangulated C] {n m m' : ℕ} (h : m = m' + 1 := by lia) :
    P.triangEnvelopeIter (n + m) =
      (extensionProduct (P.triangEnvelopeIter n) (P.triangEnvelopeIter m')).retractClosure := by
  simp only [triangEnvelopeIter, retractClosure_extensionProduct_retractClosure_retractClosure,
    extensionProductIter_add' _ h]

variable {P} in
/-
**CategoryTheory.ObjectProperty.monotone_triangEnvelopeIter** 是 Mathlib 中的一个引理，位
于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：monotone_triangEnvelopeIter {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat
) : P.triangEnvelopeIter n <= Q.triangEnvelopeIter n
参数：hPQ : P <= Q；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.monotone_retractClosure`：monotone_retractC
losure (h : P <= Q) : retractClosure P <= retractClosure Q
· 使用引理 `CategoryTheory.ObjectProperty.monotone_extensionProductIter`：monotone_ex
tensionProductIter {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat) : P.extension
ProductIter n <= Q.extensionProductIter n
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_monotone`：limitsClosure_mono
tone {Q : ObjectProperty C} (h : P <= Q) : P.limitsClosure J <= Q.limitsClosure 
J
· 使用引理 `CategoryTheory.ObjectProperty.monotone_shiftClosure`：monotone_shiftClosu
re (h : P <= Q) : P.shiftClosure A <= Q.shiftClosure A
-/
lemma monotone_triangEnvelopeIter {Q : ObjectProperty C} (hPQ : P ≤ Q) (n : ℕ) :
    P.triangEnvelopeIter n ≤ Q.triangEnvelopeIter n :=
  monotone_retractClosure <| monotone_extensionProductIter
    (monotone_retractClosure <| limitsClosure_monotone _ <| monotone_shiftClosure hPQ) n
/-
**CategoryTheory.ObjectProperty.monotone'_triangEnvelopeIter** 是 Mathlib 中的一个定理，
位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.HasShift C ℤ] [
inst_3 : CategoryTheory.Preadditive C]   [inst_4 : ∀ (n : ℤ), (CategoryTheory.sh
iftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]   (P : Cat
egoryTheory.ObjectProperty C) {n m : ℕ},   autoParam (n ≤ m) CategoryTheory.Obje
ctProperty.monotone'_triangEnvelopeIter._auto_1 →     P.triangEnvelopeIter n ≤ P
.triangEnvelopeIter m
参数：n : ℤ；CategoryTheory.shiftFunctor C n；P : CategoryTheory.ObjectProperty C；n ≤
 m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.monotone_retractClosure`：monotone_retractC
losure (h : P <= Q) : retractClosure P <= retractClosure Q
· 使用定理 `CategoryTheory.ObjectProperty.monotone'_extensionProductIter`：∀ {C : Typ
e u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Li
mits.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.instContainsZeroOfHa
sZeroObjectOfNonempty`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] 
(P : CategoryTheory.ObjectProperty C) [P.IsStableUnderRetracts]   [CategoryTheor
y.L…
· 使用定理 `CategoryTheory.ObjectProperty.instIsStableUnderRetractsRetractClosure`：∀
 {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.Obje
ctProperty C),   P.retractClosure.IsStableUnderRetracts
· 使用定理 `CategoryTheory.ObjectProperty.instNonemptyRetractClosure`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C)
 [P.Nonempty],   P.retractClosure.Nonempty
· 使用定理 `CategoryTheory.ObjectProperty.instNonemptyLimitsClosure`：∀ {C : Type u} 
[inst : CategoryTheory.Category.{v, u} C] (P : CategoryTheory.ObjectProperty C) 
{α : Type t}   (J : α → Type u') [inst_1 : (a…
· 使用定理 `CategoryTheory.ObjectProperty.instNonemptyShiftClosure`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectPropert
y C) {A : Type u_2}   [inst_1 : AddMonoid A]…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_bot`：shiftClosure_bot : shift
Closure (⊥ : ObjectProperty C) A = ⊥
· 使用引理 `CategoryTheory.ObjectProperty.limitsClosure_bot`：limitsClosure_bot [fora
ll (a : α), Nonempty (J a)] : limitsClosure (⊥ : ObjectProperty C) J = ⊥
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_bot`：retractClosure_bot : r
etractClosure (⊥ : ObjectProperty C) = ⊥
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_bot`：extensionProduct
Iter_bot (n : Nat) : extensionProductIter (⊥ : ObjectProperty C) n = ⊥
-/
lemma monotone'_triangEnvelopeIter {n m : ℕ} (h : n ≤ m := by lia) :
    P.triangEnvelopeIter n ≤ P.triangEnvelopeIter m := by
  apply monotone_retractClosure
  by_cases! hP : P.Nonempty
  · exact monotone'_extensionProductIter _ h
  · simp [hP]
/-
**CategoryTheory.ObjectProperty.le_triangEnvelopeIter** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：le_triangEnvelopeIter (n : Nat) : P <= P.triangEnvelopeIter n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ObjectProperty.le_shiftClosure`：le_shiftClosure : P <= P.
shiftClosure A
· 使用引理 `CategoryTheory.ObjectProperty.le_limitsClosure`：le_limitsClosure : P <= 
P.limitsClosure J
· 使用引理 `CategoryTheory.ObjectProperty.le_retractClosure`：le_retractClosure : P <
= retractClosure P
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.ObjectProperty.triangEnvelopeIter_zero`：triangEnvelopeIte
r_zero : P.triangEnvelopeIter 0 = (P.shiftClosure Int).binaryProductsClosure.ret
ractClosure
· 使用定理 `CategoryTheory.ObjectProperty.monotone'_triangEnvelopeIter`：∀ {C : Type 
u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limi
ts.HasZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
-/
lemma le_triangEnvelopeIter (n : ℕ) : P ≤ P.triangEnvelopeIter n :=
  calc
    P ≤ P.shiftClosure ℤ := le_shiftClosure _
    _ ≤ (P.shiftClosure ℤ).binaryProductsClosure := le_limitsClosure _ _
    _ ≤ (P.shiftClosure ℤ).binaryProductsClosure.retractClosure := le_retractClosure _
    _ ≤ P.triangEnvelopeIter n := by
      rw [← triangEnvelopeIter_zero]
      exact P.monotone'_triangEnvelopeIter (Nat.zero_le n)

/-- An object property `P` is called a strong triangulated generator, if every object
can be reached from objects in `P` by shifts, binary products, retracts and at most `n`
extensions, for some fixed `n`. -/
@[stacks 09SJ "(2)"]
/-
**CategoryTheory.ObjectProperty.IsStrongTriangulatedGenerator** 是 Mathlib 中的一个定义
，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsStrongTriangulatedGenerator : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object property `P` is called a strong triangulated generator, if every objec
t
can be reached from objects in `P` by shifts, binary products, retracts and at m
ost `n`
extensions, for some fixed `n`.
-/
def IsStrongTriangulatedGenerator : Prop := ∃ n, P.triangEnvelopeIter n = ⊤
/-
**CategoryTheory.ObjectProperty.isStrongTriangulatedGenerator_iff** 是 Mathlib 中的
一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isStrongTriangulatedGenerator_iff : P.IsStrongTriangulatedGenerator ↔ exis
ts n, P.triangEnvelopeIter n = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isStrongTriangulatedGenerator_iff :
    P.IsStrongTriangulatedGenerator ↔ ∃ n, P.triangEnvelopeIter n = ⊤ := Iff.rfl

/-- All objects that can be reached by shifts, binary products, retracts and extensions
from objects in `P`. This is the smallest triangulated object property closed under retracts
that contains `P`, see `ObjectProperty.triangEnvelope_le_iff`. -/
/-
**CategoryTheory.ObjectProperty.triangEnvelope** 是 Mathlib 中的一个定义，位于命名空间 `Catego
ryTheory.ObjectProperty`。
形式化陈述：triangEnvelope : ObjectProperty C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
All objects that can be reached by shifts, binary products, retracts and extensi
ons
from objects in `P`. This is the smallest triangulated object property closed un
der retracts
that contains `P`, see `ObjectProperty.triangEnvelope_le_iff`.
-/
def triangEnvelope : ObjectProperty C := ⨆ n, P.triangEnvelopeIter n
/-
**CategoryTheory.ObjectProperty.prop_triangEnvelope_iff** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：prop_triangEnvelope_iff (X : C) : P.triangEnvelope X ↔ exists n, P.triangE
nvelopeIter n X
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.ObjectProperty.prop_iSup_iff`：∀ {C : Type u} [inst : Cate
goryTheory.Category.{v, u} C] {α : Sort u_1} (P : α → CategoryTheory.ObjectPrope
rty C)   (X : C), (⨆ a, P a) X ↔ …
-/
lemma prop_triangEnvelope_iff (X : C) : P.triangEnvelope X ↔ ∃ n, P.triangEnvelopeIter n X :=
  prop_iSup_iff _ X
/-
**CategoryTheory.ObjectProperty.triangEnvelopeIter_le_triangEnvelope** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelopeIter_le_triangEnvelope (n : Nat) : P.triangEnvelopeIter n <=
 P.triangEnvelope
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
lemma triangEnvelopeIter_le_triangEnvelope (n : ℕ) : P.triangEnvelopeIter n ≤ P.triangEnvelope :=
  le_iSup _ _
/-
**CategoryTheory.ObjectProperty.le_triangEnvelope** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory.ObjectProperty`。
形式化陈述：le_triangEnvelope : P <= P.triangEnvelope
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.le_triangEnvelopeIter`：le_triangEnvelopeIt
er (n : Nat) : P <= P.triangEnvelopeIter n
· 使用引理 `CategoryTheory.ObjectProperty.triangEnvelopeIter_le_triangEnvelope`：tria
ngEnvelopeIter_le_triangEnvelope (n : Nat) : P.triangEnvelopeIter n <= P.triangE
nvelope
-/
lemma le_triangEnvelope : P ≤ P.triangEnvelope :=
  (P.le_triangEnvelopeIter 0).trans (P.triangEnvelopeIter_le_triangEnvelope 0)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] : P.triangEnvelope.Nonempty :=
  .mono P.le_triangEnvelope

variable {P} in
/-
**CategoryTheory.ObjectProperty.monotone_triangEnvelope** 是 Mathlib 中的一个引理，位于命名空
间 `CategoryTheory.ObjectProperty`。
形式化陈述：monotone_triangEnvelope {Q : ObjectProperty C} (h : P <= Q) : P.triangEnve
lope <= Q.triangEnvelope
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `CategoryTheory.ObjectProperty.monotone_triangEnvelopeIter`：monotone_tria
ngEnvelopeIter {Q : ObjectProperty C} (hPQ : P <= Q) (n : Nat) : P.triangEnvelop
eIter n <= Q.triangEnvelopeIter n
· 使用引理 `CategoryTheory.ObjectProperty.triangEnvelopeIter_le_triangEnvelope`：tria
ngEnvelopeIter_le_triangEnvelope (n : Nat) : P.triangEnvelopeIter n <= P.triangE
nvelope
-/
lemma monotone_triangEnvelope {Q : ObjectProperty C} (h : P ≤ Q) :
    P.triangEnvelope ≤ Q.triangEnvelope :=
  iSup_le fun n => (P.monotone_triangEnvelopeIter h n).trans
    (Q.triangEnvelopeIter_le_triangEnvelope n)
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.triangEnvelope.IsStableUnderRetracts where
  of_retract := by
    intro X Y r hY
    rw [prop_triangEnvelope_iff] at hY ⊢
    obtain ⟨n, hn⟩ := hY
    exact ⟨n, IsStableUnderRetracts.of_retract r hn⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : P.triangEnvelope.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := IsStableUnderShiftBy.mk <| by
    intro X hX
    rw [prop_triangEnvelope_iff] at hX
    obtain ⟨n, hn⟩ := hX
    rw [prop_shift_iff, prop_triangEnvelope_iff]
    exact ⟨n, IsStableUnderShiftBy.le_shift _ hn⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTriangulated C] : P.triangEnvelope.IsTriangulatedClosed₂ := by
  apply IsTriangulatedClosed₂.mk'
  intro T hT h₁ h₂
  rw [prop_triangEnvelope_iff] at h₁ h₂ ⊢
  obtain ⟨n, hn⟩ := h₁
  obtain ⟨m, hm⟩ := h₂
  use n + (m + 1)
  rw [triangEnvelopeIter_add' P rfl]
  exact le_retractClosure _ _ ⟨_, _, _, _, _, hT, hn, hm⟩
/-
**CategoryTheory.ObjectProperty.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Objec
tProperty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.Nonempty] [IsTriangulated C] : P.triangEnvelope.IsTriangulated where
/-
**CategoryTheory.ObjectProperty.triangEnvelope_le_iff** 是 Mathlib 中的一个引理，位于命名空间 
`CategoryTheory.ObjectProperty`。
形式化陈述：triangEnvelope_le_iff {Q : ObjectProperty C} [Q.IsStableUnderRetracts] [Q.
IsTriangulated] : P.triangEnvelope <= Q ↔ P <= Q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.ObjectProperty.le_triangEnvelope`：le_triangEnvelope : P <
= P.triangEnvelope
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.ObjectProperty.triangEnvelope.eq_1`：∀ {C : Type u_1} [ins
t : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZer
oObject C]   [inst_2 : CategoryTheory.H…
· 使用定理 `iSup_le_iff`：iSup_le_iff : iSup f <= a ↔ forall i, f i <= a
· 使用定理 `CategoryTheory.ObjectProperty.triangEnvelopeIter.eq_1`：∀ {C : Type u_1} 
[inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.Ha
sZeroObject C]   [inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.ObjectProperty.retractClosure_le_iff`：retractClosure_le_i
ff (Q : ObjectProperty C) [IsStableUnderRetracts Q] : retractClosure P <= Q ↔ P 
<= Q
· 使用引理 `CategoryTheory.ObjectProperty.extensionProductIter_le_of_isTriangulatedC
losed₂`：extensionProductIter_le_of_isTriangulatedClosed₂ {Q : ObjectProperty C} 
[Q.IsTriangulatedClosed₂] [Q.IsClosedUnderIsomorphisms] (h : P <= Q)…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsTriangulatedClosed₂`：∀ 
{C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryT
heory.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.IsStableUnderRetracts.instIsClosedUnderIso
morphisms`：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (P : Categor
yTheory.ObjectProperty C)   [P.IsStableUnderRetracts], P.IsClosedUnderI…
· 使用引理 `CategoryTheory.ObjectProperty.binaryProductsClosure_le_iff`：binaryProduc
tsClosure_le_iff [HasTerminal C] {P Q : ObjectProperty C} [Q.IsClosedUnderBinary
Products] [Q.IsClosedUnderLimitsOfShape (Discret…
· 使用定理 `CategoryTheory.Pretriangulated.instHasFiniteProducts`：∀ {C : Type u} [in
st : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroOb
ject C]   [inst_2 : CategoryTheory.HasShif…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderBinaryProductsOfIsTriangu
latedOfIsClosedUnderIsomorphisms`：∀ {C : Type u_1} [inst : CategoryTheory.Catego
ry.{v_1, u_1} C] [inst_1 : CategoryTheory.Limits.HasZeroObject C]   [inst_2 : Ca
tegoryTheory.H…
· 使用定理 `CategoryTheory.ObjectProperty.instIsClosedUnderLimitsOfShapeDiscretePEmp
tyOfContainsZeroOfIsClosedUnderIsomorphisms`：∀ {C : Type u_1} [inst : CategoryTh
eory.Category.{v_1, u_1} C] (P : CategoryTheory.ObjectProperty C) [P.ContainsZer
o]   [P.IsClosedUnderIsom…
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toContainsZero`：∀ {C : Type
 u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheory.Lim
its.HasZeroObject C}   {inst_2 : CategoryTheory.H…
· 使用引理 `CategoryTheory.ObjectProperty.shiftClosure_le_iff`：shiftClosure_le_iff [
IsClosedUnderIsomorphisms Q] [Q.IsStableUnderShift A] : shiftClosure P A <= Q ↔ 
P <= Q
· 使用定理 `CategoryTheory.ObjectProperty.IsTriangulated.toIsStableUnderShift`：∀ {C 
: Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {inst_1 : CategoryTheo
ry.Limits.HasZeroObject C}   {inst_2 : CategoryTheory.H…
-/
lemma triangEnvelope_le_iff {Q : ObjectProperty C} [Q.IsStableUnderRetracts] [Q.IsTriangulated] :
    P.triangEnvelope ≤ Q ↔ P ≤ Q := by
  refine ⟨fun h ↦ le_trans P.le_triangEnvelope h, fun h ↦ ?_⟩
  rw [triangEnvelope, iSup_le_iff]
  intro n
  rw [triangEnvelopeIter, retractClosure_le_iff]
  apply extensionProductIter_le_of_isTriangulatedClosed₂
  rwa [retractClosure_le_iff, binaryProductsClosure_le_iff, shiftClosure_le_iff]

/-- An object property `P` is called a classical generator, if every object can be reached
from objects in `P` by shifts, binary products, retracts and extensions. -/
@[stacks 09SJ "(1)"]
/-
**CategoryTheory.ObjectProperty.IsClassicalTriangulatedGenerator** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：IsClassicalTriangulatedGenerator : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An object property `P` is called a classical generator, if every object can be r
eached
from objects in `P` by shifts, binary products, retracts and extensions.
-/
def IsClassicalTriangulatedGenerator : Prop := P.triangEnvelope = ⊤
/-
**CategoryTheory.ObjectProperty.isClassicalTriangulatedGenerator_iff** 是 Mathlib
 中的一个引理，位于命名空间 `CategoryTheory.ObjectProperty`。
形式化陈述：isClassicalTriangulatedGenerator_iff : P.IsClassicalTriangulatedGenerator 
↔ P.triangEnvelope = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isClassicalTriangulatedGenerator_iff :
    P.IsClassicalTriangulatedGenerator ↔ P.triangEnvelope = ⊤ := Iff.rfl
/-
**CategoryTheory.ObjectProperty.IsStrongTriangulatedGenerator.isClassicalTriangu
latedGenerator** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.ObjectProperty.IsStrong
TriangulatedGenerator`。
形式化陈述：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : C
ategoryTheory.Limits.HasZeroObject C]   [inst_2 : CategoryTheory.HasShift C ℤ] [
inst_3 : CategoryTheory.Preadditive C]   [inst_4 : ∀ (n : ℤ), (CategoryTheory.sh
iftFunctor C n).Additive] [inst_5 : CategoryTheory.Pretriangulated C]   (P : Cat
egoryTheory.ObjectProperty C), P.IsStrongTriangulatedGenerator → P.IsClassicalTr
iangulatedGenerator
参数：n : ℤ；CategoryTheory.shiftFunctor C n；P : CategoryTheory.ObjectProperty C。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.ObjectProperty.isClassicalTriangulatedGenerator_iff`：isCl
assicalTriangulatedGenerator_iff : P.IsClassicalTriangulatedGenerator ↔ P.triang
Envelope = ⊤
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用引理 `CategoryTheory.ObjectProperty.triangEnvelopeIter_le_triangEnvelope`：tria
ngEnvelopeIter_le_triangEnvelope (n : Nat) : P.triangEnvelopeIter n <= P.triangE
nvelope
-/
lemma IsStrongTriangulatedGenerator.isClassicalTriangulatedGenerator
    (h : P.IsStrongTriangulatedGenerator) : P.IsClassicalTriangulatedGenerator := by
  obtain ⟨n, hn⟩ := h
  rw [isClassicalTriangulatedGenerator_iff, eq_top_iff]
  exact hn ▸ (P.triangEnvelopeIter_le_triangEnvelope n)

end CategoryTheory.ObjectProperty

