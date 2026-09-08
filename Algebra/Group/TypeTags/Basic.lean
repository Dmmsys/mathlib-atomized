/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Algebra.Group.Torsion
public import Mathlib.Algebra.Notation.Pi.Basic
public import Mathlib.Data.FunLike.Basic
public import Mathlib.Logic.Function.Iterate
public import Mathlib.Logic.Equiv.Defs

/-!
# Type tags that turn additive structures into multiplicative, and vice versa

We define two type tags:

* `Additive α`: turns any multiplicative structure on `α` into the corresponding
  additive structure on `Additive α`;
* `Multiplicative α`: turns any additive structure on `α` into the corresponding
  multiplicative structure on `Multiplicative α`.

We also define instances `Additive.*` and `Multiplicative.*` that actually transfer the structures.

## See also

This file is similar to `Mathlib/Order/Synonym.lean`.

-/

@[expose] public section

assert_not_exists MonoidWithZero DenselyOrdered MonoidHom Finite

universe u v

variable {α : Type u} {β : Type v}

/-- If `α` carries some multiplicative structure, then `Additive α` carries the corresponding
additive structure. -/
/-
**Additive** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Additive (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` carries some multiplicative structure, then `Additive α` carries the corr
esponding
additive structure.
-/
def Additive (α : Type*) := α

/-- If `α` carries some additive structure, then `Multiplicative α` carries the corresponding
multiplicative structure. -/
/-
**Multiplicative** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Multiplicative (α : Type*)
参数：α : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` carries some additive structure, then `Multiplicative α` carries the corr
esponding
multiplicative structure.
-/
def Multiplicative (α : Type*) := α

namespace Additive

/-- Reinterpret `x : α` as an element of `Additive α`. -/
@[implicit_reducible]
/-
**Additive.ofMul** 是 Mathlib 中的一个定义，位于命名空间 `Additive`。
形式化陈述：ofMul : α ≃ Additive α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `x : α` as an element of `Additive α`.
-/
def ofMul : α ≃ Additive α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Additive α` as an element of `α`. -/
@[implicit_reducible]
/-
**Additive.toMul** 是 Mathlib 中的一个定义，位于命名空间 `Additive`。
形式化陈述：toMul : Additive α ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `x : Additive α` as an element of `α`.
-/
def toMul : Additive α ≃ α := ofMul.symm

@[simp]
/-
**Additive.ofMul_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：ofMul_symm_eq : (@ofMul α).symm = toMul
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofMul_symm_eq : (@ofMul α).symm = toMul :=
  rfl

@[simp]
/-
**Additive.toMul_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：toMul_symm_eq : (@toMul α).symm = ofMul
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toMul_symm_eq : (@toMul α).symm = ofMul :=
  rfl
/-
**Additive.ext** 是 Mathlib 中的一个定理，位于命名空间 `Additive`。
形式化陈述：∀ {α : Type u} {a b : Additive α}, Additive.toMul a = Additive.toMul b → a
 = b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[ext] lemma ext {a b : Additive α} (hab : a.toMul = b.toMul) : a = b := hab

@[simp]
/-
**Additive.** 是 Mathlib 中的一个引理，位于命名空间 `Additive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «forall» {p : Additive α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofMul a) := Iff.rfl

@[simp]
/-
**Additive.** 是 Mathlib 中的一个引理，位于命名空间 `Additive`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «exists» {p : Additive α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofMul a) := Iff.rfl

/-- Recursion principle for `Additive`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Additive.rec** 是 Mathlib 中的一个定义，位于命名空间 `Additive`。
形式化陈述：rec {motive : Additive α -> Sort*} (ofMul : forall a, motive (ofMul a)) : 
forall a, motive a
参数：ofMul : forall a, motive (ofMul a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for `Additive`, supported by `cases` and `induction`.
-/
def rec {motive : Additive α → Sort*} (ofMul : ∀ a, motive (ofMul a)) : ∀ a, motive a :=
  fun a => ofMul (a.toMul)

end Additive

namespace Multiplicative

/-- Reinterpret `x : α` as an element of `Multiplicative α`. -/
@[implicit_reducible]
/-
**Multiplicative.ofAdd** 是 Mathlib 中的一个定义，位于命名空间 `Multiplicative`。
形式化陈述：ofAdd : α ≃ Multiplicative α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `x : α` as an element of `Multiplicative α`.
-/
def ofAdd : α ≃ Multiplicative α :=
  ⟨fun x => x, fun x => x, fun _ => rfl, fun _ => rfl⟩

/-- Reinterpret `x : Multiplicative α` as an element of `α`. -/
@[implicit_reducible]
/-
**Multiplicative.toAdd** 是 Mathlib 中的一个定义，位于命名空间 `Multiplicative`。
形式化陈述：toAdd : Multiplicative α ≃ α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Reinterpret `x : Multiplicative α` as an element of `α`.
-/
def toAdd : Multiplicative α ≃ α := ofAdd.symm

@[simp]
/-
**Multiplicative.ofAdd_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：ofAdd_symm_eq : (@ofAdd α).symm = toAdd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem ofAdd_symm_eq : (@ofAdd α).symm = toAdd :=
  rfl

@[simp]
/-
**Multiplicative.toAdd_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：toAdd_symm_eq : (@toAdd α).symm = ofAdd
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toAdd_symm_eq : (@toAdd α).symm = ofAdd :=
  rfl
/-
**Multiplicative.ext** 是 Mathlib 中的一个定理，位于命名空间 `Multiplicative`。
形式化陈述：∀ {α : Type u} {a b : Multiplicative α}, Multiplicative.toAdd a = Multipli
cative.toAdd b → a = b
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[ext] lemma ext {a b : Multiplicative α} (hab : a.toAdd = b.toAdd) : a = b := hab

@[simp]
/-
**Multiplicative.** 是 Mathlib 中的一个引理，位于命名空间 `Multiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «forall» {p : Multiplicative α → Prop} : (∀ a, p a) ↔ ∀ a, p (ofAdd a) := Iff.rfl

@[simp]
/-
**Multiplicative.** 是 Mathlib 中的一个引理，位于命名空间 `Multiplicative`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma «exists» {p : Multiplicative α → Prop} : (∃ a, p a) ↔ ∃ a, p (ofAdd a) := Iff.rfl

/-- Recursion principle for `Multiplicative`, supported by `cases` and `induction`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**Multiplicative.rec** 是 Mathlib 中的一个定义，位于命名空间 `Multiplicative`。
形式化陈述：rec {motive : Multiplicative α -> Sort*} (ofAdd : forall a, motive (ofAdd 
a)) : forall a, motive a
参数：ofAdd : forall a, motive (ofAdd a)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Recursion principle for `Multiplicative`, supported by `cases` and `induction`.
-/
def rec {motive : Multiplicative α → Sort*} (ofAdd : ∀ a, motive (ofAdd a)) : ∀ a, motive a :=
  fun a => ofAdd (a.toAdd)

end Multiplicative

open Additive (ofMul toMul)
open Multiplicative (ofAdd toAdd)

@[simp]
/-
**toAdd_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_ofAdd (x : α) : (ofAdd x).toAdd = x :=
  rfl

@[simp]
/-
**ofAdd_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_toAdd (x : Multiplicative α) : ofAdd x.toAdd = x
参数：x : Multiplicative α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_toAdd (x : Multiplicative α) : ofAdd x.toAdd = x :=
  rfl

@[simp]
/-
**toMul_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_ofMul (x : α) : (ofMul x).toMul = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_ofMul (x : α) : (ofMul x).toMul = x :=
  rfl

@[simp]
/-
**ofMul_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_toMul (x : Additive α) : ofMul x.toMul = x
参数：x : Additive α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_toMul (x : Additive α) : ofMul x.toMul = x :=
  rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (Additive α) := toMul.injective.subsingleton
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Subsingleton α] : Subsingleton (Multiplicative α) := toAdd.injective.subsingleton
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Additive α) :=
  ⟨ofMul default⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited α] : Inhabited (Multiplicative α) :=
  ⟨ofAdd default⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (Additive α) := toMul.unique
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Unique α] : Unique (Multiplicative α) := toAdd.unique
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : DecidableEq α] : DecidableEq (Multiplicative α) := h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [h : DecidableEq α] : DecidableEq (Additive α) := h
/-
**Additive.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.instNontrivial [Nontrivial α] : Nontrivial (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance Additive.instNontrivial [Nontrivial α] : Nontrivial (Additive α) :=
  ofMul.injective.nontrivial
/-
**Multiplicative.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.instNontrivial [Nontrivial α] : Nontrivial (Multiplicative 
α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
instance Multiplicative.instNontrivial [Nontrivial α] : Nontrivial (Multiplicative α) :=
  ofAdd.injective.nontrivial
/-
**Additive.add** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.add [Mul α] : Add (Additive α) where add x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.add [Mul α] : Add (Additive α) where
  add x y := ofMul (x.toMul * y.toMul)
/-
**Multiplicative.mul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.mul [Add α] : Mul (Multiplicative α) where mul x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.mul [Add α] : Mul (Multiplicative α) where
  mul x y := ofAdd (x.toAdd + y.toAdd)

@[simp]
/-
**ofAdd_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_add [Add α] (x y : α) : ofAdd (x + y) = ofAdd x * ofAdd y := rfl

@[simp]
/-
**toAdd_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.t
oAdd
参数：x y : Multiplicative α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_mul [Add α] (x y : Multiplicative α) : (x * y).toAdd = x.toAdd + y.toAdd := rfl

@[simp]
/-
**ofMul_mul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_mul [Mul α] (x y : α) : ofMul (x * y) = ofMul x + ofMul y := rfl

@[simp]
/-
**toMul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul
参数：x y : Additive α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_add [Mul α] (x y : Additive α) : (x + y).toMul = x.toMul * y.toMul := rfl
/-
**Additive.addSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
-/
instance Additive.addSemigroup [Semigroup α] : AddSemigroup (Additive α) :=
  { Additive.add with add_assoc := @mul_assoc α _ }
/-
**Multiplicative.semigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
-/
instance Multiplicative.semigroup [AddSemigroup α] : Semigroup (Multiplicative α) :=
  { Multiplicative.mul with mul_assoc := @add_assoc α _ }
/-
**Additive.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addCommSemigroup [CommSemigroup α] : AddCommSemigroup (Additive α) :=
  { Additive.addSemigroup with add_comm := @mul_comm α _ }
/-
**Multiplicative.commSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multipl
icative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.commSemigroup [AddCommSemigroup α] : CommSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup with mul_comm := @add_comm α _ }
/-
**Additive.isLeftCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Ad
ditive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
-/
instance Additive.isLeftCancelAdd [Mul α] [IsLeftCancelMul α] : IsLeftCancelAdd (Additive α) :=
  ⟨@mul_left_cancel α _ _⟩
/-
**Multiplicative.isLeftCancelMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] : IsLeftCancelM
ul (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_left_cancel`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] {a 
b c : G}, a + b = a + c → b = c
-/
instance Multiplicative.isLeftCancelMul [Add α] [IsLeftCancelAdd α] :
    IsLeftCancelMul (Multiplicative α) :=
  ⟨@add_left_cancel α _ _⟩
/-
**Additive.isRightCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd 
(Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
-/
instance Additive.isRightCancelAdd [Mul α] [IsRightCancelMul α] : IsRightCancelAdd (Additive α) :=
  ⟨fun _ _ _ ↦ mul_right_cancel (G := α)⟩
/-
**Multiplicative.isRightCancelMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] : IsRightCanc
elMul (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `add_right_cancel`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] {
a b c : G}, a + b = c + b → a = c
-/
instance Multiplicative.isRightCancelMul [Add α] [IsRightCancelAdd α] :
    IsRightCancelMul (Multiplicative α) :=
  ⟨fun _ _ _ ↦ add_right_cancel (G := α)⟩
/-
**Additive.isCancelAdd** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
-/
instance Additive.isCancelAdd [Mul α] [IsCancelMul α] : IsCancelAdd (Additive α) :=
  ⟨⟩
/-
**Multiplicative.isCancelMul** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multipli
cative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelAdd.toIsLeftCancelAdd`：∀ {G : Type u} {inst : Add G} [self : IsC
ancelAdd G], IsLeftCancelAdd G
· 使用定理 `IsCancelAdd.toIsRightCancelAdd`：∀ {G : Type u} {inst : Add G} [self : Is
CancelAdd G], IsRightCancelAdd G
-/
instance Multiplicative.isCancelMul [Add α] [IsCancelAdd α] : IsCancelMul (Multiplicative α) :=
  ⟨⟩
/-
**Additive.addLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] : AddLeftCancelSem
igroup (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addLeftCancelSemigroup [LeftCancelSemigroup α] :
    AddLeftCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isLeftCancelAdd with }
/-
**Multiplicative.leftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] : LeftCancel
Semigroup (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.leftCancelSemigroup [AddLeftCancelSemigroup α] :
    LeftCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isLeftCancelMul with }
/-
**Additive.addRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addRightCancelSemigroup [RightCancelSemigroup α] : AddRightCancel
Semigroup (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addRightCancelSemigroup [RightCancelSemigroup α] :
    AddRightCancelSemigroup (Additive α) :=
  { Additive.addSemigroup, Additive.isRightCancelAdd with }
/-
**Multiplicative.rightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] : RightCan
celSemigroup (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.rightCancelSemigroup [AddRightCancelSemigroup α] :
    RightCancelSemigroup (Multiplicative α) :=
  { Multiplicative.semigroup, Multiplicative.isRightCancelMul with }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [One α] : Zero (Additive α) :=
  ⟨Additive.ofMul 1⟩

@[simp]
/-
**ofMul_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_one [One α] : @Additive.ofMul α 1 = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_one [One α] : @Additive.ofMul α 1 = 0 := rfl

@[simp]
/-
**ofMul_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofMul_eq_zero {A : Type*} [One A] {x : A} : Additive.ofMul x = 0 ↔ x = 1 := Iff.rfl

@[simp]
/-
**toMul_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_zero [One α] : (0 : Additive α).toMul = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_zero [One α] : (0 : Additive α).toMul = 1 := rfl

@[simp]
/-
**toMul_eq_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toMul_eq_one {α : Type*} [One α] {x : Additive α} : x.toMul = 1 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toMul_eq_one {α : Type*} [One α] {x : Additive α} :
    x.toMul = 1 ↔ x = 0 :=
  Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero α] : One (Multiplicative α) :=
  ⟨Multiplicative.ofAdd 0⟩

@[simp]
/-
**ofAdd_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_zero [Zero α] : @Multiplicative.ofAdd α 0 = 1 :=
  rfl

@[simp]
/-
**ofAdd_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x
 = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ofAdd_eq_one {A : Type*} [Zero A] {x : A} : Multiplicative.ofAdd x = 1 ↔ x = 0 :=
  Iff.rfl

@[simp]
/-
**toAdd_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_one [Zero α] : (1 : Multiplicative α).toAdd = 0 :=
  rfl

@[simp]
/-
**toAdd_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：toAdd_eq_zero {α : Type*} [Zero α] {x : Multiplicative α} : x.toAdd = 0 ↔ 
x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toAdd_eq_zero {α : Type*} [Zero α] {x : Multiplicative α} :
    x.toAdd = 0 ↔ x = 1 :=
  Iff.rfl
/-
**Additive.addZeroClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where ze
ro_add
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
instance Additive.addZeroClass [MulOneClass α] : AddZeroClass (Additive α) where
  zero_add := @one_mul α _
  add_zero := @mul_one α _
/-
**Multiplicative.mulOneClass** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative 
α) where one_mul
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
instance Multiplicative.mulOneClass [AddZeroClass α] : MulOneClass (Multiplicative α) where
  one_mul := @zero_add α _
  mul_one := @add_zero α _
/-
**Additive.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) where nsmul n a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Monoid.npow_zero`：∀ {M : Type u} [self : Monoid M] (x : M), x ^ 0 = 1
· 使用定理 `Monoid.npow_succ`：∀ {M : Type u} [self : Monoid M] (n : ℕ) (x : M), x ^ 
(n + 1) = x ^ n * x
-/
instance Additive.addMonoid [h : Monoid α] : AddMonoid (Additive α) where
  nsmul n a := ofMul (a.toMul ^ n)
  nsmul_zero := h.npow_zero
  nsmul_succ := h.npow_succ
/-
**Multiplicative.monoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) where 
npow n a
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoid.nsmul_zero`：∀ {M : Type u} [self : AddMonoid M] (x : M), 0 • x
 = 0
· 使用定理 `AddMonoid.nsmul_succ`：∀ {M : Type u} [self : AddMonoid M] (n : ℕ) (x : M
), (n + 1) • x = n • x + x
-/
instance Multiplicative.monoid [h : AddMonoid α] : Monoid (Multiplicative α) where
  npow n a := ofAdd (n • a.toAdd)
  npow_zero := h.nsmul_zero
  npow_succ := h.nsmul_succ

@[simp]
/-
**ofMul_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_pow [Monoid α] (n : Nat) (a : α) : ofMul (a ^ n) = n • ofMul a
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_pow [Monoid α] (n : ℕ) (a : α) : ofMul (a ^ n) = n • ofMul a :=
  rfl

@[simp]
/-
**toMul_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_nsmul [Monoid α] (n : Nat) (a : Additive α) : (n • a).toMul = a.toMu
l ^ n
参数：n : Nat；a : Additive α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_nsmul [Monoid α] (n : ℕ) (a : Additive α) : (n • a).toMul = a.toMul ^ n :=
  rfl

@[simp]
/-
**ofAdd_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_nsmul [AddMonoid α] (n : Nat) (a : α) : ofAdd (n • a) = ofAdd a ^ n
参数：n : Nat；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_nsmul [AddMonoid α] (n : ℕ) (a : α) : ofAdd (n • a) = ofAdd a ^ n :=
  rfl

@[simp]
/-
**toAdd_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_pow [AddMonoid α] (a : Multiplicative α) (n : Nat) : (a ^ n).toAdd =
 n • a.toAdd
参数：a : Multiplicative α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_pow [AddMonoid α] (a : Multiplicative α) (n : ℕ) : (a ^ n).toAdd = n • a.toAdd :=
  rfl

section Monoid
variable [Monoid α]

@[simp]
/-
**isAddLeftRegular_ofMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isAddLeftRegular_ofMul {a : α} : IsAddLeftRegular (Additive.ofMul a) ↔ IsL
eftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isAddLeftRegular_ofMul {a : α} : IsAddLeftRegular (Additive.ofMul a) ↔ IsLeftRegular a := .rfl

@[simp]
/-
**isLeftRegular_toMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_toMul {a : Additive α} : IsLeftRegular a.toMul ↔ IsAddLeftRe
gular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_toMul {a : Additive α} : IsLeftRegular a.toMul ↔ IsAddLeftRegular a := .rfl

@[simp]
/-
**isAddRightRegular_ofMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isAddRightRegular_ofMul {a : α} : IsAddRightRegular (Additive.ofMul a) ↔ I
sRightRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isAddRightRegular_ofMul {a : α} : IsAddRightRegular (Additive.ofMul a) ↔ IsRightRegular a :=
  .rfl

@[simp]
/-
**isRightRegular_toMul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_toMul {a : Additive α} : IsRightRegular a.toMul ↔ IsAddRigh
tRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_toMul {a : Additive α} : IsRightRegular a.toMul ↔ IsAddRightRegular a := .rfl
/-
**isAddRegular_ofMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {a : α}, IsAddRegular (Additive.ofMul a) 
↔ IsRegular a
参数：Additive.ofMul a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isAddRegular_ofMul {a : α} : IsAddRegular (Additive.ofMul a) ↔ IsRegular a := by
  simp [isAddRegular_iff, isRegular_iff]
/-
**isRegular_toMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : Monoid α] {a : Additive α}, IsRegular (Additive.toM
ul a) ↔ IsAddRegular a
参数：Additive.toMul a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isRegular_toMul {a : Additive α} : IsRegular a.toMul ↔ IsAddRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

end Monoid

section AddMonoid
variable [AddMonoid α]

@[simp]
/-
**isLeftRegular_ofAdd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isLeftRegular_ofAdd {a : α} : IsLeftRegular (Multiplicative.ofAdd a) ↔ IsA
ddLeftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isLeftRegular_ofAdd {a : α} : IsLeftRegular (Multiplicative.ofAdd a) ↔ IsAddLeftRegular a :=
  .rfl

@[simp]
/-
**isAddLeftRegular_toAdd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isAddLeftRegular_toAdd {a : Multiplicative α} : IsAddLeftRegular a.toAdd ↔
 IsLeftRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isAddLeftRegular_toAdd {a : Multiplicative α} : IsAddLeftRegular a.toAdd ↔ IsLeftRegular a :=
  .rfl

@[simp]
/-
**isRightRegular_ofAdd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isRightRegular_ofAdd {a : α} : IsRightRegular (Multiplicative.ofAdd a) ↔ I
sAddRightRegular a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isRightRegular_ofAdd {a : α} :
    IsRightRegular (Multiplicative.ofAdd a) ↔ IsAddRightRegular a := .rfl
/-
**isAddRightRegular_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : AddMonoid α] {a : Multiplicative α},   IsAddRightRe
gular (Multiplicative.toAdd a) ↔ IsRightRegular a
参数：Multiplicative.toAdd a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma isAddRightRegular_toAdd {a : Multiplicative α} :
    IsAddRightRegular a.toAdd ↔ IsRightRegular a := .rfl
/-
**isRegular_ofAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : AddMonoid α] {a : α}, IsRegular (Multiplicative.ofA
dd a) ↔ IsAddRegular a
参数：Multiplicative.ofAdd a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isRegular_ofAdd {a : α} : IsRegular (Multiplicative.ofAdd a) ↔ IsAddRegular a := by
  simp [isAddRegular_iff, isRegular_iff]
/-
**isAddRegular_toAdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {α : Type u} [inst : AddMonoid α] {a : Multiplicative α}, IsAddRegular (
Multiplicative.toAdd a) ↔ IsRegular a
参数：Multiplicative.toAdd a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma isAddRegular_toAdd {a : Multiplicative α} : IsAddRegular a.toAdd ↔ IsRegular a := by
  simp [isAddRegular_iff, isRegular_iff]

end AddMonoid

/-
**Additive.addLeftCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (A
dditive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addLeftCancelMonoid [LeftCancelMonoid α] : AddLeftCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addLeftCancelSemigroup with }
/-
**Multiplicative.leftCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] : LeftCancelMonoid
 (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.leftCancelMonoid [AddLeftCancelMonoid α] :
    LeftCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.leftCancelSemigroup with }
/-
**Additive.addRightCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid
 (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addRightCancelMonoid [RightCancelMonoid α] : AddRightCancelMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addRightCancelSemigroup with }
/-
**Multiplicative.rightCancelMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] : RightCancelMon
oid (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.rightCancelMonoid [AddRightCancelMonoid α] :
    RightCancelMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.rightCancelSemigroup with }
/-
**Additive.addCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addCommMonoid [CommMonoid α] : AddCommMonoid (Additive α) :=
  { Additive.addMonoid, Additive.addCommSemigroup with }
/-
**Multiplicative.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α
)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.commMonoid [AddCommMonoid α] : CommMonoid (Multiplicative α) :=
  { Multiplicative.monoid, Multiplicative.commSemigroup with }
/-
**Additive.instAddCancelCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Additive`。
形式化陈述：{α : Type u} → [CancelCommMonoid α] → AddCancelCommMonoid (Additive α)
参数：Additive α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.instAddCancelCommMonoid [CancelCommMonoid α] :
    AddCancelCommMonoid (Additive α) where
/-
**Multiplicative.instCancelCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `Multiplicative`
。
形式化陈述：{α : Type u} → [AddCancelCommMonoid α] → CancelCommMonoid (Multiplicative 
α)
参数：Multiplicative α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.instCancelCommMonoid [AddCancelCommMonoid α] :
    CancelCommMonoid (Multiplicative α) where
/-
**Additive.neg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.neg [Inv α] : Neg (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.neg [Inv α] : Neg (Additive α) :=
  ⟨fun x => ofAdd x.toMul⁻¹⟩

@[simp]
/-
**ofMul_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_inv [Inv α] (x : α) : ofMul x⁻¹ = -ofMul x :=
  rfl

@[simp]
/-
**toMul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹
参数：x : Additive α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_neg [Inv α] (x : Additive α) : (-x).toMul = x.toMul⁻¹ :=
  rfl
/-
**Multiplicative.inv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.inv [Neg α] : Inv (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.inv [Neg α] : Inv (Multiplicative α) :=
  ⟨fun x => ofMul (-x.toAdd)⟩

@[simp]
/-
**ofAdd_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_neg [Neg α] (x : α) : ofAdd (-x) = (ofAdd x)⁻¹ :=
  rfl

@[simp]
/-
**toAdd_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd
参数：x : Multiplicative α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_inv [Neg α] (x : Multiplicative α) : x⁻¹.toAdd = -x.toAdd :=
  rfl
/-
**Additive.sub** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.sub [Div α] : Sub (Additive α) where sub x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.sub [Div α] : Sub (Additive α) where
  sub x y := ofMul (x.toMul / y.toMul)
/-
**Multiplicative.div** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.div [Sub α] : Div (Multiplicative α) where div x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.div [Sub α] : Div (Multiplicative α) where
  div x y := ofAdd (x.toAdd - y.toAdd)

@[simp]
/-
**ofAdd_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_sub [Sub α] (x y : α) : ofAdd (x - y) = ofAdd x / ofAdd y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_sub [Sub α] (x y : α) : ofAdd (x - y) = ofAdd x / ofAdd y :=
  rfl

@[simp]
/-
**toAdd_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.t
oAdd
参数：x y : Multiplicative α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_div [Sub α] (x y : Multiplicative α) : (x / y).toAdd = x.toAdd - y.toAdd :=
  rfl

@[simp]
/-
**ofMul_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_div [Div α] (x y : α) : ofMul (x / y) = ofMul x - ofMul y
参数：x y : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_div [Div α] (x y : α) : ofMul (x / y) = ofMul x - ofMul y :=
  rfl

@[simp]
/-
**toMul_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul
参数：x y : Additive α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_sub [Div α] (x y : Additive α) : (x - y).toMul = x.toMul / y.toMul :=
  rfl
/-
**Additive.involutiveNeg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
instance Additive.involutiveNeg [InvolutiveInv α] : InvolutiveNeg (Additive α) :=
  { Additive.neg with neg_neg := @inv_inv α _ }
/-
**Multiplicative.involutiveInv** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplica
tive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
instance Multiplicative.involutiveInv [InvolutiveNeg α] : InvolutiveInv (Multiplicative α) :=
  { Multiplicative.inv with inv_inv := @neg_neg α _ }
/-
**Additive.subNegMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.subNegMonoid [h : DivInvMonoid α] : SubNegMonoid (Additive α) whe
re sub_eq_add_neg
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `DivInvMonoid.div_eq_mul_inv`：∀ {G : Type u} [self : DivInvMonoid G] (a b
 : G), a / b = a * b⁻¹
· 使用定理 `DivInvMonoid.zpow_zero'`：∀ {G : Type u} [self : DivInvMonoid G] (a : G),
 a ^ 0 = 1
· 使用定理 `DivInvMonoid.zpow_succ'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) 
(a : G), a ^ ↑n.succ = a ^ ↑n * a
· 使用定理 `DivInvMonoid.zpow_neg'`：∀ {G : Type u} [self : DivInvMonoid G] (n : ℕ) (
a : G), a ^ Int.negSucc n = (a ^ ↑n.succ)⁻¹
-/
instance Additive.subNegMonoid [h : DivInvMonoid α] : SubNegMonoid (Additive α) where
  sub_eq_add_neg := h.div_eq_mul_inv
  zsmul n a := ofMul (a.toMul ^ n)
  zsmul_zero' := h.zpow_zero'
  zsmul_succ' := h.zpow_succ'
  zsmul_neg' := h.zpow_neg'
/-
**Multiplicative.divInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.divInvMonoid [h : SubNegMonoid α] : DivInvMonoid (Multiplic
ative α) where div_eq_mul_inv
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SubNegMonoid.sub_eq_add_neg`：∀ {G : Type u} [self : SubNegMonoid G] (a b
 : G), a - b = a + -b
· 使用定理 `SubNegMonoid.zsmul_zero'`：∀ {G : Type u} [self : SubNegMonoid G] (a : G)
, 0 • a = 0
· 使用定理 `SubNegMonoid.zsmul_succ'`：∀ {G : Type u} [self : SubNegMonoid G] (n : ℕ)
 (a : G), ↑n.succ • a = ↑n • a + a
· 使用定理 `SubNegMonoid.zsmul_neg'`：∀ {G : Type u} [self : SubNegMonoid G] (n : ℕ) 
(a : G), Int.negSucc n • a = -(↑n.succ • a)
-/
instance Multiplicative.divInvMonoid [h : SubNegMonoid α] : DivInvMonoid (Multiplicative α) where
  div_eq_mul_inv := h.sub_eq_add_neg
  zpow n a := ofAdd (n • a.toAdd)
  zpow_zero' := h.zsmul_zero'
  zpow_succ' := h.zsmul_succ'
  zpow_neg' := h.zsmul_neg'

@[simp]
/-
**ofMul_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofMul_zpow [DivInvMonoid α] (z : Int) (a : α) : ofMul (a ^ z) = z • ofMul 
a
参数：z : Int；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMul_zpow [DivInvMonoid α] (z : ℤ) (a : α) : ofMul (a ^ z) = z • ofMul a :=
  rfl

@[simp]
/-
**toMul_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toMul_zsmul [DivInvMonoid α] (z : Int) (a : Additive α) : (z • a).toMul = 
a.toMul ^ z
参数：z : Int；a : Additive α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMul_zsmul [DivInvMonoid α] (z : ℤ) (a : Additive α) : (z • a).toMul = a.toMul ^ z :=
  rfl

@[simp]
/-
**ofAdd_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ofAdd_zsmul [SubNegMonoid α] (z : Int) (a : α) : ofAdd (z • a) = ofAdd a ^
 z
参数：z : Int；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofAdd_zsmul [SubNegMonoid α] (z : ℤ) (a : α) : ofAdd (z • a) = ofAdd a ^ z :=
  rfl

@[simp]
/-
**toAdd_zpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：toAdd_zpow [SubNegMonoid α] (a : Multiplicative α) (z : Int) : (a ^ z).toA
dd = z • a.toAdd
参数：a : Multiplicative α；z : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toAdd_zpow [SubNegMonoid α] (a : Multiplicative α) (z : ℤ) : (a ^ z).toAdd = z • a.toAdd :=
  rfl
/-
**Additive.subtractionMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additiv
e α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_eq_of_mul_eq_one_right`：inv_eq_of_mul_eq_one_right : a * b = 1 -> a⁻
¹ = b
-/
instance Additive.subtractionMonoid [DivisionMonoid α] : SubtractionMonoid (Additive α) :=
  { Additive.subNegMonoid, Additive.involutiveNeg with
    neg_add_rev := @mul_inv_rev α _
    neg_eq_of_add := @inv_eq_of_mul_eq_one_right α _ }
/-
**Multiplicative.divisionMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Mult
iplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_eq_of_add_eq_zero_right`：∀ {G : Type u_1} [inst : SubtractionMonoid 
G] {a b : G}, a + b = 0 → -a = b
-/
instance Multiplicative.divisionMonoid [SubtractionMonoid α] : DivisionMonoid (Multiplicative α) :=
  { Multiplicative.divInvMonoid, Multiplicative.involutiveInv with
    mul_inv_rev := @neg_add_rev α _
    inv_eq_of_mul := @neg_eq_of_add_eq_zero_right α _ }
/-
**Additive.subtractionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.subtractionCommMonoid [DivisionCommMonoid α] : SubtractionCommMon
oid (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.subtractionCommMonoid [DivisionCommMonoid α] :
    SubtractionCommMonoid (Additive α) :=
  { Additive.subtractionMonoid, Additive.addCommSemigroup with }
/-
**Multiplicative.divisionCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] : DivisionComm
Monoid (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.divisionCommMonoid [SubtractionCommMonoid α] :
    DivisionCommMonoid (Multiplicative α) :=
  { Multiplicative.divisionMonoid, Multiplicative.commSemigroup with }
/-
**Additive.addGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addGroup [Group α] : AddGroup (Additive α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
-/
instance Additive.addGroup [Group α] : AddGroup (Additive α) :=
  { Additive.subNegMonoid with neg_add_cancel := @inv_mul_cancel α _ }
/-
**Multiplicative.group** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.group [AddGroup α] : Group (Multiplicative α)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
instance Multiplicative.group [AddGroup α] : Group (Multiplicative α) :=
  { Multiplicative.divInvMonoid with inv_mul_cancel := @neg_add_cancel α _ }
/-
**Additive.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Additive.addCommGroup [CommGroup α] : AddCommGroup (Additive α) :=
  { Additive.addGroup, Additive.addCommMonoid with }
/-
**Multiplicative.commGroup** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Multiplicative.commGroup [AddCommGroup α] : CommGroup (Multiplicative α) :=
  { Multiplicative.group, Multiplicative.commMonoid with }
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid α] [IsMulTorsionFree α] : IsAddTorsionFree (Additive α) where
  nsmul_right_injective _ := pow_left_injective (M := α)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid α] [IsAddTorsionFree α] : IsMulTorsionFree (Multiplicative α) where
  pow_left_injective _ := nsmul_right_injective (M := α)

/-- If `α` has some multiplicative structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicative structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
/-
**Additive.coeToFun** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Additive.coeToFun {α : Type*} {β : α -> Sort*} [CoeFun α β] : CoeFun (Addi
tive α) fun a => β a.toMul
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has some multiplicative structure and coerces to a function,
then `Additive α` should also coerce to the same function.

This allows `Additive` to be used on bundled function types with a multiplicativ
e structure, which
is often used for composition, without affecting the behavior of the function it
self.
-/
instance Additive.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Additive α) fun a => β a.toMul :=
  ⟨fun a => CoeFun.coe a.toMul⟩

/-- If `α` has some additive structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additive structure, which
is often used for composition, without affecting the behavior of the function itself.
-/
/-
**Multiplicative.coeToFun** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Multiplicative.coeToFun {α : Type*} {β : α -> Sort*} [CoeFun α β] : CoeFun
 (Multiplicative α) fun a => β a.toAdd
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` has some additive structure and coerces to a function,
then `Multiplicative α` should also coerce to the same function.

This allows `Multiplicative` to be used on bundled function types with an additi
ve structure, which
is often used for composition, without affecting the behavior of the function it
self.
-/
instance Multiplicative.coeToFun {α : Type*} {β : α → Sort*} [CoeFun α β] :
    CoeFun (Multiplicative α) fun a => β a.toAdd :=
  ⟨fun a => CoeFun.coe a.toAdd⟩
/-
**Pi.mulSingle_multiplicativeOfAdd_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι -> 
Type*} [(i : ι) -> AddMonoid (M i)] (i : ι) (a : M i) (j : ι) : Pi.mulSingle (M
参数：i : ι；M i；i : ι；a : M i；j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma Pi.mulSingle_multiplicativeOfAdd_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → AddMonoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.mulSingle (M := fun i ↦ Multiplicative (M i)) i (.ofAdd a) j = .ofAdd (Pi.single i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [mulSingle, ne_eq, h, not_false_eq_true, Function.update_of_ne, one_apply, single,
      zero_apply, ofAdd_zero]
/-
**Pi.single_additiveOfMul_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [(
i : ι) -> Monoid (M i)] (i : ι) (a : M i) (j : ι) : Pi.single (M
参数：i : ι；M i；i : ι；a : M i；j : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用引理 `Pi.mulSingle_eq_same`：mulSingle_eq_same (i : ι) (x : M i) : mulSingle i 
x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma Pi.single_additiveOfMul_eq {ι : Type*} [DecidableEq ι] {M : ι → Type*}
    [(i : ι) → Monoid (M i)] (i : ι) (a : M i) (j : ι) :
    Pi.single (M := fun i ↦ Additive (M i)) i (.ofMul a) j = .ofMul (Pi.mulSingle i a j) := by
  rcases eq_or_ne j i with rfl | h
  · simp only [mulSingle_eq_same, single_eq_same]
  · simp only [single, ne_eq, h, not_false_eq_true, Function.update_of_ne, zero_apply, mulSingle,
      one_apply, ofMul_one]
