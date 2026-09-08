/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Logic.Function.Basic
public import Mathlib.Tactic.Common

/-!

# Tuples of types, and their categorical structure.

## Features

* `TypeVec n` - n-tuples of types
* `α ⟹ β`    - n-tuples of maps
* `f ⊚ g`     - composition

Also, support functions for operating with n-tuples of types, such as:

* `append1 α β`    - append type `β` to n-tuple `α` to obtain an (n+1)-tuple
* `drop α`         - drops the last element of an (n+1)-tuple
* `last α`         - returns the last element of an (n+1)-tuple
* `appendFun f g` - appends a function g to an n-tuple of functions
* `dropFun f`     - drops the last function from an n+1-tuple
* `lastFun f`     - returns the last function of a tuple.

Since e.g. `append1 α.drop α.last` is propositionally equal to `α` but not definitionally equal
to it, we need support functions and lemmas to mediate between constructions.
-/

@[expose] public section

universe u v w x

/-- n-tuples of types, as a category -/
@[pp_with_univ]
/-
**TypeVec** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TypeVec (n : Nat)
参数：n : Nat。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
n-tuples of types, as a category
-/
def TypeVec (n : ℕ) :=
  Fin2 n → Type*
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {n} : Inhabited (TypeVec.{u} n) :=
  ⟨fun _ => PUnit⟩

namespace TypeVec

variable {n : ℕ}

/-- arrow in the category of `TypeVec` -/
/-
**TypeVec.Arrow** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：Arrow (α : TypeVec.{u} n) (β : TypeVec.{v} n)
参数：α : TypeVec.{u} n；β : TypeVec.{v} n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
arrow in the category of `TypeVec`
-/
def Arrow (α : TypeVec.{u} n) (β : TypeVec.{v} n) :=
  ∀ i : Fin2 n, α i → β i

@[inherit_doc] scoped[MvFunctor] infixl:40 " ⟹ " => TypeVec.Arrow
open MvFunctor

variable {α : TypeVec.{u} n} {β : TypeVec.{v} n} {γ : TypeVec.{w} n} {δ : TypeVec.{x} n} in
section

/-- Extensionality for arrows -/
@[ext]
/-
**TypeVec.Arrow.ext** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec.Arrow`。
形式化陈述：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f g : α.Arrow β), (∀ (i
 : Fin2 n), f i = g i) → f = g
参数：f g : α.Arrow β；∀ (i : Fin2 n), f i = g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Extensionality for arrows
-/
theorem Arrow.ext (f g : α ⟹ β) :
    (∀ i, f i = g i) → f = g := by
  intro h; funext i; apply h
/-
**TypeVec.Arrow.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.Arrow`。
形式化陈述：{n : ℕ} → (α : TypeVec.{u_1} n) → (β : TypeVec.{u_2} n) → [(i : Fin2 n) → 
Inhabited (β i)] → Inhabited (α.Arrow β)
参数：α : TypeVec.{u_1} n；β : TypeVec.{u_2} n；i : Fin2 n；β i；α.Arrow β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Arrow.inhabited (α β : TypeVec n) [∀ i, Inhabited (β i)] : Inhabited (α ⟹ β) :=
  ⟨fun _ _ => default⟩

/-- identity of arrow composition -/
/-
**TypeVec.id** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：id {α : TypeVec n} : α ⟹ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
identity of arrow composition
-/
def id {α : TypeVec n} : α ⟹ α := fun _ x => x


/-- arrow composition in the category of `TypeVec` -/
/-
**TypeVec.comp** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：comp (g : β ⟹ γ) (f : α ⟹ β) : α ⟹ γ
参数：g : β ⟹ γ；f : α ⟹ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
arrow composition in the category of `TypeVec`
-/
def comp (g : β ⟹ γ) (f : α ⟹ β)
    : α ⟹ γ :=
  fun i x => g i (f i x)

@[inherit_doc] scoped[MvFunctor] infixr:80 " ⊚ " => TypeVec.comp -- type as \oo

@[simp]
/-
**TypeVec.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：id_comp (f : α ⟹ β) : id ⊚ f = f
参数：f : α ⟹ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : α ⟹ β) : id ⊚ f = f :=
  rfl

@[simp]
/-
**TypeVec.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：comp_id (f : α ⟹ β) : f ⊚ id = f
参数：f : α ⟹ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : α ⟹ β) : f ⊚ id = f :=
  rfl
/-
**TypeVec.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：comp_assoc (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) : (h ⊚ g) ⊚ f = h ⊚ g ⊚ f
参数：h : γ ⟹ δ；g : β ⟹ γ；f : α ⟹ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc
    (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) :
    (h ⊚ g) ⊚ f = h ⊚ g ⊚ f :=
  rfl
end

/-- Support for extending a `TypeVec` by one element. -/
/-
**TypeVec.append1** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → TypeVec.{u_1} n → Type u_1 → TypeVec.{u_1} (n + 1)
参数：n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Support for extending a `TypeVec` by one element.
-/
def append1 (α : TypeVec n) (β : Type*) : TypeVec (n + 1)
  | Fin2.fs i => α i
  | Fin2.fz => β

@[inherit_doc] infixl:67 " ::: " => append1

/-- retain only a `n-length` prefix of the argument -/
/-
**TypeVec.drop** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：drop (α : TypeVec.{u} (n + 1)) : TypeVec n
参数：α : TypeVec.{u} (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
retain only a `n-length` prefix of the argument
-/
def drop (α : TypeVec.{u} (n + 1)) : TypeVec n := fun i => α i.fs

/-- take the last value of a `(n+1)-length` vector -/
/-
**TypeVec.last** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：last (α : TypeVec.{u} (n + 1)) : Type _
参数：α : TypeVec.{u} (n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
take the last value of a `(n+1)-length` vector
-/
def last (α : TypeVec.{u} (n + 1)) : Type _ :=
  α Fin2.fz
/-
**TypeVec.last.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.last`。
形式化陈述：{n : ℕ} → (α : TypeVec.{u_1} (n + 1)) → [Inhabited (α Fin2.fz)] → Inhabite
d α.last
参数：α : TypeVec.{u_1} (n + 1)；α Fin2.fz。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance last.inhabited (α : TypeVec (n + 1)) [Inhabited (α Fin2.fz)] : Inhabited (last α) :=
  ⟨show α Fin2.fz from default⟩
/-
**TypeVec.drop_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：drop_append1 {α : TypeVec n} {β : Type*} {i : Fin2 n} : drop (append1 α β)
 i = α i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem drop_append1 {α : TypeVec n} {β : Type*} {i : Fin2 n} : drop (append1 α β) i = α i :=
  rfl
/-
**TypeVec.drop_append1'** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：drop_append1' {α : TypeVec n} {β : Type*} : drop (append1 α β) = α
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TypeVec.drop_append1`：drop_append1 {α : TypeVec n} {β : Type*} {i : Fin2
 n} : drop (append1 α β) i = α i
-/
theorem drop_append1' {α : TypeVec n} {β : Type*} : drop (append1 α β) = α :=
  funext fun _ => drop_append1
/-
**TypeVec.last_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：last_append1 {α : TypeVec n} {β : Type*} : last (append1 α β) = β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem last_append1 {α : TypeVec n} {β : Type*} : last (append1 α β) = β :=
  rfl

@[simp]
/-
**TypeVec.append1_drop_last** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α
参数：α : TypeVec (n + 1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem append1_drop_last (α : TypeVec (n + 1)) : append1 (drop α) (last α) = α :=
  funext fun i => by cases i <;> rfl

/-- cases on `(n+1)-length` vectors -/
@[elab_as_elim]
/-
**TypeVec.append1Cases** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：append1Cases {C : TypeVec (n + 1) -> Sort u} (H : forall α β, C (append1 α
 β)) (γ) : C γ
参数：n + 1；H : forall α β, C (append1 α β)；γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
cases on `(n+1)-length` vectors
-/
def append1Cases {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (γ) : C γ := by
  rw [← @append1_drop_last _ γ]; apply H

@[simp]
/-
**TypeVec.append1_cases_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：append1_cases_append1 {C : TypeVec (n + 1) -> Sort u} (H : forall α β, C (
append1 α β)) (α β) : @append1Cases _ C H (append1 α β) = H α β
参数：n + 1；H : forall α β, C (append1 α β)；α β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem append1_cases_append1 {C : TypeVec (n + 1) → Sort u} (H : ∀ α β, C (append1 α β)) (α β) :
    @append1Cases _ C H (append1 α β) = H α β :=
  rfl

/-- append an arrow and a function for arbitrary source and target type vectors -/
/-
**TypeVec.splitFun** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} →   {α : TypeVec.{u_1} (n + 1)} → {α' : TypeVec.{u_2} (n + 1)} → α
.drop.Arrow α'.drop → (α.last → α'.last) → α.Arrow α'
参数：n + 1；n + 1；α.last → α'.last。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
append an arrow and a function for arbitrary source and target type vectors
-/
def splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') : α ⟹ α'
  | Fin2.fs i => f i
  | Fin2.fz => g

/-- append an arrow and a function as well as their respective source and target types / typevecs -/
/-
**TypeVec.appendFun** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β -> β') : a
ppend1 α β ⟹ append1 α' β'
参数：f : α ⟹ α'；g : β -> β'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
append an arrow and a function as well as their respective source and target typ
es / typevecs
-/
def appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    append1 α β ⟹ append1 α' β' :=
  splitFun f g

@[inherit_doc] infixl:0 " ::: " => appendFun

/-- split off the prefix of an arrow -/
/-
**TypeVec.dropFun** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β
参数：n + 1；f : α ⟹ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
split off the prefix of an arrow
-/
def dropFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : drop α ⟹ drop β := fun i => f i.fs

/-- split off the last function of an arrow -/
/-
**TypeVec.lastFun** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α -> last β
参数：n + 1；f : α ⟹ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
split off the last function of an arrow
-/
def lastFun {α β : TypeVec (n + 1)} (f : α ⟹ β) : last α → last β :=
  f Fin2.fz

/-- arrow in the category of `0-length` vectors -/
/-
**TypeVec.nilFun** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
arrow in the category of `0-length` vectors
-/
def nilFun {α : TypeVec 0} {β : TypeVec 0} : α ⟹ β := fun i => by apply Fin2.elim0 i
/-
**TypeVec.eq_of_drop_last_eq** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f =
 dropFun g) (h₁ : lastFun f = lastFun g) : f = g
参数：n + 1；h₀ : dropFun f = dropFun g；h₁ : lastFun f = lastFun g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem eq_of_drop_last_eq {α β : TypeVec (n + 1)} {f g : α ⟹ β} (h₀ : dropFun f = dropFun g)
    (h₁ : lastFun f = lastFun g) : f = g := by
  refine funext (fun x => ?_)
  cases x
  · apply h₁
  · apply congr_fun h₀

@[simp]
/-
**TypeVec.dropFun_splitFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last
 α -> last α') : dropFun (splitFun f g) = f
参数：n + 1；f : drop α ⟹ drop α'；g : last α -> last α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    dropFun (splitFun f g) = f :=
  rfl

/-- turn an equality into an arrow -/
/-
**TypeVec.Arrow.mp** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.Arrow`。
形式化陈述：{n : ℕ} → {α β : TypeVec.{u_1} n} → α = β → α.Arrow β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
turn an equality into an arrow
-/
def Arrow.mp {α β : TypeVec n} (h : α = β) : α ⟹ β
  | _ => Eq.mp (congr_fun h _)

/-- turn an equality into an arrow, with reverse direction -/
/-
**TypeVec.Arrow.mpr** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.Arrow`。
形式化陈述：{n : ℕ} → {α β : TypeVec.{u_1} n} → α = β → β.Arrow α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
turn an equality into an arrow, with reverse direction
-/
def Arrow.mpr {α β : TypeVec n} (h : α = β) : β ⟹ α
  | _ => Eq.mpr (congr_fun h _)

/-- decompose a vector into its prefix appended with its last element -/
/-
**TypeVec.toAppend1DropLast** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α)
参数：n + 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.append1_drop_last`：append1_drop_last (α : TypeVec (n + 1)) : app
end1 (drop α) (last α) = α

--- 原说明 ---
decompose a vector into its prefix appended with its last element
-/
def toAppend1DropLast {α : TypeVec (n + 1)} : α ⟹ (drop α ::: last α) :=
  Arrow.mpr (append1_drop_last _)

/-- stitch two bits of a vector back together -/
/-
**TypeVec.fromAppend1DropLast** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α
参数：n + 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.append1_drop_last`：append1_drop_last (α : TypeVec (n + 1)) : app
end1 (drop α) (last α) = α

--- 原说明 ---
stitch two bits of a vector back together
-/
def fromAppend1DropLast {α : TypeVec (n + 1)} : (drop α ::: last α) ⟹ α :=
  Arrow.mp (append1_drop_last _)

@[simp]
/-
**TypeVec.lastFun_splitFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last
 α -> last α') : lastFun (splitFun f g) = g
参数：n + 1；f : drop α ⟹ drop α'；g : last α -> last α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_splitFun {α α' : TypeVec (n + 1)} (f : drop α ⟹ drop α') (g : last α → last α') :
    lastFun (splitFun f g) = g :=
  rfl

@[simp]
/-
**TypeVec.dropFun_appendFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β ->
 β') : dropFun (f ::: g) = f
参数：f : α ⟹ α'；g : β -> β'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    dropFun (f ::: g) = f :=
  rfl

@[simp]
/-
**TypeVec.lastFun_appendFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β ->
 β') : lastFun (f ::: g) = g
参数：f : α ⟹ α'；g : β -> β'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_appendFun {α α' : TypeVec n} {β β' : Type*} (f : α ⟹ α') (g : β → β') :
    lastFun (f ::: g) = g :=
  rfl
/-
**TypeVec.split_dropFun_lastFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') : splitFun (dr
opFun f) (lastFun f) = f
参数：n + 1；f : α ⟹ α'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem split_dropFun_lastFun {α α' : TypeVec (n + 1)} (f : α ⟹ α') :
    splitFun (dropFun f) (lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
/-
**TypeVec.splitFun_inj** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : la
st α -> last α'} (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g'
参数：n + 1；H : splitFun f g = splitFun f' g'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.dropFun_splitFun`：dropFun_splitFun {α α' : TypeVec (n + 1)} (f :
 drop α ⟹ drop α') (g : last α -> last α') : dropFun (splitFun f g) = f
· 使用定理 `TypeVec.lastFun_splitFun`：lastFun_splitFun {α α' : TypeVec (n + 1)} (f :
 drop α ⟹ drop α') (g : last α -> last α') : lastFun (splitFun f g) = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop α ⟹ drop α'} {g g' : last α → last α'}
    (H : splitFun f g = splitFun f' g') : f = f' ∧ g = g' := by
  rw [← dropFun_splitFun f g, H, ← lastFun_splitFun f g, H]; simp
/-
**TypeVec.appendFun_inj** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_inj {α α' : TypeVec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β 
-> β'} : (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _) -> f = f' ∧ g =
 g'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.splitFun_inj`：splitFun_inj {α α' : TypeVec (n + 1)} {f f' : drop
 α ⟹ drop α'} {g g' : last α -> last α'} (H : splitFun f g = splitFun f' g') : f
 = f' ∧ g …
-/
theorem appendFun_inj {α α' : TypeVec n} {β β' : Type*} {f f' : α ⟹ α'} {g g' : β → β'} :
    (f ::: g : (α ::: β) ⟹ _) = (f' ::: g' : (α ::: β) ⟹ _)
    → f = f' ∧ g = g' :=
  splitFun_inj
/-
**TypeVec.splitFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁) (f₁ : 
drop α₁ ⟹ drop α₂) (g₀ : last α₀ -> last α₁) (g₁ : last α₁ -> last α₂) : splitFu
n (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀
参数：n + 1；f₀ : drop α₀ ⟹ drop α₁；f₁ : drop α₁ ⟹ drop α₂；g₀ : last α₀ -> last α₁；g
₁ : last α₁ -> last α₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : drop α₀ ⟹ drop α₁)
    (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ → last α₁) (g₁ : last α₁ → last α₂) :
    splitFun (f₁ ⊚ f₀) (g₁ ∘ g₀) = splitFun f₁ g₁ ⊚ splitFun f₀ g₀ :=
  eq_of_drop_last_eq rfl rfl
/-
**TypeVec.appendFun_comp_splitFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 
1)} (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε -> β) (g₁ : β -> δ) : appendFun 
f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α'
参数：n + 1；f₀ : drop ε ⟹ α；f₁ : α ⟹ γ；g₀ : last ε -> β；g₁ : β -> δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.splitFun_comp`：splitFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : 
drop α₀ ⟹ drop α₁) (f₁ : drop α₁ ⟹ drop α₂) (g₀ : last α₀ -> last α₁) (g₁ : last
 α₁ -> last…
-/
theorem appendFun_comp_splitFun {α γ : TypeVec n} {β δ : Type*} {ε : TypeVec (n + 1)}
    (f₀ : drop ε ⟹ α) (f₁ : α ⟹ γ) (g₀ : last ε → β) (g₁ : β → δ) :
    appendFun f₁ g₁ ⊚ splitFun f₀ g₀ = splitFun (α' := γ.append1 δ) (f₁ ⊚ f₀) (g₁ ∘ g₀) :=
  (splitFun_comp _ _ _ _).symm
/-
**TypeVec.appendFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_comp {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*} (f₀ : α₀ ⟹ α₁) (f
₁ : α₁ ⟹ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂) : (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g
₁) ⊚ (f₀ ::: g₀)
参数：f₀ : α₀ ⟹ α₁；f₁ : α₁ ⟹ α₂；g₀ : β₀ -> β₁；g₁ : β₁ -> β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem appendFun_comp {α₀ α₁ α₂ : TypeVec n}
    {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂)
    (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ⊚ f₀ ::: g₁ ∘ g₀) = (f₁ ::: g₁) ⊚ (f₀ ::: g₀) :=
  eq_of_drop_last_eq rfl rfl
/-
**TypeVec.appendFun_comp'** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*} (f₀ : α₀ ⟹ α₁) (
f₁ : α₁ ⟹ α₂) (g₀ : β₀ -> β₁) (g₁ : β₁ -> β₂) : (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ 
⊚ f₀ ::: g₁ ∘ g₀)
参数：f₀ : α₀ ⟹ α₁；f₁ : α₁ ⟹ α₂；g₀ : β₀ -> β₁；g₁ : β₁ -> β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem appendFun_comp' {α₀ α₁ α₂ : TypeVec n} {β₀ β₁ β₂ : Type*}
    (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (f₁ ::: g₁) ⊚ (f₀ ::: g₀) = (f₁ ⊚ f₀ ::: g₁ ∘ g₀) :=
  eq_of_drop_last_eq rfl rfl
/-
**TypeVec.nilFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nilFun ⊚ f₀ = f₀
参数：f₀ : α₀ ⟹ Fin2.elim0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem nilFun_comp {α₀ : TypeVec 0} (f₀ : α₀ ⟹ Fin2.elim0) : nilFun ⊚ f₀ = f₀ :=
  funext Fin2.elim0
/-
**TypeVec.appendFun_comp_id** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ -> β₁) (g₁ 
: β₁ -> β₂) : (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀)
参数：g₀ : β₀ -> β₁；g₁ : β₁ -> β₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem appendFun_comp_id {α : TypeVec n} {β₀ β₁ β₂ : Type u} (g₀ : β₀ → β₁) (g₁ : β₁ → β₂) :
    (@id _ α ::: g₁ ∘ g₀) = (id ::: g₁) ⊚ (id ::: g₀) :=
  eq_of_drop_last_eq rfl rfl

@[simp]
/-
**TypeVec.dropFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) : 
dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀
参数：n + 1；f₀ : α₀ ⟹ α₁；f₁ : α₁ ⟹ α₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    dropFun (f₁ ⊚ f₀) = dropFun f₁ ⊚ dropFun f₀ :=
  rfl

@[simp]
/-
**TypeVec.lastFun_comp** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) : 
lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀
参数：n + 1；f₀ : α₀ ⟹ α₁；f₁ : α₁ ⟹ α₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_comp {α₀ α₁ α₂ : TypeVec (n + 1)} (f₀ : α₀ ⟹ α₁) (f₁ : α₁ ⟹ α₂) :
    lastFun (f₁ ⊚ f₀) = lastFun f₁ ∘ lastFun f₀ :=
  rfl
/-
**TypeVec.appendFun_aux** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_aux {α α' : TypeVec n} {β β' : Type*} (f : (α ::: β) ⟹ (α' ::: β
')) : (dropFun f ::: lastFun f) = f
参数：f : (α ::: β) ⟹ (α' ::: β')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem appendFun_aux {α α' : TypeVec n} {β β' : Type*} (f : (α ::: β) ⟹ (α' ::: β')) :
    (dropFun f ::: lastFun f) = f :=
  eq_of_drop_last_eq rfl rfl
/-
**TypeVec.appendFun_id_id** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：appendFun_id_id {α : TypeVec n} {β : Type*} : (@TypeVec.id n α ::: @_root_
.id β) = TypeVec.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.eq_of_drop_last_eq`：eq_of_drop_last_eq {α β : TypeVec (n + 1)} {
f g : α ⟹ β} (h₀ : dropFun f = dropFun g) (h₁ : lastFun f = lastFun g) : f = g
-/
theorem appendFun_id_id {α : TypeVec n} {β : Type*} :
    (@TypeVec.id n α ::: @_root_.id β) = TypeVec.id :=
  eq_of_drop_last_eq rfl rfl
/-
**TypeVec.subsingleton0** 是 Mathlib 中的一个实例，位于命名空间 `TypeVec`。
形式化陈述：subsingleton0 : Subsingleton (TypeVec 0)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
instance subsingleton0 : Subsingleton (TypeVec 0) :=
  ⟨fun _ _ => funext Fin2.elim0⟩

-- See `Mathlib/Tactic/Attr/Register.lean` for `register_simp_attr typevec`

/-- cases distinction for 0-length type vector -/
/-
**TypeVec.casesNil** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{β : TypeVec.{u_2} 0 → Sort u_1} → β Fin2.elim0 → (v : TypeVec.{u_2} 0) → 
β v
参数：v : TypeVec.{u_2} 0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
cases distinction for 0-length type vector
-/
protected def casesNil {β : TypeVec 0 → Sort*} (f : β Fin2.elim0) : ∀ v, β v :=
  fun v => cast (by congr; funext i; cases i) f

/-- cases distinction for (n+1)-length type vector -/
/-
**TypeVec.casesCons** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：(n : ℕ) →   {β : TypeVec.{u_2} (n + 1) → Sort u_1} →     ((t : Type u_2) →
 (v : TypeVec.{u_2} n) → β (v ::: t)) → (v : TypeVec.{u_2} (n + 1)) → β v
参数：t : Type u_2；v : TypeVec.{u_2} n；v ::: t；n + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
cases distinction for (n+1)-length type vector
-/
protected def casesCons (n : ℕ) {β : TypeVec (n + 1) → Sort*}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) :
    ∀ v, β v :=
  fun v : TypeVec (n + 1) => cast (by simp) (f v.last v.drop)
/-
**TypeVec.casesNil_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：∀ {β : TypeVec.{u_2} 0 → Sort u_1} (f : β Fin2.elim0), TypeVec.casesNil f 
Fin2.elim0 = f
参数：f : β Fin2.elim0。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem casesNil_append1 {β : TypeVec 0 → Sort*} (f : β Fin2.elim0) :
    TypeVec.casesNil f Fin2.elim0 = f :=
  rfl
/-
**TypeVec.casesCons_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：∀ (n : ℕ) {β : TypeVec.{u_2} (n + 1) → Sort u_1} (f : (t : Type u_2) → (v 
: TypeVec.{u_2} n) → β (v ::: t))   (v : TypeVec.{u_2} n) (α : Type u_2), TypeVe
c.casesCons n f (v ::: α) = f α v
参数：n : ℕ；n + 1；f : (t : Type u_2) → (v : TypeVec.{u_2} n) → β (v ::: t)；v : Type
Vec.{u_2} n；α : Type u_2；v ::: α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem casesCons_append1 (n : ℕ) {β : TypeVec (n + 1) → Sort*}
    (f : ∀ (t) (v : TypeVec n), β (v ::: t)) (v : TypeVec n) (α) :
    TypeVec.casesCons n f (v ::: α) = f α v :=
  rfl

/-- cases distinction for an arrow in the category of 0-length type vectors -/
/-
**TypeVec.typevecCasesNil** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
cases distinction for an arrow in the category of 0-length type vectors
-/
def typevecCasesNil₃ {β : ∀ v v' : TypeVec 0, v ⟹ v' → Sort*}
    (f : β Fin2.elim0 Fin2.elim0 nilFun) :
    ∀ v v' fs, β v v' fs := fun v v' fs => by
  refine cast ?_ f
  have eq₁ : v = Fin2.elim0 := by funext i; contradiction
  have eq₂ : v' = Fin2.elim0 := by funext i; contradiction
  have eq₃ : fs = nilFun := by funext i; contradiction
  cases eq₁; cases eq₂; cases eq₃; rfl

/-- cases distinction for an arrow in the category of (n+1)-length type vectors -/
/-
**TypeVec.typevecCasesCons** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
cases distinction for an arrow in the category of (n+1)-length type vectors
-/
def typevecCasesCons₃ (n : ℕ) {β : ∀ v v' : TypeVec (n + 1), v ⟹ v' → Sort*}
    (F : ∀ (t t') (f : t → t') (v v' : TypeVec n) (fs : v ⟹ v'),
    β (v ::: t) (v' ::: t') (fs ::: f)) :
    ∀ v v' fs, β v v' fs := by
  intro v v'
  rw [← append1_drop_last v, ← append1_drop_last v']
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F

/-- specialized cases distinction for an arrow in the category of 0-length type vectors -/
/-
**TypeVec.typevecCasesNil** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
specialized cases distinction for an arrow in the category of 0-length type vect
ors
-/
def typevecCasesNil₂ {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort*} (f : β nilFun) : ∀ f, β f := by
  intro g
  suffices g = nilFun by rwa [this]
  ext ⟨⟩

/-- specialized cases distinction for an arrow in the category of (n+1)-length type vectors -/
/-
**TypeVec.typevecCasesCons** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
specialized cases distinction for an arrow in the category of (n+1)-length type 
vectors
-/
def typevecCasesCons₂ (n : ℕ) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f)) : ∀ fs, β fs := by
  intro fs
  rw [← split_dropFun_lastFun fs]
  apply F
/-
**TypeVec.typevecCasesNil** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem typevecCasesNil₂_appendFun {β : Fin2.elim0 ⟹ Fin2.elim0 → Sort*} (f : β nilFun) :
    typevecCasesNil₂ f nilFun = f :=
  rfl
/-
**TypeVec.typevecCasesCons** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem typevecCasesCons₂_appendFun (n : ℕ) (t t' : Type*) (v v' : TypeVec n)
    {β : (v ::: t) ⟹ (v' ::: t') → Sort*}
    (F : ∀ (f : t → t') (fs : v ⟹ v'), β (fs ::: f))
    (f fs) :
    typevecCasesCons₂ n t t' v v' F (fs ::: f) = F f fs :=
  rfl

-- for lifting predicates and relations
/-- `PredLast α p x` predicates `p` of the last element of `x : α.append1 β`. -/
/-
**TypeVec.PredLast** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → (α : TypeVec.{u_1} n) → {β : Type u_1} → (β → Prop) → ⦃i : Fin2 
(n + 1)⦄ → (α ::: β) i → Prop
参数：α : TypeVec.{u_1} n；β → Prop。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`PredLast α p x` predicates `p` of the last element of `x : α.append1 β`.
-/
def PredLast (α : TypeVec n) {β : Type*} (p : β → Prop) : ∀ ⦃i⦄, (α.append1 β) i → Prop
  | Fin2.fs _ => fun _ => True
  | Fin2.fz => p

/-- `RelLast α r x y` says that `p` the last elements of `x y : α.append1 β` are related by `r` and
all the other elements are equal. -/
/-
**TypeVec.RelLast** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → (α : TypeVec.{u} n) → {β γ : Type u} → (β → γ → Prop) → ⦃i : Fin
2 (n + 1)⦄ → (α ::: β) i → (α ::: γ) i → Prop
参数：α : TypeVec.{u} n；β → γ → Prop。
该定义给出了一个带前提的构造。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RelLast α r x y` says that `p` the last elements of `x y : α.append1 β` are rel
ated by `r` and
all the other elements are equal.
-/
def RelLast (α : TypeVec n) {β γ : Type u} (r : β → γ → Prop) :
    ∀ ⦃i⦄, (α.append1 β) i → (α.append1 γ) i → Prop
  | Fin2.fs _ => Eq
  | Fin2.fz => r

section Liftp'

open Nat

/-- `repeat n t` is a `n-length` type vector that contains `n` occurrences of `t` -/
/-
**TypeVec.** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`repeat n t` is a `n-length` type vector that contains `n` occurrences of `t`
-/
def «repeat» : ∀ (n : ℕ), Type u → TypeVec n
  | 0, _ => Fin2.elim0
  | Nat.succ i, t => append1 («repeat» i t) t

/-- `prod α β` is the pointwise product of the components of `α` and `β` -/
/-
**TypeVec.prod** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → TypeVec.{u} n → TypeVec.{u} n → TypeVec.{u} n
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prod α β` is the pointwise product of the components of `α` and `β`
-/
def prod : ∀ {n}, TypeVec.{u} n → TypeVec.{u} n → TypeVec n
  | 0, _, _ => Fin2.elim0
  | n + 1, α, β => (@prod n (drop α) (drop β)) ::: (last α × last β)

@[inherit_doc] scoped[MvFunctor] infixl:45 " ⊗ " => TypeVec.prod

/-- `const x α` is an arrow that ignores its source and constructs a `TypeVec` that
contains nothing but `x` -/
/-
**TypeVec.const** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{β : Type u_1} → β → {n : ℕ} → (α : TypeVec.{u_2} n) → α.Arrow (TypeVec.re
peat n β)
参数：α : TypeVec.{u_2} n；TypeVec.repeat n β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`const x α` is an arrow that ignores its source and constructs a `TypeVec` that
contains nothing but `x`
-/
protected def const {β} (x : β) : ∀ {n} (α : TypeVec n), α ⟹ «repeat» _ β
  | succ _, α, Fin2.fs _ => TypeVec.const x (drop α) _
  | succ _, _, Fin2.fz => fun _ => x

open Function (uncurry)

/-- vector of equality on a product of vectors -/
/-
**TypeVec.repeatEq** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → (α : TypeVec.{u_1} n) → (α.prod α).Arrow (TypeVec.repeat n Prop)
参数：α : TypeVec.{u_1} n；α.prod α；TypeVec.repeat n Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
vector of equality on a product of vectors
-/
def repeatEq : ∀ {n} (α : TypeVec n), (α ⊗ α) ⟹ «repeat» _ Prop
  | 0, _ => nilFun
  | succ _, α => repeatEq (drop α) ::: uncurry Eq
/-
**TypeVec.const_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：const_append1 {β γ} (x : γ) {n} (α : TypeVec n) : TypeVec.const x (α ::: β
) = appendFun (TypeVec.const x α) fun _ => x
参数：x : γ；α : TypeVec n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem const_append1 {β γ} (x : γ) {n} (α : TypeVec n) :
    TypeVec.const x (α ::: β) = appendFun (TypeVec.const x α) fun _ => x := by
  ext i : 1; cases i <;> rfl
/-
**TypeVec.eq_nilFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun
参数：f : α ⟹ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem eq_nilFun {α β : TypeVec 0} (f : α ⟹ β) : f = nilFun := by
  ext x; cases x
/-
**TypeVec.id_eq_nilFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem id_eq_nilFun {α : TypeVec 0} : @id _ α = nilFun := by
  ext x; cases x
/-
**TypeVec.const_nil** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun
参数：x : β；α : TypeVec 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem const_nil {β} (x : β) (α : TypeVec 0) : TypeVec.const x α = nilFun := by
  ext i : 1; cases i

@[typevec]
/-
**TypeVec.repeat_eq_append1** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：repeat_eq_append1 {β} {n} (α : TypeVec n) : repeatEq (α ::: β) = splitFun 
(α
参数：α : TypeVec n。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem repeat_eq_append1 {β} {n} (α : TypeVec n) :
    repeatEq (α ::: β) = splitFun (α := (α ⊗ α) ::: _)
    (α' := («repeat» n Prop) ::: _) (repeatEq α) (uncurry Eq) := by
  induction n <;> rfl

@[typevec]
/-
**TypeVec.repeat_eq_nil** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：repeat_eq_nil (α : TypeVec 0) : repeatEq α = nilFun
参数：α : TypeVec 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem repeat_eq_nil (α : TypeVec 0) : repeatEq α = nilFun := by ext i; cases i

/-- predicate on a type vector to constrain only the last object -/
/-
**TypeVec.PredLast'** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：PredLast' (α : TypeVec n) {β : Type*} (p : β -> Prop) : (α ::: β) ⟹ «repea
t» (n + 1) Prop
参数：α : TypeVec n；p : β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
predicate on a type vector to constrain only the last object
-/
def PredLast' (α : TypeVec n) {β : Type*} (p : β → Prop) :
    (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (TypeVec.const True α) p

/-- predicate on the product of two type vectors to constrain only their last object -/
/-
**TypeVec.RelLast'** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：RelLast' (α : TypeVec n) {β : Type*} (p : β -> β -> Prop) : (α ::: β) otim
es (α ::: β) ⟹ «repeat» (n + 1) Prop
参数：α : TypeVec n；p : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
predicate on the product of two type vectors to constrain only their last object
-/
def RelLast' (α : TypeVec n) {β : Type*} (p : β → β → Prop) :
    (α ::: β) ⊗ (α ::: β) ⟹ «repeat» (n + 1) Prop :=
  splitFun (repeatEq α) (uncurry p)

/-- given `F : TypeVec.{u} (n+1) → Type u`, `curry F : Type u → TypeVec.{u} → Type u`,
i.e. its first argument can be fed in separately from the rest of the vector of arguments -/
/-
**TypeVec.Curry** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：Curry (F : TypeVec.{u} (n + 1) -> Type*) (α : Type u) (β : TypeVec.{u} n) 
: Type _
参数：F : TypeVec.{u} (n + 1) -> Type*；α : Type u；β : TypeVec.{u} n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
given `F : TypeVec.{u} (n+1) → Type u`, `curry F : Type u → TypeVec.{u} → Type u
`,
i.e. its first argument can be fed in separately from the rest of the vector of 
arguments
-/
def Curry (F : TypeVec.{u} (n + 1) → Type*) (α : Type u) (β : TypeVec.{u} n) : Type _ :=
  F (β ::: α)
/-
**TypeVec.Curry.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.Curry`。
形式化陈述：{n : ℕ} →   (F : TypeVec.{u} (n + 1) → Type u_1) →     (α : Type u) → (β :
 TypeVec.{u} n) → [I : Inhabited (F (β ::: α))] → Inhabited (TypeVec.Curry F α β
)
参数：F : TypeVec.{u} (n + 1) → Type u_1；α : Type u；β : TypeVec.{u} n；F (β ::: α)；T
ypeVec.Curry F α β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Curry.inhabited (F : TypeVec.{u} (n + 1) → Type*) (α : Type u) (β : TypeVec.{u} n)
    [I : Inhabited (F <| (β ::: α))] : Inhabited (Curry F α β) :=
  I

/-- arrow to remove one element of a `repeat` vector -/
/-
**TypeVec.dropRepeat** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：(α : Type u_1) → {n : ℕ} → (TypeVec.repeat n.succ α).drop.Arrow (TypeVec.r
epeat n α)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
arrow to remove one element of a `repeat` vector
-/
def dropRepeat (α : Type*) : ∀ {n}, drop («repeat» (succ n) α) ⟹ «repeat» n α
  | succ _, Fin2.fs i => dropRepeat α i
  | succ _, Fin2.fz => fun (a : α) => a

/-- projection for a repeat vector -/
/-
**TypeVec.ofRepeat** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{α : Type u_1} → {n : ℕ} → {i : Fin2 n} → TypeVec.repeat n α i → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
projection for a repeat vector
-/
def ofRepeat {α : Sort _} : ∀ {n i}, «repeat» n α i → α
  | _, Fin2.fz => fun (a : α) => a
  | _, Fin2.fs i => @ofRepeat _ _ i
/-
**TypeVec.const_iff_true** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) 
↔ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TypeVec.const.eq_1`：∀ {β : Type u_1} (x : β) (n : ℕ) (α : TypeVec.{u_2} 
n.succ) (a : Fin2 n),   TypeVec.const x α a.fs =     match (motive := (x : ℕ) → 
(x_1 : T…
-/
theorem const_iff_true {α : TypeVec n} {i x p} : ofRepeat (TypeVec.const p α i x) ↔ p := by
  induction i with
  | fz => rfl
  | fs _ ih =>
    rw [TypeVec.const]
    exact ih

section

/-- left projection of a `prod` vector -/
/-
**TypeVec.prod.fst** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.prod`。
形式化陈述：{n : ℕ} → {α β : TypeVec.{u} n} → (α.prod β).Arrow α
参数：α.prod β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
left projection of a `prod` vector
-/
def prod.fst : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ α
  | succ _, α, β, Fin2.fs i => @prod.fst _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.fst

/-- right projection of a `prod` vector -/
/-
**TypeVec.prod.snd** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.prod`。
形式化陈述：{n : ℕ} → {α β : TypeVec.{u} n} → (α.prod β).Arrow β
参数：α.prod β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
right projection of a `prod` vector
-/
def prod.snd : ∀ {n} {α β : TypeVec.{u} n}, α ⊗ β ⟹ β
  | succ _, α, β, Fin2.fs i => @prod.snd _ (drop α) (drop β) i
  | succ _, _, _, Fin2.fz => Prod.snd

/-- introduce a product where both components are the same -/
/-
**TypeVec.prod.diag** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.prod`。
形式化陈述：{n : ℕ} → {α : TypeVec.{u} n} → α.Arrow (α.prod α)
参数：α.prod α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
introduce a product where both components are the same
-/
def prod.diag : ∀ {n} {α : TypeVec.{u} n}, α ⟹ α ⊗ α
  | succ _, α, Fin2.fs _, x => @prod.diag _ (drop α) _ x
  | succ _, _, Fin2.fz, x => (x, x)

/-- constructor for `prod` -/
/-
**TypeVec.prod.mk** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.prod`。
形式化陈述：{n : ℕ} → {α β : TypeVec.{u} n} → (i : Fin2 n) → α i → β i → α.prod β i
参数：i : Fin2 n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
constructor for `prod`
-/
def prod.mk : ∀ {n} {α β : TypeVec.{u} n} (i : Fin2 n), α i → β i → (α ⊗ β) i
  | succ _, α, β, Fin2.fs i => mk (α := fun i => α i.fs) (β := fun i => β i.fs) i
  | succ _, _, _, Fin2.fz => Prod.mk

end


set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.prod_fst_mk** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) : TypeVec.p
rod.fst i (prod.mk i a b) = a
参数：i : Fin2 n；a : α i；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TypeVec.prod.mk.eq_2`：∀ (n : ℕ) (x_4 x_5 : TypeVec.{u} n.succ), TypeVec.
prod.mk Fin2.fz = Prod.mk
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TypeVec.prod.fst.eq_2`：∀ (n : ℕ) (x_4 x_5 : TypeVec.{u} n.succ), TypeVec
.prod.fst Fin2.fz = Prod.fst
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.fst i (prod.mk i a b) = a := by
  induction i with
  | fz => simp_all only [prod.fst, prod.mk]
  | fs _ i_ih => apply i_ih

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.prod_snd_mk** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) : TypeVec.p
rod.snd i (prod.mk i a b) = b
参数：i : Fin2 n；a : α i；b : β i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TypeVec.prod.mk.eq_2`：∀ (n : ℕ) (x_4 x_5 : TypeVec.{u} n.succ), TypeVec.
prod.mk Fin2.fz = Prod.mk
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TypeVec.prod.snd.eq_2`：∀ (n : ℕ) (x_4 x_5 : TypeVec.{u} n.succ), TypeVec
.prod.snd Fin2.fz = Prod.snd
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i) (b : β i) :
    TypeVec.prod.snd i (prod.mk i a b) = b := by
  induction i with
  | fz => simp_all [prod.snd, prod.mk]
  | fs _ i_ih => apply i_ih

/-- `prod` is functorial -/
/-
**TypeVec.prod.map** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec.prod`。
形式化陈述：{n : ℕ} → {α α' β β' : TypeVec.{u} n} → α.Arrow β → α'.Arrow β' → (α.prod 
α').Arrow (β.prod β')
参数：α.prod α'；β.prod β'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`prod` is functorial
-/
protected def prod.map : ∀ {n} {α α' β β' : TypeVec.{u} n}, α ⟹ β → α' ⟹ β' → α ⊗ α' ⟹ β ⊗ β'
  | succ _, α, α', β, β', x, y, Fin2.fs _, a =>
    @prod.map _ (drop α) (drop α') (drop β) (drop β') (dropFun x) (dropFun y) _ a
  | succ _, _, _, _, _, x, y, Fin2.fz, a => (x _ a.1, y _ a.2)



@[inherit_doc] scoped[MvFunctor] infixl:45 " ⊗' " => TypeVec.prod.map
/-
**TypeVec.fst_prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') : TypeVec.pr
od.fst ⊚ (f otimes' g) = f ⊚ TypeVec.prod.fst
参数：f : α ⟹ β；g : α' ⟹ β'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem fst_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.fst ⊚ (f ⊗' g) = f ⊚ TypeVec.prod.fst := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
/-
**TypeVec.snd_prod_mk** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') : TypeVec.pr
od.snd ⊚ (f otimes' g) = g ⊚ TypeVec.prod.snd
参数：f : α ⟹ β；g : α' ⟹ β'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem snd_prod_mk {α α' β β' : TypeVec n} (f : α ⟹ β) (g : α' ⟹ β') :
    TypeVec.prod.snd ⊚ (f ⊗' g) = g ⊚ TypeVec.prod.snd := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
/-
**TypeVec.fst_diag** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem fst_diag {α : TypeVec n} : TypeVec.prod.fst ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
/-
**TypeVec.snd_diag** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem snd_diag {α : TypeVec n} : TypeVec.prod.snd ⊚ (prod.diag : α ⟹ _) = id := by
  funext i; induction i with
  | fz => rfl
  | fs _ i_ih => apply i_ih
/-
**TypeVec.repeatEq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：repeatEq_iff_eq {α : TypeVec n} {i x y} : ofRepeat (repeatEq α i (prod.mk 
_ x y)) ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TypeVec.repeatEq.eq_2`：∀ (n : ℕ) (α : TypeVec.{u_1} n.succ), α.repeatEq 
= (α.drop.repeatEq ::: Function.uncurry Eq)
-/
theorem repeatEq_iff_eq {α : TypeVec n} {i x y} :
    ofRepeat (repeatEq α i (prod.mk _ x y)) ↔ x = y := by
  induction i with
  | fz => rfl
  | fs _ i_ih =>
    rw [repeatEq]
    exact i_ih

/-- given a predicate vector `p` over vector `α`, `Subtype_ p` is the type of vectors
that contain an `α` that satisfies `p` -/
/-
**TypeVec.Subtype_** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → {α : TypeVec.{u} n} → α.Arrow (TypeVec.repeat n Prop) → TypeVec.
{u} n
参数：TypeVec.repeat n Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
given a predicate vector `p` over vector `α`, `Subtype_ p` is the type of vector
s
that contain an `α` that satisfies `p`
-/
def Subtype_ : ∀ {n} {α : TypeVec.{u} n}, (α ⟹ «repeat» n Prop) → TypeVec n
  | _, _, p, Fin2.fz => Subtype fun x => p Fin2.fz x
  | _, _, p, Fin2.fs i => Subtype_ (dropFun p) i

/-- projection on `Subtype_` -/
/-
**TypeVec.subtypeVal** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → {α : TypeVec.{u} n} → (p : α.Arrow (TypeVec.repeat n Prop)) → (T
ypeVec.Subtype_ p).Arrow α
参数：p : α.Arrow (TypeVec.repeat n Prop)；TypeVec.Subtype_ p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
projection on `Subtype_`
-/
def subtypeVal : ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop), Subtype_ p ⟹ α
  | succ n, _, _, Fin2.fs i => @subtypeVal n _ _ i
  | succ _, _, _, Fin2.fz => Subtype.val

/-- arrow that rearranges the type of `Subtype_` to turn a subtype of vector into
a vector of subtypes -/
/-
**TypeVec.toSubtype** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} →   {α : TypeVec.{u} n} →     (p : α.Arrow (TypeVec.repeat n Prop)
) →       TypeVec.Arrow (fun i => { x // TypeVec.ofRepeat (p i x) }) (TypeVec.Su
btype_ p)
参数：p : α.Arrow (TypeVec.repeat n Prop)；fun i => { x // TypeVec.ofRepeat (p i x) 
}；TypeVec.Subtype_ p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
arrow that rearranges the type of `Subtype_` to turn a subtype of vector into
a vector of subtypes
-/
def toSubtype :
    ∀ {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop),
      (fun i : Fin2 n => { x // ofRepeat <| p i x }) ⟹ Subtype_ p
  | succ _, _, p, Fin2.fs i, x => toSubtype (dropFun p) i x
  | succ _, _, _, Fin2.fz, x => x

/-- arrow that rearranges the type of `Subtype_` to turn a vector of subtypes
into a subtype of vector -/
/-
**TypeVec.ofSubtype** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} →   {α : TypeVec.{u} n} →     (p : α.Arrow (TypeVec.repeat n Prop)
) → (TypeVec.Subtype_ p).Arrow fun i => { x // TypeVec.ofRepeat (p i x) }
参数：p : α.Arrow (TypeVec.repeat n Prop)；TypeVec.Subtype_ p；p i x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
arrow that rearranges the type of `Subtype_` to turn a vector of subtypes
into a subtype of vector
-/
def ofSubtype {n} {α : TypeVec.{u} n} (p : α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x // ofRepeat <| p i x }
  | Fin2.fs i, x => ofSubtype _ i x
  | Fin2.fz, x => x

/-- similar to `toSubtype` adapted to relations (i.e. predicate on product) -/
/-
**TypeVec.toSubtype'** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：toSubtype'_of_subtype' {α : TypeVec n} (r : α otimes α ⟹ «repeat» n Prop) 
: toSubtype' r ⊚ ofSubtype' r = id
参数：r : α otimes α ⟹ «repeat» n Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
similar to `toSubtype` adapted to relations (i.e. predicate on product)
-/
def toSubtype' {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ «repeat» n Prop) :
    (fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }) ⟹ Subtype_ p
  | Fin2.fs i, x => toSubtype' (dropFun p) i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩

/-- similar to `of_subtype` adapted to relations (i.e. predicate on product) -/
/-
**TypeVec.ofSubtype'** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} →   {α : TypeVec.{u} n} →     (p : (α.prod α).Arrow (TypeVec.repea
t n Prop)) →       (TypeVec.Subtype_ p).Arrow fun i => { x // TypeVec.ofRepeat (
p i (TypeVec.prod.mk i x.1 x.2)) }
参数：p : (α.prod α).Arrow (TypeVec.repeat n Prop)；TypeVec.Subtype_ p；p i (TypeVec.
prod.mk i x.1 x.2)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
similar to `of_subtype` adapted to relations (i.e. predicate on product)
-/
def ofSubtype' {n} {α : TypeVec.{u} n} (p : α ⊗ α ⟹ «repeat» n Prop) :
    Subtype_ p ⟹ fun i : Fin2 n => { x : α i × α i // ofRepeat <| p i (prod.mk _ x.1 x.2) }
  | Fin2.fs i, x => ofSubtype' _ i x
  | Fin2.fz, x => ⟨x.val, cast (by congr) x.property⟩

/-- similar to `diag` but the target vector is a `Subtype_`
guaranteeing the equality of the components -/
/-
**TypeVec.diagSub** 是 Mathlib 中的一个定义，位于命名空间 `TypeVec`。
形式化陈述：{n : ℕ} → {α : TypeVec.{u} n} → α.Arrow (TypeVec.Subtype_ α.repeatEq)
参数：TypeVec.Subtype_ α.repeatEq。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
similar to `diag` but the target vector is a `Subtype_`
guaranteeing the equality of the components
-/
def diagSub {n} {α : TypeVec.{u} n} : α ⟹ Subtype_ (repeatEq α)
  | Fin2.fs _, x => @diagSub _ (drop α) _ x
  | Fin2.fz, x => ⟨(x, x), rfl⟩
/-
**TypeVec.subtypeVal_nil** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：subtypeVal_nil {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 Prop) : TypeVec.su
btypeVal ps = nilFun
参数：ps : α ⟹ «repeat» 0 Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
-/
theorem subtypeVal_nil {α : TypeVec.{u} 0} (ps : α ⟹ «repeat» 0 Prop) :
    TypeVec.subtypeVal ps = nilFun :=
  funext <| by rintro ⟨⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.diag_sub_val** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：diag_sub_val {n} {α : TypeVec.{u} n} : subtypeVal (repeatEq α) ⊚ diagSub =
 prod.diag
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TypeVec.subtypeVal.eq_2`：∀ (n : ℕ) (x_4 : TypeVec.{u} n.succ) (x_5 : x_4
.Arrow (TypeVec.repeat n.succ Prop)),   TypeVec.subtypeVal x_5 Fin2.fz = Subtype
.val
· 使用定理 `TypeVec.prod.diag.eq_2`：∀ (n : ℕ) (x_4 : TypeVec.{u} n.succ) (x_5 : x_4 
Fin2.fz), TypeVec.prod.diag Fin2.fz x_5 = (x_5, x_5)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem diag_sub_val {n} {α : TypeVec.{u} n} : subtypeVal (repeatEq α) ⊚ diagSub = prod.diag := by
  ext i x
  induction i with
  | fz => simp only [comp, subtypeVal, diagSub, prod.diag]
  | fs _ i_ih => apply @i_ih (drop α)
/-
**TypeVec.prod_id** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：prod_id : forall {n} {α β : TypeVec.{u} n}, (id otimes' id) = (id : α otim
es β ⟹ _)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem prod_id : ∀ {n} {α β : TypeVec.{u} n}, (id ⊗' id) = (id : α ⊗ β ⟹ _) := by
  intros
  ext i a
  induction i with
  | fz => cases a; rfl
  | fs _ i_ih => apply i_ih
/-
**TypeVec.append_prod_appendFun** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u}
 {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : φ -> φ'} {g₁ : ψ -> ψ'} : ((f₀ otimes' g₀) ::
: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) otimes' (g₀ ::: g₁))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem append_prod_appendFun {n} {α α' β β' : TypeVec.{u} n} {φ φ' ψ ψ' : Type u}
    {f₀ : α ⟹ α'} {g₀ : β ⟹ β'} {f₁ : φ → φ'} {g₁ : ψ → ψ'} :
    ((f₀ ⊗' g₀) ::: (_root_.Prod.map f₁ g₁)) = ((f₀ ::: f₁) ⊗' (g₀ ::: g₁)) := by
  ext i a
  cases i
  · cases a
    rfl
  · rfl

end Liftp'

@[simp]
/-
**TypeVec.dropFun_diag** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_diag {α} : dropFun (@prod.diag (n + 1) α) = prod.diag := rfl

@[simp]
/-
**TypeVec.dropFun_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) : dropFun (subtypeV
al p) = subtypeVal _
参数：p : α ⟹ «repeat» (n + 1) Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (subtypeVal p) = subtypeVal _ :=
  rfl

@[simp]
/-
**TypeVec.lastFun_subtypeVal** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) : lastFun (subtypeV
al p) = Subtype.val
参数：p : α ⟹ «repeat» (n + 1) Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_subtypeVal {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (subtypeVal p) = Subtype.val :=
  rfl

@[simp]
/-
**TypeVec.dropFun_toSubtype** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) : dropFun (toSubtype
 p) = toSubtype _
参数：p : α ⟹ «repeat» (n + 1) Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (toSubtype p) = toSubtype _ := rfl

@[simp]
/-
**TypeVec.lastFun_toSubtype** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) : lastFun (toSubtype
 p) = _root_.id
参数：p : α ⟹ «repeat» (n + 1) Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_toSubtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (toSubtype p) = _root_.id := rfl

@[simp]
/-
**TypeVec.dropFun_of_subtype** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) : dropFun (ofSubtyp
e p) = ofSubtype _
参数：p : α ⟹ «repeat» (n + 1) Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    dropFun (ofSubtype p) = ofSubtype _ := rfl

@[simp]
/-
**TypeVec.lastFun_of_subtype** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) : lastFun (ofSubtyp
e p) = _root_.id
参数：p : α ⟹ «repeat» (n + 1) Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_of_subtype {α} (p : α ⟹ «repeat» (n + 1) Prop) :
    lastFun (ofSubtype p) = _root_.id := rfl

@[simp]
/-
**TypeVec.dropFun_RelLast'** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_RelLast' {α : TypeVec n} {β} (R : β -> β -> Prop) : dropFun (RelLa
st' α R) = repeatEq α
参数：R : β -> β -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_RelLast' {α : TypeVec n} {β} (R : β → β → Prop) :
    dropFun (RelLast' α R) = repeatEq α :=
  rfl

attribute [simp] drop_append1'

@[simp]
/-
**TypeVec.dropFun_prod** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') : dr
opFun (f otimes' f') = (dropFun f otimes' dropFun f')
参数：n + 1；f : α ⟹ β；f' : α' ⟹ β'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    dropFun (f ⊗' f') = (dropFun f ⊗' dropFun f') := rfl

@[simp]
/-
**TypeVec.lastFun_prod** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') : la
stFun (f otimes' f') = Prod.map (lastFun f) (lastFun f')
参数：n + 1；f : α ⟹ β；f' : α' ⟹ β'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_prod {α α' β β' : TypeVec (n + 1)} (f : α ⟹ β) (f' : α' ⟹ β') :
    lastFun (f ⊗' f') = Prod.map (lastFun f) (lastFun f') := rfl

@[simp]
/-
**TypeVec.dropFun_from_append1_drop_last** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_from_append1_drop_last {α : TypeVec (n + 1)} : dropFun (@fromAppen
d1DropLast _ α) = id
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    dropFun (@fromAppend1DropLast _ α) = id :=
  rfl

@[simp]
/-
**TypeVec.lastFun_from_append1_drop_last** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：lastFun_from_append1_drop_last {α : TypeVec (n + 1)} : lastFun (@fromAppen
d1DropLast _ α) = _root_.id
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lastFun_from_append1_drop_last {α : TypeVec (n + 1)} :
    lastFun (@fromAppend1DropLast _ α) = _root_.id :=
  rfl

@[simp]
/-
**TypeVec.dropFun_id** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id
参数：n + 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dropFun_id {α : TypeVec (n + 1)} : dropFun (@TypeVec.id _ α) = id :=
  rfl

@[simp]
/-
**TypeVec.prod_map_id** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α otimes' @TypeVec.id _ β) 
= id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.prod_id`：prod_id : forall {n} {α β : TypeVec.{u} n}, (id otimes'
 id) = (id : α otimes β ⟹ _)
-/
theorem prod_map_id {α β : TypeVec n} : (@TypeVec.id _ α ⊗' @TypeVec.id _ β) = id := prod_id

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.toSubtype_of_subtype** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：toSubtype_of_subtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) : toSubtype
 p ⊚ ofSubtype p = id
参数：p : α ⟹ «repeat» n Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TypeVec.toSubtype.eq_2`：∀ (n : ℕ) (x_5 : TypeVec.{u} n.succ) (x_6 : x_5.
Arrow (TypeVec.repeat n.succ Prop))   (x_7 : { x // TypeVec.ofRepeat (x_6 Fin2.f
z x) }), Typ…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TypeVec.toSubtype.eq_1`：∀ (n : ℕ) (x_5 : TypeVec.{u} n.succ) (p : x_5.Ar
row (TypeVec.repeat n.succ Prop)) (i : Fin2 n)   (x_6 : { x // TypeVec.ofRepeat 
(p i.fs x) }…
-/
theorem toSubtype_of_subtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    toSubtype p ⊚ ofSubtype p = id := by
  ext i x
  induction i <;> simp only [id, toSubtype, comp, ofSubtype] at *
  simp [*]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.subtypeVal_toSubtype** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：subtypeVal_toSubtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) : subtypeVa
l p ⊚ toSubtype p = fun _ => Subtype.val
参数：p : α ⟹ «repeat» n Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TypeVec.toSubtype.eq_2`：∀ (n : ℕ) (x_5 : TypeVec.{u} n.succ) (x_6 : x_5.
Arrow (TypeVec.repeat n.succ Prop))   (x_7 : { x // TypeVec.ofRepeat (x_6 Fin2.f
z x) }), Typ…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TypeVec.subtypeVal.eq_2`：∀ (n : ℕ) (x_4 : TypeVec.{u} n.succ) (x_5 : x_4
.Arrow (TypeVec.repeat n.succ Prop)),   TypeVec.subtypeVal x_5 Fin2.fz = Subtype
.val
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TypeVec.toSubtype.eq_1`：∀ (n : ℕ) (x_5 : TypeVec.{u} n.succ) (p : x_5.Ar
row (TypeVec.repeat n.succ Prop)) (i : Fin2 n)   (x_6 : { x // TypeVec.ofRepeat 
(p i.fs x) }…
· 使用定理 `TypeVec.subtypeVal.eq_1`：∀ (n : ℕ) (x_4 : TypeVec.{u} n.succ) (x_5 : x_4
.Arrow (TypeVec.repeat n.succ Prop)) (i : Fin2 n),   TypeVec.subtypeVal x_5 i.fs
 = TypeVec.su…
-/
theorem subtypeVal_toSubtype {α : TypeVec n} (p : α ⟹ «repeat» n Prop) :
    subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val := by
  ext i x
  induction i <;> simp only [toSubtype, comp, subtypeVal] at *
  simp [*]

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.toSubtype_of_subtype_assoc** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：toSubtype_of_subtype_assoc {α β : TypeVec n} (p : α ⟹ «repeat» n Prop) (f 
: β ⟹ Subtype_ p) : @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f
参数：p : α ⟹ «repeat» n Prop；f : β ⟹ Subtype_ p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TypeVec.comp_assoc`：comp_assoc (h : γ ⟹ δ) (g : β ⟹ γ) (f : α ⟹ β) : (h 
⊚ g) ⊚ f = h ⊚ g ⊚ f
· 使用定理 `TypeVec.toSubtype_of_subtype`：toSubtype_of_subtype {α : TypeVec n} (p : 
α ⟹ «repeat» n Prop) : toSubtype p ⊚ ofSubtype p = id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSubtype_of_subtype_assoc
    {α β : TypeVec n} (p : α ⟹ «repeat» n Prop) (f : β ⟹ Subtype_ p) :
    @toSubtype n _ p ⊚ ofSubtype _ ⊚ f = f := by
  rw [← comp_assoc, toSubtype_of_subtype]; simp

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**TypeVec.toSubtype'_of_subtype'** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：∀ {n : ℕ} {α : TypeVec.{u_1} n} (r : (α.prod α).Arrow (TypeVec.repeat n Pr
op)),   TypeVec.comp (TypeVec.toSubtype' r) (TypeVec.ofSubtype' r) = TypeVec.id
参数：r : (α.prod α).Arrow (TypeVec.repeat n Prop)；TypeVec.toSubtype' r；TypeVec.ofS
ubtype' r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `TypeVec.toSubtype'`：toSubtype'_of_subtype' {α : TypeVec n} (r : α otimes
 α ⟹ «repeat» n Prop) : toSubtype' r ⊚ ofSubtype' r = id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toSubtype'_of_subtype' {α : TypeVec n} (r : α ⊗ α ⟹ «repeat» n Prop) :
    toSubtype' r ⊚ ofSubtype' r = id := by
  ext i x
  induction i
  <;> dsimp only [id, toSubtype', comp, ofSubtype'] at *
  <;> simp [*]

set_option backward.isDefEq.respectTransparency false in
/-
**TypeVec.subtypeVal_toSubtype'** 是 Mathlib 中的一个定理，位于命名空间 `TypeVec`。
形式化陈述：subtypeVal_toSubtype' {α : TypeVec n} (r : α otimes α ⟹ «repeat» n Prop) :
 subtypeVal r ⊚ toSubtype' r = fun i x => prod.mk i x.1.fst x.1.snd
参数：r : α otimes α ⟹ «repeat» n Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `TypeVec.toSubtype'`：toSubtype'_of_subtype' {α : TypeVec n} (r : α otimes
 α ⟹ «repeat» n Prop) : toSubtype' r ⊚ ofSubtype' r = id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `TypeVec.subtypeVal.eq_2`：∀ (n : ℕ) (x_4 : TypeVec.{u} n.succ) (x_5 : x_4
.Arrow (TypeVec.repeat n.succ Prop)),   TypeVec.subtypeVal x_5 Fin2.fz = Subtype
.val
· 使用定理 `TypeVec.prod.mk.eq_2`：∀ (n : ℕ) (x_4 x_5 : TypeVec.{u} n.succ), TypeVec.
prod.mk Fin2.fz = Prod.mk
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TypeVec.subtypeVal.eq_1`：∀ (n : ℕ) (x_4 : TypeVec.{u} n.succ) (x_5 : x_4
.Arrow (TypeVec.repeat n.succ Prop)) (i : Fin2 n),   TypeVec.subtypeVal x_5 i.fs
 = TypeVec.su…
· 使用定理 `TypeVec.prod.mk.eq_1`：∀ (n : ℕ) (α β : TypeVec.{u} n.succ) (i : Fin2 n),
 TypeVec.prod.mk i.fs = TypeVec.prod.mk i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
theorem subtypeVal_toSubtype' {α : TypeVec n} (r : α ⊗ α ⟹ «repeat» n Prop) :
    subtypeVal r ⊚ toSubtype' r = fun i x => prod.mk i x.1.fst x.1.snd := by
  ext i x
  induction i <;> simp only [toSubtype', comp, subtypeVal, prod.mk] at *
  simp [*]

end TypeVec

