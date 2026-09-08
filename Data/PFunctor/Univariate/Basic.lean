/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.W.Basic

/-!
# Polynomial Functors

This file defines polynomial functors and the W-type construction as a polynomial functor.
(For the M-type construction, see `Mathlib/Data/PFunctor/Univariate/M.lean`.)
-/

@[expose] public section

universe u v uA uB uA₁ uB₁ uA₂ uB₂ v₁ v₂ v₃

-- Note: `set_option linter.checkUnivs` should not apply here,
-- we really do want two separate universe levels
set_option linter.checkUnivs false in
/-- A polynomial functor `P` is given by a type `A` and a family `B` of types over `A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` and
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to the relevant
elements of `α`.
-/
@[pp_with_univ]
/-
**PFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (max (uA + 1) (uB + 1))
参数：max (uA + 1) (uB + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A polynomial functor `P` is given by a type `A` and a family `B` of types over `
A`. `P` maps
any type `α` to a new type `P α`, which is defined as the sigma type `Σ x, P.B x
 → α`.

An element of `P α` is a pair `⟨a, f⟩`, where `a` is an element of a type `A` an
d
`f : B a → α`. Think of `a` as the shape of the object and `f` as an index to th
e relevant
elements of `α`.
-/
structure PFunctor where
  /-- The head type -/
  A : Type uA
  /-- The child family of types -/
  B : A → Type uB

namespace PFunctor

/-
**PFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `PFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited PFunctor :=
  ⟨⟨default, default⟩⟩

variable (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃}

/-- Applying `P` to an object of `Type` -/
@[coe]
/-
**PFunctor.Obj** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor`。
形式化陈述：Obj (α : Type v) : Type (max v uA uB)
参数：α : Type v。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `P` to an object of `Type`
-/
def Obj (α : Type v) : Type (max v uA uB) :=
  Σ x : P.A, P.B x → α
/-
**PFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `PFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun PFunctor.{uA, uB} (fun _ => Type v → Type (max v uA uB)) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
/-
**PFunctor.map** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor`。
形式化陈述：map (f : α -> β) : P α -> P β
参数：f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `P` to a morphism of `Type`
-/
def map (f : α → β) : P α → P β :=
  fun ⟨a, g⟩ => ⟨a, f ∘ g⟩
/-
**PFunctor.Obj.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Obj`。
形式化陈述：(P : PFunctor.{uA, uB}) → {α : Type v₁} → [Inhabited P.A] → [Inhabited α] 
→ Inhabited (↑P α)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Obj.inhabited [Inhabited P.A] [Inhabited α] : Inhabited (P α) :=
  ⟨⟨default, default⟩⟩
/-
**PFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `PFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Functor P.Obj where map := @map P

/-- We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic. -/
@[simp]
/-
**PFunctor.map_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：map_eq_map {α β : Type v} (f : α -> β) (x : P α) : f < > x = P.map f x
参数：f : α -> β；x : P α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We prefer `PFunctor.map` to `Functor.map` because it is universe-polymorphic.
-/
theorem map_eq_map {α β : Type v} (f : α → β) (x : P α) : f <$> x = P.map f x :=
  rfl

@[simp]
/-
**PFunctor.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (f : α → β) (a : P.A
) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
参数：P : PFunctor.{uA, uB}；f : α → β；a : P.A；g : P.B a → α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_eq (f : α → β) (a : P.A) (g : P.B a → α) :
    P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩ :=
  rfl

@[simp]
/-
**PFunctor.id_map** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} (x : ↑P α), P.map id x = x
参数：P : PFunctor.{uA, uB}；x : ↑P α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem id_map : ∀ x : P α, P.map id x = x := fun ⟨_, _⟩ => rfl

@[simp]
/-
**PFunctor.map_map** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} {γ : Type v₃} (f : α
 → β) (g : β → γ) (x : ↑P α),   P.map g (P.map f x) = P.map (g ∘ f) x
参数：P : PFunctor.{uA, uB}；f : α → β；g : β → γ；x : ↑P α；P.map f x；g ∘ f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem map_map (f : α → β) (g : β → γ) :
    ∀ x : P α, P.map g (P.map f x) = P.map (g ∘ f) x := fun ⟨_, _⟩ => rfl
/-
**PFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `PFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor (Obj.{v} P) where
  map_const := rfl
  id_map x := P.id_map x
  comp_map f g x := P.map_map f g x |>.symm

/-- Re-export existing definition of W-types and adapt it to a packaged definition of polynomial
functor. -/
/-
**PFunctor.W** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor`。
形式化陈述：W : Type (max uA uB)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Re-export existing definition of W-types and adapt it to a packaged definition o
f polynomial
functor.
-/
def W : Type (max uA uB) :=
  WType P.B

/- Inhabitants of W types is awkward to encode as an instance assumption because there needs to be a
value `a : P.A` such that `P.B a` is empty to yield a finite tree. -/

variable {P}

/-- The root element of a W tree -/
/-
**PFunctor.W.head** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.W`。
形式化陈述：{P : PFunctor.{uA, uB}} → P.W → P.A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The root element of a W tree
-/
def W.head : W P → P.A
  | ⟨a, _f⟩ => a

/-- The children of the root of a W tree -/
/-
**PFunctor.W.children** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.W`。
形式化陈述：{P : PFunctor.{uA, uB}} → (x : P.W) → P.B x.head → P.W
参数：x : P.W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The children of the root of a W tree
-/
def W.children : ∀ x : W P, P.B (W.head x) → W P
  | ⟨_a, f⟩ => f

/-- The destructor for W-types -/
/-
**PFunctor.W.dest** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.W`。
形式化陈述：{P : PFunctor.{uA, uB}} → P.W → ↑P P.W
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The destructor for W-types
-/
def W.dest : W P → P (W P)
  | ⟨a, f⟩ => ⟨a, f⟩

/-- The constructor for W-types -/
/-
**PFunctor.W.mk** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.W`。
形式化陈述：{P : PFunctor.{uA, uB}} → ↑P P.W → P.W
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constructor for W-types
-/
def W.mk : P (W P) → W P
  | ⟨a, f⟩ => ⟨a, f⟩

@[simp]
/-
**PFunctor.W.dest_mk** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.W`。
形式化陈述：∀ {P : PFunctor.{uA, uB}} (p : ↑P P.W), (PFunctor.W.mk p).dest = p
参数：p : ↑P P.W；PFunctor.W.mk p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem W.dest_mk (p : P (W P)) : W.dest (W.mk p) = p := by cases p; rfl

@[simp]
/-
**PFunctor.W.mk_dest** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor.W`。
形式化陈述：∀ {P : PFunctor.{uA, uB}} (p : P.W), PFunctor.W.mk p.dest = p
参数：p : P.W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem W.mk_dest (p : W P) : W.mk (W.dest p) = p := by cases p; rfl

variable (P)

/-- `Idx` identifies a location inside the application of a polynomial functor. For `F : PFunctor`,
`x : F α` and `i : F.Idx`, `i` can designate one part of `x` or is invalid, if `i.1 ≠ x.1`. -/
/-
**PFunctor.Idx** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor`。
形式化陈述：Idx : Type (max uA uB)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Idx` identifies a location inside the application of a polynomial functor. For 
`F : PFunctor`,
`x : F α` and `i : F.Idx`, `i` can designate one part of `x` or is invalid, if `
i.1 ≠ x.1`.
-/
def Idx : Type (max uA uB) :=
  Σ x : P.A, P.B x
/-
**PFunctor.Idx.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Idx`。
形式化陈述：(P : PFunctor.{uA, uB}) → [inst : Inhabited P.A] → [Inhabited (P.B default
)] → Inhabited P.Idx
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Idx.inhabited [Inhabited P.A] [Inhabited (P.B default)] : Inhabited P.Idx :=
  ⟨⟨default, default⟩⟩

variable {P}

/-- `x.iget i` takes the component of `x` designated by `i` if any is or returns a default value -/
/-
**PFunctor.Obj.iget** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.Obj`。
形式化陈述：{P : PFunctor.{uA, uB}} → [DecidableEq P.A] → {α : Type u_1} → [Inhabited 
α] → ↑P α → P.Idx → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`x.iget i` takes the component of `x` designated by `i` if any is or returns a d
efault value
-/
def Obj.iget [DecidableEq P.A] {α} [Inhabited α] (x : P α) (i : P.Idx) : α :=
  if h : i.1 = x.1 then x.2 (cast (congr_arg _ h) i.2) else default

@[simp]
/-
**PFunctor.fst_map** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：fst_map (x : P α) (f : α -> β) : (P.map f x).1 = x.1
参数：x : P α；f : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem fst_map (x : P α) (f : α → β) : (P.map f x).1 = x.1 := by cases x; rfl

@[simp]
/-
**PFunctor.iget_map** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α) (f : α ->
 β) (i : P.Idx) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i)
参数：x : P α；f : α -> β；i : P.Idx；h : i.1 = x.1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.fst_map`：fst_map (x : P α) (f : α -> β) : (P.map f x).1 = x.1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem iget_map [DecidableEq P.A] [Inhabited α] [Inhabited β] (x : P α)
    (f : α → β) (i : P.Idx) (h : i.1 = x.1) : (P.map f x).iget i = f (x.iget i) := by
  simp only [Obj.iget, fst_map, *, dif_pos]
  cases x
  rfl

end PFunctor

/-
Composition of polynomial functors.
-/
namespace PFunctor

/-- Composition for polynomial functors -/
/-
**PFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor`。
形式化陈述：comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) : PFunctor.{max
 uA₁ uA₂ uB₂, max uB₁ uB₂}
参数：P₂ : PFunctor.{uA₂, uB₂}；P₁ : PFunctor.{uA₁, uB₁}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition for polynomial functors
-/
def comp (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) :
    PFunctor.{max uA₁ uA₂ uB₂, max uB₁ uB₂} :=
  ⟨Σ a₂ : P₂.1, P₂.2 a₂ → P₁.1, fun a₂a₁ => Σ u : P₂.2 a₂a₁.1, P₁.2 (a₂a₁.2 u)⟩

/-- Constructor for composition -/
/-
**PFunctor.comp.mk** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.comp`。
形式化陈述：(P₂ : PFunctor.{uA₂, uB₂}) → (P₁ : PFunctor.{uA₁, uB₁}) → {α : Type v} → ↑
P₂ (↑P₁ α) → ↑(P₂.comp P₁) α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for composition
-/
def comp.mk (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : P₂ (P₁ α)) :
    comp P₂ P₁ α :=
  ⟨⟨x.1, Sigma.fst ∘ x.2⟩, fun a₂a₁ => (x.2 a₂a₁.1).2 a₂a₁.2⟩

/-- Destructor for composition -/
/-
**PFunctor.comp.get** 是 Mathlib 中的一个定义，位于命名空间 `PFunctor.comp`。
形式化陈述：(P₂ : PFunctor.{uA₂, uB₂}) → (P₁ : PFunctor.{uA₁, uB₁}) → {α : Type v} → ↑
(P₂.comp P₁) α → ↑P₂ (↑P₁ α)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for composition
-/
def comp.get (P₂ : PFunctor.{uA₂, uB₂}) (P₁ : PFunctor.{uA₁, uB₁}) {α : Type v} (x : comp P₂ P₁ α) :
    P₂ (P₁ α) :=
  ⟨x.1.1, fun a₂ => ⟨x.1.2 a₂, fun a₁ => x.2 ⟨a₂, a₁⟩⟩⟩

end PFunctor

/-
Lifting predicates and relations.
-/
namespace PFunctor

variable {P : PFunctor.{uA, uB}}

open Functor

set_option backward.isDefEq.respectTransparency false in
/-
**PFunctor.liftp_iff** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：liftp_iff {α : Type u} (p : α -> Prop) (x : P α) : Liftp p x ↔ exists a f,
 x = ⟨a, f⟩ ∧ forall i, p (f i)
参数：p : α -> Prop；x : P α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.map_eq_map`：map_eq_map {α β : Type v} (f : α -> β) (x : P α) : 
f < > x = P.map f x
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftp_iff {α : Type u} (p : α → Prop) (x : P α) :
    Liftp p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i => (f i).val, ?_, fun i => (f i).property⟩
    rw [← hy, h, map_eq_map, PFunctor.map_eq]
    congr
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i => ⟨f i, pf i⟩⟩
  rw [xeq]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**PFunctor.liftp_iff'** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：liftp_iff' {α : Type u} (p : α -> Prop) (a : P.A) (f : P.B a -> α) : @Lift
p.{u} P.Obj _ α p ⟨a, f⟩ ↔ forall i, p (f i)
参数：p : α -> Prop；a : P.A；f : P.B a -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem liftp_iff' {α : Type u} (p : α → Prop) (a : P.A) (f : P.B a → α) :
    @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ ∀ i, p (f i) := by
  simp only [liftp_iff]; constructor <;> intro h
  · rcases h with ⟨a', f', heq, h'⟩
    cases heq
    assumption
  repeat' first | constructor | assumption
/-
**PFunctor.liftr_iff** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：liftr_iff {α : Type u} (r : α -> α -> Prop) (x y : P α) : Liftr r x y ↔ ex
ists a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ forall i, r (f₀ i) (f₁ i)
参数：r : α -> α -> Prop；x y : P α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : P α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq]
    rfl
  rw [yeq]; rfl

open Set
/-
**PFunctor.supp_eq** 是 Mathlib 中的一个定理，位于命名空间 `PFunctor`。
形式化陈述：supp_eq {α : Type u} (a : P.A) (f : P.B a -> α) : @supp.{u} P.Obj _ α (⟨a,
 f⟩ : P α) = f '' univ
参数：a : P.A；f : P.B a -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `PFunctor.liftp_iff'`：liftp_iff' {α : Type u} (p : α -> Prop) (a : P.A) (
f : P.B a -> α) : @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ forall i, p (f i)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem supp_eq {α : Type u} (a : P.A) (f : P.B a → α) :
    @supp.{u} P.Obj _ α (⟨a, f⟩ : P α) = f '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun x => ∃ y : P.B a, f y = x
    rw [liftp_iff']
    intro
    exact ⟨_, rfl⟩
  · simp only [liftp_iff']
    cases h
    subst x
    tauto

end PFunctor

