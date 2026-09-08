/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Yaël Dillies
-/
module

public import Mathlib.Data.Set.BooleanAlgebra
public import Mathlib.Data.SetLike.Basic
public import Mathlib.Order.Hom.Basic

/-!
# Closure operators between preorders

We define (bundled) closure operators on a preorder as monotone (increasing), extensive
(inflationary) and idempotent functions.
We define closed elements for the operator as elements which are fixed by it.

Lower adjoints to a function between preorders `u : β → α` allow to generalise closure operators to
situations where the closure operator we are dealing with naturally decomposes as `u ∘ l` where `l`
is a worthy function to have on its own. Typical examples include
`l : Set G → Subgroup G := Subgroup.closure`, `u : Subgroup G → Set G := (↑)`, where `G` is a group.
This shows there is a close connection between closure operators, lower adjoints and Galois
connections/insertions: every Galois connection induces a lower adjoint which itself induces a
closure operator by composition (see `GaloisConnection.lowerAdjoint` and
`LowerAdjoint.closureOperator`), and every closure operator on a partial order induces a Galois
insertion from the set of closed elements to the underlying type (see `ClosureOperator.gi`).

## Main definitions

* `ClosureOperator`: A closure operator is a monotone function `f : α → α` such that
  `∀ x, x ≤ f x` and `∀ x, f (f x) = f x`.
* `LowerAdjoint`: A lower adjoint to `u : β → α` is a function `l : α → β` such that `l` and `u`
  form a Galois connection.

## Implementation details

Although `LowerAdjoint` is technically a generalisation of `ClosureOperator` (by defining
`toFun := id`), it is desirable to have both as otherwise `id`s would be carried all over the
place when using concrete closure operators such as `ConvexHull`.

`LowerAdjoint` really is a semibundled `structure` version of `GaloisConnection`.

## References

* https://en.wikipedia.org/wiki/Closure_operator#Closure_operators_on_partially_ordered_sets
-/

@[expose] public section

open Set

/-! ### Closure operator -/


variable (α : Type*) {ι : Sort*} {κ : ι → Sort*}

/-- A closure operator on the preorder `α` is a monotone function which is extensive (every `x`
is less than its closure) and idempotent. -/
/-
**ClosureOperator** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：ClosureOperator [Preorder α] extends α ->o α where /-- An element is less 
than or equal its closure -/ le_closure' : forall x, x <= toFun x /-- Closures a
re idempotent -/ idempotent' : forall x, toFun (toFun x) = toFun x /-- Predicate
 for an element to be closed.  By default, this is defined as `c.IsClosed x
继承自：α ->o α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A closure operator on the preorder `α` is a monotone function which is extensive
 (every `x`
is less than its closure) and idempotent. -/
-/
structure ClosureOperator [Preorder α] extends α →o α where
  /-- An element is less than or equal its closure -/
  le_closure' : ∀ x, x ≤ toFun x
  /-- Closures are idempotent -/
  idempotent' : ∀ x, toFun (toFun x) = toFun x
  /-- Predicate for an element to be closed.

  By default, this is defined as `c.IsClosed x := (c x = x)` (see `isClosed_iff`).
  We allow an override to fix definitional equalities. -/
  IsClosed (x : α) : Prop := toFun x = x
  isClosed_iff {x : α} : IsClosed x ↔ toFun x = x := by aesop

namespace ClosureOperator

/-
**ClosureOperator.** 是 Mathlib 中的一个实例，位于命名空间 `ClosureOperator`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : FunLike (ClosureOperator α) α α where
  coe c := c.1
  coe_injective := by rintro ⟨⟩ ⟨⟩ h; obtain rfl := DFunLike.ext' h; congr with x; simp_all
/-
**ClosureOperator.** 是 Mathlib 中的一个实例，位于命名空间 `ClosureOperator`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : OrderHomClass (ClosureOperator α) α α where
  map_rel f _ _ h := f.mono h

initialize_simps_projections ClosureOperator (toFun → apply, IsClosed → isClosed)


/-- If `c` is a closure operator on `α` and `e` an order-isomorphism
between `α` and `β` then `e ∘ c ∘ e⁻¹` is a closure operator on `β`. -/
@[simps apply]
/-
**ClosureOperator.conjBy** 是 Mathlib 中的一个定义，位于命名空间 `ClosureOperator`。
形式化陈述：conjBy {α β} [Preorder α] [Preorder β] (c : ClosureOperator α) (e : α ≃o β
) : ClosureOperator β where toFun
参数：c : ClosureOperator α；e : α ≃o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.instOrderHomClass`：∀ (α : Type u_1) [inst : Preorder α],
 OrderHomClass (ClosureOperator α) α α

--- 原说明 ---
If `c` is a closure operator on `α` and `e` an order-isomorphism
between `α` and `β` then `e ∘ c ∘ e⁻¹` is a closure operator on `β`.
-/
def conjBy {α β} [Preorder α] [Preorder β] (c : ClosureOperator α)
    (e : α ≃o β) : ClosureOperator β where
  toFun := e.conj c
  IsClosed b := c.IsClosed (e.symm b)
  monotone' _ _ h :=
    (map_le_map_iff e).mpr <| c.monotone <| (map_le_map_iff e.symm).mpr h
  le_closure' _ := e.symm_apply_le.mp (c.le_closure' _)
  idempotent' _ :=
    congrArg e <| Eq.trans (congrArg c (e.symm_apply_apply _)) (c.idempotent' _)
  isClosed_iff := Iff.trans c.isClosed_iff e.eq_symm_apply
/-
**ClosureOperator.conjBy_refl** 是 Mathlib 中的一个引理，位于命名空间 `ClosureOperator`。
形式化陈述：conjBy_refl {α} [Preorder α] (c : ClosureOperator α) : c.conjBy (OrderIso.
refl α) = c
参数：c : ClosureOperator α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma conjBy_refl {α} [Preorder α] (c : ClosureOperator α) :
    c.conjBy (OrderIso.refl α) = c := rfl
/-
**ClosureOperator.conjBy_trans** 是 Mathlib 中的一个引理，位于命名空间 `ClosureOperator`。
形式化陈述：conjBy_trans {α β γ} [Preorder α] [Preorder β] [Preorder γ] (e₁ : α ≃o β) 
(e₂ : β ≃o γ) (c : ClosureOperator α) : c.conjBy (e₁.trans e₂) = (c.conjBy e₁).c
onjBy e₂
参数：e₁ : α ≃o β；e₂ : β ≃o γ；c : ClosureOperator α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma conjBy_trans {α β γ} [Preorder α] [Preorder β] [Preorder γ]
    (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : ClosureOperator α) :
    c.conjBy (e₁.trans e₂) = (c.conjBy e₁).conjBy e₂ := rfl

section Preorder

variable [Preorder α]

/-- The identity function as a closure operator. -/
@[simps!]
/-
**ClosureOperator.id** 是 Mathlib 中的一个定义，位于命名空间 `ClosureOperator`。
形式化陈述：id : ClosureOperator α where toOrderHom
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
The identity function as a closure operator.
-/
def id : ClosureOperator α where
  toOrderHom := OrderHom.id
  le_closure' _ := le_rfl
  idempotent' _ := rfl
  IsClosed _ := True
/-
**ClosureOperator.** 是 Mathlib 中的一个实例，位于命名空间 `ClosureOperator`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ClosureOperator α) :=
  ⟨id α⟩

variable {α} (c : ClosureOperator α)

@[ext]
/-
**ClosureOperator.ext** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：ext : forall c₁ c₂ : ClosureOperator α, (forall x, c₁ x = c₂ x) -> c₁ = c₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext : ∀ c₁ c₂ : ClosureOperator α, (∀ x, c₁ x = c₂ x) → c₁ = c₂ :=
  DFunLike.ext

@[gcongr, mono]
/-
**ClosureOperator.monotone** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：monotone : Monotone c
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
-/
theorem monotone : Monotone c :=
  c.monotone'

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
/-
**ClosureOperator.le_closure** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：le_closure (x : α) : x <= c x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure'`：∀ {α : Type u_1} [inst : Preorder α] (self 
: ClosureOperator α) (x : α), x ≤ self.toFun x

--- 原说明 ---
Every element is less than its closure. This property is sometimes referred to a
s extensivity or
inflationarity.
-/
theorem le_closure (x : α) : x ≤ c x :=
  c.le_closure' x

@[simp]
/-
**ClosureOperator.idempotent** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：idempotent (x : α) : c (c x) = c x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent'`：∀ {α : Type u_1} [inst : Preorder α] (self 
: ClosureOperator α) (x : α), self.toFun (self.toFun x) = self.toFun x
-/
theorem idempotent (x : α) : c (c x) = c x :=
  c.idempotent' x
/-
**ClosureOperator.isClosed_closure** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] (c : ClosureOperator α) (x : α), c.Is
Closed (c x)
参数：c : ClosureOperator α；x : α；c x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
@[simp] lemma isClosed_closure (x : α) : c.IsClosed (c x) := c.isClosed_iff.2 <| c.idempotent x

/-- The type of elements closed under a closure operator. -/
/-
**ClosureOperator.Closeds** 是 Mathlib 中的一个缩写定义，位于命名空间 `ClosureOperator`。
形式化陈述：Closeds
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of elements closed under a closure operator.
-/
abbrev Closeds := {x // c.IsClosed x}

/-- Send an element to a closed element (by taking the closure). -/
/-
**ClosureOperator.toCloseds** 是 Mathlib 中的一个定义，位于命名空间 `ClosureOperator`。
形式化陈述：toCloseds (x : α) : c.Closeds
参数：x : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)

--- 原说明 ---
Send an element to a closed element (by taking the closure).
-/
def toCloseds (x : α) : c.Closeds := ⟨c x, c.isClosed_closure x⟩

variable {c} {x y : α}
/-
**ClosureOperator.IsClosed.closure_eq** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator
.IsClosed`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {c : ClosureOperator α} {x : α}, c.Is
Closed x → c x = x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
-/
theorem IsClosed.closure_eq : c.IsClosed x → c x = x := c.isClosed_iff.1

/-- The set of closed elements for `c` is exactly its range. -/
/-
**ClosureOperator.setOfPred_isClosed_eq_range_closure** 是 Mathlib 中的一个定理，位于命名空间 
`ClosureOperator`。
形式化陈述：setOfPred_isClosed_eq_range_closure : {x | c.IsClosed x} = Set.range c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `ClosureOperator.IsClosed.closure_eq`：∀ {α : Type u_1} [inst : Preorder α
] {c : ClosureOperator α} {x : α}, c.IsClosed x → c x = x
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)

--- 原说明 ---
The set of closed elements for `c` is exactly its range.
-/
theorem setOfPred_isClosed_eq_range_closure : {x | c.IsClosed x} = Set.range c := by
  ext x; exact ⟨fun hx ↦ ⟨x, hx.closure_eq⟩, by rintro ⟨y, rfl⟩; exact c.isClosed_closure _⟩

@[deprecated (since := "2026-07-09")]
alias setOf_isClosed_eq_range_closure := setOfPred_isClosed_eq_range_closure
/-
**ClosureOperator.le_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：le_closure_iff : x <= c y ↔ c x <= c y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem le_closure_iff : x ≤ c y ↔ c x ≤ c y :=
  ⟨fun h ↦ c.idempotent y ▸ c.monotone h, (c.le_closure x).trans⟩

@[simp]
/-
**ClosureOperator.IsClosed.closure_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOper
ator.IsClosed`。
形式化陈述：∀ {α : Type u_1} [inst : Preorder α] {c : ClosureOperator α} {x y : α}, c.
IsClosed y → (c x ≤ y ↔ x ≤ y)
参数：c x ≤ y ↔ x ≤ y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ClosureOperator.IsClosed.closure_eq`：∀ {α : Type u_1} [inst : Preorder α
] {c : ClosureOperator α} {x : α}, c.IsClosed x → c x = x
· 使用定理 `ClosureOperator.le_closure_iff`：le_closure_iff : x <= c y ↔ c x <= c y
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem IsClosed.closure_le_iff (hy : c.IsClosed y) : c x ≤ y ↔ x ≤ y := by
  rw [← hy.closure_eq, ← le_closure_iff]
/-
**ClosureOperator.closure_min** 是 Mathlib 中的一个引理，位于命名空间 `ClosureOperator`。
形式化陈述：closure_min (hxy : x <= y) (hy : c.IsClosed y) : c x <= y
参数：hxy : x <= y；hy : c.IsClosed y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosureOperator.IsClosed.closure_le_iff`：∀ {α : Type u_1} [inst : Preord
er α] {c : ClosureOperator α} {x y : α}, c.IsClosed y → (c x ≤ y ↔ x ≤ y)
-/
lemma closure_min (hxy : x ≤ y) (hy : c.IsClosed y) : c x ≤ y := hy.closure_le_iff.2 hxy
/-
**ClosureOperator.closure_isGLB** 是 Mathlib 中的一个引理，位于命名空间 `ClosureOperator`。
形式化陈述：closure_isGLB (x : α) : IsGLB { y | x <= y ∧ c.IsClosed y } (c x) where le
ft _
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `and_imp`：∀ {a b c : Prop}, a ∧ b → c ↔ a → b → c
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
-/
lemma closure_isGLB (x : α) : IsGLB { y | x ≤ y ∧ c.IsClosed y } (c x) where
  left _ := and_imp.mpr closure_min
  right _ h := h ⟨c.le_closure x, c.isClosed_closure x⟩

end Preorder

section PartialOrder

variable {α} [PartialOrder α] {c : ClosureOperator α} {x y : α}

/-- Constructor for a closure operator using the weaker idempotency axiom: `f (f x) ≤ f x`. -/
@[simps]
/-
**ClosureOperator.mk'** 是 Mathlib 中的一个定义，位于命名空间 `ClosureOperator`。
形式化陈述：mk' (f : α -> α) (hf₁ : Monotone f) (hf₂ : forall x, x <= f x) (hf₃ : fora
ll x, f (f x) <= f x) : ClosureOperator α where toFun
参数：f : α -> α；hf₁ : Monotone f；hf₂ : forall x, x <= f x；hf₃ : forall x, f (f x) 
<= f x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for a closure operator using the weaker idempotency axiom: `f (f x) 
≤ f x`.
-/
def mk' (f : α → α) (hf₁ : Monotone f) (hf₂ : ∀ x, x ≤ f x) (hf₃ : ∀ x, f (f x) ≤ f x) :
    ClosureOperator α where
  toFun := f
  monotone' := hf₁
  le_closure' := hf₂
  idempotent' x := (hf₃ x).antisymm (hf₁ (hf₂ x))

/-- Convenience constructor for a closure operator using the weaker minimality axiom:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice. -/
@[simps]
/-
**ClosureOperator.mk** 是 Mathlib 中的一个ctor，位于命名空间 `ClosureOperator`。
形式化陈述：{α : Type u_1} →   [inst : Preorder α] →     (toOrderHom : α →o α) →      
 (∀ (x : α), x ≤ toOrderHom.toFun x) →         (∀ (x : α), toOrderHom.toFun (toO
rderHom.toFun x) = toOrderHom.toFun x) →           (IsClosed : α → Prop) →      
       autoParam (∀ {x : α}, IsClosed x ↔ toOrderHom.toFun x = x) ClosureOperato
r.isClosed_iff._autoParam →               ClosureOperator α
参数：toOrderHom : α →o α；∀ (x : α), x ≤ toOrderHom.toFun x；∀ (x : α), toOrderHom.t
oFun (toOrderHom.toFun x) = toOrderHom.toFun x；IsClosed : α → Prop；∀ {x : α}, Is
Closed x ↔ toOrderHom.toFun x = x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Convenience constructor for a closure operator using the weaker minimality axiom
:
`x ≤ f y → f x ≤ f y`, which is sometimes easier to prove in practice.
-/
def mk₂ (f : α → α) (hf : ∀ x, x ≤ f x) (hmin : ∀ ⦃x y⦄, x ≤ f y → f x ≤ f y) :
    ClosureOperator α where
  toFun := f
  monotone' _ y hxy := hmin (hxy.trans (hf y))
  le_closure' := hf
  idempotent' _ := (hmin le_rfl).antisymm (hf _)

/-- Construct a closure operator from an inflationary function `f` and a "closedness" predicate `p`
witnessing minimality of `f x` among closed elements greater than `x`. -/
@[simps!]
/-
**ClosureOperator.ofPred** 是 Mathlib 中的一个定义，位于命名空间 `ClosureOperator`。
形式化陈述：ofPred (f : α -> α) (p : α -> Prop) (hf : forall x, x <= f x) (hfp : foral
l x, p (f x)) (hmin : forall ⦃x y⦄, x <= y -> p y -> f x <= y) : ClosureOperator
 α where __
参数：f : α -> α；p : α -> Prop；hf : forall x, x <= f x；hfp : forall x, p (f x)；hmin
 : forall ⦃x y⦄, x <= y -> p y -> f x <= y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a closure operator from an inflationary function `f` and a "closedness
" predicate `p`
witnessing minimality of `f x` among closed elements greater than `x`.
-/
def ofPred (f : α → α) (p : α → Prop) (hf : ∀ x, x ≤ f x) (hfp : ∀ x, p (f x))
    (hmin : ∀ ⦃x y⦄, x ≤ y → p y → f x ≤ y) : ClosureOperator α where
  __ := mk₂ f hf fun _ y hxy => hmin hxy (hfp y)
  IsClosed := p
  isClosed_iff := ⟨fun hx ↦ (hmin le_rfl hx).antisymm <| hf _, fun hx ↦ hx ▸ hfp _⟩
/-
**ClosureOperator.isClosed_iff_closure_le** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOper
ator`。
形式化陈述：isClosed_iff_closure_le : c.IsClosed x ↔ c x <= x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ClosureOperator.IsClosed.closure_eq`：∀ {α : Type u_1} [inst : Preorder α
] {c : ClosureOperator α} {x : α}, c.IsClosed x → c x = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem isClosed_iff_closure_le : c.IsClosed x ↔ c x ≤ x :=
  ⟨fun h ↦ h.closure_eq.le, fun h ↦ c.isClosed_iff.2 <| h.antisymm <| c.le_closure x⟩
/-
**ClosureOperator.ext_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：ext_isClosed (c₁ c₂ : ClosureOperator α) (h : forall x, c₁.IsClosed x ↔ c₂
.IsClosed x) : c₁ = c₂
参数：c₁ c₂ : ClosureOperator α；h : forall x, c₁.IsClosed x ↔ c₂.IsClosed x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.ext`：ext : forall c₁ c₂ : ClosureOperator α, (forall x, 
c₁ x = c₂ x) -> c₁ = c₂
· 使用定理 `IsGLB.unique`：∀ {α : Type u_1} [inst : PartialOrder α] {s : Set α} {a b 
: α}, IsGLB s a → IsGLB s b → a = b
· 使用引理 `ClosureOperator.closure_isGLB`：closure_isGLB (x : α) : IsGLB { y | x <= 
y ∧ c.IsClosed y } (c x) where left _
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext_isClosed (c₁ c₂ : ClosureOperator α)
    (h : ∀ x, c₁.IsClosed x ↔ c₂.IsClosed x) : c₁ = c₂ :=
  ext c₁ c₂ <| fun x => IsGLB.unique (c₁.closure_isGLB x) <| by simpa [h] using c₂.closure_isGLB x

/-- A closure operator is equal to the closure operator obtained by feeding `c.closed` into the
`ofPred` constructor. -/
/-
**ClosureOperator.eq_ofPred_closed** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：eq_ofPred_closed (c : ClosureOperator α) : c = ofPred c c.IsClosed c.le_cl
osure c.isClosed_closure fun _ _ => closure_min
参数：c : ClosureOperator α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.ext`：ext : forall c₁ c₂ : ClosureOperator α, (forall x, 
c₁ x = c₂ x) -> c₁ = c₂
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
· 使用定理 `ClosureOperator.isClosed_closure`：∀ {α : Type u_1} [inst : Preorder α] (
c : ClosureOperator α) (x : α), c.IsClosed (c x)
· 使用引理 `ClosureOperator.closure_min`：closure_min (hxy : x <= y) (hy : c.IsClosed
 y) : c x <= y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosureOperator.ofPred_apply`：∀ {α : Type u_1} [inst : PartialOrder α] (
f : α → α) (p : α → Prop) (hf : ∀ (x : α), x ≤ f x) (hfp : ∀ (x : α), p (f x))  
 (hmin : ∀ ⦃x y : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A closure operator is equal to the closure operator obtained by feeding `c.close
d` into the
`ofPred` constructor.
-/
theorem eq_ofPred_closed (c : ClosureOperator α) :
    c = ofPred c c.IsClosed c.le_closure c.isClosed_closure fun _ _ ↦ closure_min := by
  ext
  simp

end PartialOrder

variable {α}

section OrderTop

variable [PartialOrder α] [OrderTop α] (c : ClosureOperator α)

@[simp]
/-
**ClosureOperator.closure_top** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：closure_top : c ⊤ = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem closure_top : c ⊤ = ⊤ :=
  le_top.antisymm (c.le_closure _)
/-
**ClosureOperator.isClosed_top** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : OrderTop α] (c : Closur
eOperator α), c.IsClosed ⊤
参数：c : ClosureOperator α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
· 使用定理 `ClosureOperator.closure_top`：closure_top : c ⊤ = ⊤
-/
@[simp] lemma isClosed_top : c.IsClosed ⊤ := c.isClosed_iff.2 c.closure_top

end OrderTop

/-
**ClosureOperator.closure_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：closure_inf_le [SemilatticeInf α] (c : ClosureOperator α) (x y : α) : c (x
 ⊓ y) <= c x ⊓ c y
参数：c : ClosureOperator α；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
theorem closure_inf_le [SemilatticeInf α] (c : ClosureOperator α) (x y : α) :
    c (x ⊓ y) ≤ c x ⊓ c y :=
  c.monotone.map_inf_le _ _

section SemilatticeSup

variable [SemilatticeSup α] (c : ClosureOperator α)

/-
**ClosureOperator.closure_sup_closure_le** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOpera
tor`。
形式化陈述：closure_sup_closure_le (x y : α) : c x ⊔ c y <= c (x ⊔ y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.le_map_sup`：le_map_sup [SemilatticeSup α] [SemilatticeSup β] {f
 : α -> β} (h : Monotone f) (x y : α) : f x ⊔ f y <= f (x ⊔ y)
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
-/
theorem closure_sup_closure_le (x y : α) : c x ⊔ c y ≤ c (x ⊔ y) :=
  c.monotone.le_map_sup _ _
/-
**ClosureOperator.closure_sup_closure_left** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOpe
rator`。
形式化陈述：closure_sup_closure_left (x y : α) : c (c x ⊔ y) = c (x ⊔ y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ClosureOperator.le_closure_iff`：le_closure_iff : x <= c y ↔ c x <= c y
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
-/
theorem closure_sup_closure_left (x y : α) : c (c x ⊔ y) = c (x ⊔ y) :=
  le_antisymm
    (le_closure_iff.1 (sup_le (c.monotone le_sup_left) (le_sup_right.trans (c.le_closure _))))
    (by grw [← c.le_closure x])
/-
**ClosureOperator.closure_sup_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOp
erator`。
形式化陈述：closure_sup_closure_right (x y : α) : c (x ⊔ c y) = c (x ⊔ y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `ClosureOperator.closure_sup_closure_left`：closure_sup_closure_left (x y 
: α) : c (c x ⊔ y) = c (x ⊔ y)
-/
theorem closure_sup_closure_right (x y : α) : c (x ⊔ c y) = c (x ⊔ y) := by
  rw [sup_comm, closure_sup_closure_left, sup_comm (a := x)]
/-
**ClosureOperator.closure_sup_closure** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator
`。
形式化陈述：closure_sup_closure (x y : α) : c (c x ⊔ c y) = c (x ⊔ y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ClosureOperator.closure_sup_closure_left`：closure_sup_closure_left (x y 
: α) : c (c x ⊔ y) = c (x ⊔ y)
· 使用定理 `ClosureOperator.closure_sup_closure_right`：closure_sup_closure_right (x 
y : α) : c (x ⊔ c y) = c (x ⊔ y)
-/
theorem closure_sup_closure (x y : α) : c (c x ⊔ c y) = c (x ⊔ y) := by
  rw [closure_sup_closure_left, closure_sup_closure_right]

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] (c : ClosureOperator α)

/-- Define a closure operator from a predicate that's preserved under infima. -/
@[simps!]
/-
**ClosureOperator.ofCompletePred** 是 Mathlib 中的一个定义，位于命名空间 `ClosureOperator`。
形式化陈述：ofCompletePred (p : α -> Prop) (hsinf : forall s, (forall a in s, p a) -> 
p (sInf s)) : ClosureOperator α
参数：p : α -> Prop；hsinf : forall s, (forall a in s, p a) -> p (sInf s)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define a closure operator from a predicate that's preserved under infima.
-/
def ofCompletePred (p : α → Prop) (hsinf : ∀ s, (∀ a ∈ s, p a) → p (sInf s)) : ClosureOperator α :=
  ofPred (fun a ↦ ⨅ b : {b // a ≤ b ∧ p b}, b) p
    (fun a ↦ by simp +contextual)
    (fun _ ↦ hsinf _ <| forall_mem_range.2 fun b ↦ b.2.2)
    (fun _ b hab hb ↦ iInf_le_of_le ⟨b, hab, hb⟩ le_rfl)
/-
**ClosureOperator.sInf_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
形式化陈述：sInf_isClosed {c : ClosureOperator α} {S : Set α} (H : forall x in S, c.Is
Closed x) : c.IsClosed (sInf S)
参数：H : forall x in S, c.IsClosed x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ClosureOperator.isClosed_iff_closure_le`：isClosed_iff_closure_le : c.IsC
losed x ↔ c x <= x
· 使用定理 `le_of_le_of_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Monotone.map_sInf_le`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLa
ttice α] [inst_1 : CompleteLattice β] {s : Set α} {f : α → β},   Monotone f → f 
(sInf s) ≤…
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `biInf_congr`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f g : ι 
→ α} {p : ι → Prop},   (∀ (i : ι), p i → f i = g i) → ⨅ i, ⨅ (_ : p i), f i = ⨅ 
i…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ClosureOperator.isClosed_iff`：∀ {α : Type u_1} [inst : Preorder α] (self
 : ClosureOperator α) {x : α}, self.IsClosed x ↔ self.toFun x = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_eq_iInf`：∀ {α : Type u_1} [inst : CompleteLattice α] {s : Set α}, s
Inf s = ⨅ a ∈ s, a
-/
theorem sInf_isClosed {c : ClosureOperator α} {S : Set α}
    (H : ∀ x ∈ S, c.IsClosed x) : c.IsClosed (sInf S) :=
  isClosed_iff_closure_le.mpr <| le_of_le_of_eq c.monotone.map_sInf_le <|
    Eq.trans (biInf_congr (c.isClosed_iff.mp <| H · ·)) sInf_eq_iInf.symm

@[simp]
/-
**ClosureOperator.closure_iSup_closure** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperato
r`。
形式化陈述：closure_iSup_closure (f : ι -> α) : c (⨆ i, c (f i)) = c (⨆ i, f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `ClosureOperator.le_closure_iff`：le_closure_iff : x <= c y ↔ c x <= c y
· 使用定理 `iSup_le`：iSup_le (h : forall i, f i <= a) : iSup f <= a
· 使用定理 `ClosureOperator.monotone`：monotone : Monotone c
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `iSup_mono`：iSup_mono (h : forall i, f i <= g i) : iSup f <= iSup g
· 使用定理 `ClosureOperator.le_closure`：le_closure (x : α) : x <= c x
-/
theorem closure_iSup_closure (f : ι → α) : c (⨆ i, c (f i)) = c (⨆ i, f i) :=
  le_antisymm (le_closure_iff.1 <| iSup_le fun i => c.monotone <| le_iSup f i) <|
    c.monotone <| iSup_mono fun _ => c.le_closure _

@[simp]
/-
**ClosureOperator.closure_iSup** 是 Mathlib 中的一个定理，位于命名空间 `ClosureOperator`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem closure_iSup₂_closure (f : ∀ i, κ i → α) :
    c (⨆ (i) (j), c (f i j)) = c (⨆ (i) (j), f i j) :=
  le_antisymm (le_closure_iff.1 <| iSup₂_le fun i j => c.monotone <| le_iSup₂ i j) <|
    c.monotone <| iSup₂_mono fun _ _ => c.le_closure _

end CompleteLattice

end ClosureOperator

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Conjugating `ClosureOperators` on `α` and on `β` by a fixed isomorphism
`e : α ≃o β` gives an equivalence `ClosureOperator α ≃ ClosureOperator β`. -/
@[simps apply symm_apply]
/-
**OrderIso.equivClosureOperator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIso.equivClosureOperator {α β} [Preorder α] [Preorder β] (e : α ≃o β)
 : ClosureOperator α ≃ ClosureOperator β where toFun c
参数：e : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Conjugating `ClosureOperators` on `α` and on `β` by a fixed isomorphism
`e : α ≃o β` gives an equivalence `ClosureOperator α ≃ ClosureOperator β`.
-/
def OrderIso.equivClosureOperator {α β} [Preorder α] [Preorder β] (e : α ≃o β) :
    ClosureOperator α ≃ ClosureOperator β where
  toFun     c := c.conjBy e
  invFun    c := c.conjBy e.symm
  left_inv  c := Eq.trans (c.conjBy_trans _ _).symm
                 <| Eq.trans (congrArg _ e.self_trans_symm) c.conjBy_refl
  right_inv c := Eq.trans (c.conjBy_trans _ _).symm
                 <| Eq.trans (congrArg _ e.symm_trans_self) c.conjBy_refl

/-! ### Lower adjoint -/


variable {α} {β : Type*}

/-- A lower adjoint of `u` on the preorder `α` is a function `l` such that `l` and `u` form a Galois
connection. It allows us to define closure operators whose output does not match the input. In
practice, `u` is often `(↑) : β → α`. -/
/-
**LowerAdjoint** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_1} → {β : Type u_4} → [Preorder α] → [Preorder β] → (β → α) → 
Type (max u_1 u_4)
参数：β → α；max u_1 u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lower adjoint of `u` on the preorder `α` is a function `l` such that `l` and `
u` form a Galois
connection. It allows us to define closure operators whose output does not match
 the input. In
practice, `u` is often `(↑) : β → α`.
-/
structure LowerAdjoint [Preorder α] [Preorder β] (u : β → α) where
  /-- The underlying function -/
  toFun : α → β
  /-- The underlying function is a lower adjoint. -/
  gc' : GaloisConnection toFun u

namespace LowerAdjoint

variable (α)

/-- The identity function as a lower adjoint to itself. -/
@[simps]
/-
**LowerAdjoint.id** 是 Mathlib 中的一个定义，位于命名空间 `LowerAdjoint`。
形式化陈述：(α : Type u_1) → [inst : Preorder α] → LowerAdjoint id
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.id`：∀ {α : Type u} [pα : Preorder α], GaloisConnection 
id id

--- 原说明 ---
The identity function as a lower adjoint to itself.
-/
protected def id [Preorder α] : LowerAdjoint (id : α → α) where
  toFun x := x
  gc' := GaloisConnection.id

variable {α}
/-
**LowerAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `LowerAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Preorder α] : Inhabited (LowerAdjoint (id : α → α)) :=
  ⟨LowerAdjoint.id α⟩

section Preorder

variable [Preorder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-
**LowerAdjoint.** 是 Mathlib 中的一个实例，位于命名空间 `LowerAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (LowerAdjoint u) fun _ => α → β where coe := toFun
/-
**LowerAdjoint.gc** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：gc : GaloisConnection l u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.gc'`：∀ {α : Type u_1} {β : Type u_4} [inst : Preorder α] [i
nst_1 : Preorder β] {u : β → α} (self : LowerAdjoint u),   GaloisConnection self
.toFun…
-/
theorem gc : GaloisConnection l u :=
  l.gc'

@[ext]
/-
**LowerAdjoint.ext** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：∀ {α : Type u_1} {β : Type u_4} [inst : Preorder α] [inst_1 : Preorder β] 
{u : β → α} (l₁ l₂ : LowerAdjoint u),   l₁.toFun = l₂.toFun → l₁ = l₂
参数：l₁ l₂ : LowerAdjoint u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ext : ∀ l₁ l₂ : LowerAdjoint u, (l₁ : α → β) = (l₂ : α → β) → l₁ = l₂
  | ⟨l₁, _⟩, ⟨l₂, _⟩, h => by
    congr

@[gcongr, mono]
/-
**LowerAdjoint.monotone** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：monotone : Monotone (u ∘ l)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `GaloisConnection.monotone_u`：monotone_u : Monotone u
· 使用定理 `LowerAdjoint.gc`：gc : GaloisConnection l u
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
-/
theorem monotone : Monotone (u ∘ l) :=
  l.gc.monotone_u.comp l.gc.monotone_l

/-- Every element is less than its closure. This property is sometimes referred to as extensivity or
inflationarity. -/
/-
**LowerAdjoint.le_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：le_closure (x : α) : x <= u (l x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.le_u_l`：le_u_l (a) : a <= u (l a)
· 使用定理 `LowerAdjoint.gc`：gc : GaloisConnection l u

--- 原说明 ---
Every element is less than its closure. This property is sometimes referred to a
s extensivity or
inflationarity.
-/
theorem le_closure (x : α) : x ≤ u (l x) :=
  l.gc.le_u_l _

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-- Every lower adjoint induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps]
/-
**LowerAdjoint.closureOperator** 是 Mathlib 中的一个定义，位于命名空间 `LowerAdjoint`。
形式化陈述：closureOperator : ClosureOperator α where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every lower adjoint induces a closure operator given by the composition. This is
 the partial
order version of the statement that every adjunction induces a monad.
-/
def closureOperator : ClosureOperator α where
  toFun x := u (l x)
  monotone' := l.monotone
  le_closure' := l.le_closure
  idempotent' x := l.gc.u_l_u_eq_u (l x)
/-
**LowerAdjoint.idempotent** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：idempotent (x : α) : u (l (u (l x))) = u (l x)
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.idempotent`：idempotent (x : α) : c (c x) = c x
-/
theorem idempotent (x : α) : u (l (u (l x))) = u (l x) :=
  l.closureOperator.idempotent _
/-
**LowerAdjoint.le_closure_iff** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：le_closure_iff (x y : α) : x <= u (l y) ↔ u (l x) <= u (l y)
参数：x y : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.le_closure_iff`：le_closure_iff : x <= c y ↔ c x <= c y
-/
theorem le_closure_iff (x y : α) : x ≤ u (l y) ↔ u (l x) ≤ u (l y) :=
  l.closureOperator.le_closure_iff

end PartialOrder

section Preorder

variable [Preorder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-- An element `x` is closed for `l : LowerAdjoint u` if it is a fixed point: `u (l x) = x` -/
/-
**LowerAdjoint.closed** 是 Mathlib 中的一个定义，位于命名空间 `LowerAdjoint`。
形式化陈述：closed : Set α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `x` is closed for `l : LowerAdjoint u` if it is a fixed point: `u (l 
x) = x`
-/
def closed : Set α := {x | u (l x) = x}
/-
**LowerAdjoint.mem_closed_iff** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：mem_closed_iff (x : α) : x in l.closed ↔ u (l x) = x
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_closed_iff (x : α) : x ∈ l.closed ↔ u (l x) = x :=
  Iff.rfl
/-
**LowerAdjoint.closure_eq_self_of_mem_closed** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdj
oint`。
形式化陈述：closure_eq_self_of_mem_closed {x : α} (h : x in l.closed) : u (l x) = x
参数：h : x in l.closed。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem closure_eq_self_of_mem_closed {x : α} (h : x ∈ l.closed) : u (l x) = x :=
  h

end Preorder

section PartialOrder

variable [PartialOrder α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-
**LowerAdjoint.mem_closed_iff_closure_le** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint
`。
形式化陈述：mem_closed_iff_closure_le (x : α) : x in l.closed ↔ u (l x) <= x
参数：x : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.isClosed_iff_closure_le`：isClosed_iff_closure_le : c.IsC
losed x ↔ c x <= x
-/
theorem mem_closed_iff_closure_le (x : α) : x ∈ l.closed ↔ u (l x) ≤ x :=
  l.closureOperator.isClosed_iff_closure_le

@[simp]
/-
**LowerAdjoint.closure_is_closed** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_is_closed (x : α) : u (l x) in l.closed
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.idempotent`：idempotent (x : α) : u (l (u (l x))) = u (l x)
-/
theorem closure_is_closed (x : α) : u (l x) ∈ l.closed :=
  l.idempotent x

/-- The set of closed elements for `l` is the range of `u ∘ l`. -/
/-
**LowerAdjoint.closed_eq_range_close** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closed_eq_range_close : l.closed = Set.range (u ∘ l)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.setOfPred_isClosed_eq_range_closure`：setOfPred_isClosed_
eq_range_closure : {x | c.IsClosed x} = Set.range c

--- 原说明 ---
The set of closed elements for `l` is the range of `u ∘ l`.
-/
theorem closed_eq_range_close : l.closed = Set.range (u ∘ l) :=
  l.closureOperator.setOfPred_isClosed_eq_range_closure

/-- Send an `x` to an element of the set of closed elements (by taking the closure). -/
/-
**LowerAdjoint.toClosed** 是 Mathlib 中的一个定义，位于命名空间 `LowerAdjoint`。
形式化陈述：toClosed (x : α) : l.closed
参数：x : α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.closure_is_closed`：closure_is_closed (x : α) : u (l x) in l
.closed

--- 原说明 ---
Send an `x` to an element of the set of closed elements (by taking the closure).
-/
def toClosed (x : α) : l.closed :=
  ⟨u (l x), l.closure_is_closed x⟩

@[simp]
/-
**LowerAdjoint.closure_le_closed_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`
。
形式化陈述：closure_le_closed_iff_le (x : α) {y : α} (hy : y in l.closed) : u (l x) <=
 y ↔ x <= y
参数：x : α；hy : y in l.closed。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.IsClosed.closure_le_iff`：∀ {α : Type u_1} [inst : Preord
er α] {c : ClosureOperator α} {x y : α}, c.IsClosed y → (c x ≤ y ↔ x ≤ y)
-/
theorem closure_le_closed_iff_le (x : α) {y : α} (hy : y ∈ l.closed) : u (l x) ≤ y ↔ x ≤ y :=
  (show l.closureOperator.IsClosed y from hy).closure_le_iff

end PartialOrder

/-
**LowerAdjoint.closure_top** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_top [PartialOrder α] [OrderTop α] [Preorder β] {u : β -> α} (l : L
owerAdjoint u) : u (l ⊤) = ⊤
参数：l : LowerAdjoint u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_top`：closure_top : c ⊤ = ⊤
-/
theorem closure_top [PartialOrder α] [OrderTop α] [Preorder β] {u : β → α} (l : LowerAdjoint u) :
    u (l ⊤) = ⊤ :=
  l.closureOperator.closure_top
/-
**LowerAdjoint.closure_inf_le** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_inf_le [SemilatticeInf α] [Preorder β] {u : β -> α} (l : LowerAdjo
int u) (x y : α) : u (l (x ⊓ y)) <= u (l x) ⊓ u (l y)
参数：l : LowerAdjoint u；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_inf_le`：closure_inf_le [SemilatticeInf α] (c : C
losureOperator α) (x y : α) : c (x ⊓ y) <= c x ⊓ c y
-/
theorem closure_inf_le [SemilatticeInf α] [Preorder β] {u : β → α} (l : LowerAdjoint u) (x y : α) :
    u (l (x ⊓ y)) ≤ u (l x) ⊓ u (l y) :=
  l.closureOperator.closure_inf_le x y

section SemilatticeSup

variable [SemilatticeSup α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-
**LowerAdjoint.closure_sup_closure_le** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_sup_closure_le (x y : α) : u (l x) ⊔ u (l y) <= u (l (x ⊔ y))
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_le`：closure_sup_closure_le (x y : α)
 : c x ⊔ c y <= c (x ⊔ y)
-/
theorem closure_sup_closure_le (x y : α) : u (l x) ⊔ u (l y) ≤ u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_le x y
/-
**LowerAdjoint.closure_sup_closure_left** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`
。
形式化陈述：closure_sup_closure_left (x y : α) : u (l (u (l x) ⊔ y)) = u (l (x ⊔ y))
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_left`：closure_sup_closure_left (x y 
: α) : c (c x ⊔ y) = c (x ⊔ y)
-/
theorem closure_sup_closure_left (x y : α) : u (l (u (l x) ⊔ y)) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_left x y
/-
**LowerAdjoint.closure_sup_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint
`。
形式化陈述：closure_sup_closure_right (x y : α) : u (l (x ⊔ u (l y))) = u (l (x ⊔ y))
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure_right`：closure_sup_closure_right (x 
y : α) : c (x ⊔ c y) = c (x ⊔ y)
-/
theorem closure_sup_closure_right (x y : α) : u (l (x ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure_right x y
/-
**LowerAdjoint.closure_sup_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_sup_closure (x y : α) : u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y))
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_sup_closure`：closure_sup_closure (x y : α) : c (
c x ⊔ c y) = c (x ⊔ y)
-/
theorem closure_sup_closure (x y : α) : u (l (u (l x) ⊔ u (l y))) = u (l (x ⊔ y)) :=
  l.closureOperator.closure_sup_closure x y

end SemilatticeSup

section CompleteLattice

variable [CompleteLattice α] [Preorder β] {u : β → α} (l : LowerAdjoint u)

/-
**LowerAdjoint.closure_iSup_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_iSup_closure (f : ι -> α) : u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, 
f i))
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.closure_iSup_closure`：closure_iSup_closure (f : ι -> α) 
: c (⨆ i, c (f i)) = c (⨆ i, f i)
-/
theorem closure_iSup_closure (f : ι → α) : u (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i)) :=
  l.closureOperator.closure_iSup_closure _
/-
**LowerAdjoint.closure_iSup** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem closure_iSup₂_closure (f : ∀ i, κ i → α) :
    u (l <| ⨆ (i) (j), u (l <| f i j)) = u (l <| ⨆ (i) (j), f i j) :=
  l.closureOperator.closure_iSup₂_closure _

end CompleteLattice

-- Lemmas for `LowerAdjoint ((↑) : α → Set β)`, where `SetLike α β`
section CoeToSet

variable [SetLike α β]

section Preorder

variable [Preorder α] (l : LowerAdjoint ((↑) : α → Set β))

/-
**LowerAdjoint.subset_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：subset_closure (s : Set β) : s subseteq l s
参数：s : Set β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.le_closure`：le_closure (x : α) : x <= u (l x)
-/
theorem subset_closure (s : Set β) : s ⊆ l s :=
  l.le_closure s
/-
**LowerAdjoint.notMem_of_notMem_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`
。
形式化陈述：notMem_of_notMem_closure {s : Set β} {P : β} (hP : P ∉ l s) : P ∉ s
参数：hP : P ∉ l s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.subset_closure`：subset_closure (s : Set β) : s subseteq l s
-/
theorem notMem_of_notMem_closure {s : Set β} {P : β} (hP : P ∉ l s) : P ∉ s := fun h =>
  hP (subset_closure _ s h)
/-
**LowerAdjoint.le_iff_subset** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：le_iff_subset (s : Set β) (S : α) : l s <= S ↔ s subseteq S
参数：s : Set β；S : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.gc`：gc : GaloisConnection l u
-/
theorem le_iff_subset (s : Set β) (S : α) : l s ≤ S ↔ s ⊆ S :=
  l.gc s S
/-
**LowerAdjoint.mem_iff** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：mem_iff (s : Set β) (x : β) : x in l s ↔ forall S : α, s subseteq S -> x i
n S
参数：s : Set β；x : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LowerAdjoint.le_iff_subset`：le_iff_subset (s : Set β) (S : α) : l s <= S
 ↔ s subseteq S
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem mem_iff (s : Set β) (x : β) : x ∈ l s ↔ ∀ S : α, s ⊆ S → x ∈ S := by
  simp_rw [← SetLike.mem_coe, ← Set.singleton_subset_iff, ← l.le_iff_subset]
  exact ⟨fun h S => h.trans, fun h => h _ le_rfl⟩
/-
**LowerAdjoint.closure_union_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjo
int`。
形式化陈述：closure_union_closure_subset (x y : α) : (l x : Set β) union l y subseteq 
l (x union y)
参数：x y : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LowerAdjoint.closure_sup_closure_le`：closure_sup_closure_le (x y : α) : 
u (l x) ⊔ u (l y) <= u (l (x ⊔ y))
-/
theorem closure_union_closure_subset (x y : α) : (l x : Set β) ∪ l y ⊆ l (x ∪ y) :=
  l.closure_sup_closure_le x y

@[simp]
/-
**LowerAdjoint.closure_union_closure_left** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoin
t`。
形式化陈述：closure_union_closure_left (x y : α) : l (l x union y) = l (x union y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `LowerAdjoint.closure_sup_closure_left`：closure_sup_closure_left (x y : α
) : u (l (u (l x) ⊔ y)) = u (l (x ⊔ y))
-/
theorem closure_union_closure_left (x y : α) : l (l x ∪ y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_left x y)

@[simp]
/-
**LowerAdjoint.closure_union_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoi
nt`。
形式化陈述：closure_union_closure_right (x y : α) : l (x union l y) = l (x union y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `LowerAdjoint.closure_sup_closure_right`：closure_sup_closure_right (x y :
 α) : u (l (x ⊔ u (l y))) = u (l (x ⊔ y))
-/
theorem closure_union_closure_right (x y : α) : l (x ∪ l y) = l (x ∪ y) :=
  SetLike.coe_injective (l.closure_sup_closure_right x y)
/-
**LowerAdjoint.closure_union_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_union_closure (x y : α) : l (l x union l y) = l (x union y)
参数：x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LowerAdjoint.closure_union_closure_right`：closure_union_closure_right (x
 y : α) : l (x union l y) = l (x union y)
· 使用定理 `LowerAdjoint.closure_union_closure_left`：closure_union_closure_left (x y
 : α) : l (l x union y) = l (x union y)
-/
theorem closure_union_closure (x y : α) : l (l x ∪ l y) = l (x ∪ y) := by
  rw [closure_union_closure_right, closure_union_closure_left]

@[simp]
/-
**LowerAdjoint.closure_iUnion_closure** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：closure_iUnion_closure (f : ι -> α) : l (⋃ i, l (f i)) = l (⋃ i, f i)
参数：f : ι -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `LowerAdjoint.closure_iSup_closure`：closure_iSup_closure (f : ι -> α) : u
 (l (⨆ i, u (l (f i)))) = u (l (⨆ i, f i))
-/
theorem closure_iUnion_closure (f : ι → α) : l (⋃ i, l (f i)) = l (⋃ i, f i) :=
  SetLike.coe_injective <| l.closure_iSup_closure _

@[simp]
/-
**LowerAdjoint.closure_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem closure_iUnion₂_closure (f : ∀ i, κ i → α) :
    l (⋃ (i) (j), l (f i j)) = l (⋃ (i) (j), f i j) :=
  SetLike.coe_injective <| l.closure_iSup₂_closure _

end Preorder

section PartialOrder

variable [PartialOrder α] (l : LowerAdjoint ((↑) : α → Set β))

/-
**LowerAdjoint.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LowerAdjoint`。
形式化陈述：eq_of_le {s : Set β} {S : α} (h₁ : s subseteq S) (h₂ : S <= l s) : l s = S
参数：h₁ : s subseteq S；h₂ : S <= l s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LowerAdjoint.le_iff_subset`：le_iff_subset (s : Set β) (S : α) : l s <= S
 ↔ s subseteq S
-/
theorem eq_of_le {s : Set β} {S : α} (h₁ : s ⊆ S) (h₂ : S ≤ l s) : l s = S :=
  ((l.le_iff_subset _ _).2 h₁).antisymm h₂

end PartialOrder

end CoeToSet

end LowerAdjoint

/-! ### Translations between `GaloisConnection`, `LowerAdjoint`, `ClosureOperator` -/

/-- Every Galois connection induces a lower adjoint. -/
@[simps]
/-
**GaloisConnection.lowerAdjoint** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GaloisConnection.lowerAdjoint [Preorder α] [Preorder β] {l : α -> β} {u : 
β -> α} (gc : GaloisConnection l u) : LowerAdjoint u where toFun
参数：gc : GaloisConnection l u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Galois connection induces a lower adjoint.
-/
def GaloisConnection.lowerAdjoint [Preorder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : LowerAdjoint u where
  toFun := l
  gc' := gc

/-- Every Galois connection induces a closure operator given by the composition. This is the partial
order version of the statement that every adjunction induces a monad. -/
@[simps!]
/-
**GaloisConnection.closureOperator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GaloisConnection.closureOperator [PartialOrder α] [Preorder β] {l : α -> β
} {u : β -> α} (gc : GaloisConnection l u) : ClosureOperator α
参数：gc : GaloisConnection l u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Galois connection induces a closure operator given by the composition. Thi
s is the partial
order version of the statement that every adjunction induces a monad.
-/
def GaloisConnection.closureOperator [PartialOrder α] [Preorder β] {l : α → β} {u : β → α}
    (gc : GaloisConnection l u) : ClosureOperator α :=
  gc.lowerAdjoint.closureOperator

/-- The set of closed elements has a Galois insertion to the underlying type. -/
/-
**ClosureOperator.gi** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ClosureOperator.gi [PartialOrder α] (c : ClosureOperator α) : GaloisInsert
ion c.toCloseds (↑) where choice x hx
参数：c : ClosureOperator α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The set of closed elements has a Galois insertion to the underlying type.
-/
def ClosureOperator.gi [PartialOrder α] (c : ClosureOperator α) :
    GaloisInsertion c.toCloseds (↑) where
  choice x hx := ⟨x, isClosed_iff_closure_le.2 hx⟩
  gc _ y := y.2.closure_le_iff
  le_l_u _ := c.le_closure _
  choice_eq x hx := le_antisymm (c.le_closure x) hx

/-- The Galois insertion associated to a closure operator can be used to reconstruct the closure
operator.
Note that the inverse in the opposite direction does not hold in general. -/
@[simp]
/-
**closureOperator_gi_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：closureOperator_gi_self [PartialOrder α] (c : ClosureOperator α) : c.gi.gc
.closureOperator = c
参数：c : ClosureOperator α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ClosureOperator.ext`：ext : forall c₁ c₂ : ClosureOperator α, (forall x, 
c₁ x = c₂ x) -> c₁ = c₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The Galois insertion associated to a closure operator can be used to reconstruct
 the closure
operator.
Note that the inverse in the opposite direction does not hold in general.
-/
theorem closureOperator_gi_self [PartialOrder α] (c : ClosureOperator α) :
    c.gi.gc.closureOperator = c := by
  ext x
  rfl
