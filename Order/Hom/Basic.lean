/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.Disjoint
public import Mathlib.Order.RelIso.Basic
public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.PPWithUniv

/-!
# Order homomorphisms

This file defines order homomorphisms, which are bundled monotone functions. A preorder
homomorphism `f : α →o β` is a function `α → β` along with a proof that `∀ x y, x ≤ y → f x ≤ f y`.

## Main definitions

In this file we define the following bundled monotone maps:
* `OrderHom α β` a.k.a. `α →o β`: Preorder homomorphism.
  An `OrderHom α β` is a function `f : α → β` such that `a₁ ≤ a₂ → f a₁ ≤ f a₂`
* `OrderEmbedding α β` a.k.a. `α ↪o β`: Relation embedding.
  An `OrderEmbedding α β` is an embedding `f : α ↪ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelEmbedding α β (≤) (≤)`.
* `OrderIso`: Relation isomorphism.
  An `OrderIso α β` is an equivalence `f : α ≃ β` such that `a ≤ b ↔ f a ≤ f b`.
  Defined as an abbreviation of `@RelIso α β (≤) (≤)`.

We also define many `OrderHom`s. In some cases we define two versions, one with `ₘ` suffix and
one without it (e.g., `OrderHom.compₘ` and `OrderHom.comp`). This means that the former
function is a "more bundled" version of the latter. We can't just drop the "less bundled" version
because the more bundled version usually does not work with dot notation.

* `OrderHom.id`: identity map as `α →o α`;
* `OrderHom.curry`: an order isomorphism between `α × β →o γ` and `α →o β →o γ`;
* `OrderHom.comp`: composition of two bundled monotone maps;
* `OrderHom.compₘ`: composition of bundled monotone maps as a bundled monotone map;
* `OrderHom.const`: constant function as a bundled monotone map;
* `OrderHom.prod`: combine `α →o β` and `α →o γ` into `α →o β × γ`;
* `OrderHom.prodₘ`: a more bundled version of `OrderHom.prod`;
* `OrderHom.prodIso`: order isomorphism between `α →o β × γ` and `(α →o β) × (α →o γ)`;
* `OrderHom.diag`: diagonal embedding of `α` into `α × α` as a bundled monotone map;
* `OrderHom.onDiag`: restrict a monotone map `α →o α →o β` to the diagonal;
* `OrderHom.fst`: projection `Prod.fst : α × β → α` as a bundled monotone map;
* `OrderHom.snd`: projection `Prod.snd : α × β → β` as a bundled monotone map;
* `OrderHom.prodMap`: `Prod.map f g` as a bundled monotone map;
* `Pi.evalOrderHom`: evaluation of a function at a point `Function.eval i` as a bundled
  monotone map;
* `OrderHom.coeFnHom`: coercion to function as a bundled monotone map;
* `OrderHom.apply`: application of an `OrderHom` at a point as a bundled monotone map;
* `OrderHom.pi`: combine a family of monotone maps `f i : α →o π i` into a monotone map
  `α →o Π i, π i`;
* `OrderHom.piIso`: order isomorphism between `α →o Π i, π i` and `Π i, α →o π i`;
* `OrderHom.subtype.val`: embedding `Subtype.val : Subtype p → α` as a bundled monotone map;
* `OrderHom.dual`: reinterpret a monotone map `α →o β` as a monotone map `αᵒᵈ →o βᵒᵈ`;
* `OrderHom.dualIso`: order isomorphism between `α →o β` and `(αᵒᵈ →o βᵒᵈ)ᵒᵈ`;
* `OrderHom.compl`: order isomorphism `α ≃o αᵒᵈ` given by taking complements in a
  Boolean algebra;

We also define two functions to convert other bundled maps to `α →o β`:

* `OrderEmbedding.toOrderHom`: convert `α ↪o β` to `α →o β`;
* `RelHom.toOrderHom`: convert a `RelHom` between strict orders to an `OrderHom`.

## Tags

monotone map, bundled morphism
-/

@[expose] public section

-- Developments relating order homs and sets belong in `Order.Hom.Set` or later.
assert_not_imported Mathlib.Data.Set.Basic

open OrderDual

variable {F α β γ δ : Type*}

/-- Bundled monotone (aka, increasing) function -/
/-
**OrderHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_6) → (β : Type u_7) → [Preorder α] → [Preorder β] → Type (max 
u_6 u_7)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled monotone (aka, increasing) function
-/
structure OrderHom (α β : Type*) [Preorder α] [Preorder β] where
  /-- The underlying function of an `OrderHom`. -/
  toFun : α → β
  /-- The underlying function of an `OrderHom` is monotone. -/
  monotone' : Monotone toFun

/-- Notation for an `OrderHom`. -/
infixr:25 " →o " => OrderHom

/-- An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelEmbedding (≤) (≤)`. -/
/-
**OrderEmbedding** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：OrderEmbedding (α β : Type*) [LE α] [LE β]
参数：α β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order embedding is an embedding `f : α ↪ β` such that `a ≤ b ↔ (f a) ≤ (f b)`
.
This definition is an abbreviation of `RelEmbedding (≤) (≤)`.
-/
abbrev OrderEmbedding (α β : Type*) [LE α] [LE β] :=
  @RelEmbedding α β (· ≤ ·) (· ≤ ·)

to_dual_insert_cast_fun OrderEmbedding :=
  fun i ↦ ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i ↦ ⟨i.1, by rw [forall_comm]; exact @i.2⟩

/-- Notation for an `OrderEmbedding`. -/
infixl:25 " ↪o " => OrderEmbedding

/-- An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelIso (≤) (≤)`. -/
/-
**OrderIso** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：OrderIso (α β : Type*) [LE α] [LE β]
参数：α β : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism is an equivalence such that `a ≤ b ↔ (f a) ≤ (f b)`.
This definition is an abbreviation of `RelIso (≤) (≤)`.
-/
abbrev OrderIso (α β : Type*) [LE α] [LE β] :=
  @RelIso α β (· ≤ ·) (· ≤ ·)

to_dual_insert_cast_fun OrderIso :=
  fun i ↦ ⟨i.1, by rw [forall_comm]; exact @i.2⟩,
  fun i ↦ ⟨i.1, by rw [forall_comm]; exact @i.2⟩

/-- Notation for an `OrderIso`. -/
infixl:25 " ≃o " => OrderIso

-- These instances are here just to make `to_dual` work correctly
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α β : Type*) [LE α] [LE β] : FunLike (α ↪o β) α β := RelEmbedding.instFunLike
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (α β : Type*) [LE α] [LE β] : FunLike (α ≃o β) α β := RelIso.instFunLike

section

/-- `OrderHomClass F α b` asserts that `F` is a type of `≤`-preserving morphisms. -/
/-
**OrderHomClass** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F 
α β]
参数：F : Type*；α β : outParam Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderHomClass F α b` asserts that `F` is a type of `≤`-preserving morphisms.
-/
abbrev OrderHomClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [FunLike F α β] :=
  RelHomClass F ((· ≤ ·) : α → α → Prop) ((· ≤ ·) : β → β → Prop)

to_dual_insert_cast OrderHomClass := by grind only [RelHomClass]

/-- `OrderIsoClass F α β` states that `F` is a type of order isomorphisms.

You should extend this class when you extend `OrderIso`. -/
/-
**OrderIsoClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_6) → (α : outParam (Type u_7)) → (β : outParam (Type u_8)) → [
LE α] → [LE β] → [EquivLike F α β] → Prop
参数：Type u_7；Type u_8。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`OrderIsoClass F α β` states that `F` is a type of order isomorphisms.

You should extend this class when you extend `OrderIso`.
-/
class OrderIsoClass (F : Type*) (α β : outParam Type*) [LE α] [LE β] [EquivLike F α β] :
    Prop where
  /-- An order isomorphism respects `≤`. -/
  map_le_map_iff (f : F) {a b : α} : f a ≤ f b ↔ a ≤ b

attribute [to_dual self] OrderIsoClass.map_le_map_iff

end

export OrderIsoClass (map_le_map_iff)

attribute [simp] map_le_map_iff

/-- Turn an element of a type `F` satisfying `OrderIsoClass F α β` into an actual
`OrderIso`. This is declared as the default coercion from `F` to `α ≃o β`. -/
@[coe]
/-
**OrderIsoClass.toOrderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：OrderIsoClass.toOrderIso [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F 
α β] (f : F) : α ≃o β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…

--- 原说明 ---
Turn an element of a type `F` satisfying `OrderIsoClass F α β` into an actual
`OrderIso`. This is declared as the default coercion from `F` to `α ≃o β`.
-/
def OrderIsoClass.toOrderIso [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] (f : F) :
    α ≃o β :=
  { EquivLike.toEquiv f with map_rel_iff' := map_le_map_iff f }

/-- Any type satisfying `OrderIsoClass` can be cast into `OrderIso` via
`OrderIsoClass.toOrderIso`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `OrderIsoClass` can be cast into `OrderIso` via
`OrderIsoClass.toOrderIso`.
-/
instance [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β] : CoeTC F (α ≃o β) :=
  ⟨OrderIsoClass.toOrderIso⟩

-- See note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) OrderIsoClass.toOrderHomClass [LE α] [LE β]
    [EquivLike F α β] [OrderIsoClass F α β] : OrderHomClass F α β :=
  { EquivLike.toEmbeddingLike (E := F) with
    map_rel := fun f _ _ => (map_le_map_iff f).2 }

namespace OrderHomClass

variable [Preorder α] [Preorder β] [FunLike F α β] [OrderHomClass F α β]

/-
**OrderHomClass.monotone** 是 Mathlib 中的一个定理，位于命名空间 `OrderHomClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F α β] (f : F), Monoton
e ⇑f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
protected theorem monotone (f : F) : Monotone f := fun _ _ => map_rel f

@[gcongr]
/-
**OrderHomClass.mono** 是 Mathlib 中的一个定理，位于命名空间 `OrderHomClass`。
形式化陈述：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1
 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomClass F α β] (f : F), Monoton
e ⇑f
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
protected theorem mono (f : F) : Monotone f := fun _ _ => map_rel f

/-- Turn an element of a type `F` satisfying `OrderHomClass F α β` into an actual
`OrderHom`. This is declared as the default coercion from `F` to `α →o β`. -/
@[coe]
/-
**OrderHomClass.toOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderHomClass`。
形式化陈述：toOrderHom (f : F) : α ->o β where toFun
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…

--- 原说明 ---
Turn an element of a type `F` satisfying `OrderHomClass F α β` into an actual
`OrderHom`. This is declared as the default coercion from `F` to `α →o β`.
-/
def toOrderHom (f : F) : α →o β where
  toFun := f
  monotone' := OrderHomClass.monotone f

/-- Any type satisfying `OrderHomClass` can be cast into `OrderHom` via
`OrderHomClass.toOrderHom`. -/
/-
**OrderHomClass.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHomClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any type satisfying `OrderHomClass` can be cast into `OrderHom` via
`OrderHomClass.toOrderHom`.
-/
instance : CoeTC F (α →o β) :=
  ⟨toOrderHom⟩

end OrderHomClass

section OrderIsoClass

section LE

variable [LE α] [LE β] [EquivLike F α β] [OrderIsoClass F α β]

@[to_dual (attr := simp) le_map_inv_iff]
/-
**map_inv_le_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b <= a ↔ b <= f a
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquivLike.right_inv`：∀ {E : Sort u_1} {α : outParam (Sort u_2)} {β : out
Param (Sort u_3)} [self : EquivLike E α β] (e : E),   Function.RightInverse (Equ
ivLike.in…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…
-/
theorem map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f b ≤ a ↔ b ≤ f a := by
  convert! (map_le_map_iff f).symm
  exact (EquivLike.right_inv f _).symm

@[to_dual self]
/-
**map_inv_le_map_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_le_map_inv_iff (f : F) {a b : β} : EquivLike.inv f b <= EquivLike.
inv f a ↔ b <= a
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_inv_le_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b ≤ EquivLike.inv f a ↔ b ≤ a := by
  simp

end LE

variable [Preorder α] [Preorder β] [EquivLike F α β] [OrderIsoClass F α β]

@[to_dual self]
/-
**map_lt_map_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_iff_lt_of_le_iff_le'`：lt_iff_lt_of_le_iff_le' {β} [Preorder α] [Preor
der β] {a b : α} {c d : β} (H : a <= b ↔ c <= d) (H' : b <= a ↔ d <= c) : b < a 
↔ d < c
· 使用定理 `OrderIsoClass.map_le_map_iff`：∀ {F : Type u_6} {α : outParam (Type u_7)}
 {β : outParam (Type u_8)} {inst : LE α} {inst_1 : LE β}   {inst_2 : EquivLike F
 α β} [self : Orde…
-/
theorem map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b :=
  lt_iff_lt_of_le_iff_le' (map_le_map_iff f) (map_le_map_iff f)

@[to_dual (attr := simp) lt_map_inv_iff]
/-
**map_inv_lt_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_lt_map_iff`：map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_inv_lt_iff (f : F) {a : α} {b : β} : EquivLike.inv f b < a ↔ b < f a := by
  rw [← map_lt_map_iff f]
  simp only [EquivLike.apply_inv_apply]

@[to_dual self]
/-
**map_inv_lt_map_inv_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_inv_lt_map_inv_iff (f : F) {a b : β} : EquivLike.inv f b < EquivLike.i
nv f a ↔ b < a
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.apply_inv_apply`：apply_inv_apply (e : E) (b : β) : e (inv e b)
 = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_inv_lt_map_inv_iff (f : F) {a b : β} :
    EquivLike.inv f b < EquivLike.inv f a ↔ b < a := by
  simp

end OrderIsoClass

namespace OrderHom

variable [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]

/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (α →o β) α β where
  coe := toFun
  coe_injective f g h := by cases f; cases g; congr
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderHomClass (α →o β) α β where
  map_rel f _ _ h := f.monotone' h
/-
**OrderHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α → β) (hf : Monotone f),   ⇑{ toFun := f, monotone' := hf } = f
参数：f : α → β；hf : Monotone f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_mk (f : α → β) (hf : Monotone f) : ⇑(mk f hf) = f := rfl
/-
**OrderHom.monotone** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α →o β), Monotone ⇑f
参数：f : α →o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone'`：∀ {α : Type u_6} {β : Type u_7} [inst : Preorder α] 
[inst_1 : Preorder β] (self : α →o β), Monotone self.toFun
-/
protected theorem monotone (f : α →o β) : Monotone f :=
  f.monotone'
/-
**OrderHom.mono** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α →o β), Monotone ⇑f
参数：f : α →o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
protected theorem mono (f : α →o β) : Monotone f :=
  f.monotone

/-- See Note [custom simps projection]. We give this manually so that we use `toFun` as the
projection directly instead. -/
/-
**OrderHom.Simps.coe** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom.Simps`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preorder
 β] → (α →o β) → α → β
参数：α →o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We give this manually so that we use `toFun`
 as the
projection directly instead.
-/
def Simps.coe (f : α →o β) : α → β := f

/- TODO: all other DFunLike classes use `apply` instead of `coe`
for the projection names. Maybe we should change this. -/
initialize_simps_projections OrderHom (toFun → coe)

/-
**OrderHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α →o β), f.toFun = ⇑f
参数：f : α →o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem toFun_eq_coe (f : α →o β) : f.toFun = f := rfl

-- See library note [partially-applied ext lemmas]
@[ext]
/-
**OrderHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
参数：f g : α ->o β；h : (f : α -> β) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem ext (f g : α →o β) (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h
/-
**OrderHom.coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α →o β), ↑f = f
参数：f : α →o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.instOrderHomClass`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β], OrderHomClass (α →o β) α β
-/
@[simp] theorem coe_eq (f : α →o β) : OrderHomClass.toOrderHom f = f := rfl
/-
**OrderHom._root_.OrderHomClass.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.OrderHomClass.coe_coe {F} [FunLike F α β] [OrderHomClass F α β] (f : F) :
    ⇑(f : α →o β) = f :=
  rfl

/-- One can lift an unbundled monotone function to a bundled one. -/
/-
**OrderHom.canLift** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β],
   CanLift (α → β) (α →o β) DFunLike.coe Monotone
参数：α → β；α →o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
One can lift an unbundled monotone function to a bundled one.
-/
protected instance canLift : CanLift (α → β) (α →o β) (↑) Monotone where
  prf f h := ⟨⟨f, h⟩, rfl⟩

/-- Copy of an `OrderHom` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**OrderHom.copy** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preord
er β] → (f : α →o β) → (f' : α → β) → f' = ⇑f → α →o β
参数：f : α →o β；f' : α → β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of an `OrderHom` with a new `toFun` equal to the old one. Useful to fix def
initional
equalities.
-/
protected def copy (f : α →o β) (f' : α → β) (h : f' = f) : α →o β :=
  ⟨f', h.symm.subst f.monotone'⟩

@[simp]
/-
**OrderHom.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：coe_copy (f : α ->o β) (f' : α -> β) (h : f' = f) : (f.copy f' h) = f'
参数：f : α ->o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (f : α →o β) (f' : α → β) (h : f' = f) : (f.copy f' h) = f' :=
  rfl
/-
**OrderHom.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：copy_eq (f : α ->o β) (f' : α -> β) (h : f' = f) : f.copy f' h = f
参数：f : α ->o β；f' : α -> β；h : f' = f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (f : α →o β) (f' : α → β) (h : f' = f) : f.copy f' h = f :=
  DFunLike.ext' h
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} (β : Type*) [PartialOrder α] [PartialOrder β] [DecidableEq (α → β)] :
    DecidableEq (α →o β) := fun a b =>
  decidable_of_iff (a.toFun = b.toFun) OrderHom.ext_iff.symm

/-- The identity function as bundled monotone function. -/
@[simps -fullyApplied]
/-
**OrderHom.id** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：id : α ->o α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_id`：monotone_id [Preorder α] : Monotone (id : α -> α)

--- 原说明 ---
The identity function as bundled monotone function.
-/
def id : α →o α :=
  ⟨_root_.id, monotone_id⟩
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (α →o α) :=
  ⟨id⟩

variable (α β) in
/-- Order homomorphisms are equivalent to relation homomorphisms between `LE` relations. -/
/-
**OrderHom.equivRelHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：equivRelHom : (α ->o β) ≃ @RelHom α β (· <= ·) (· <= ·) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f

--- 原说明 ---
Order homomorphisms are equivalent to relation homomorphisms between `LE` relati
ons.
-/
def equivRelHom : (α →o β) ≃ @RelHom α β (· ≤ ·) (· ≤ ·) where
  toFun f := ⟨f, @f.monotone⟩
  invFun f := ⟨f, @f.map_rel⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ g a`. -/
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preorder structure of `α →o β` is pointwise inequality: `f ≤ g ↔ ∀ a, f a ≤ 
g a`.
-/
instance : Preorder (α →o β) :=
  @Preorder.lift (α →o β) (α → β) _ DFunLike.coe
/-
**OrderHom.** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {β : Type*} [PartialOrder β] : PartialOrder (α →o β) :=
  @PartialOrder.lift (α →o β) (α → β) _ toFun ext

@[to_dual self]
/-
**OrderHom.le_def** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：le_def {f g : α ->o β} : f <= g ↔ forall x, f x <= g x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {f g : α →o β} : f ≤ g ↔ ∀ x, f x ≤ g x :=
  Iff.rfl

@[simp, norm_cast, to_dual self]
/-
**OrderHom.coe_le_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：coe_le_coe {f g : α ->o β} : (f : α -> β) <= g ↔ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le_coe {f g : α →o β} : (f : α → β) ≤ g ↔ f ≤ g :=
  Iff.rfl

@[simp, to_dual self]
/-
**OrderHom.mk_le_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：mk_le_mk {f g : α -> β} {hf hg} : mk f hf <= mk g hg ↔ f <= g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_le_mk {f g : α → β} {hf hg} : mk f hf ≤ mk g hg ↔ f ≤ g :=
  Iff.rfl

@[mono, to_dual self]
/-
**OrderHom.apply_mono** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：apply_mono {f g : α ->o β} {x y : α} (h₁ : f <= g) (h₂ : x <= y) : f x <= 
g y
参数：h₁ : f <= g；h₂ : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem apply_mono {f g : α →o β} {x y : α} (h₁ : f ≤ g) (h₂ : x ≤ y) : f x ≤ g y :=
  (h₁ x).trans <| g.mono h₂

set_option backward.isDefEq.respectTransparency false in
/-- Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`. -/
/-
**OrderHom.curry** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：curry : (α × β ->o γ) ≃o (α ->o β ->o γ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Curry/uncurry as an order isomorphism between `α × β →o γ` and `α →o β →o γ`.
-/
def curry : (α × β →o γ) ≃o (α →o β →o γ) where
  toFun f := ⟨fun x ↦ ⟨Function.curry f x, fun _ _ h ↦ f.mono ⟨le_rfl, h⟩⟩, fun _ _ h _ =>
    f.mono ⟨h, le_rfl⟩⟩
  invFun f := ⟨Function.uncurry fun x ↦ f x, fun x y h ↦ (f.mono h.1 x.2).trans ((f y.1).mono h.2)⟩
  map_rel_iff' := by simp [le_def]

@[simp]
/-
**OrderHom.curry_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：curry_apply (f : α × β ->o γ) (x : α) (y : β) : curry f x y = f (x, y)
参数：f : α × β ->o γ；x : α；y : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_apply (f : α × β →o γ) (x : α) (y : β) : curry f x y = f (x, y) :=
  rfl

@[simp]
/-
**OrderHom.curry_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：curry_symm_apply (f : α ->o β ->o γ) (x : α × β) : curry.symm f x = f x.1 
x.2
参数：f : α ->o β ->o γ；x : α × β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curry_symm_apply (f : α →o β →o γ) (x : α × β) : curry.symm f x = f x.1 x.2 :=
  rfl

/-- The composition of two bundled monotone functions. -/
@[simps -fullyApplied]
/-
**OrderHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：comp (g : β ->o γ) (f : α ->o β) : α ->o γ
参数：g : β ->o γ；f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two bundled monotone functions.
-/
def comp (g : β →o γ) (f : α →o β) : α →o γ :=
  ⟨g ∘ f, g.mono.comp f.mono⟩

@[mono, to_dual self]
/-
**OrderHom.comp_mono** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：comp_mono ⦃g₁ g₂ : β ->o γ⦄ (hg : g₁ <= g₂) ⦃f₁ f₂ : α ->o β⦄ (hf : f₁ <= 
f₂) : g₁.comp f₁ <= g₂.comp f₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `OrderHom.mono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst
_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
theorem comp_mono ⦃g₁ g₂ : β →o γ⦄ (hg : g₁ ≤ g₂) ⦃f₁ f₂ : α →o β⦄ (hf : f₁ ≤ f₂) :
    g₁.comp f₁ ≤ g₂.comp f₂ := fun _ => (hg _).trans (g₂.mono <| hf _)
/-
**OrderHom.mk_comp_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst : Preorder α] [inst_1
 : Preorder β] [inst_2 : Preorder γ]   (g : β → γ) (f : α → β) (hg : Monotone g)
 (hf : Monotone f),   { toFun := g, monotone' := hg }.comp { toFun := f, monoton
e' := hf } = { toFun := g ∘ f, monotone' := ⋯ }
参数：g : β → γ；f : α → β；hg : Monotone g；hf : Monotone f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma mk_comp_mk (g : β → γ) (f : α → β) (hg hf) :
    comp ⟨g, hg⟩ ⟨f, hf⟩ = ⟨g ∘ f, hg.comp hf⟩ := rfl

/-- The composition of two bundled monotone functions, a fully bundled version. -/
@[simps! -fullyApplied]
/-
**OrderHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：comp (g : β ->o γ) (f : α ->o β) : α ->o γ
参数：g : β ->o γ；f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two bundled monotone functions, a fully bundled version.
-/
def compₘ : (β →o γ) →o (α →o β) →o α →o γ :=
  curry ⟨fun f : (β →o γ) × (α →o β) => f.1.comp f.2, fun _ _ h => comp_mono h.1 h.2⟩

@[simp]
/-
**OrderHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：comp_id (f : α ->o β) : comp f id = f
参数：f : α ->o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem comp_id (f : α →o β) : comp f id = f := by
  ext
  rfl

@[simp]
/-
**OrderHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：id_comp (f : α ->o β) : comp id f = f
参数：f : α ->o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem id_comp (f : α →o β) : comp id f = f := by
  ext
  rfl
/-
**OrderHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：comp_assoc (f : γ ->o δ) (g : β ->o γ) (h : α ->o β) : (f.comp g).comp h =
 f.comp (g.comp h)
参数：f : γ ->o δ；g : β ->o γ；h : α ->o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : γ →o δ) (g : β →o γ) (h : α →o β) : (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

/-- Constant function bundled as an `OrderHom`. -/
@[simps -fullyApplied]
/-
**OrderHom.const** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β ->o α ->o β wh
ere toFun b
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant function bundled as an `OrderHom`.
-/
def const (α : Type*) [Preorder α] {β : Type*} [Preorder β] : β →o α →o β where
  toFun b := ⟨Function.const α b, fun _ _ _ => le_rfl⟩
  monotone' _ _ h _ := h

@[simp]
/-
**OrderHom.const_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：const_comp (f : α ->o β) (c : γ) : (const β c).comp f = const α c
参数：f : α ->o β；c : γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_comp (f : α →o β) (c : γ) : (const β c).comp f = const α c :=
  rfl

@[simp]
/-
**OrderHom.comp_const** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：comp_const (γ : Type*) [Preorder γ] (f : α ->o β) (c : α) : f.comp (const 
γ c) = const γ (f c)
参数：γ : Type*；f : α ->o β；c : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_const (γ : Type*) [Preorder γ] (f : α →o β) (c : α) :
    f.comp (const γ c) = const γ (f c) :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. -/
@[simps]
/-
**OrderHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     {γ : Type u_4} →       [inst : Pre
order α] → [inst_1 : Preorder β] → [inst_2 : Preorder γ] → (α →o β) → (α →o γ) →
 α →o β × γ
参数：α →o β；α →o γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)`
 bundled as a
`OrderHom`.
-/
protected def prod (f : α →o β) (g : α →o γ) : α →o β × γ :=
  ⟨fun x => (f x, g x), fun _ _ h => ⟨f.mono h, g.mono h⟩⟩

@[mono, to_dual self]
/-
**OrderHom.prod_mono** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：prod_mono {f₁ f₂ : α ->o β} (hf : f₁ <= f₂) {g₁ g₂ : α ->o γ} (hg : g₁ <= 
g₂) : f₁.prod g₁ <= f₂.prod g₂
参数：hf : f₁ <= f₂；hg : g₁ <= g₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Prod.le_def`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE 
β] {x y : α × β}, x ≤ y ↔ x.1 ≤ y.1 ∧ x.2 ≤ y.2
-/
theorem prod_mono {f₁ f₂ : α →o β} (hf : f₁ ≤ f₂) {g₁ g₂ : α →o γ} (hg : g₁ ≤ g₂) :
    f₁.prod g₁ ≤ f₂.prod g₂ := fun _ => Prod.le_def.2 ⟨hf _, hg _⟩
/-
**OrderHom.comp_prod_comp_same** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：comp_prod_comp_same (f₁ f₂ : β ->o γ) (g : α ->o β) : (f₁.comp g).prod (f₂
.comp g) = (f₁.prod f₂).comp g
参数：f₁ f₂ : β ->o γ；g : α ->o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_prod_comp_same (f₁ f₂ : β →o γ) (g : α →o β) :
    (f₁.comp g).prod (f₂.comp g) = (f₁.prod f₂).comp g :=
  rfl

/-- Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)` bundled as a
`OrderHom`. This is a fully bundled version. -/
@[simps!]
/-
**OrderHom.prod** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：{α : Type u_2} →   {β : Type u_3} →     {γ : Type u_4} →       [inst : Pre
order α] → [inst_1 : Preorder β] → [inst_2 : Preorder γ] → (α →o β) → (α →o γ) →
 α →o β × γ
参数：α →o β；α →o γ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two bundled monotone maps `f`, `g`, `f.prod g` is the map `x ↦ (f x, g x)`
 bundled as a
`OrderHom`. This is a fully bundled version.
-/
def prodₘ : (α →o β) →o (α →o γ) →o α →o β × γ :=
  curry ⟨fun f : (α →o β) × (α →o γ) => f.1.prod f.2, fun _ _ h => prod_mono h.1 h.2⟩

/-- Diagonal embedding of `α` into `α × α` as an `OrderHom`. -/
@[simps!]
/-
**OrderHom.diag** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：diag : α ->o α × α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Diagonal embedding of `α` into `α × α` as an `OrderHom`.
-/
def diag : α →o α × α :=
  id.prod id

/-- Restriction of `f : α →o α →o β` to the diagonal. -/
@[simps! +simpRhs]
/-
**OrderHom.onDiag** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：onDiag (f : α ->o α ->o β) : α ->o β
参数：f : α ->o α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restriction of `f : α →o α →o β` to the diagonal.
-/
def onDiag (f : α →o α →o β) : α →o β :=
  (curry.symm f).comp diag

/-- `Prod.fst` as an `OrderHom`. -/
@[simps]
/-
**OrderHom.fst** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：fst : α × β ->o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.fst` as an `OrderHom`.
-/
def fst : α × β →o α :=
  ⟨Prod.fst, fun _ _ h => h.1⟩

/-- `Prod.snd` as an `OrderHom`. -/
@[simps]
/-
**OrderHom.snd** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：snd : α × β ->o β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.snd` as an `OrderHom`.
-/
def snd : α × β →o β :=
  ⟨Prod.snd, fun _ _ h => h.2⟩

@[simp]
/-
**OrderHom.fst_prod_snd** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：fst_prod_snd : (fst : α × β ->o α).prod snd = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem fst_prod_snd : (fst : α × β →o α).prod snd = id := by
  ext ⟨x, y⟩ : 2
  rfl

@[simp]
/-
**OrderHom.fst_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：fst_comp_prod (f : α ->o β) (g : α ->o γ) : fst.comp (f.prod g) = f
参数：f : α ->o β；g : α ->o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
-/
theorem fst_comp_prod (f : α →o β) (g : α →o γ) : fst.comp (f.prod g) = f :=
  ext _ _ rfl

@[simp]
/-
**OrderHom.snd_comp_prod** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：snd_comp_prod (f : α ->o β) (g : α ->o γ) : snd.comp (f.prod g) = g
参数：f : α ->o β；g : α ->o γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.ext`：ext (f g : α ->o β) (h : (f : α -> β) = g) : f = g
-/
theorem snd_comp_prod (f : α →o β) (g : α →o γ) : snd.comp (f.prod g) = g :=
  ext _ _ rfl

/-- Order isomorphism between the space of monotone maps to `β × γ` and the product of the spaces
of monotone maps to `β` and `γ`. -/
@[simps]
/-
**OrderHom.prodIso** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：prodIso : (α ->o β × γ) ≃o (α ->o β) × (α ->o γ) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between the space of monotone maps to `β × γ` and the product 
of the spaces
of monotone maps to `β` and `γ`.
-/
def prodIso : (α →o β × γ) ≃o (α →o β) × (α →o γ) where
  toFun f := (fst.comp f, snd.comp f)
  invFun f := f.1.prod f.2
  map_rel_iff' := forall_and.symm

/-- `Prod.map` of two `OrderHom`s as an `OrderHom` -/
@[simps]
/-
**OrderHom.prodMap** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：prodMap (f : α ->o β) (g : γ ->o δ) : α × γ ->o β × δ
参数：f : α ->o β；g : γ ->o δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` of two `OrderHom`s as an `OrderHom`
-/
def prodMap (f : α →o β) (g : γ →o δ) : α × γ →o β × δ :=
  ⟨Prod.map f g, fun _ _ h => ⟨f.mono h.1, g.mono h.2⟩⟩

variable {ι : Type*} {π : ι → Type*} [∀ i, Preorder (π i)]

/-- Evaluation of an unbundled function at a point (`Function.eval`) as an `OrderHom`. -/
@[simps -fullyApplied]
/-
**OrderHom._root_.Pi.evalOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Evaluation of an unbundled function at a point (`Function.eval`) as an `OrderHom
`.
-/
def _root_.Pi.evalOrderHom (i : ι) : (∀ j, π j) →o π i :=
  ⟨Function.eval i, Function.monotone_eval i⟩

/-- The "forgetful functor" from `α →o β` to `α → β` that takes the underlying function,
is monotone. -/
@[simps -fullyApplied]
/-
**OrderHom.coeFnHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：coeFnHom : (α ->o β) ->o α -> β where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "forgetful functor" from `α →o β` to `α → β` that takes the underlying funct
ion,
is monotone.
-/
def coeFnHom : (α →o β) →o α → β where
  toFun f := f
  monotone' _ _ h := h

/-- Function application `fun f => f a` (for fixed `a`) is a monotone function from the
monotone function space `α →o β` to `β`. See also `Pi.evalOrderHom`. -/
@[simps! -fullyApplied]
/-
**OrderHom.apply** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：apply (x : α) : (α ->o β) ->o β
参数：x : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Function application `fun f => f a` (for fixed `a`) is a monotone function from 
the
monotone function space `α →o β` to `β`. See also `Pi.evalOrderHom`.
-/
def apply (x : α) : (α →o β) →o β :=
  (Pi.evalOrderHom x).comp coeFnHom

/-- Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`. -/
@[simps]
/-
**OrderHom.pi** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：pi (f : forall i, α ->o π i) : α ->o forall i, π i
参数：f : forall i, α ->o π i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Construct a bundled monotone map `α →o Π i, π i` from a family of monotone maps
`f i : α →o π i`.
-/
def pi (f : ∀ i, α →o π i) : α →o ∀ i, π i :=
  ⟨fun x i => f i x, fun _ _ h i => (f i).mono h⟩

/-- Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of bundled monotone
maps `Π i, α →o π i`. -/
@[simps]
/-
**OrderHom.piIso** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：piIso : (α ->o forall i, π i) ≃o forall i, α ->o π i where toFun f i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between bundled monotone maps `α →o Π i, π i` and families of 
bundled monotone
maps `Π i, α →o π i`.
-/
def piIso : (α →o ∀ i, π i) ≃o ∀ i, α →o π i where
  toFun f i := (Pi.evalOrderHom i).comp f
  invFun := pi
  map_rel_iff' := forall_comm

/-- `Subtype.val` as a bundled monotone function. -/
@[simps -fullyApplied]
/-
**OrderHom.Subtype.val** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom.Subtype`。
形式化陈述：{α : Type u_2} → [inst : Preorder α] → (p : α → Prop) → Subtype p →o α
参数：p : α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subtype.val` as a bundled monotone function.
-/
def Subtype.val (p : α → Prop) : Subtype p →o α :=
  ⟨_root_.Subtype.val, fun _ _ h => h⟩

/-- `Subtype.impEmbedding` as an order embedding. -/
@[simps!]
/-
**OrderHom._root_.Subtype.orderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Subtype.impEmbedding` as an order embedding.
-/
def _root_.Subtype.orderEmbedding {p q : α → Prop} (h : ∀ a, p a → q a) :
    {x // p x} ↪o {x // q x} :=
  { Subtype.impEmbedding _ _ h with
    map_rel_iff' := by aesop }

/-- There is a unique monotone map from a subsingleton to itself. -/
/-
**OrderHom.unique** 是 Mathlib 中的一个实例，位于命名空间 `OrderHom`。
形式化陈述：unique [Subsingleton α] : Unique (α ->o α) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
There is a unique monotone map from a subsingleton to itself.
-/
instance unique [Subsingleton α] : Unique (α →o α) where
  default := OrderHom.id
  uniq _ := ext _ _ (Subsingleton.elim _ _)
/-
**OrderHom.orderHom_eq_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：orderHom_eq_id [Subsingleton α] (g : α ->o α) : g = OrderHom.id
参数：g : α ->o α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem orderHom_eq_id [Subsingleton α] (g : α →o α) : g = OrderHom.id :=
  Subsingleton.elim _ _

/-- Reinterpret a bundled monotone function as a monotone function between dual orders. -/
@[simps]
/-
**OrderHom.dual** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preorder
 β] → (α →o β) ≃ (αᵒᵈ →o βᵒᵈ)
参数：α →o β；αᵒᵈ →o βᵒᵈ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret a bundled monotone function as a monotone function between dual orde
rs.
-/
protected def dual : (α →o β) ≃ (αᵒᵈ →o βᵒᵈ) where
  toFun f := ⟨(OrderDual.toDual : β → βᵒᵈ) ∘ (f : α → β) ∘
    (OrderDual.ofDual : αᵒᵈ → α), f.mono.dual⟩
  invFun f := ⟨OrderDual.ofDual ∘ f ∘ OrderDual.toDual, f.mono.dual⟩

@[simp]
/-
**OrderHom.dual_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：dual_id : (OrderHom.id : α ->o α).dual = OrderHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_id : (OrderHom.id : α →o α).dual = OrderHom.id :=
  rfl

@[simp]
/-
**OrderHom.dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：dual_comp (g : β ->o γ) (f : α ->o β) : (g.comp f).dual = g.dual.comp f.du
al
参数：g : β ->o γ；f : α ->o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dual_comp (g : β →o γ) (f : α →o β) :
    (g.comp f).dual = g.dual.comp f.dual :=
  rfl

@[simp]
/-
**OrderHom.symm_dual_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α ->o α)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_id : OrderHom.dual.symm OrderHom.id = (OrderHom.id : α →o α) :=
  rfl

@[simp]
/-
**OrderHom.symm_dual_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：symm_dual_comp (g : βᵒᵈ ->o γᵒᵈ) (f : αᵒᵈ ->o βᵒᵈ) : OrderHom.dual.symm (g
.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f)
参数：g : βᵒᵈ ->o γᵒᵈ；f : αᵒᵈ ->o βᵒᵈ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem symm_dual_comp (g : βᵒᵈ →o γᵒᵈ) (f : αᵒᵈ →o βᵒᵈ) :
    OrderHom.dual.symm (g.comp f) = (OrderHom.dual.symm g).comp (OrderHom.dual.symm f) :=
  rfl

/-- `OrderHom.dual` as an order isomorphism. -/
/-
**OrderHom.dualIso** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：dualIso (α β : Type*) [Preorder α] [Preorder β] : (α ->o β) ≃o (αᵒᵈ ->o βᵒ
ᵈ)ᵒᵈ where toEquiv
参数：α β : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
`OrderHom.dual` as an order isomorphism.
-/
def dualIso (α β : Type*) [Preorder α] [Preorder β] : (α →o β) ≃o (αᵒᵈ →o βᵒᵈ)ᵒᵈ where
  toEquiv := OrderHom.dual.trans OrderDual.toDual
  map_rel_iff' := Iff.rfl

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o ULift β` in a
higher universe. -/
@[simps!]
/-
**OrderHom.uliftMap** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：uliftMap (f : α ->o β) : ULift α ->o ULift β
参数：f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o ULi
ft β` in a
higher universe.
-/
def uliftMap (f : α →o β) : ULift α →o ULift β :=
  ⟨fun i => ⟨f i.down⟩, fun _ _ h ↦ f.monotone h⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `α →o ULift β` in a
higher universe. -/
@[simps!]
/-
**OrderHom.uliftRightMap** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：uliftRightMap (f : α ->o β) : α ->o ULift β
参数：f : α ->o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f

--- 原说明 ---
Lift an order homomorphism `f : α →o β` to an order homomorphism `α →o ULift β` 
in a
higher universe.
-/
def uliftRightMap (f : α →o β) : α →o ULift β :=
  ⟨fun i => ⟨f i⟩, fun _ _ h ↦ f.monotone h⟩

/-- Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o β` in a
higher universe. -/
@[simps!]
/-
**OrderHom.uliftLeftMap** 是 Mathlib 中的一个定义，位于命名空间 `OrderHom`。
形式化陈述：uliftLeftMap (f : α ->o β) : ULift α ->o β
参数：f : α ->o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift an order homomorphism `f : α →o β` to an order homomorphism `ULift α →o β` 
in a
higher universe.
-/
def uliftLeftMap (f : α →o β) : ULift α →o β :=
  ⟨fun i => f i.down, fun _ _ h ↦ f.monotone h⟩

@[simp]
/-
**OrderHom.uliftLeftMap_uliftRightMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：uliftLeftMap_uliftRightMap_eq (f : α ->o β) : f.uliftLeftMap.uliftRightMap
 = f.uliftMap
参数：f : α ->o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uliftLeftMap_uliftRightMap_eq (f : α →o β) : f.uliftLeftMap.uliftRightMap = f.uliftMap :=
  rfl

@[simp]
/-
**OrderHom.uliftRightMap_uliftLeftMap_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderHom`。
形式化陈述：uliftRightMap_uliftLeftMap_eq (f : α ->o β) : f.uliftRightMap.uliftLeftMap
 = f.uliftMap
参数：f : α ->o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem uliftRightMap_uliftLeftMap_eq (f : α →o β) : f.uliftRightMap.uliftLeftMap = f.uliftMap :=
  rfl

end OrderHom

/-- Embeddings of partial orders that preserve `<` also preserve `≤`. -/
/-
**RelEmbedding.orderEmbeddingOfLTEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
 (f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)) : α ↪o β
参数：f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embeddings of partial orders that preserve `<` also preserve `≤`.
-/
def RelEmbedding.orderEmbeddingOfLTEmbedding [PartialOrder α] [PartialOrder β]
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) : α ↪o β :=
  { f with
    map_rel_iff' := by
      simp [le_iff_lt_or_eq, f.map_rel_iff, f.injective.eq_iff] }

@[simp]
/-
**RelEmbedding.orderEmbeddingOfLTEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOr
der β] {f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)} {x : α} : 
RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x
参数：(· < ·) : α -> α -> Prop；(· < ·) : β -> β -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelEmbedding.orderEmbeddingOfLTEmbedding_apply [PartialOrder α] [PartialOrder β]
    {f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)} {x : α} :
    RelEmbedding.orderEmbeddingOfLTEmbedding f x = f x :=
  rfl

namespace OrderEmbedding

section LE

variable [LE α] [LE β] [LE γ] [LE δ]

variable (α) in
/-- Identity order embedding -/
/-
**OrderEmbedding.id** 是 Mathlib 中的一个缩写定义，位于命名空间 `OrderEmbedding`。
形式化陈述：id : α ↪o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity order embedding
-/
abbrev id : α ↪o α :=
  RelEmbedding.refl (· ≤ ·)

@[simp]
/-
**OrderEmbedding.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：coe_id : ⇑(id α) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(id α) = _root_.id :=
  rfl

@[simp]
/-
**OrderEmbedding.id_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：id_toEmbedding : (id α).toEmbedding = Function.Embedding.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_toEmbedding : (id α).toEmbedding = Function.Embedding.refl α :=
  rfl

/-- Composition of two order embeddings is an order embedding -/
/-
**OrderEmbedding.comp** 是 Mathlib 中的一个缩写定义，位于命名空间 `OrderEmbedding`。
形式化陈述：comp (f : α ↪o β) (g : β ↪o γ) : α ↪o γ
参数：f : α ↪o β；g : β ↪o γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two order embeddings is an order embedding
-/
abbrev comp (f : α ↪o β) (g : β ↪o γ) : α ↪o γ :=
  RelEmbedding.trans f g

@[simp]
/-
**OrderEmbedding.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：coe_comp (f : α ↪o β) (g : β ↪o γ) : f.comp g = g ∘ f
参数：f : α ↪o β；g : β ↪o γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : α ↪o β) (g : β ↪o γ) : f.comp g = g ∘ f :=
  rfl

@[simp]
/-
**OrderEmbedding.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：id_comp (f : α ↪o β) : (id α).comp f = f
参数：f : α ↪o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
-/
theorem id_comp (f : α ↪o β) : (id α).comp f = f := by
  ext
  rfl

@[simp]
/-
**OrderEmbedding.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：comp_id (f : α ↪o β) : f.comp (id β) = f
参数：f : α ↪o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.ext`：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
-/
theorem comp_id (f : α ↪o β) : f.comp (id β) = f := by
  ext
  rfl
/-
**OrderEmbedding.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：comp_assoc (f : α ↪o β) (g : β ↪o γ) (h : γ ↪o δ) : (f.comp g).comp h = f.
comp (g.comp h)
参数：f : α ↪o β；g : β ↪o γ；h : γ ↪o δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (f : α ↪o β) (g : β ↪o γ) (h : γ ↪o δ) :
    (f.comp g).comp h = f.comp (g.comp h) :=
  rfl

end LE

section Preorder

variable [Preorder α] [Preorder β] (f : α ↪o β)

/-- `<` is preserved by order embeddings of preorders. -/
@[to_dual gtEmbedding /-- `>` is preserved by order embeddings of preorders. -/]
/-
**OrderEmbedding.ltEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：ltEmbedding : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`<` is preserved by order embeddings of preorders.
-/
def ltEmbedding : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop) :=
  { f with map_rel_iff' := by simp [lt_iff_le_not_ge, f.map_rel_iff] }

@[to_dual (attr := simp) gtEmbedding_apply]
/-
**OrderEmbedding.ltEmbedding_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：ltEmbedding_apply (x : α) : f.ltEmbedding x = f x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ltEmbedding_apply (x : α) : f.ltEmbedding x = f x :=
  rfl

@[simp, to_dual self]
/-
**OrderEmbedding.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：le_iff_le {a b} : f a <= f b ↔ a <= b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem le_iff_le {a b} : f a ≤ f b ↔ a ≤ b :=
  f.map_rel_iff

@[simp, to_dual self]
/-
**OrderEmbedding.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：lt_iff_lt {a b} : f a < f b ↔ a < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem lt_iff_lt {a b} : f a < f b ↔ a < b :=
  f.ltEmbedding.map_rel_iff
/-
**OrderEmbedding.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：eq_iff_eq {a b} : f a = f b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem eq_iff_eq {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff
/-
**OrderEmbedding.monotone** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α ↪o β), Monotone ⇑f
参数：f : α ↪o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHomClass.monotone`：∀ {F : Type u_1} {α : Type u_2} {β : Type u_3} [
inst : Preorder α] [inst_1 : Preorder β] [inst_2 : FunLike F α β]   [OrderHomCla
ss F α β] (f…
· 使用定理 `RelEmbedding.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α
 → Prop} {s : β → β → Prop}, RelHomClass (r ↪r s) r s
-/
protected theorem monotone : Monotone f :=
  OrderHomClass.monotone f
/-
**OrderEmbedding.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α ↪o β), StrictMono ⇑f
参数：f : α ↪o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
protected theorem strictMono : StrictMono f := fun _ _ => f.lt_iff_lt.2
/-
**OrderEmbedding.acc** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α ↪o β) (a : α),   Acc (fun x1 x2 => x1 < x2) (f a) → Acc (fun x1 x2 => x1 
< x2) a
参数：f : α ↪o β；a : α；fun x1 x2 => x1 < x2；f a；fun x1 x2 => x1 < x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.acc`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s 
: β → β → Prop} (f : r ↪r s) (a : α), Acc s (f a) → Acc r a
-/
protected theorem acc (a : α) : Acc (· < ·) (f a) → Acc (· < ·) a :=
  f.ltEmbedding.acc a

@[to_dual none]
/-
**OrderEmbedding.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2) → WellFounded fun x1 x2 => x1
 < x2
参数：f : α ↪o β；WellFounded fun x1 x2 => x1 < x2。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s), WellFounded s → WellFounded r
-/
protected theorem wellFounded (f : α ↪o β) :
    WellFounded ((· < ·) : β → β → Prop) → WellFounded ((· < ·) : α → α → Prop) :=
  f.ltEmbedding.wellFounded
/-
**OrderEmbedding.isWellOrder** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
[IsWellOrder β fun x1 x2 => x1 < x2]   (f : α ↪o β), IsWellOrder α fun x1 x2 => 
x1 < x2
参数：f : α ↪o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
-/
protected theorem isWellOrder [IsWellOrder β (· < ·)] (f : α ↪o β) : IsWellOrder α (· < ·) :=
  f.ltEmbedding.isWellOrder

/-- An order embedding is also an order embedding between dual orders. -/
/-
**OrderEmbedding.dual** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preorder
 β] → α ↪o β → αᵒᵈ ↪o βᵒᵈ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order embedding is also an order embedding between dual orders.
-/
protected def dual : αᵒᵈ ↪o βᵒᵈ :=
  ⟨f.toEmbedding, f.map_rel_iff⟩

/-- A preorder which embeds into a well-founded preorder is itself well-founded. -/
@[to_dual /-- A preorder which embeds into a preorder in which `(· > ·)` is well-founded
also has `(· > ·)` well-founded. -/]
/-
**OrderEmbedding.wellFoundedLT** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
[WellFoundedLT β] (f : α ↪o β),   WellFoundedLT α
参数：f : α ↪o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.wellFounded`：∀ {α : Type u_2} {β : Type u_3} [inst : Preo
rder α] [inst_1 : Preorder β] (f : α ↪o β),   (WellFounded fun x1 x2 => x1 < x2)
 → WellFounded f…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
protected theorem wellFoundedLT [WellFoundedLT β] (f : α ↪o β) : WellFoundedLT α where
  wf := f.wellFounded IsWellFounded.wf

/-- To define an order embedding from a partial order to a preorder it suffices to give a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
@[to_dual self]
/-
**OrderEmbedding.ofMapLEIff** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α -> β) (hf : forall a
 b, f a <= f b ↔ a <= b) : α ↪o β
参数：f : α -> β；hf : forall a b, f a <= f b ↔ a <= b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To define an order embedding from a partial order to a preorder it suffices to g
ive a function
together with a proof that it satisfies `f a ≤ f b ↔ a ≤ b`.
-/
def ofMapLEIff {α β} [PartialOrder α] [Preorder β] (f : α → β) (hf : ∀ a b, f a ≤ f b ↔ a ≤ b) :
    α ↪o β :=
  RelEmbedding.ofMapRelIff f hf

@[simp, to_dual self]
/-
**OrderEmbedding.coe_ofMapLEIff** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α -> β} (h) : ⇑(of
MapLEIff f h) = f
参数：h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofMapLEIff {α β} [PartialOrder α] [Preorder β] {f : α → β} (h) :
    ⇑(ofMapLEIff f h) = f :=
  rfl

/-- A strictly monotone map from a linear order is an order embedding. -/
/-
**OrderEmbedding.ofStrictMono** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α -> β) (h : StrictMo
no f) : α ↪o β
参数：f : α -> β；h : StrictMono f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.le_iff_le`：StrictMono.le_iff_le (hf : StrictMono f) {a b : α}
 : f a <= f b ↔ a <= b

--- 原说明 ---
A strictly monotone map from a linear order is an order embedding.
-/
def ofStrictMono {α β} [LinearOrder α] [Preorder β] (f : α → β) (h : StrictMono f) : α ↪o β :=
  ofMapLEIff f fun _ _ => h.le_iff_le

@[simp, grind =]
/-
**OrderEmbedding.coe_ofStrictMono** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α -> β} (h : Stri
ctMono f) : ⇑(ofStrictMono f h) = f
参数：h : StrictMono f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofStrictMono {α β} [LinearOrder α] [Preorder β] {f : α → β} (h : StrictMono f) :
    ⇑(ofStrictMono f h) = f :=
  rfl

/-- Embedding of a subtype into the ambient type as an `OrderEmbedding`. -/
/-
**OrderEmbedding.subtype** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：subtype (p : α -> Prop) : Subtype p ↪o α
参数：p : α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of a subtype into the ambient type as an `OrderEmbedding`.
-/
def subtype (p : α → Prop) : Subtype p ↪o α :=
  ⟨Function.Embedding.subtype p, Iff.rfl⟩

@[simp]
/-
**OrderEmbedding.subtype_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：subtype_apply {p : α -> Prop} (x : Subtype p) : subtype p x = x
参数：x : Subtype p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem subtype_apply {p : α → Prop} (x : Subtype p) : subtype p x = x :=
  rfl
/-
**OrderEmbedding.subtype_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：subtype_injective (p : α -> Prop) : Function.Injective (subtype p)
参数：p : α -> Prop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem subtype_injective (p : α → Prop) : Function.Injective (subtype p) :=
  Subtype.coe_injective

@[simp]
/-
**OrderEmbedding.coe_subtype** 是 Mathlib 中的一个定理，位于命名空间 `OrderEmbedding`。
形式化陈述：coe_subtype (p : α -> Prop) : ⇑(subtype p) = Subtype.val
参数：p : α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_subtype (p : α → Prop) : ⇑(subtype p) = Subtype.val :=
  rfl

/-- Convert an `OrderEmbedding` to an `OrderHom`. -/
@[simps -fullyApplied]
/-
**OrderEmbedding.toOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X ->o Y 
where toFun
参数：f : X ↪o Y。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f

--- 原说明 ---
Convert an `OrderEmbedding` to an `OrderHom`.
-/
def toOrderHom {X Y : Type*} [Preorder X] [Preorder Y] (f : X ↪o Y) : X →o Y where
  toFun := f
  monotone' := f.monotone

/-- The trivial embedding from an empty preorder to another preorder -/
/-
**OrderEmbedding.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `OrderEmbedding`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : Preorder α] → [inst_1 : Preorder
 β] → [IsEmpty α] → α ↪o β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial embedding from an empty preorder to another preorder
-/
@[simps] def ofIsEmpty [IsEmpty α] : α ↪o β where
  toFun := isEmptyElim
  inj' := isEmptyElim
  map_rel_iff' {a} := isEmptyElim a

@[simp, norm_cast]
/-
**OrderEmbedding.coe_ofIsEmpty** 是 Mathlib 中的一个引理，位于命名空间 `OrderEmbedding`。
形式化陈述：coe_ofIsEmpty [IsEmpty α] : (ofIsEmpty : α ↪o β) = (isEmptyElim : α -> β)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_ofIsEmpty [IsEmpty α] : (ofIsEmpty : α ↪o β) = (isEmptyElim : α → β) := rfl

end Preorder

end OrderEmbedding

section Disjoint

variable [PartialOrder α] [PartialOrder β] (f : OrderEmbedding α β)

/-- If the images by an order embedding of two elements are disjoint,
then they are themselves disjoint. -/
/-
**Disjoint.of_orderEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Disjoint.of_orderEmbedding [OrderBot α] [OrderBot β] {a₁ a₂ : α} : Disjoin
t (f a₁) (f a₂) -> Disjoint a₁ a₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderEmbedding.le_iff_le`：le_iff_le {a b} : f a <= f b ↔ a <= b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
If the images by an order embedding of two elements are disjoint,
then they are themselves disjoint.
-/
lemma Disjoint.of_orderEmbedding [OrderBot α] [OrderBot β] {a₁ a₂ : α} :
    Disjoint (f a₁) (f a₂) → Disjoint a₁ a₂ := by
  intro h x h₁ h₂
  rw [← f.le_iff_le] at h₁ h₂ ⊢
  calc
    f x ≤ ⊥ := h h₁ h₂
    _ ≤ f ⊥ := bot_le

/-- If the images by an order embedding of two elements are codisjoint,
then they are themselves codisjoint. -/
/-
**Codisjoint.of_orderEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Codisjoint.of_orderEmbedding [OrderTop α] [OrderTop β] {a₁ a₂ : α} : Codis
joint (f a₁) (f a₂) -> Codisjoint a₁ a₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Disjoint.of_orderEmbedding`：Disjoint.of_orderEmbedding [OrderBot α] [Ord
erBot β] {a₁ a₂ : α} : Disjoint (f a₁) (f a₂) -> Disjoint a₁ a₂

--- 原说明 ---
If the images by an order embedding of two elements are codisjoint,
then they are themselves codisjoint.
-/
lemma Codisjoint.of_orderEmbedding [OrderTop α] [OrderTop β] {a₁ a₂ : α} :
    Codisjoint (f a₁) (f a₂) → Codisjoint a₁ a₂ :=
  Disjoint.of_orderEmbedding (α := αᵒᵈ) (β := βᵒᵈ) f.dual

/-- If the images by an order embedding of two elements are complements,
then they are themselves complements. -/
/-
**IsCompl.of_orderEmbedding** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsCompl.of_orderEmbedding [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α} : 
IsCompl (f a₁) (f a₂) -> IsCompl a₁ a₂
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Disjoint.of_orderEmbedding`：Disjoint.of_orderEmbedding [OrderBot α] [Ord
erBot β] {a₁ a₂ : α} : Disjoint (f a₁) (f a₂) -> Disjoint a₁ a₂
· 使用引理 `Codisjoint.of_orderEmbedding`：Codisjoint.of_orderEmbedding [OrderTop α] 
[OrderTop β] {a₁ a₂ : α} : Codisjoint (f a₁) (f a₂) -> Codisjoint a₁ a₂

--- 原说明 ---
If the images by an order embedding of two elements are complements,
then they are themselves complements.
-/
lemma IsCompl.of_orderEmbedding [BoundedOrder α] [BoundedOrder β] {a₁ a₂ : α} :
    IsCompl (f a₁) (f a₂) → IsCompl a₁ a₂ := fun ⟨hd, hcd⟩ ↦
  ⟨Disjoint.of_orderEmbedding f hd, Codisjoint.of_orderEmbedding f hcd⟩

end Disjoint

section RelHom

variable [PartialOrder α] [Preorder β]

namespace RelHom

variable (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop))

/-- A bundled expression of the fact that a map between partial orders that is strictly monotone
is weakly monotone. -/
@[simps -fullyApplied]
/-
**RelHom.toOrderHom** 是 Mathlib 中的一个定义，位于命名空间 `RelHom`。
形式化陈述：toOrderHom : α ->o β where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bundled expression of the fact that a map between partial orders that is stric
tly monotone
is weakly monotone.
-/
def toOrderHom : α →o β where
  toFun := f
  monotone' := StrictMono.monotone fun _ _ => f.map_rel

end RelHom

/-
**RelEmbedding.toOrderHom_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelEmbedding.toOrderHom_injective (f : ((· < ·) : α -> α -> Prop) ↪r ((· <
 ·) : β -> β -> Prop)) : Function.Injective (f : ((· < ·) : α -> α -> Prop) ->r 
((· < ·) : β -> β -> Prop)).toOrderHom
参数：f : ((· < ·) : α -> α -> Prop) ↪r ((· < ·) : β -> β -> Prop)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem RelEmbedding.toOrderHom_injective
    (f : ((· < ·) : α → α → Prop) ↪r ((· < ·) : β → β → Prop)) :
    Function.Injective (f : ((· < ·) : α → α → Prop) →r ((· < ·) : β → β → Prop)).toOrderHom :=
  fun _ _ h => f.injective h

end RelHom

namespace OrderIso

section LE

variable [LE α] [LE β] [LE γ] [LE δ]

/-
**OrderIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (α ≃o β) α β :=
  inferInstance
/-
**OrderIso.** 是 Mathlib 中的一个实例，位于命名空间 `OrderIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : OrderIsoClass (α ≃o β) α β where
  map_le_map_iff f _ _ := f.map_rel_iff'

@[simp]
/-
**OrderIso.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：toFun_eq_coe {f : α ≃o β} : f.toFun = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe {f : α ≃o β} : f.toFun = f :=
  rfl

-- See note [partially-applied ext lemmas]
@[ext]
/-
**OrderIso.ext** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
参数：h : (f : α -> β) = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem ext {f g : α ≃o β} (h : (f : α → β) = g) : f = g :=
  DFunLike.coe_injective h

/-- Reinterpret an order isomorphism as an order embedding. -/
/-
**OrderIso.toOrderEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：toOrderEmbedding (e : α ≃o β) : α ↪o β
参数：e : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret an order isomorphism as an order embedding.
-/
def toOrderEmbedding (e : α ≃o β) : α ↪o β :=
  e.toRelEmbedding

@[simp]
/-
**OrderIso.coe_toOrderEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toOrderEmbedding (e : α ≃o β) : ⇑e.toOrderEmbedding = e :=
  rfl
/-
**OrderIso.bijective** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (e : α ≃o β)
, Function.Bijective ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : α ≃o β) : Function.Bijective e :=
  e.toEquiv.bijective
/-
**OrderIso.injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (e : α ≃o β)
, Function.Injective ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : α ≃o β) : Function.Injective e :=
  e.toEquiv.injective
/-
**OrderIso.surjective** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (e : α ≃o β)
, Function.Surjective ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : α ≃o β) : Function.Surjective e :=
  e.toEquiv.surjective
/-
**OrderIso.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_eq_iff_eq`：apply_eq_iff_eq (f : α ≃ β) {x y : α} : f x = f y
 ↔ x = y
-/
theorem apply_eq_iff_eq (e : α ≃o β) {x y : α} : e x = e y ↔ x = y :=
  e.toEquiv.apply_eq_iff_eq

/-- Identity order isomorphism. -/
/-
**OrderIso.refl** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：refl (α : Type*) [LE α] : α ≃o α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity order isomorphism.
-/
def refl (α : Type*) [LE α] : α ≃o α :=
  RelIso.refl (· ≤ ·)

@[simp]
/-
**OrderIso.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_refl : ⇑(refl α) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ⇑(refl α) = id :=
  rfl

@[simp]
/-
**OrderIso.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：refl_apply (x : α) : refl α x = x
参数：x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : α) : refl α x = x :=
  rfl

@[simp]
/-
**OrderIso.refl_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：refl_toEquiv : (refl α).toEquiv = Equiv.refl α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_toEquiv : (refl α).toEquiv = Equiv.refl α :=
  rfl

/-- Inverse of an order isomorphism. -/
/-
**OrderIso.symm** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：symm (e : α ≃o β) : β ≃o α
参数：e : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Inverse of an order isomorphism.
-/
def symm (e : α ≃o β) : β ≃o α := RelIso.symm e
/-
**OrderIso.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (e : α ≃ β) 
  (map_rel_iff' : ∀ {a b : α}, e a ≤ e b ↔ a ≤ b),   OrderIso.symm { toEquiv := 
e, map_rel_iff' := map_rel_iff' } = { toEquiv := e.symm, map_rel_iff' := ⋯ }
参数：e : α ≃ β；map_rel_iff' : ∀ {a b : α}, e a ≤ e b ↔ a ≤ b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_mk (e : α ≃ β) (map_rel_iff') :
    symm (.mk e map_rel_iff') = .mk e.symm (by simp [← map_rel_iff']) := rfl

@[simp]
/-
**OrderIso.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x
参数：e : α ≃o β；x : β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : α ≃o β) (x : β) : e (e.symm x) = x :=
  e.toEquiv.apply_symm_apply x

@[simp]
/-
**OrderIso.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x
参数：e : α ≃o β；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : α ≃o β) (x : α) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[simp]
/-
**OrderIso.symm_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_refl (α : Type*) [LE α] : (refl α).symm = refl α
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_refl (α : Type*) [LE α] : (refl α).symm = refl α :=
  rfl
/-
**OrderIso.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : α ≃o β) {x : α} {y : β} : e.symm y = x ↔ y = e x :=
  e.toEquiv.symm_apply_eq
/-
**OrderIso.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：eq_symm_apply (e : α ≃o β) {x : α} {y : β} : x = e.symm y ↔ e x = y
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : α ≃o β) {x : α} {y : β} : x = e.symm y ↔ e x = y :=
  e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/-
**OrderIso.apply_eq_iff_eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.
symm y
参数：e : α ≃o β；x : α；y : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `OrderIso.eq_symm_apply`：eq_symm_apply (e : α ≃o β) {x : α} {y : β} : x =
 e.symm y ↔ e x = y
-/
theorem apply_eq_iff_eq_symm_apply (e : α ≃o β) (x : α) (y : β) : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[simp]
/-
**OrderIso.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_symm (e : α ≃o β) : e.symm.symm = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : α ≃o β) : e.symm.symm = e := rfl
/-
**OrderIso.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_bijective : Function.Bijective (OrderIso.symm : (α ≃o β) -> β ≃o α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `OrderIso.symm_symm`：symm_symm (e : α ≃o β) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (OrderIso.symm : (α ≃o β) → β ≃o α) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**OrderIso.symm_injective** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_injective : Function.Injective (symm : α ≃o β -> β ≃o α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `OrderIso.symm_bijective`：symm_bijective : Function.Bijective (OrderIso.s
ymm : (α ≃o β) -> β ≃o α)
-/
theorem symm_injective : Function.Injective (symm : α ≃o β → β ≃o α) :=
  symm_bijective.injective

@[simp]
/-
**OrderIso.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：toEquiv_symm (e : α ≃o β) : e.symm.toEquiv = e.toEquiv.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm (e : α ≃o β) : e.symm.toEquiv = e.toEquiv.symm :=
  rfl

@[simp]
/-
**OrderIso.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_toEquiv (e : α ≃o β) : ⇑e.toEquiv = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEquiv (e : α ≃o β) : ⇑e.toEquiv = e := rfl

@[simp]
/-
**OrderIso.coe_symm_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_symm_toEquiv (e : α ≃o β) : ⇑e.toEquiv.symm = e.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_symm_toEquiv (e : α ≃o β) : ⇑e.toEquiv.symm = e.symm := rfl

/-- Composition of two order isomorphisms is an order isomorphism. -/
@[trans]
/-
**OrderIso.trans** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ
参数：e : α ≃o β；e' : β ≃o γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two order isomorphisms is an order isomorphism.
-/
def trans (e : α ≃o β) (e' : β ≃o γ) : α ≃o γ :=
  RelIso.trans e e'

@[simp]
/-
**OrderIso.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e
参数：e : α ≃o β；e' : β ≃o γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e : α ≃o β) (e' : β ≃o γ) : ⇑(e.trans e') = e' ∘ e :=
  rfl

@[simp]
/-
**OrderIso.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x)
参数：e : α ≃o β；e' : β ≃o γ；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e : α ≃o β) (e' : β ≃o γ) (x : α) : e.trans e' x = e' (e x) :=
  rfl

@[simp]
/-
**OrderIso.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：refl_trans (e : α ≃o β) : (refl α).trans e = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem refl_trans (e : α ≃o β) : (refl α).trans e = e := by
  ext x
  rfl

@[simp]
/-
**OrderIso.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：trans_refl (e : α ≃o β) : e.trans (refl β) = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem trans_refl (e : α ≃o β) : e.trans (refl β) = e := by
  ext x
  rfl

@[simp]
/-
**OrderIso.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) : (e₁.trans e₂).symm 
c = e₁.symm (e₂.symm c)
参数：e₁ : α ≃o β；e₂ : β ≃o γ；c : γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : α ≃o β) (e₂ : β ≃o γ) (c : γ) :
    (e₁.trans e₂).symm c = e₁.symm (e₂.symm c) :=
  rfl
/-
**OrderIso.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.tran
s e₁.symm
参数：e₁ : α ≃o β；e₂ : β ≃o γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (e₁ : α ≃o β) (e₂ : β ≃o γ) : (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
/-
**OrderIso.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：self_trans_symm (e : α ≃o β) : e.trans e.symm = OrderIso.refl α
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.self_trans_symm`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop} (e : r ≃r s), e.trans e.symm = RelIso.refl r
-/
theorem self_trans_symm (e : α ≃o β) : e.trans e.symm = OrderIso.refl α :=
  RelIso.self_trans_symm e

@[simp]
/-
**OrderIso.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：symm_trans_self (e : α ≃o β) : e.symm.trans e = OrderIso.refl β
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.symm_trans_self`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop} (e : r ≃r s), e.symm.trans e = RelIso.refl s
-/
theorem symm_trans_self (e : α ≃o β) : e.symm.trans e = OrderIso.refl β :=
  RelIso.symm_trans_self e
/-
**OrderIso.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：trans_assoc (f : α ≃o β) (g : β ≃o γ) (h : γ ≃o δ) : (f.trans g).trans h =
 f.trans (g.trans h)
参数：f : α ≃o β；g : β ≃o γ；h : γ ≃o δ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc (f : α ≃o β) (g : β ≃o γ) (h : γ ≃o δ) :
    (f.trans g).trans h = f.trans (g.trans h) :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- An order isomorphism between the domains and codomains of two prosets of
order homomorphisms gives an order isomorphism between the two function prosets. -/
@[simps apply symm_apply]
/-
**OrderIso.arrowCongr** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：arrowCongr {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ] (
f : α ≃o γ) (g : β ≃o δ) : (α ->o β) ≃o (γ ->o δ) where toFun p
参数：f : α ≃o γ；g : β ≃o δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An order isomorphism between the domains and codomains of two prosets of
order homomorphisms gives an order isomorphism between the two function prosets.
-/
def arrowCongr {α β γ δ} [Preorder α] [Preorder β] [Preorder γ] [Preorder δ]
    (f : α ≃o γ) (g : β ≃o δ) : (α →o β) ≃o (γ →o δ) where
  toFun p := .comp g <| .comp p f.symm
  invFun p := .comp g.symm <| .comp p f
  left_inv p := DFunLike.coe_injective <| by
    change (g.symm ∘ g) ∘ p ∘ (f.symm ∘ f) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.self_trans_symm, OrderIso.coe_refl, Function.comp_id]
  right_inv p := DFunLike.coe_injective <| by
    change (g ∘ g.symm) ∘ p ∘ (f ∘ f.symm) = p
    simp only [← OrderIso.coe_trans, Function.id_comp,
               OrderIso.symm_trans_self, OrderIso.coe_refl, Function.comp_id]
  map_rel_iff' {p q} := by
    simp only [Equiv.coe_fn_mk, OrderHom.le_def, OrderHom.comp_coe,
               OrderHomClass.coe_coe, Function.comp_apply, map_le_map_iff]
    exact Iff.symm f.forall_congr_left

/-- If `α` and `β` are order-isomorphic then the two orders of order-homomorphisms
from `α` and `β` to themselves are order-isomorphic. -/
@[simps! apply symm_apply]
/-
**OrderIso.conj** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α ->o α) ≃ (β ->o β)
参数：f : α ≃o β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α` and `β` are order-isomorphic then the two orders of order-homomorphisms
from `α` and `β` to themselves are order-isomorphic.
-/
def conj {α β} [Preorder α] [Preorder β] (f : α ≃o β) : (α →o α) ≃ (β →o β) :=
  arrowCongr f f

/-- Transport an `OrderEmbedding` across a pair of `OrderIso`s, by pre- and post-composition.

This is `Equiv.embeddingCongr`/`RelIso.relEmbeddingCongr` for `OrderEmbedding`. -/
/-
**OrderIso.orderEmbeddingCongr** 是 Mathlib 中的一个缩写定义，位于命名空间 `OrderIso`。
形式化陈述：orderEmbeddingCongr (f : α ≃o γ) (g : β ≃o δ) : (α ↪o β) ≃ (γ ↪o δ)
参数：f : α ≃o γ；g : β ≃o δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport an `OrderEmbedding` across a pair of `OrderIso`s, by pre- and post-com
position.

This is `Equiv.embeddingCongr`/`RelIso.relEmbeddingCongr` for `OrderEmbedding`.
-/
abbrev orderEmbeddingCongr (f : α ≃o γ) (g : β ≃o δ) : (α ↪o β) ≃ (γ ↪o δ) :=
  RelIso.relEmbeddingCongr f g

@[simp]
/-
**OrderIso.orderEmbeddingCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：orderEmbeddingCongr_apply (f : α ≃o γ) (g : β ≃o δ) (h : α ↪o β) : orderEm
beddingCongr f g h = .trans (.trans f.symm h) g
参数：f : α ≃o γ；g : β ≃o δ；h : α ↪o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderEmbeddingCongr_apply (f : α ≃o γ) (g : β ≃o δ) (h : α ↪o β) :
    orderEmbeddingCongr f g h = .trans (.trans f.symm h) g :=
  rfl

@[simp]
/-
**OrderIso.orderEmbeddingCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：orderEmbeddingCongr_symm_apply (f : α ≃o γ) (g : β ≃o δ) (h : γ ↪o δ) : (o
rderEmbeddingCongr f g).symm h = .trans (.trans f h) g.symm
参数：f : α ≃o γ；g : β ≃o δ；h : γ ↪o δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem orderEmbeddingCongr_symm_apply (f : α ≃o γ) (g : β ≃o δ) (h : γ ↪o δ) :
    (orderEmbeddingCongr f g).symm h = .trans (.trans f h) g.symm :=
  rfl

/-- Transport an `OrderIso` across a pair of `OrderIso`s, by pre- and post-composition.

This is `Equiv.equivCongr`/`RelIso.relIsoCongr` for `OrderIso`. -/
/-
**OrderIso.orderIsoCongr** 是 Mathlib 中的一个缩写定义，位于命名空间 `OrderIso`。
形式化陈述：orderIsoCongr (f : α ≃o γ) (g : β ≃o δ) : (α ≃o β) ≃ (γ ≃o δ)
参数：f : α ≃o γ；g : β ≃o δ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport an `OrderIso` across a pair of `OrderIso`s, by pre- and post-compositi
on.

This is `Equiv.equivCongr`/`RelIso.relIsoCongr` for `OrderIso`.
-/
abbrev orderIsoCongr (f : α ≃o γ) (g : β ≃o δ) : (α ≃o β) ≃ (γ ≃o δ) :=
  RelIso.relIsoCongr f g

@[simp]
/-
**OrderIso.orderIsoCongr_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：orderIsoCongr_apply (f : α ≃o γ) (g : β ≃o δ) (h : α ≃o β) : orderIsoCongr
 f g h = .trans (.trans f.symm h) g
参数：f : α ≃o γ；g : β ≃o δ；h : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem orderIsoCongr_apply (f : α ≃o γ) (g : β ≃o δ) (h : α ≃o β) :
    orderIsoCongr f g h = .trans (.trans f.symm h) g :=
  rfl

@[simp]
/-
**OrderIso.orderIsoCongr_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：orderIsoCongr_symm_apply (f : α ≃o γ) (g : β ≃o δ) (h : γ ≃o δ) : (orderIs
oCongr f g).symm h = .trans (.trans f h) g.symm
参数：f : α ≃o γ；g : β ≃o δ；h : γ ≃o δ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem orderIsoCongr_symm_apply (f : α ≃o γ) (g : β ≃o δ) (h : γ ≃o δ) :
    (orderIsoCongr f g).symm h = .trans (.trans f h) g.symm :=
  rfl

/-- A surjective order embedding is an order isomorphism. -/
@[simps!]
/-
**OrderIso.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：ofSurjective (f : α ↪o β) (hf : Function.Surjective f) : α ≃o β
参数：f : α ↪o β；hf : Function.Surjective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A surjective order embedding is an order isomorphism.
-/
noncomputable def ofSurjective (f : α ↪o β) (hf : Function.Surjective f) : α ≃o β :=
  RelIso.ofSurjective f hf

/-- Surjective order embeddings are equivalent to order isomorphisms. -/
@[simps apply symm_apply]
/-
**OrderIso.equivEmbeddingSurjective** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：equivEmbeddingSurjective : α ≃o β ≃ { f : α ↪o β // Function.Surjective f 
} where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.surjective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst
_1 : LE β] (e : α ≃o β), Function.Surjective ⇑e

--- 原说明 ---
Surjective order embeddings are equivalent to order isomorphisms.
-/
noncomputable def equivEmbeddingSurjective :
    α ≃o β ≃ { f : α ↪o β // Function.Surjective f } where
  toFun f := ⟨f, f.surjective⟩
  invFun f := ofSurjective f f.prop
  left_inv _ := by ext; rfl
  right_inv _ := rfl

/-- `Prod.swap` as an `OrderIso`. -/
/-
**OrderIso.prodComm** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：prodComm : α × β ≃o β × α where toEquiv
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.swap_le_swap`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1
 : LE β] {x y : α × β}, x.swap ≤ y.swap ↔ x ≤ y

--- 原说明 ---
`Prod.swap` as an `OrderIso`.
-/
def prodComm : α × β ≃o β × α where
  toEquiv := Equiv.prodComm α β
  map_rel_iff' := Prod.swap_le_swap

set_option backward.isDefEq.respectTransparency false in
/-- `Equiv.prodAssoc` promoted to an order isomorphism. -/
@[simps! (attr := grind =)]
/-
**OrderIso.prodAssoc** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：prodAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] : (α × β) × γ ≃o α × (β × γ
) where toEquiv
参数：α β γ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.prodAssoc` promoted to an order isomorphism.
-/
def prodAssoc (α β γ : Type*) [LE α] [LE β] [LE γ] :
    (α × β) × γ ≃o α × (β × γ) where
  toEquiv := .prodAssoc α β γ
  map_rel_iff' := @fun ⟨⟨_, _⟩, _⟩ ⟨⟨_, _⟩, _⟩ ↦ by simp [Equiv.prodAssoc, and_assoc]

@[simp]
/-
**OrderIso.coe_prodComm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_prodComm : ⇑(prodComm : α × β ≃o β × α) = Prod.swap :=
  rfl

@[simp]
/-
**OrderIso.prodComm_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem prodComm_symm : (prodComm : α × β ≃o β × α).symm = prodComm :=
  rfl

variable (α)

/-- The order isomorphism between a type and its double dual. -/
/-
**OrderIso.dualDual** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：dualDual : α ≃o αᵒᵈᵒᵈ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism between a type and its double dual.
-/
def dualDual : α ≃o αᵒᵈᵒᵈ :=
  refl α

@[simp]
/-
**OrderIso.coe_dualDual** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_dualDual : ⇑(dualDual α) = toDual ∘ toDual :=
  rfl

@[simp]
/-
**OrderIso.coe_dualDual_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_dualDual_symm : ⇑(dualDual α).symm = ofDual ∘ ofDual :=
  rfl

variable {α}

@[simp]
/-
**OrderIso.dualDual_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：dualDual_apply (a : α) : dualDual α a = toDual (toDual a)
参数：a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dualDual_apply (a : α) : dualDual α a = toDual (toDual a) :=
  rfl

@[simp]
/-
**OrderIso.dualDual_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a)
参数：a : αᵒᵈᵒᵈ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem dualDual_symm_apply (a : αᵒᵈᵒᵈ) : (dualDual α).symm a = ofDual (ofDual a) :=
  rfl

end LE

open Set

section LE

variable [LE α] [LE β]

@[gcongr, to_dual self]
/-
**OrderIso.le_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <= y
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
-/
theorem le_iff_le (e : α ≃o β) {x y : α} : e x ≤ e y ↔ x ≤ y :=
  e.map_rel_iff

@[to_dual symm_apply_le]
/-
**OrderIso.le_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：le_symm_apply (e : α ≃o β) {x : α} {y : β} : x <= e.symm y ↔ e x <= y
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.rel_symm_apply`：rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y
) ↔ s (e x) y
-/
theorem le_symm_apply (e : α ≃o β) {x : α} {y : β} : x ≤ e.symm y ↔ e x ≤ y :=
  e.rel_symm_apply

end LE

variable [Preorder α] [Preorder β]

/-
**OrderIso.monotone** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ≃o β), Monotone ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
protected theorem monotone (e : α ≃o β) : Monotone e :=
  e.toOrderEmbedding.monotone
/-
**OrderIso.strictMono** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [inst_1 : Preorder β] 
(e : α ≃o β), StrictMono ⇑e
参数：e : α ≃o β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preor
der α] [inst_1 : Preorder β] (f : α ↪o β), StrictMono ⇑f
-/
protected theorem strictMono (e : α ≃o β) : StrictMono e :=
  e.toOrderEmbedding.strictMono

@[simp, gcongr, to_dual self]
/-
**OrderIso.lt_iff_lt** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderEmbedding.lt_iff_lt`：lt_iff_lt {a b} : f a < f b ↔ a < b
-/
theorem lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y :=
  e.toOrderEmbedding.lt_iff_lt

@[to_dual symm_apply_lt]
/-
**OrderIso.lt_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x < e.symm y ↔ e x < y
参数：e : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_symm_apply (e : α ≃o β) {x : α} {y : β} : x < e.symm y ↔ e x < y := by
  rw [← e.lt_iff_lt, e.apply_symm_apply]

/-- Converts an `OrderIso` into a `RelIso (<) (<)`. -/
@[to_dual /-- Converts an `OrderIso` into a `RelIso (>) (>)`. -/]
/-
**OrderIso.toRelIsoLT** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：toRelIsoLT (e : α ≃o β) : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β 
-> Prop)
参数：e : α ≃o β。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.lt_iff_lt`：lt_iff_lt (e : α ≃o β) {x y : α} : e x < e y ↔ x < y

--- 原说明 ---
Converts an `OrderIso` into a `RelIso (<) (<)`.
-/
def toRelIsoLT (e : α ≃o β) : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop) :=
  ⟨e.toEquiv, lt_iff_lt e⟩

@[to_dual (attr := simp)]
/-
**OrderIso.toRelIsoLT_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x
参数：e : α ≃o β；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRelIsoLT_apply (e : α ≃o β) (x : α) : e.toRelIsoLT x = e x :=
  rfl

@[to_dual]
/-
**OrderIso.toRelIsoLT_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：toRelIsoLT_symm (e : α ≃o β) : e.symm.toRelIsoLT = e.toRelIsoLT.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toRelIsoLT_symm (e : α ≃o β) : e.symm.toRelIsoLT = e.toRelIsoLT.symm :=
  rfl

@[to_dual (attr := simp)]
/-
**OrderIso.coe_toRelIsoLT** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT = e := rfl

@[to_dual (attr := simp)]
/-
**OrderIso.coe_symm_toRelIsoLT** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：coe_symm_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT.symm = e.symm
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_symm_toRelIsoLT (e : α ≃o β) : ⇑e.toRelIsoLT.symm = e.symm := rfl

/-- Converts a `RelIso (<) (<)` into an `OrderIso`. -/
/-
**OrderIso.ofRelIsoLT** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : ((· < ·) : α -> α 
-> Prop) ≃r ((· < ·) : β -> β -> Prop)) : α ≃o β
参数：e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Converts a `RelIso (<) (<)` into an `OrderIso`.
-/
def ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : α ≃o β :=
  ⟨e.toEquiv, by simp [le_iff_eq_or_lt, e.map_rel_iff, e.injective.eq_iff]⟩

@[simp]
/-
**OrderIso.ofRelIsoLT_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β] (e : ((· < ·) : α
 -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) (x : α) : ofRelIsoLT e x = e x
参数：e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)；x : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRelIsoLT_apply {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) (x : α) : ofRelIsoLT e x = e x :=
  rfl

@[simp]
/-
**OrderIso.ofRelIsoLT_symm** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β] (e : ((· < ·) : α 
-> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) : (ofRelIsoLT e).symm = ofRelIsoLT 
e.symm
参数：e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofRelIsoLT_symm {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) :
    (ofRelIsoLT e).symm = ofRelIsoLT e.symm :=
  rfl

@[simp]
/-
**OrderIso.ofRelIsoLT_toRelIsoLT** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β)
 : ofRelIsoLT (toRelIsoLT e) = e
参数：e : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.ext`：ext {f g : α ≃o β} (h : (f : α -> β) = g) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem ofRelIsoLT_toRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : α ≃o β) :
    ofRelIsoLT (toRelIsoLT e) = e := by
  ext
  simp

@[simp]
/-
**OrderIso.toRelIsoLT_ofRelIsoLT** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β] (e : ((· < ·
) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)) : toRelIsoLT (ofRelIsoLT e) =
 e
参数：e : ((· < ·) : α -> α -> Prop) ≃r ((· < ·) : β -> β -> Prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toRelIsoLT_ofRelIsoLT {α β} [PartialOrder α] [PartialOrder β]
    (e : ((· < ·) : α → α → Prop) ≃r ((· < ·) : β → β → Prop)) : toRelIsoLT (ofRelIsoLT e) = e := by
  ext
  simp

/-- To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear orders,
it suffices to prove `cmp a (g b) = cmp (f a) b`. -/
/-
**OrderIso.ofCmpEqCmp** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α -> β) (g : β -> α)
 (h : forall (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β
参数：f : α -> β；g : β -> α；h : forall (a : α) (b : β), cmp a (g b) = cmp (f a) b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that `f : α → β`, `g : β → α` make up an order isomorphism of linear ord
ers,
it suffices to prove `cmp a (g b) = cmp (f a) b`.
-/
def ofCmpEqCmp {α β} [LinearOrder α] [LinearOrder β] (f : α → β) (g : β → α)
    (h : ∀ (a : α) (b : β), cmp a (g b) = cmp (f a) b) : α ≃o β :=
  have gf : ∀ a : α, a = g (f a) := by
    intro
    rw [← cmp_eq_eq_iff, h, cmp_self_eq_eq]
  { toFun := f, invFun := g, left_inv := fun a => (gf a).symm,
    right_inv := by
      intro
      rw [← cmp_eq_eq_iff, ← h, cmp_self_eq_eq],
    map_rel_iff' := by
      intro a b
      apply le_iff_le_of_cmp_eq_cmp
      convert! (h a (f b)).symm
      apply gf }

/-- To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is enough to show
that `g` is the inverse of `f`. -/
@[simps apply]
/-
**OrderIso.ofHomInv** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：ofHomInv (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ : g.comp f 
= .id) : α ≃o β where toFun
参数：f : α ->o β；g : β ->o α；h₁ : f.comp g = .id；h₂ : g.comp f = .id。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show that `f : α →o β` and `g : β →o α` make up an order isomorphism it is en
ough to show
that `g` is the inverse of `f`.
-/
def ofHomInv (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id) :
    α ≃o β where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₂
  right_inv := DFunLike.congr_fun h₁
  map_rel_iff' :=
    { mp h := by simpa [h₂] using show g.comp f _ ≤ g.comp f _ from map_rel g h
      mpr h := f.monotone h }

@[simp]
/-
**OrderIso.ofHomInv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：ofHomInv_symm_apply (f : α ->o β) (g : β ->o α) (h₁ : f.comp g = .id) (h₂ 
: g.comp f = .id) (a : β) : (ofHomInv f g h₁ h₂).symm a = g a
参数：f : α ->o β；g : β ->o α；h₁ : f.comp g = .id；h₂ : g.comp f = .id；a : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofHomInv_symm_apply (f : α →o β) (g : β →o α) (h₁ : f.comp g = .id) (h₂ : g.comp f = .id)
    (a : β) : (ofHomInv f g h₁ h₂).symm a = g a := rfl

/-- Order isomorphism between `α → β` and `β`, where `α` has a unique element. -/
@[simps! toEquiv apply]
/-
**OrderIso.funUnique** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：funUnique (α β : Type*) [Unique α] [Preorder β] : (α -> β) ≃o β where toEq
uiv
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Order isomorphism between `α → β` and `β`, where `α` has a unique element.
-/
def funUnique (α β : Type*) [Unique α] [Preorder β] : (α → β) ≃o β where
  toEquiv := Equiv.funUnique α β
  map_rel_iff' := by simp [Pi.le_def, Unique.forall_iff]

@[simp]
/-
**OrderIso.funUnique_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：funUnique_symm_apply {α β : Type*} [Unique α] [Preorder β] : ((funUnique α
 β).symm : β -> α -> β) = Function.const α
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem funUnique_symm_apply {α β : Type*} [Unique α] [Preorder β] :
    ((funUnique α β).symm : β → α → β) = Function.const α :=
  rfl

/-- The order isomorphism `α ≃o β` when `α` and `β` are preordered types
containing unique elements. -/
@[simps!]
/-
**OrderIso.ofUnique** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：ofUnique (α β : Type*) [Unique α] [Unique β] [Preorder α] [Preorder β] : α
 ≃o β where toEquiv
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order isomorphism `α ≃o β` when `α` and `β` are preordered types
containing unique elements.
-/
noncomputable def ofUnique
    (α β : Type*) [Unique α] [Unique β] [Preorder α] [Preorder β] :
    α ≃o β where
  toEquiv := Equiv.ofUnique α β
  map_rel_iff' := by simp

/-- `Equiv.equivOfIsEmpty` promoted to an `OrderIso`. -/
/-
**OrderIso.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：ofIsEmpty (α β : Type*) [Preorder α] [Preorder β] [IsEmpty α] [IsEmpty β] 
: α ≃o β
参数：α β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Equiv.equivOfIsEmpty` promoted to an `OrderIso`.
-/
def ofIsEmpty (α β : Type*) [Preorder α] [Preorder β] [IsEmpty α] [IsEmpty β] : α ≃o β :=
  ⟨Equiv.equivOfIsEmpty α β, @isEmptyElim _ _ _⟩

end OrderIso

namespace Equiv

variable [Preorder α] [Preorder β]

/-- If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism. -/
/-
**Equiv.toOrderIso** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β
参数：e : α ≃ β；h₁ : Monotone e；h₂ : Monotone e.symm。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If `e` is an equivalence with monotone forward and inverse maps, then `e` is an
order isomorphism.
-/
def toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : α ≃o β :=
  ⟨e, ⟨fun h => by simpa only [e.symm_apply_apply] using h₂ h, fun h => h₁ h⟩⟩

@[simp]
/-
**Equiv.coe_toOrderIso** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : ⇑(e.
toOrderIso h₁ h₂) = e
参数：e : α ≃ β；h₁ : Monotone e；h₂ : Monotone e.symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem coe_toOrderIso (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    ⇑(e.toOrderIso h₁ h₂) = e :=
  rfl

@[simp]
/-
**Equiv.toOrderIso_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) : 
(e.toOrderIso h₁ h₂).toEquiv = e
参数：e : α ≃ β；h₁ : Monotone e；h₂ : Monotone e.symm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toOrderIso_toEquiv (e : α ≃ β) (h₁ : Monotone e) (h₂ : Monotone e.symm) :
    (e.toOrderIso h₁ h₂).toEquiv = e :=
  rfl

end Equiv

namespace StrictMono

variable [LinearOrder α] [Preorder β]
variable (f : α → β) (h_mono : StrictMono f)

/-- A strictly monotone function with a right inverse is an order isomorphism. -/
@[simps -fullyApplied]
/-
**StrictMono.orderIsoOfRightInverse** 是 Mathlib 中的一个定义，位于命名空间 `StrictMono`。
形式化陈述：orderIsoOfRightInverse (g : β -> α) (hg : Function.RightInverse g f) : α ≃
o β
参数：g : β -> α；hg : Function.RightInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A strictly monotone function with a right inverse is an order isomorphism.
-/
def orderIsoOfRightInverse (g : β → α) (hg : Function.RightInverse g f) : α ≃o β :=
  { OrderEmbedding.ofStrictMono f h_mono with
    toFun := f,
    invFun := g,
    left_inv := fun _ => h_mono.injective <| hg _,
    right_inv := hg }

end StrictMono

/-- An order isomorphism is also an order isomorphism between dual orders. -/
/-
**OrderIso.dual** 是 Mathlib 中的一个定义，位于命名空间 `OrderIso`。
形式化陈述：{α : Type u_2} → {β : Type u_3} → [inst : LE α] → [inst_1 : LE β] → α ≃o β
 → αᵒᵈ ≃o βᵒᵈ
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y

--- 原说明 ---
An order isomorphism is also an order isomorphism between dual orders.
-/
protected def OrderIso.dual [LE α] [LE β] (f : α ≃o β) : αᵒᵈ ≃o βᵒᵈ :=
  ⟨f.toEquiv, f.le_iff_le⟩

section
variable [LE α] [LE β] (f : α ≃o β)

/-
**OrderIso.dual_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (f : α ≃o β)
 (x : αᵒᵈ),   f.dual x = OrderDual.toDual (f (OrderDual.ofDual x))
参数：f : α ≃o β；x : αᵒᵈ；f (OrderDual.ofDual x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma OrderIso.dual_apply (x) : f.dual x = .toDual (f x.ofDual) := rfl
/-
**OrderIso.dual_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (f : α ≃o β)
 (x : βᵒᵈ),   f.dual.symm x = OrderDual.toDual (f.symm (OrderDual.ofDual x))
参数：f : α ≃o β；x : βᵒᵈ；f.symm (OrderDual.ofDual x)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma OrderIso.dual_symm_apply (x) : f.dual.symm x = .toDual (f.symm x.ofDual) := rfl
/-
**OrderIso.symm_dual** 是 Mathlib 中的一个定理，位于命名空间 `OrderIso`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 : LE β] (f : α ≃o β)
, f.symm.dual = f.dual.symm
参数：f : α ≃o β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma OrderIso.symm_dual : f.symm.dual = f.dual.symm := rfl

end

section LatticeIsos

@[to_dual]
/-
**OrderIso.map_bot'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx
 : forall x', x <= x') (hy : forall y', y <= y') : f x = y
参数：f : α ≃o β；hx : forall x', x <= x'；hy : forall y', y <= y'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
-/
theorem OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β) {x : α} {y : β} (hx : ∀ x', x ≤ x')
    (hy : ∀ y', y ≤ y') : f x = y := by
  refine le_antisymm ?_ (hy _)
  rw [← f.apply_symm_apply y, f.le_iff_le]
  apply hx

@[to_dual]
/-
**OrderIso.map_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α 
≃o β) : f ⊥ = ⊥
参数：f : α ≃o β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.map_bot'`：OrderIso.map_bot' [LE α] [PartialOrder β] (f : α ≃o β
) {x : α} {y : β} (hx : forall x', x <= x') (hy : forall y', y <= y') : f x = y
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] [OrderBot β] (f : α ≃o β) : f ⊥ = ⊥ :=
  f.map_bot' (fun _ => bot_le) fun _ => bot_le

@[to_dual le_map_sup]
/-
**OrderEmbedding.map_inf_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o 
β) (x y : α) : f (x ⊓ y) <= f x ⊓ f y
参数：f : α ↪o β；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.map_inf_le`：∀ {α : Type u} {β : Type v} [inst : SemilatticeInf 
α] [inst_1 : SemilatticeInf β] {f : α → β},   Monotone f → ∀ (x y : α), f (x ⊓ y
) ≤ f x ⊓…
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
-/
theorem OrderEmbedding.map_inf_le [SemilatticeInf α] [SemilatticeInf β] (f : α ↪o β) (x y : α) :
    f (x ⊓ y) ≤ f x ⊓ f y :=
  f.monotone.map_inf_le x y

@[to_dual]
/-
**OrderIso.map_inf** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y :
 α) : f (x ⊓ y) = f x ⊓ f y
参数：f : α ≃o β；x y : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `OrderEmbedding.map_inf_le`：OrderEmbedding.map_inf_le [SemilatticeInf α] 
[SemilatticeInf β] (f : α ↪o β) (x y : α) : f (x ⊓ y) <= f x ⊓ f y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `OrderIso.le_iff_le`：le_iff_le (e : α ≃o β) {x y : α} : e x <= e y ↔ x <=
 y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
theorem OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β] (f : α ≃o β) (x y : α) :
    f (x ⊓ y) = f x ⊓ f y := by
  refine (f.toOrderEmbedding.map_inf_le x y).antisymm ?_
  apply f.symm.le_iff_le.1
  simpa using f.symm.toOrderEmbedding.map_inf_le (f x) (f y)

@[to_dual]
/-
**OrderIso.isMax_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.isMax_apply {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) 
{x : α} : IsMax (f x) ↔ IsMax x
参数：f : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.isMax_of_apply`：StrictMono.isMax_of_apply (hf : StrictMono f)
 (ha : IsMax (f a)) : IsMax a
· 使用定理 `OrderIso.strictMono`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α]
 [inst_1 : Preorder β] (e : α ≃o β), StrictMono ⇑e
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem OrderIso.isMax_apply {α β : Type*} [Preorder α] [Preorder β] (f : α ≃o β) {x : α} :
    IsMax (f x) ↔ IsMax x := by
  refine ⟨f.strictMono.isMax_of_apply, ?_⟩
  conv_lhs => rw [← f.symm_apply_apply x]
  exact f.symm.strictMono.isMax_of_apply

/-- Note that this goal could also be stated `(Disjoint on f) a b` -/
/-
**Disjoint.map_orderIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [
OrderBot β] {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b)
参数：f : α ≃o β；ha : Disjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_inf`：OrderIso.map_inf [SemilatticeInf α] [SemilatticeInf β]
 (f : α ≃o β) (x y : α) : f (x ⊓ y) = f x ⊓ f y
· 使用定理 `OrderIso.map_bot`：OrderIso.map_bot [LE α] [PartialOrder β] [OrderBot α] 
[OrderBot β] (f : α ≃o β) : f ⊥ = ⊥
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥

--- 原说明 ---
Note that this goal could also be stated `(Disjoint on f) a b`
-/
theorem Disjoint.map_orderIso [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) (ha : Disjoint a b) : Disjoint (f a) (f b) := by
  rw [disjoint_iff_inf_le, ← f.map_inf, ← f.map_bot]
  exact f.monotone ha.le_bot

/-- Note that this goal could also be stated `(Codisjoint on f) a b` -/
@[to_dual existing] -- We can remove this use of `existing` once we get https://github.com/leanprover-community/mathlib4/pull/32438
/-
**Codisjoint.map_orderIso** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β]
 [OrderTop β] {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f
 b)
参数：f : α ≃o β；ha : Codisjoint a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `codisjoint_iff_le_sup`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_
1 : OrderTop α] {a b : α}, Codisjoint a b ↔ ⊤ ≤ a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.map_sup`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup
 α] [inst_1 : SemilatticeSup β] (f : α ≃o β) (x y : α),   f (x ⊔ y) = f x ⊔ f y
· 使用定理 `OrderIso.map_top`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_1 
: PartialOrder β] [inst_2 : OrderTop α] [inst_3 : OrderTop β]   (f : α ≃o β), f 
⊤ = ⊤
· 使用定理 `OrderIso.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (e : α ≃o β), Monotone ⇑e
· 使用定理 `Codisjoint.top_le`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : 
OrderTop α] {a b : α}, Codisjoint a b → ⊤ ≤ a ⊔ b

--- 原说明 ---
Note that this goal could also be stated `(Codisjoint on f) a b`
-/
theorem Codisjoint.map_orderIso [SemilatticeSup α] [OrderTop α] [SemilatticeSup β] [OrderTop β]
    {a b : α} (f : α ≃o β) (ha : Codisjoint a b) : Codisjoint (f a) (f b) := by
  rw [codisjoint_iff_le_sup, ← f.map_sup, ← f.map_top]
  exact f.monotone ha.top_le

@[to_dual (attr := simp)]
/-
**disjoint_map_orderIso_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf 
β] [OrderBot β] {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b
参数：f : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.map_orderIso`：Disjoint.map_orderIso [SemilatticeInf α] [OrderBo
t α] [SemilatticeInf β] [OrderBot β] {a b : α} (f : α ≃o β) (ha : Disjoint a b) 
: Disjoint …
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem disjoint_map_orderIso_iff [SemilatticeInf α] [OrderBot α] [SemilatticeInf β] [OrderBot β]
    {a b : α} (f : α ≃o β) : Disjoint (f a) (f b) ↔ Disjoint a b :=
  ⟨fun h => f.symm_apply_apply a ▸ f.symm_apply_apply b ▸ h.map_orderIso f.symm,
   fun h => h.map_orderIso f⟩

section BoundedOrder

variable [Lattice α] [Lattice β] [BoundedOrder α] [BoundedOrder β] (f : α ≃o β)

/-
**OrderIso.isCompl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y)
参数：h : IsCompl x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.map_orderIso`：Disjoint.map_orderIso [SemilatticeInf α] [OrderBo
t α] [SemilatticeInf β] [OrderBot β] {a b : α} (f : α ≃o β) (ha : Disjoint a b) 
: Disjoint …
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Codisjoint.map_orderIso`：Codisjoint.map_orderIso [SemilatticeSup α] [Ord
erTop α] [SemilatticeSup β] [OrderTop β] {a b : α} (f : α ≃o β) (ha : Codisjoint
 a b) : Codis…
· 使用定理 `IsCompl.codisjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : B
oundedOrder α] {x y : α}, IsCompl x y → Codisjoint x y
-/
theorem OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl (f x) (f y) :=
  ⟨h.1.map_orderIso _, h.2.map_orderIso _⟩
/-
**OrderIso.isCompl_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isCompl`：OrderIso.isCompl {x y : α} (h : IsCompl x y) : IsCompl
 (f x) (f y)
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsCompl (f x) (f y) :=
  ⟨f.isCompl, fun h => f.symm_apply_apply x ▸ f.symm_apply_apply y ▸ f.symm.isCompl h⟩
/-
**OrderIso.complementedLattice** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.complementedLattice [ComplementedLattice α] (f : α ≃o β) : Comple
mentedLattice β
参数：f : α ≃o β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ComplementedLattice.exists_isCompl`：∀ {α : Type u_2} {inst : Lattice α} 
{inst_1 : BoundedOrder α} [self : ComplementedLattice α] (a : α), ∃ b, IsCompl a
 b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `OrderIso.isCompl_iff`：OrderIso.isCompl_iff {x y : α} : IsCompl x y ↔ IsC
ompl (f x) (f y)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.symm_apply_apply`：symm_apply_apply (e : α ≃o β) (x : α) : e.sym
m (e x) = x
-/
theorem OrderIso.complementedLattice [ComplementedLattice α] (f : α ≃o β) : ComplementedLattice β :=
  ⟨fun x => by
    obtain ⟨y, hy⟩ := exists_isCompl (f.symm x)
    rw [← f.symm_apply_apply y] at hy
    exact ⟨f y, f.symm.isCompl_iff.2 hy⟩⟩
/-
**OrderIso.complementedLattice_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：OrderIso.complementedLattice_iff (f : α ≃o β) : ComplementedLattice α ↔ Co
mplementedLattice β
参数：f : α ≃o β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.complementedLattice`：OrderIso.complementedLattice [Complemented
Lattice α] (f : α ≃o β) : ComplementedLattice β
-/
theorem OrderIso.complementedLattice_iff (f : α ≃o β) :
    ComplementedLattice α ↔ ComplementedLattice β :=
  ⟨by intro; exact f.complementedLattice,
   by intro; exact f.symm.complementedLattice⟩

end BoundedOrder

end LatticeIsos

section DenselyOrdered

-- could live in a more upstream file, but hard to find a good place
/-
**StrictMono.denselyOrdered_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：StrictMono.denselyOrdered_range {X Y : Type*} [LinearOrder X] [DenselyOrde
red X] [Preorder Y] {f : X -> Y} (hf : StrictMono f) : DenselyOrdered (Set.range
 f)
参数：hf : StrictMono f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.substr`：∀ {α : Sort u} {p : α → Prop} {a b : α}, b = a → p a → p b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `StrictMono.lt_iff_lt`：StrictMono.lt_iff_lt (hf : StrictMono f) {a b : α}
 : f a < f b ↔ a < b
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
-/
lemma StrictMono.denselyOrdered_range {X Y : Type*} [LinearOrder X] [DenselyOrdered X] [Preorder Y]
    {f : X → Y} (hf : StrictMono f) :
    DenselyOrdered (Set.range f) := by
  constructor
  simpa [← exists_and_left, ← exists_and_right, exists_comm, hf.lt_iff_lt]
    using fun _ _ ↦ exists_between
/-
**denselyOrdered_iff_of_orderIsoClass** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：denselyOrdered_iff_of_orderIsoClass {X Y F : Type*} [Preorder X] [Preorder
 Y] [EquivLike F X Y] [OrderIsoClass F X Y] (f : F) : DenselyOrdered X ↔ Densely
Ordered Y
参数：f : F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_inv_lt_map_inv_iff`：map_inv_lt_map_inv_iff (f : F) {a b : β} : Equiv
Like.inv f b < EquivLike.inv f a ↔ b < a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_lt_map_iff`：map_lt_map_iff (f : F) {a b : α} : f a < f b ↔ a < b
-/
lemma denselyOrdered_iff_of_orderIsoClass {X Y F : Type*} [Preorder X] [Preorder Y]
    [EquivLike F X Y] [OrderIsoClass F X Y] (f : F) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  constructor
  · intro H
    refine ⟨fun a b h ↦ ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_inv_lt_map_inv_iff f).mpr h)
    exact ⟨f c, by simpa using hc⟩
  · intro H
    refine ⟨fun a b h ↦ ?_⟩
    obtain ⟨c, hc⟩ := exists_between ((map_lt_map_iff f).mpr h)
    exact ⟨EquivLike.inv f c, by simpa using hc⟩
/-
**denselyOrdered_iff_of_strictAnti** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：denselyOrdered_iff_of_strictAnti {X Y F : Type*} [LinearOrder X] [Preorder
 Y] [EquivLike F X Y] (f : F) (hf : StrictAnti f) : DenselyOrdered X ↔ DenselyOr
dered Y
参数：f : F；hf : StrictAnti f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `denselyOrdered_orderDual`：denselyOrdered_orderDual [LT α] : DenselyOrder
ed αᵒᵈ ↔ DenselyOrdered α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `StrictAnti.le_iff_ge`：StrictAnti.le_iff_ge (hf : StrictAnti f) {a b : α}
 : f a <= f b ↔ b <= a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `denselyOrdered_iff_of_orderIsoClass`：denselyOrdered_iff_of_orderIsoClass
 {X Y F : Type*} [Preorder X] [Preorder Y] [EquivLike F X Y] [OrderIsoClass F X 
Y] (f : F) : DenselyOrder…
· 使用定理 `OrderIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α
] [inst_1 : LE β], OrderIsoClass (α ≃o β) α β
-/
lemma denselyOrdered_iff_of_strictAnti {X Y F : Type*} [LinearOrder X] [Preorder Y]
    [EquivLike F X Y] (f : F) (hf : StrictAnti f) :
    DenselyOrdered X ↔ DenselyOrdered Y := by
  rw [← denselyOrdered_orderDual]
  let e : Xᵒᵈ ≃o Y := ⟨OrderDual.ofDual.trans (f : X ≃ Y), ?_⟩
  · exact denselyOrdered_iff_of_orderIsoClass e
  · simp only [Equiv.trans_apply, EquivLike.coe_coe, OrderDual.forall, OrderDual.ofDual_toDual,
      OrderDual.toDual_le_toDual]
    intro a b
    rw [hf.le_iff_ge]

end DenselyOrdered

universe v u in
/-- The bijection `ULift.{v} α ≃ α` as an isomorphism of orders. -/
@[pp_with_univ, simps!]
/-
**ULift.orderIso** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ULift.orderIso {α : Type u} [Preorder α] : ULift.{v} α ≃o α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The bijection `ULift.{v} α ≃ α` as an isomorphism of orders.
-/
def ULift.orderIso {α : Type u} [Preorder α] :
    ULift.{v} α ≃o α :=
  Equiv.ulift.toOrderIso (fun _ _ ↦ id) (fun _ _ ↦ id)
