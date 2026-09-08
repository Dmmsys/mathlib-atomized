/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Tactic.Monotonicity.Attr
public import Mathlib.Tactic.SetLike
public import Mathlib.Data.Set.Basic

/-!
# Typeclass for types with a set-like extensionality property

The `Membership` typeclass is used to let terms of a type have elements.
Many instances of `Membership` have a set-like extensionality property:
things are equal iff they have the same elements.  The `SetLike`
typeclass provides a unified interface to define a `Membership` that is
extensional in this way.

The main use of `SetLike` is for algebraic subobjects (such as
`Submonoid` and `Submodule`), whose non-proof data consists only of a
carrier set.  In such a situation, the projection to the carrier set
is injective.

In general, a type `A` is `SetLike` with elements of type `B` if it
has an injective map to `Set B`.  This module provides standard
boilerplate for every `SetLike`: a `coe_sort`, a `coe` to set,
and various extensionality and simp lemmas. The order induced by set inclusion is
called `PartialOrder.ofSetlike`: this is not an instance for flexibility in choosing orders.
The class `IsConcreteLE` abstractly states the order is equal to that induced by set inclusion;
an instance is automatically available when defining a `PartialOrder` as
`.ofSetLike (MySubobject X) X`.

A typical subobject should be declared as:
```
structure MySubobject (X : Type*) [ObjectTypeclass X] where
  (carrier : Set X)
  (op_mem' : ∀ {x : X}, x ∈ carrier → sorry ∈ carrier)

namespace MySubobject

variable {X : Type*} [ObjectTypeclass X] {x : X}

instance : SetLike (MySubobject X) X :=
  ⟨MySubobject.carrier, fun p q h => by cases p; cases q; congr!⟩

instance : PartialOrder (MySubobject X) := .ofSetLike (MySubobject X) X

@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl

@[ext] theorem ext {p q : MySubobject X} (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q := SetLike.ext h

/-- Copy of a `MySubobject` with a new `carrier` equal to the old one. Useful to fix definitional
equalities. See Note [range copy pattern]. -/
protected def copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) : MySubobject X :=
  { carrier := s
    op_mem' := hs.symm ▸ p.op_mem' }

@[simp] lemma coe_copy (p : MySubobject X) (s : Set X) (hs : s = ↑p) :
  (p.copy s hs : Set X) = s := rfl

lemma copy_eq (p : MySubobject X) (s : Set X) (hs : s = ↑p) : p.copy s hs = p :=
  SetLike.coe_injective hs

end MySubobject
```

An alternative to `SetLike` could have been an extensional `Membership` typeclass:
```
class ExtMembership (α : out_param <| Type u) (β : Type v) extends Membership α β where
  (ext_iff : ∀ {s t : β}, s = t ↔ ∀ (x : α), x ∈ s ↔ x ∈ t)
```
While this is equivalent, `SetLike` conveniently uses a carrier set projection directly.

## Tags

subobjects
-/

@[expose] public section

assert_not_exists RelIso

/-- A class to indicate that there is a canonical injection between `A` and `Set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `Membership`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `SetLike.coe` is a projection, implementers should create a simp lemma such as
```
@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) := Iff.rfl
```
to normalize terms.

If you declare an unbundled subclass of `SetLike`, for example:
```
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] where
  ...
```
Then you should *not* repeat the `outParam` declaration so `SetLike` will supply the value instead.
This ensures your subclass will not have issues with synthesis of the `[Mul M]` parameter starting
before the value of `M` is known.
-/
@[notation_class* carrier Simps.findCoercionArgs]
/-
**SetLike** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type u_1 → outParam (Type u_2) → Type (max u_1 u_2)
参数：Type u_2；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class to indicate that there is a canonical injection between `A` and `Set B`.

This has the effect of giving terms of `A` elements of type `B` (through a `Memb
ership`
instance) and a compatible coercion to `Type*` as a subtype.

Note: if `SetLike.coe` is a projection, implementers should create a simp lemma 
such as
```
@[simp] lemma mem_carrier {p : MySubobject X} : x ∈ p.carrier ↔ x ∈ (p : Set X) 
:= Iff.rfl
```
to normalize terms.

If you declare an unbundled subclass of `SetLike`, for example:
```
class MulMemClass (S : Type*) (M : Type*) [Mul M] [SetLike S M] where
  ...
```
Then you should *not* repeat the `outParam` declaration so `SetLike` will supply
 the value instead.
This ensures your subclass will not have issues with synthesis of the `[Mul M]` 
parameter starting
before the value of `M` is known.
-/
class SetLike (A : Type*) (B : outParam Type*) where
  /-- The coercion from a term of a `SetLike` to its corresponding `Set`. -/
  protected coe : A → Set B
  /-- The coercion from a term of a `SetLike` to its corresponding `Set` is injective. -/
  coe_injective : Function.Injective coe

attribute [coe] SetLike.coe

namespace SetLike

variable {A : Type*} {B : Type*} [i : SetLike A B]

@[deprecated (since := "2026-06-04")] alias coe_injective' := coe_injective

/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC A (Set B) where coe := SetLike.coe
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instMembership : Membership B A :=
  ⟨fun p x => x ∈ (p : Set B)⟩
/-
**SetLike.** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) : CoeSort A (Type _) :=
  ⟨fun p => { x : B // x ∈ p }⟩

section Delab
open Lean PrettyPrinter.Delaborator SubExpr

/-- For terms that match the `CoeSort` instance's body, pretty print as `↥S`
rather than as `{ x // x ∈ S }`. The discriminating feature is that membership
uses the `SetLike.instMembership` instance. -/
@[app_delab Subtype]
meta def delabSubtypeSetLike : Delab := whenPPOption getPPNotation do
  let #[_, .lam n _ body _] := (← getExpr).getAppArgs | failure
  guard <| body.isAppOf ``Membership.mem
  let #[_, _, inst, _, .bvar 0] := body.getAppArgs | failure
  guard <| inst.isAppOfArity ``instMembership 3
  let S ← withAppArg <| withBindingBody n <| withNaryArg 3 delab
  `(↥$S)

end Delab

variable (p q : A)

@[simp, norm_cast]
/-
**SetLike.coe_sort_coe** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：coe_sort_coe : ((p : Set B) : Type _) = p
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sort_coe : ((p : Set B) : Type _) = p :=
  rfl

variable {p q}
/-
**SetLike.** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «exists» {q : p → Prop} : (∃ x, q x) ↔ ∃ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.exists
/-
**SetLike.** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem «forall» {q : p → Prop} : (∀ x, q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, ‹_›⟩ :=
  SetCoe.forall

@[simp, norm_cast]
/-
**SetLike.coe_set_eq** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：coe_set_eq : (p : Set B) = q ↔ p = q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem coe_set_eq : (p : Set B) = q ↔ p = q :=
  coe_injective.eq_iff
/-
**SetLike.coe_ne_coe** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q : A}, ↑p ≠ ↑q ↔ p ≠
 q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
@[norm_cast] lemma coe_ne_coe : (p : Set B) ≠ q ↔ p ≠ q := coe_injective.ne_iff
/-
**SetLike.ext'** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：ext' (h : (p : Set B) = q) : p = q
参数：h : (p : Set B) = q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
-/
theorem ext' (h : (p : Set B) = q) : p = q :=
  coe_injective h
/-
**SetLike.ext'_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q : A}, p = q ↔ ↑p = 
↑q
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `SetLike.coe_set_eq`：coe_set_eq : (p : Set B) = q ↔ p = q
-/
theorem ext'_iff : p = q ↔ (p : Set B) = q :=
  coe_set_eq.symm

/-- Note: implementers of `SetLike` must copy this lemma in order to tag it with `@[ext]`. -/
/-
**SetLike.ext** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：ext (h : forall x, x in p ↔ x in q) : p = q
参数：h : forall x, x in p ↔ x in q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b

--- 原说明 ---
Note: implementers of `SetLike` must copy this lemma in order to tag it with `@[
ext]`.
-/
theorem ext (h : ∀ x, x ∈ p ↔ x ∈ q) : p = q :=
  coe_injective <| Set.ext h
/-
**SetLike.ext_iff** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：ext_iff : p = q ↔ forall x, x in p ↔ x in q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.ext_iff`：∀ {α : Type u} {a b : Set α}, a = b ↔ ∀ (x : α), x ∈ a ↔ x 
∈ b
-/
theorem ext_iff : p = q ↔ ∀ x, x ∈ p ↔ x ∈ q :=
  coe_injective.eq_iff.symm.trans Set.ext_iff

@[simp, push]
/-
**SetLike.mem_coe** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：mem_coe {x : B} : x in (p : Set B) ↔ x in p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_coe {x : B} : x ∈ (p : Set B) ↔ x ∈ p :=
  Iff.rfl

@[simp, norm_cast]
/-
**SetLike.coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：coe_eq_coe {x y : p} : (x : B) = y ↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
-/
theorem coe_eq_coe {x y : p} : (x : B) = y ↔ x = y :=
  Subtype.ext_iff.symm

@[simp]
/-
**SetLike.coe_mem** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：coe_mem (x : p) : (x : B) in p
参数：x : p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_mem (x : p) : (x : B) ∈ p :=
  x.2

@[aesop 5% (rule_sets := [SetLike!])]
/-
**SetLike.mem_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `SetLike`。
形式化陈述：mem_of_subset {s : Set B} (hp : s subseteq p) {x : B} (hx : x in s) : x in
 p
参数：hp : s subseteq p；hx : x in s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mem_of_subset {s : Set B} (hp : s ⊆ p) {x : B} (hx : x ∈ s) : x ∈ p := hp hx

@[simp]
/-
**SetLike.eta** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p : A} (x : ↥p) (hx : ↑
x ∈ p), ⟨↑x, hx⟩ = x
参数：x : ↥p；hx : ↑x ∈ p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem eta (x : p) (hx : (x : B) ∈ p) : (⟨x, hx⟩ : p) = x := rfl
/-
**SetLike.setOfPred_mem_eq** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] (a : A), {b | b ∈ a} = ↑
a
参数：a : A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma setOfPred_mem_eq (a : A) : {b | b ∈ a} = a := rfl

@[deprecated (since := "2026-07-09")] alias setOf_mem_eq := setOfPred_mem_eq

@[nontriviality]
/-
**SetLike.mem_of_subsingleton** 是 Mathlib 中的一个引理，位于命名空间 `SetLike`。
形式化陈述：mem_of_subsingleton [Subsingleton B] (S : A) [h : Nonempty S] {b : B} : b 
in S
参数：S : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `nonempty_subtype`：nonempty_subtype {α} {p : α -> Prop} : Nonempty (Subty
pe p) ↔ exists a : α, p a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
lemma mem_of_subsingleton [Subsingleton B] (S : A) [h : Nonempty S] {b : B} : b ∈ S := by
  obtain ⟨s, hs⟩ := nonempty_subtype.mp h
  simpa [Subsingleton.elim b s]

/-- If `s` is a proper element of a `SetLike` structure (i.e., `s ≠ ⊤`) and the top element
coerces to the universal set, then there exists an element not in `s`. -/
/-
**SetLike.exists_not_mem_of_ne_top** 是 Mathlib 中的一个引理，位于命名空间 `SetLike`。
形式化陈述：exists_not_mem_of_ne_top [LE A] [OrderTop A] (s : A) (hs : s != ⊤) (h_top 
: ((⊤ : A) : Set B) = Set.univ
参数：s : A；hs : s != ⊤。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
If `s` is a proper element of a `SetLike` structure (i.e., `s ≠ ⊤`) and the top 
element
coerces to the universal set, then there exists an element not in `s`.
-/
lemma exists_not_mem_of_ne_top [LE A] [OrderTop A] (s : A) (hs : s ≠ ⊤)
    (h_top : ((⊤ : A) : Set B) = Set.univ := by simp) :
    ∃ b : B, b ∉ s := by
  simpa [-SetLike.coe_set_eq, SetLike.ext'_iff, h_top, Set.ne_univ_iff_exists_notMem] using hs

end SetLike

/-- A class to indicate that the canonical injection between `A` and `Set B` is order-preserving.

An instance of this class is automatically available on any partial order defined as
`PartialOrder.ofSetLike`.
-/
/-
**IsConcreteLE** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_1) → (B : outParam (Type u_2)) → [SetLike A B] → [LE A] → Prop
参数：Type u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class to indicate that the canonical injection between `A` and `Set B` is orde
r-preserving.

An instance of this class is automatically available on any partial order define
d as
`PartialOrder.ofSetLike`.
-/
class IsConcreteLE (A : Type*) (B : outParam Type*) [SetLike A B] [LE A] where
  /-- The coercion from a `SetLike` type preserves the ordering. -/
  protected coe_subset_coe' {S T : A} : SetLike.coe S ⊆ SetLike.coe T ↔ S ≤ T

section default

variable (A B : Type*) [SetLike A B]

/-- The order induced from a `SetLike` instance by inclusion.

An order defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteLE`.
-/
/-
**LE.ofSetLike** 是 Mathlib 中的一个定义，位于命名空间 `LE`。
形式化陈述：(A : Type u_1) → (B : Type u_2) → [SetLike A B] → LE A
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The order induced from a `SetLike` instance by inclusion.

An order defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteLE`.
-/
@[reducible] def LE.ofSetLike : LE A where
  le := fun H K => ∀ ⦃x⦄, x ∈ H → x ∈ K
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : letI := LE.ofSetLike A B; IsConcreteLE A B :=
  letI := LE.ofSetLike A B; { coe_subset_coe' := Iff.rfl }

/-- The partial order induced from a `SetLike` instance by inclusion.

A partial order defined as `.ofSetLike` will automatically make available an instance
of `IsConcreteLE`.
-/
/-
**PartialOrder.ofSetLike** 是 Mathlib 中的一个定义，位于命名空间 `PartialOrder`。
形式化陈述：(A : Type u_1) → (B : Type u_2) → [SetLike A B] → PartialOrder A
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `PartialOrder.le_antisymm`：∀ {α : Type u_2} [self : PartialOrder α] (a b 
: α), a ≤ b → b ≤ a → a = b

--- 原说明 ---
The partial order induced from a `SetLike` instance by inclusion.

A partial order defined as `.ofSetLike` will automatically make available an ins
tance
of `IsConcreteLE`.
-/
@[reducible] def PartialOrder.ofSetLike : PartialOrder A where
  __ := LE.ofSetLike A B
  lt s t := letI := LE.ofSetLike A B; s ≤ t ∧ ¬t ≤ s
  __ := PartialOrder.lift (SetLike.coe : A → Set B) SetLike.coe_injective

end default

namespace SetLike

variable {A B : Type*} [SetLike A B]

section LE

variable [LE A] [IsConcreteLE A B] {p q : A}

/-
**SetLike.coe_subset_coe** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [inst_1 : LE A] [IsCo
ncreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConcreteLE.coe_subset_coe'`：∀ {A : Type u_1} {B : outParam (Type u_2)}
 {inst : SetLike A B} {inst_1 : LE A} [self : IsConcreteLE A B] {S T : A},   ↑S 
⊆ ↑T ↔ S ≤ T
-/
@[simp, norm_cast, gcongr] lemma coe_subset_coe {S T : A} : (S : Set B) ⊆ T ↔ S ≤ T :=
  IsConcreteLE.coe_subset_coe'
/-
**SetLike.le_def** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x in T
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem le_def {S T : A} : S ≤ T ↔ ∀ ⦃x : B⦄, x ∈ S → x ∈ T := by
  simp [← coe_subset_coe, Set.subset_def]

@[gcongr low] -- lower priority than `Set.mem_of_subset_of_mem`
alias ⟨_root_.mem_of_le_of_mem, _⟩ := le_def

@[deprecated (since := "2026-01-07")] alias GCongr.mem_of_le_of_mem := _root_.mem_of_le_of_mem
/-
**SetLike.not_le_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：not_le_iff_exists : ¬p <= q ↔ exists x in p, x ∉ q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
-/
theorem not_le_iff_exists : ¬p ≤ q ↔ ∃ x ∈ p, x ∉ q := by
  simpa [← coe_subset_coe] using! Set.not_subset

end LE

section Preorder

variable [Preorder A] [IsConcreteLE A B] {p q : A}

@[gcongr, mono]
/-
**SetLike.coe_mono** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：coe_mono : Monotone (SetLike.coe : A -> Set B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
-/
theorem coe_mono : Monotone (SetLike.coe : A → Set B) := fun _ _ => coe_subset_coe.mpr

end Preorder

section PartialOrder

variable [PartialOrder A] [IsConcreteLE A B] {p q : A}

/-
**SetLike.coe_ssubset_coe** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike A B] [inst_1 : PartialOrde
r A] [IsConcreteLE A B] {S T : A},   ↑S ⊂ ↑T ↔ S < T
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ssubset_iff_subset_ne`：∀ {α : Type u_2} [UsesSetNotationForOrder α] [ins
t : PartialOrder α] {a b : α}, a ⊂ b ↔ a ⊆ b ∧ a ≠ b
· 使用定理 `lt_iff_le_and_ne`：lt_iff_le_and_ne : a < b ↔ a <= b ∧ a != b
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `SetLike.coe_ne_coe`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p
 q : A}, ↑p ≠ ↑q ↔ p ≠ q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp, norm_cast, gcongr] lemma coe_ssubset_coe {S T : A} : (S : Set B) ⊂ T ↔ S < T := by
  rw [ssubset_iff_subset_ne, lt_iff_le_and_ne, coe_subset_coe, SetLike.coe_ne_coe]

@[gcongr, mono]
/-
**SetLike.coe_strictMono** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：coe_strictMono : StrictMono (SetLike.coe : A -> Set B)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.coe_ssubset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike
 A B] [inst_1 : PartialOrder A] [IsConcreteLE A B] {S T : A},   ↑S ⊂ ↑T ↔ S < T
-/
theorem coe_strictMono : StrictMono (SetLike.coe : A → Set B) := fun _ _ => coe_ssubset_coe.mpr
/-
**SetLike.exists_of_lt** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：exists_of_lt : p < q -> exists x in q, x ∉ p
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.exists_of_ssubset`：exists_of_ssubset {s t : Set α} (h : s ⊂ t) : exi
sts x in t, x ∉ s
-/
theorem exists_of_lt : p < q → ∃ x ∈ q, x ∉ p := by
  simpa [← coe_ssubset_coe] using! Set.exists_of_ssubset
/-
**SetLike.lt_iff_le_and_exists** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：lt_iff_le_and_exists : p < q ↔ p <= q ∧ exists x in q, x ∉ p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `SetLike.not_le_iff_exists`：not_le_iff_exists : ¬p <= q ↔ exists x in p, 
x ∉ q
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem lt_iff_le_and_exists : p < q ↔ p ≤ q ∧ ∃ x ∈ q, x ∉ p := by
  rw [lt_iff_le_not_ge, not_le_iff_exists]

/-- membership is inherited from `Set X` -/
/-
**SetLike.instSubtypeSet** 是 Mathlib 中的一个缩写定义，位于命名空间 `SetLike`。
形式化陈述：instSubtypeSet {X} {p : Set X -> Prop} : SetLike {s // p s} X where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
membership is inherited from `Set X`
-/
abbrev instSubtypeSet {X} {p : Set X → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective := Subtype.val_injective

/-- membership is inherited from `S` -/
/-
**SetLike.instSubtype** 是 Mathlib 中的一个缩写定义，位于命名空间 `SetLike`。
形式化陈述：instSubtype {X S} [SetLike S X] {p : S -> Prop} : SetLike {s // p s} X whe
re coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
membership is inherited from `S`
-/
abbrev instSubtype {X S} [SetLike S X] {p : S → Prop} : SetLike {s // p s} X where
  coe := (↑)
  coe_injective := SetLike.coe_injective.comp Subtype.val_injective

section

attribute [local instance] instSubtypeSet instSubtype

/-
**SetLike.mem_mk_set** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {X : Type u_3} {p : Set X → Prop} {U : Set X} {h : p U} {x : X}, x ∈ ⟨U,
 h⟩ ↔ x ∈ U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk_set {X} {p : Set X → Prop} {U : Set X} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl
/-
**SetLike.mem_mk** 是 Mathlib 中的一个定理，位于命名空间 `SetLike`。
形式化陈述：∀ {X : Type u_3} {S : Type u_4} [inst : SetLike S X] {p : S → Prop} {U : S
} {h : p U} {x : X}, x ∈ ⟨U, h⟩ ↔ x ∈ U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma mem_mk {X S} [SetLike S X] {p : S → Prop} {U : S} {h : p U} {x : X} :
    x ∈ Subtype.mk U h ↔ x ∈ U := Iff.rfl

end

end PartialOrder

end SetLike

