/-
Copyright (c) 2019 Amelia Livingston. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Amelia Livingston
-/
module

public import Mathlib.Algebra.Group.InjSurj
public import Mathlib.Algebra.Group.Units.Defs
public import Mathlib.Data.Setoid.Basic
public import Mathlib.Tactic.FastInstance
import Mathlib.Order.GaloisConnection.Basic

/-!
# Congruence relations

This file defines congruence relations: equivalence relations that preserve a binary operation,
which in this case is multiplication or addition. The principal definition is a `structure`
extending a `Setoid` (an equivalence relation), and the inductive definition of the smallest
congruence relation containing a binary relation is also given (see `ConGen`).

The file also proves basic properties of the quotient of a type by a congruence relation, and the
complete lattice of congruence relations on a type. We then establish an order-preserving bijection
between the set of congruence relations containing a congruence relation `c` and the set of
congruence relations on the quotient by `c`.

The second half of the file concerns congruence relations on monoids, in which case the
quotient by the congruence relation is also a monoid.

## Implementation notes

The inductive definition of a congruence relation could be a nested inductive type, defined using
the equivalence closure of a binary relation `EqvGen`, but the recursor generated does not work.
A nested inductive definition could conceivably shorten proofs, because they would allow invocation
of the corresponding lemmas about `EqvGen`.

The lemmas `refl`, `symm` and `trans` are not tagged with `@[refl]`, `@[symm]`, and `@[trans]`
respectively as these tags do not work on a structure coerced to a binary relation.

There is a coercion from elements of a type to the element's equivalence class under a
congruence relation.

A congruence relation on a monoid `M` can be thought of as a submonoid of `M × M` for which
membership is an equivalence relation, but whilst this fact is established in the file, it is not
used, since this perspective adds more layers of definitional unfolding.

## Tags

congruence, congruence relation, quotient, quotient by congruence relation, monoid,
quotient monoid, isomorphism theorems
-/

@[expose] public section


variable (M : Type*) {N : Type*} {P : Type*}

open Function Setoid

/-- A congruence relation on a type with an addition is an equivalence relation which
preserves addition. -/
/-
**AddCon** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Add M] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence relation on a type with an addition is an equivalence relation whic
h
preserves addition.
-/
structure AddCon [Add M] extends Setoid M where
  /-- Additive congruence relations are closed under addition -/
  add' : ∀ {w x y z}, r w x → r y z → r (w + y) (x + z)

/-- A congruence relation on a type with a multiplication is an equivalence relation which
preserves multiplication. -/
@[to_additive AddCon]
/-
**Con** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_1) → [Mul M] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence relation on a type with a multiplication is an equivalence relation
 which
preserves multiplication.
-/
structure Con [Mul M] extends Setoid M where
  /-- Congruence relations are closed under multiplication -/
  mul' : ∀ {w x y z}, r w x → r y z → r (w * y) (x * z)

/-- The equivalence relation underlying an additive congruence relation. -/
add_decl_doc AddCon.toSetoid

/-- The equivalence relation underlying a multiplicative congruence relation. -/
add_decl_doc Con.toSetoid

variable {M}

/-- The inductively defined smallest additive congruence relation containing a given binary
relation. -/
/-
**AddConGen.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddConGen`。
形式化陈述：{M : Type u_1} → [Add M] → (M → M → Prop) → M → M → Prop
参数：M → M → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inductively defined smallest additive congruence relation containing a given
 binary
relation.
-/
inductive AddConGen.Rel [Add M] (r : M → M → Prop) : M → M → Prop
  | of : ∀ x y, r x y → AddConGen.Rel r x y
  | refl : ∀ x, AddConGen.Rel r x x
  | symm : ∀ {x y}, AddConGen.Rel r x y → AddConGen.Rel r y x
  | trans : ∀ {x y z}, AddConGen.Rel r x y → AddConGen.Rel r y z → AddConGen.Rel r x z
  | add : ∀ {w x y z}, AddConGen.Rel r w x → AddConGen.Rel r y z → AddConGen.Rel r (w + y) (x + z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
relation. -/
@[to_additive AddConGen.Rel]
/-
**ConGen.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `ConGen`。
形式化陈述：{M : Type u_1} → [Mul M] → (M → M → Prop) → M → M → Prop
参数：M → M → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inductively defined smallest multiplicative congruence relation containing a
 given binary
relation.
-/
inductive ConGen.Rel [Mul M] (r : M → M → Prop) : M → M → Prop
  | of : ∀ x y, r x y → ConGen.Rel r x y
  | refl : ∀ x, ConGen.Rel r x x
  | symm : ∀ {x y}, ConGen.Rel r x y → ConGen.Rel r y x
  | trans : ∀ {x y z}, ConGen.Rel r x y → ConGen.Rel r y z → ConGen.Rel r x z
  | mul : ∀ {w x y z}, ConGen.Rel r w x → ConGen.Rel r y z → ConGen.Rel r (w * y) (x * z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
relation. -/
@[to_additive /-- The inductively defined smallest additive congruence relation containing
a given binary relation. -/]
/-
**conGen** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：conGen [Mul M] (r : M -> M -> Prop) : Con M
参数：r : M -> M -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def conGen [Mul M] (r : M → M → Prop) : Con M :=
  ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩

namespace Con

section

variable [Mul M] [Mul N] [Mul P] {c d : Con M}

@[to_additive]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Con M) :=
  ⟨conGen emptyRelation⟩
/-
**Con.toSetoid_injective** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M], Function.Injective Con.toSetoid
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Con.mul'`：∀ {M : Type u_1} [inst : Mul M] (self : Con M) {w x y z : M}, 
  self.toSetoid w x → self.toSetoid y z → self.toSetoid (w * y) (x * z)
-/
@[to_additive] lemma toSetoid_injective : Injective (toSetoid (M := M)) :=
  fun c d ↦ by cases c; congr!
/-
**Con.toSetoid_inj** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] {c d : Con M}, c.toSetoid = d.toSetoid ↔ c
 = d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Con.toSetoid_injective`：∀ {M : Type u_1} [inst : Mul M], Function.Inject
ive Con.toSetoid
-/
@[to_additive (attr := simp)] lemma toSetoid_inj : c.toSetoid = d.toSetoid ↔ c = d :=
  toSetoid_injective.eq_iff

/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive
/-- A coercion from an additive congruence relation to its underlying binary relation. -/]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (Con M) M (M → Prop) where
  coe c := c.r
  coe_injective x y h := by
    rcases x with ⟨⟨x, _⟩, _⟩
    rcases y with ⟨⟨y, _⟩, _⟩
    have : x = y := h
    subst x; rfl

variable (c)

@[to_additive (attr := simp)]
/-
**Con.rel_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：rel_eq_coe (c : Con M) : c.r = c
参数：c : Con M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rel_eq_coe (c : Con M) : c.r = c :=
  rfl

/-- Congruence relations are reflexive. -/
@[to_additive /-- Additive congruence relations are reflexive. -/]
/-
**Con.refl** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] (c : Con M) (x : M), c x x
参数：c : Con M；x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x

--- 原说明 ---
Congruence relations are reflexive.
-/
protected theorem refl (x) : c x x :=
  c.toSetoid.refl' x

/-- Congruence relations are symmetric. -/
@[to_additive /-- Additive congruence relations are symmetric. -/]
/-
**Con.symm** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y : M}, c x y → c y x
参数：c : Con M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x

--- 原说明 ---
Congruence relations are symmetric.
-/
protected theorem symm {x y} : c x y → c y x := c.toSetoid.symm'

/-- Congruence relations are transitive. -/
@[to_additive /-- Additive congruence relations are transitive. -/]
/-
**Con.trans** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {x y z : M}, c x y → c y z → c
 x z
参数：c : Con M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z

--- 原说明 ---
Congruence relations are transitive.
-/
protected theorem trans {x y z} : c x y → c y z → c x z := c.toSetoid.trans'

/-- Multiplicative congruence relations preserve multiplication. -/
@[to_additive /-- Additive congruence relations preserve addition. -/]
/-
**Con.mul** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w x → c y z →
 c (w * y) (x * z)
参数：c : Con M；w * y；x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.mul'`：∀ {M : Type u_1} [inst : Mul M] (self : Con M) {w x y z : M}, 
  self.toSetoid w x → self.toSetoid y z → self.toSetoid (w * y) (x * z)

--- 原说明 ---
Multiplicative congruence relations preserve multiplication.
-/
protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) := c.mul'

@[to_additive (attr := simp)]
/-
**Con.rel_mk** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b :=
  Iff.rfl

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
`x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
@[to_additive instMembershipProd
  /-- Given a type `M` with an addition, `x, y ∈ M`, and an additive congruence relation
`c` on `M`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/]
/-
**Con.instMembershipProd** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：instMembershipProd : Membership (M × M) (Con M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMembershipProd : Membership (M × M) (Con M) :=
  ⟨fun c x => c x.1 x.2⟩

variable {c}

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive /-- The map sending an additive congruence relation to its underlying binary relation
is injective. -/]
/-
**Con.ext'** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：ext' {c d : Con M} (H : ⇑c = ⇑d) : c = d
参数：H : ⇑c = ⇑d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem ext' {c d : Con M} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
@[to_additive (attr := ext) /-- Extensionality rule for additive congruence relations. -/]
/-
**Con.ext** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：ext {c d : Con M} (H : forall x y, c x y ↔ d x y) : c = d
参数：H : forall x y, c x y ↔ d x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.ext'`：ext' {c d : Con M} (H : ⇑c = ⇑d) : c = d
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Extensionality rule for congruence relations.
-/
theorem ext {c d : Con M} (H : ∀ x y, c x y ↔ d x y) : c = d :=
  ext' <| by ext; apply H

/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
@[to_additive /-- Two additive congruence relations are equal iff their underlying binary relations
are equal. -/]
/-
**Con.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_inj {c d : Con M} : ⇑c = ⇑d ↔ c = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem coe_inj {c d : Con M} : ⇑c = ⇑d ↔ c = d := DFunLike.coe_injective.eq_iff

variable (c)

-- Quotients
/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
@[to_additive /-- Defining the quotient by an additive congruence relation of a type with
an addition. -/]
/-
**Con.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：{M : Type u_1} → [inst : Mul M] → Con M → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def Quotient :=
  Quotient c.toSetoid

variable {c}

/-- The morphism into the quotient by a congruence relation -/
@[to_additive (attr := coe)
/-- The morphism into the quotient by an additive congruence relation -/]
/-
**Con.toQuotient** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：toQuotient : M -> c.Quotient
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
def toQuotient : M → c.Quotient :=
  Quotient.mk''

variable (c)

/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
@[to_additive /-- Coercion from a type with an addition to its quotient by an additive congruence
relation -/]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 10) : CoeTC M c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
@[to_additive
/-- The quotient by a decidable additive congruence relation has decidable equality. -/]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 500) [∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[to_additive (attr := simp)]
/-
**Con.quot_mk_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：quot_mk_eq_coe {M : Type*} [Mul M] (c : Con M) (x : M) : Quot.mk c x = (x 
: c.Quotient)
参数：c : Con M；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_coe {M : Type*} [Mul M] (c : Con M) (x : M) : Quot.mk c x = (x : c.Quotient) :=
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `elab_as_elim`
/-- The function on the quotient by a congruence relation `c` induced by a function that is
constant on `c`'s equivalence classes. -/
@[to_additive /-- The function on the quotient by a congruence relation `c`
induced by a function that is constant on `c`'s equivalence classes. -/]
/-
**Con.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：{M : Type u_1} →   [inst : Mul M] → {β : Sort u_4} → {c : Con M} → c.Quoti
ent → (f : M → β) → (∀ (a b : M), c a b → f a = f b) → β
参数：f : M → β；∀ (a b : M), c a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def liftOn {β} {c : Con M} (q : c.Quotient) (f : M → β) (h : ∀ a b, c a b → f a = f b) :
    β :=
  Quotient.liftOn' q f h

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `elab_as_elim`
/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
that is constant on `c`'s equivalence classes. -/
@[to_additive /-- The binary function on the quotient by a congruence relation `c`
induced by a binary function that is constant on `c`'s equivalence classes. -/]
/-
**Con.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：{M : Type u_1} →   [inst : Mul M] → {β : Sort u_4} → {c : Con M} → c.Quoti
ent → (f : M → β) → (∀ (a b : M), c a b → f a = f b) → β
参数：f : M → β；∀ (a b : M), c a b → f a = f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected def liftOn₂ {β} {c : Con M} (q r : c.Quotient) (f : M → M → β)
    (h : ∀ a₁ a₂ b₁ b₂, c a₁ b₁ → c a₂ b₂ → f a₁ a₂ = f b₁ b₂) : β :=
  Quotient.liftOn₂' q r f h

/-- A version of `Quotient.hrecOn₂'` for quotients by `Con`. -/
@[to_additive /-- A version of `Quotient.hrecOn₂'` for quotients by `AddCon`. -/]
/-
**Con.hrecOn** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `Quotient.hrecOn₂'` for quotients by `Con`.
-/
protected def hrecOn₂ {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort*}
    (a : cM.Quotient) (b : cN.Quotient) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → f x y ≍ f x' y') : φ a b :=
  Quotient.hrecOn₂' a b f h

@[to_additive (attr := simp)]
/-
**Con.hrec_on** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem hrec_on₂_coe {cM : Con M} {cN : Con N} {φ : cM.Quotient → cN.Quotient → Sort*} (a : M)
    (b : N) (f : ∀ (x : M) (y : N), φ x y)
    (h : ∀ x y x' y', cM x x' → cN y y' → f x y ≍ f x' y') :
    Con.hrecOn₂ (↑a) (↑b) f h = f a b :=
  rfl

variable {c}

/-- The inductive principle used to prove propositions about the elements of a quotient by a
congruence relation. -/
@[to_additive (attr := elab_as_elim) /-- The inductive principle used to prove propositions about
the elements of a quotient by an additive congruence relation. -/]
/-
**Con.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] {c : Con M} {C : c.Quotient → Prop} (q : c
.Quotient), (∀ (x : M), C ↑x) → C q
参数：q : c.Quotient；∀ (x : M), C ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem induction_on {C : c.Quotient → Prop} (q : c.Quotient) (H : ∀ x : M, C x) : C q :=
  Quotient.inductionOn' q H

/-- A version of `Con.induction_on` for predicates which takes two arguments. -/
@[to_additive (attr := elab_as_elim)
/-- A version of `AddCon.induction_on` for predicates which takes two arguments. -/]
/-
**Con.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] {c : Con M} {C : c.Quotient → Prop} (q : c
.Quotient), (∀ (x : M), C ↑x) → C q
参数：q : c.Quotient；∀ (x : M), C ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
protected theorem induction_on₂ {d : Con N} {C : c.Quotient → d.Quotient → Prop} (p : c.Quotient)
    (q : d.Quotient) (H : ∀ (x : M) (y : N), C x y) : C p q :=
  Quotient.inductionOn₂' p q H

variable (c)

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[to_additive (attr := simp) /-- Two elements are related by an additive congruence relation `c` iff
they are represented by the same element of the quotient by `c`. -/]
/-
**Con.eq** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {a b : M}, ↑a = ↑b ↔ c a b
参数：c : Con M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
protected theorem eq {a b : M} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''

/-- The multiplication induced on the quotient by a congruence relation on a type with a
multiplication. -/
@[to_additive /-- The addition induced on the quotient by an additive congruence relation on a type
with an addition. -/]
/-
**Con.hasMul** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：hasMul : Mul c.Quotient
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
-/
instance hasMul : Mul c.Quotient :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h1 _ _ h2 => c.mul h1 h2⟩

variable {c}

/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
definition). -/
@[to_additive (attr := simp) /-- The coercion to the quotient of an additive congruence relation
commutes with addition (by definition). -/]
/-
**Con.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_mul (x y : M) : (↑(x * y) : c.Quotient) = ↑x * ↑y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : M) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl

/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
that is constant on `c`'s equivalence classes. -/
@[to_additive (attr := simp) /-- Definition of the function on the quotient by an additive
congruence relation `c` induced by a function that is constant on `c`'s equivalence classes. -/]
/-
**Con.liftOn_coe** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M] {β : Sort u_4} (c : Con M) (f : M → β) (h 
: ∀ (a b : M), c a b → f a = f b) (x : M),   Con.liftOn (↑x) f h = f x
参数：c : Con M；f : M → β；h : ∀ (a b : M), c a b → f a = f b；x : M；↑x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem liftOn_coe {β} (c : Con M) (f : M → β) (h : ∀ a b, c a b → f a = f b) (x : M) :
    Con.liftOn (x : c.Quotient) f h = f x :=
  rfl

-- The complete lattice of congruence relations on a type
/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
`x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive /-- For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d`
iff `∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LE (Con M) where
  le c d := ∀ ⦃x y⦄, c x y → d x y

/-- Definition of `≤` for congruence relations. -/
@[to_additive /-- Definition of `≤` for additive congruence relations. -/]
/-
**Con.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：le_def {c d : Con M} : c <= d ↔ forall {x y}, c x y -> d x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of `≤` for congruence relations.
-/
theorem le_def {c d : Con M} : c ≤ d ↔ ∀ {x y}, c x y → d x y :=
  Iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive /-- The infimum of a set of additive congruence relations on a given type with
an addition. -/]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Con M) where
  sInf S :=
    { r := fun x y => ∀ c : Con M, c ∈ S → c x y
      iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm <| h c hc,
        fun h1 h2 c hc => c.trans (h1 c hc) <| h2 c hc⟩
      mul' := fun h1 h2 c hc => c.mul (h1 c hc) <| h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying equivalence relation. -/
@[to_additive /-- The infimum of a set of additive congruence relations is the same as the infimum
of the set's image under the map to the underlying equivalence relation. -/]
/-
**Con.sInf_toSetoid** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：sInf_toSetoid (S : Set (Con M)) : (sInf S).toSetoid = sInf (toSetoid '' S)
参数：S : Set (Con M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.ext`：ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a 
b ↔ t a b) -> s = t | ⟨r, _⟩, ⟨p, _⟩, Eq => by have : r = p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem sInf_toSetoid (S : Set (Con M)) : (sInf S).toSetoid = sInf (toSetoid '' S) :=
  Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying binary relation. -/
@[to_additive (attr := simp, norm_cast)
  /-- The infimum of a set of additive congruence relations is the same as the infimum
  of the set's image under the map to the underlying binary relation. -/]
/-
**Con.coe_sInf** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_sInf (S : Set (Con M)) : ⇑(sInf S) = sInf ((⇑) '' S)
参数：S : Set (Con M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `sInf_image`：∀ {α : Type u_1} {β : Type u_2} [inst : CompleteLattice α] {
s : Set β} {f : β → α}, sInf (f '' s) = ⨅ a ∈ s, f a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `iInf_apply`：∀ {α : Type u_8} {β : α → Type u_9} {ι : Sort u_10} [inst : 
(i : α) → InfSet (β i)] {f : ι → (a : α) → β a} {a : α},   (⨅ i, f i) a = ⨅ i, f
…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iInf_Prop_eq`：iInf_Prop_eq {p : ι -> Prop} : ⨅ i, p i = forall i, p i
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_sInf (S : Set (Con M)) :
    ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Con.coe_iInf** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_iInf {ι : Sort*} (f : ι -> Con M) : ⇑(iInf f) = ⨅ i, ⇑(f i)
参数：f : ι -> Con M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iInf.eq_1`：∀ {α : Type u} {ι : Sort v} [inst : InfSet α] (s : ι → α), iI
nf s = sInf (Set.range s)
· 使用定理 `Con.coe_sInf`：coe_sInf (S : Set (Con M)) : ⇑(sInf S) = sInf ((⇑) '' S)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `sInf_range`：∀ {α : Type u_1} {ι : Sort u_4} [inst : InfSet α] {f : ι → α
}, sInf (Set.range f) = iInf f
· 使用定理 `Function.comp_def`：∀ {α : Sort u_1} {β : Sort u_2} {δ : Sort u_3} (f : β
 → δ) (g : α → β), f ∘ g = fun x => f (g x)
-/
theorem coe_iInf {ι : Sort*} (f : ι → Con M) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf, coe_sInf, ← Set.range_comp, sInf_range, Function.comp_def]

@[to_additive]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Con M) where
  le_refl _ _ _ := id
  le_trans _ _ _ h1 h2 _ _ h := h2 <| h1 h
  le_antisymm _ _ hc hd := ext fun _ _ => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive /-- The complete lattice of additive congruence relations on a given type with
an addition. -/]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Con M) where
  __ := completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : ∀ r ∈ s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
        hr hr'
          h⟩
  inf c d := ⟨c.toSetoid ⊓ d.toSetoid, fun h1 h2 => ⟨c.mul h1.1 h2.1, d.mul h1.2 h2.2⟩⟩
  inf_le_left _ _ := fun _ _ h => h.1
  inf_le_right _ _ := fun _ _ h => h.2
  le_inf _ _ _ hb hc := fun _ _ h => ⟨hb h, hc h⟩
  top := { Setoid.completeLattice.top with mul' := by tauto }
  le_top _ := fun _ _ _ => trivial
  bot := { Setoid.completeLattice.bot with mul' := fun h1 h2 => h1 ▸ h2 ▸ rfl }
  bot_le c := fun x _ h => h ▸ c.refl x

/-- The infimum of two congruence relations equals the infimum of the underlying binary
operations. -/
@[to_additive (attr := simp, norm_cast)
  /-- The infimum of two additive congruence relations equals the infimum of the underlying binary
  operations. -/]
/-
**Con.coe_inf** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_inf {c d : Con M} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inf {c d : Con M} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d :=
  rfl
/-
**Con.toSetoid_top** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M], ⊤.toSetoid = ⊤
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma toSetoid_top : (⊤ : Con M).toSetoid = ⊤ := rfl
/-
**Con.toSetoid_bot** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Mul M], ⊥.toSetoid = ⊥
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive (attr := simp)] lemma toSetoid_bot : (⊥ : Con M).toSetoid = ⊥ := rfl

@[to_additive (attr := simp)]
/-
**Con.toSetoid_eq_top** 是 Mathlib 中的一个引理，位于命名空间 `Con`。
形式化陈述：toSetoid_eq_top : c.toSetoid = ⊤ ↔ c = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Con.toSetoid_top`：∀ {M : Type u_1} [inst : Mul M], ⊤.toSetoid = ⊤
· 使用定理 `Con.toSetoid_inj`：∀ {M : Type u_1} [inst : Mul M] {c d : Con M}, c.toSet
oid = d.toSetoid ↔ c = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toSetoid_eq_top : c.toSetoid = ⊤ ↔ c = ⊤ := by rw [← toSetoid_top, toSetoid_inj]

@[to_additive (attr := simp)]
/-
**Con.toSetoid_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `Con`。
形式化陈述：toSetoid_eq_bot : c.toSetoid = ⊥ ↔ c = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Con.toSetoid_bot`：∀ {M : Type u_1} [inst : Mul M], ⊥.toSetoid = ⊥
· 使用定理 `Con.toSetoid_inj`：∀ {M : Type u_1} [inst : Mul M] {c d : Con M}, c.toSet
oid = d.toSetoid ↔ c = d
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma toSetoid_eq_bot : c.toSetoid = ⊥ ↔ c = ⊥ := by rw [← toSetoid_bot, toSetoid_inj]

/-- Definition of the infimum of two congruence relations. -/
@[to_additive /-- Definition of the infimum of two additive congruence relations. -/]
/-
**Con.inf_iff_and** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：inf_iff_and {c d : Con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Definition of the infimum of two congruence relations.
-/
theorem inf_iff_and {c d : Con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl

@[to_additive]
/-
**Con.le_conGen** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：le_conGen {r : M -> M -> Prop} : r <= ⇑(conGen r)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_conGen {r : M → M → Prop} : r ≤ ⇑(conGen r) := ConGen.Rel.of

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
the infimum of the set of congruence relations containing `r`. -/
@[to_additive /-- The inductively defined smallest additive congruence relation
containing a binary relation `r` equals the infimum of the set of additive congruence relations
containing `r`. -/]
/-
**Con.conGen_eq** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_eq (r : M -> M -> Prop) : conGen r = sInf { s : Con M | forall x y,
 r x y -> s x y }
参数：r : M -> M -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
-/
theorem conGen_eq (r : M → M → Prop) : conGen r = sInf { s : Con M | ∀ x y, r x y → s x y } :=
  le_antisymm
    (le_sInf (fun s hs x y (hxy : (conGen r) x y) =>
      show s x y by
        apply ConGen.Rel.recOn (motive := fun x y _ => s x y) hxy
        · exact fun x y h => hs x y h
        · exact s.refl'
        · exact fun _ => s.symm'
        · exact fun _ _ => s.trans'
        · exact fun _ _ => s.mul))
    (sInf_le ConGen.Rel.of)

/-- The smallest congruence relation containing a binary relation `r` is contained in any
congruence relation containing `r`. -/
@[to_additive /-- The smallest additive congruence relation containing a binary
relation `r` is contained in any additive congruence relation containing `r`. -/]
/-
**Con.conGen_le** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_le {r : M -> M -> Prop} {c : Con M} : conGen r <= c ↔ r <= ⇑c
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Con.le_conGen`：le_conGen {r : M -> M -> Prop} : r <= ⇑(conGen r)
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Con.conGen_eq`：conGen_eq (r : M -> M -> Prop) : conGen r = sInf { s : Co
n M | forall x y, r x y -> s x y }
-/
theorem conGen_le {r : M → M → Prop} {c : Con M} : conGen r ≤ c ↔ r ≤ ⇑c :=
  ⟨le_trans le_conGen, conGen_eq r ▸ fun h => sInf_le h⟩

variable (M) in
/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
binary relations on `M`. -/
@[to_additive /-- There is a Galois insertion of additive congruence relations on a type with
an addition `M` into binary relations on `M`. -/]
/-
**Con.gi** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：(M : Type u_1) → [inst : Mul M] → GaloisInsertion conGen DFunLike.coe
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Con.conGen_le`：conGen_le {r : M -> M -> Prop} {c : Con M} : conGen r <= 
c ↔ r <= ⇑c
-/
protected def gi : GaloisInsertion (conGen (M := M)) DFunLike.coe where
  choice r _ := conGen r
  gc _ _ := conGen_le
  le_l_u _ := le_conGen
  choice_eq _ _ := rfl

@[to_additive]
/-
**Con.conGen_monotone** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_monotone : Monotone (conGen (M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.monotone_l`：∀ {α : Type u} {β : Type v} [inst : Preorde
r α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u → Mon
otone l
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem conGen_monotone : Monotone (conGen (M := M)) :=
  Con.gi M |>.gc.monotone_l

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
containing `s` contains the smallest congruence relation containing `r`. -/
@[to_additive /-- Given binary relations `r, s` with `r` contained in `s`, the
smallest additive congruence relation containing `s` contains the smallest additive congruence
relation containing `r`. -/]
/-
**Con.conGen_mono** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_mono {r s : M -> M -> Prop} (h : forall x y, r x y -> s x y) : conG
en r <= conGen s
参数：h : forall x y, r x y -> s x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.conGen_monotone`：conGen_monotone : Monotone (conGen (M
-/
theorem conGen_mono {r s : M → M → Prop} (h : ∀ x y, r x y → s x y) : conGen r ≤ conGen s :=
  conGen_monotone h

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[to_additive (attr := simp) addConGen_of_addCon /-- Additive congruence relations equal the
smallest additive congruence relation in which they are contained. -/]
/-
**Con.conGen_of_con** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_of_con (c : Con M) : conGen c = c
参数：c : Con M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisInsertion.l_u_eq`：l_u_eq [Preorder α] [PartialOrder β] (gi : Galoi
sInsertion l u) (b : β) : l (u b) = b
-/
theorem conGen_of_con (c : Con M) : conGen c = c :=
  Con.gi M |>.l_u_eq _

/-- The map sending a binary relation to the smallest congruence relation in which it is
contained is idempotent. -/
@[to_additive /-- The map sending a binary relation to the smallest additive
congruence relation in which it is contained is idempotent. -/]
/-
**Con.conGen_idem** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_idem (r : M -> M -> Prop) : conGen (conGen r) = conGen r
参数：r : M -> M -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_u_l_eq_l`：∀ {α : Type u} {β : Type v} [inst : Partial
Order α] [inst_1 : Preorder β] {u : α → β} {l : β → α},   GaloisConnection l u →
 ∀ (b : β), l (u …
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem conGen_idem (r : M → M → Prop) : conGen (conGen r) = conGen r :=
  Con.gi M |>.gc.l_u_l_eq_l _
/-
**Con.conGen_sup** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_sup (r s : M -> M -> Prop) : conGen (r ⊔ s) = conGen r ⊔ conGen s
参数：r s : M -> M -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem conGen_sup (r s : M → M → Prop) : conGen (r ⊔ s) = conGen r ⊔ conGen s :=
  Con.gi M |>.gc.l_sup
/-
**Con.conGen_sSup** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_sSup (rs : Set (M -> M -> Prop)) : conGen (sSup rs) = ⨆ r in rs, co
nGen r
参数：rs : Set (M -> M -> Prop)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sSup`：l_sSup {s : Set α} : l (sSup s) = ⨆ a in s, l a
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem conGen_sSup (rs : Set (M → M → Prop)) : conGen (sSup rs) = ⨆ r ∈ rs, conGen r :=
  Con.gi M |>.gc.l_sSup
/-
**Con.conGen_iSup** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：conGen_iSup {ι : Sort*} (r : ι -> M -> M -> Prop) : conGen (iSup r) = ⨆ i,
 conGen (r i)
参数：r : ι -> M -> M -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_iSup`：l_iSup {f : ι -> α} : l (iSup f) = ⨆ i, l (f i)
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…
-/
theorem conGen_iSup {ι : Sort*} (r : ι → M → M → Prop) : conGen (iSup r) = ⨆ i, conGen (r i) :=
  Con.gi M |>.gc.l_iSup

/-- The supremum of two congruence relations equals the smallest congruence relation containing
the supremum of the underlying binary operations. -/
@[to_additive /-- The supremum of two additive congruence relations equals the smallest additive
congruence relation containing the supremum of the underlying binary operations. -/]
/-
**Con.sup_def** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：sup_def (c d : Con M) : c ⊔ d = conGen (⇑c ⊔ ⇑d)
参数：c d : Con M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisInsertion.l_sup_u`：l_sup_u [SemilatticeSup α] [SemilatticeSup β] (
gi : GaloisInsertion l u) (a b : β) : l (u a ⊔ u b) = a ⊔ b
-/
theorem sup_def (c d : Con M) : c ⊔ d = conGen (⇑c ⊔ ⇑d) :=
  Con.gi M |>.l_sup_u _ _ |>.symm

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
the binary relation '`x` is related to `y` by `c` or `d`'. -/
@[to_additive /-- The supremum of additive congruence relations `c, d` equals the
smallest additive congruence relation containing the binary relation '`x` is related to `y`
by `c` or `d`'. -/]
/-
**Con.sup_eq_conGen** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：sup_eq_conGen (c d : Con M) : c ⊔ d = conGen fun x y => c x y ∨ d x y
参数：c d : Con M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.sup_def`：sup_def (c d : Con M) : c ⊔ d = conGen (⇑c ⊔ ⇑d)
-/
theorem sup_eq_conGen (c d : Con M) : c ⊔ d = conGen fun x y => c x y ∨ d x y :=
  sup_def _ _

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
containing the supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive /-- The supremum of a set of additive congruence relations is the same as the smallest
additive congruence relation containing the supremum of the set's image under the map to the
underlying binary relation. -/]
/-
**Con.sSup_def** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：sSup_def (S : Set (Con M)) : sSup S = conGen (sSup ((⇑) '' S))
参数：S : Set (Con M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `GaloisInsertion.l_sSup_u_image`：l_sSup_u_image [CompleteLattice α] [Comp
leteLattice β] (gi : GaloisInsertion l u) (s : Set β) : l (sSup (u '' s)) = sSup
 s
-/
theorem sSup_def (S : Set (Con M)) : sSup S = conGen (sSup ((⇑) '' S)) :=
  Con.gi M |>.l_sSup_u_image _ |>.symm

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by `c`'. -/
@[to_additive /-- The supremum of a set of additive congruence relations `S`
equals the smallest additive congruence relation containing the binary relation 'there exists
`c ∈ S` such that `x` is related to `y` by `c`'. -/]
/-
**Con.sSup_eq_conGen** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：sSup_eq_conGen (S : Set (Con M)) : sSup S = conGen fun x y => exists c : C
on M, c in S ∧ c x y
参数：S : Set (Con M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Con.sSup_def`：sSup_def (S : Set (Con M)) : sSup S = conGen (sSup ((⇑) ''
 S))
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_apply`：iSup_apply {α : Type*} {β : α -> Type*} {ι : Sort*} [forall 
i, SupSet (β i)] {f : ι -> forall a, β a} {a : α} : (⨆ i, f i) a = ⨆ i, f i a
· 使用定理 `iSup_Prop_eq`：iSup_Prop_eq {p : ι -> Prop} : ⨆ i, p i = exists i, p i
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem sSup_eq_conGen (S : Set (Con M)) :
    sSup S = conGen fun x y => ∃ c : Con M, c ∈ S ∧ c x y := by
  rw [sSup_def]
  congr! with x y
  simp

variable (c)


/-- Given types with multiplications `M, N` and a congruence relation `c` on `N`, a
multiplication-preserving map `f : M → N` induces a congruence relation on `f`'s domain
defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/
@[to_additive /-- Given types with additions `M, N` and an additive congruence relation `c` on `N`,
an addition-preserving map `f : M → N` induces an additive congruence relation on `f`'s domain
defined by '`x ≈ y` iff `f(x)` is related to `f(y)` by `c`.' -/]
/-
**Con.comap** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：comap (f : M -> N) (H : forall x y, f (x * y) = f x * f y) (c : Con N) : C
on M
参数：f : M -> N；H : forall x y, f (x * y) = f x * f y；c : Con N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def comap (f : M → N) (H : ∀ x y, f (x * y) = f x * f y) (c : Con N) : Con M :=
  { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }

@[to_additive (attr := simp)]
/-
**Con.comap_rel** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：comap_rel {f : M -> N} (H : forall x y, f (x * y) = f x * f y) {c : Con N}
 {x y : M} : comap f H c x y ↔ c (f x) (f y)
参数：H : forall x y, f (x * y) = f x * f y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_rel {f : M → N} (H : ∀ x y, f (x * y) = f x * f y) {c : Con N} {x y : M} :
    comap f H c x y ↔ c (f x) (f y) :=
  Iff.rfl

@[to_additive (attr := simp)]
/-
**Con.comap_id** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：comap_id (c : Con M) : c.comap id (by intros; rfl) = c
参数：c : Con M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_id (c : Con M) : c.comap id (by intros; rfl) = c := rfl

@[to_additive (attr := simp)]
/-
**Con.comap_comp** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：comap_comp (c : Con P) (g : N -> P) (f : M -> N) (hg) (hf) : c.comap (g ∘ 
f) (by grind) = (c.comap g hg).comap f hf
参数：c : Con P；g : N -> P；f : M -> N；hg；hf。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_comp (c : Con P) (g : N → P) (f : M → N) (hg) (hf) :
    c.comap (g ∘ f) (by grind) = (c.comap g hg).comap f hf := rfl

@[to_additive]
/-
**Con.le_comap_conGen** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：le_comap_conGen (r : N -> N -> Prop) (f : M -> N) (hf) : conGen (r.onFun f
) <= (conGen r).comap f hf
参数：r : N -> N -> Prop；f : M -> N；hf。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Con.conGen_le`：conGen_le {r : M -> M -> Prop} {c : Con M} : conGen r <= 
c ↔ r <= ⇑c
-/
theorem le_comap_conGen (r : N → N → Prop) (f : M → N) (hf) :
    conGen (r.onFun f) ≤ (conGen r).comap f hf :=
  conGen_le.2 fun _ _ h => ConGen.Rel.of _ _ h

@[to_additive]
/-
**Con.comap_injective** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：comap_injective (f : M -> N) (hf : Function.Surjective f) (hf') : Function
.Injective (comap f hf')
参数：f : M -> N；hf : Function.Surjective f；hf'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Setoid.comap_injective`：comap_injective (f : α -> β) (hf : Function.Surj
ective f) : Function.Injective (comap f)
· 使用定理 `Con.toSetoid_injective`：∀ {M : Type u_1} [inst : Mul M], Function.Inject
ive Con.toSetoid
-/
theorem comap_injective (f : M → N) (hf : Function.Surjective f) (hf') :
    Function.Injective (comap f hf') :=
  .of_comp (f := toSetoid) <| (Setoid.comap_injective f hf).comp toSetoid_injective

end

section

variable [Mul M] [One M] (c : Con M)

@[to_additive]
/-
**Con.one** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：one : One c.Quotient where -- Using Quotient.mk'' here instead of c.toQuot
ient -- since c.toQuotient is not reducible. -- This would lead to non-defeq dia
monds since this instance ends up in -- quotients modulo ideals. one
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance one : One c.Quotient where
  -- Using Quotient.mk'' here instead of c.toQuotient
  -- since c.toQuotient is not reducible.
  -- This would lead to non-defeq diamonds since this instance ends up in
  -- quotients modulo ideals.
  one := Quotient.mk'' (1 : M)
  -- one := ((1 : M) : c.Quotient)

variable {c}

/-- The 1 of the quotient of a monoid by a congruence relation is the equivalence class of the
monoid's 1. -/
@[to_additive (attr := simp) /-- The 0 of the quotient of an `AddMonoid` by an additive congruence
relation is the equivalence class of the `AddMonoid`'s 0. -/]
/-
**Con.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：coe_one : ((1 : M) : c.Quotient) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : M) : c.Quotient) = 1 :=
  rfl

/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
@[to_additive /-- There exists an element of the quotient of an `AddMonoid` by a congruence relation
(namely 0). -/]
/-
**Con.Quotient.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `Con.Quotient`。
形式化陈述：{M : Type u_1} → [inst : Mul M] → [One M] → {c : Con M} → Inhabited c.Quot
ient
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Quotient.inhabited : Inhabited c.Quotient :=
  ⟨((1 : M) : c.Quotient)⟩

end

section MulOneClass

variable [MulOneClass M] (c : Con M)

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive /-- The quotient of an `AddMonoid` by an additive congruence relation is
an `AddMonoid`. -/]
/-
**Con.mulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：mulOneClass : MulOneClass c.Quotient where mul_one x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance mulOneClass : MulOneClass c.Quotient where
  mul_one x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M → c.Quotient) <| mul_one _
  one_mul x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M → c.Quotient) <| one_mul _

end MulOneClass

section Monoids

/-- Multiplicative congruence relations preserve natural powers. -/
@[to_additive /-- Additive congruence relations preserve natural scaling. -/]
/-
**Con.pow** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_4} [inst : Monoid M] (c : Con M) (n : ℕ) {w x : M}, c w x → 
c (w ^ n) (x ^ n)
参数：c : Con M；n : ℕ；w ^ n；x ^ n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multiplicative congruence relations preserve natural powers.
-/
protected theorem pow {M : Type*} [Monoid M] (c : Con M) :
    ∀ (n : ℕ) {w x}, c w x → c (w ^ n) (x ^ n)
  | 0, w, x, _ => by simpa using c.refl _
  | Nat.succ n, w, x, h => by simpa [pow_succ] using c.mul (Con.pow c n h) h

@[to_additive]
/-
**Con.** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {M : Type*} [Monoid M] (c : Con M) : Pow c.Quotient ℕ where
  pow x n := Quotient.map' (fun x => x ^ n) (fun _ _ => c.pow n) x

/-- The quotient of a semigroup by a congruence relation is a semigroup. -/
@[to_additive /-- The quotient of an `AddSemigroup` by an additive congruence relation is
an `AddSemigroup`. -/]
/-
**Con.semigroup** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：semigroup {M : Type*} [Semigroup M] (c : Con M) : Semigroup c.Quotient
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance semigroup {M : Type*} [Semigroup M] (c : Con M) : Semigroup c.Quotient := fast_instance%
  Function.Surjective.semigroup _ Quotient.mk''_surjective fun _ _ => rfl

/-- The quotient of a commutative magma by a congruence relation is a commutative magma. -/
@[to_additive /-- The quotient of an `AddCommMagma` by an additive congruence relation is
an `AddCommMagma`. -/]
/-
**Con.commMagma** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：commMagma {M : Type*} [CommMagma M] (c : Con M) : CommMagma c.Quotient
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMagma {M : Type*} [CommMagma M] (c : Con M) : CommMagma c.Quotient := fast_instance%
  Function.Surjective.commMagma _ Quotient.mk''_surjective fun _ _ => rfl

/-- The quotient of a commutative semigroup by a congruence relation is a semigroup. -/
@[to_additive /-- The quotient of an `AddCommSemigroup` by an additive congruence relation is
an `AddCommSemigroup`. -/]
/-
**Con.commSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：commSemigroup {M : Type*} [CommSemigroup M] (c : Con M) : CommSemigroup c.
Quotient
参数：c : Con M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
instance commSemigroup {M : Type*} [CommSemigroup M] (c : Con M) : CommSemigroup c.Quotient :=
  Function.Surjective.commSemigroup _ Quotient.mk''_surjective fun _ _ => rfl

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive /-- The quotient of an `AddMonoid` by an additive congruence relation is
an `AddMonoid`. -/]
/-
**Con.monoid** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：monoid {M : Type*} [Monoid M] (c : Con M) : Monoid c.Quotient
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance monoid {M : Type*} [Monoid M] (c : Con M) : Monoid c.Quotient := fast_instance%
  Function.Surjective.monoid _ Quotient.mk''_surjective rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The quotient of a `CommMonoid` by a congruence relation is a `CommMonoid`. -/
@[to_additive /-- The quotient of an `AddCommMonoid` by an additive congruence
relation is an `AddCommMonoid`. -/]
/-
**Con.commMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：commMonoid {M : Type*} [CommMonoid M] (c : Con M) : CommMonoid c.Quotient
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commMonoid {M : Type*} [CommMonoid M] (c : Con M) : CommMonoid c.Quotient := fast_instance%
  fast_instance% Function.Surjective.commMonoid _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) fun _ _ => rfl

/-- Sometimes, a group is defined as a quotient of a monoid by a congruence relation.
Usually, the inverse operation is defined as `Setoid.map f _` for some `f`.
This lemma allows to avoid code duplication in the definition of the inverse operation:
instead of proving both `∀ x y, c x y → c (f x) (f y)` (to define the operation)
and `∀ x, c (f x * x) 1` (to prove the group laws), one can only prove the latter. -/
@[to_additive /-- Sometimes, an additive group is defined as a quotient of a monoid
  by an additive congruence relation.
  Usually, the inverse operation is defined as `Setoid.map f _` for some `f`.
  This lemma allows to avoid code duplication in the definition of the inverse operation:
  instead of proving both `∀ x y, c x y → c (f x) (f y)` (to define the operation)
  and `∀ x, c (f x + x) 0` (to prove the group laws), one can only prove the latter. -/]
/-
**Con.map_of_mul_left_rel_one** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：map_of_mul_left_rel_one [Monoid M] (c : Con M) (f : M -> M) (hf : forall x
, c (f x * x) 1) {x y} (h : c x y) : c (f x) (f y)
参数：c : Con M；f : M -> M；hf : forall x, c (f x * x) 1；h : c x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Units.ext`：ext {u v : αˣ} (huv : u.val = v.val) : u = v
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem map_of_mul_left_rel_one [Monoid M] (c : Con M)
    (f : M → M) (hf : ∀ x, c (f x * x) 1) {x y} (h : c x y) : c (f x) (f y) := by
  simp only [← Con.eq, coe_one, coe_mul] at *
  have hf' : ∀ x : M, (x : c.Quotient) * f x = 1 := fun x ↦
    calc
      (x : c.Quotient) * f x = f (f x) * f x * (x * f x) := by simp [hf]
      _ = f (f x) * (f x * x) * f x := by simp_rw [mul_assoc]
      _ = 1 := by simp [hf]
  have : (⟨_, _, hf' x, hf x⟩ : c.Quotientˣ) = ⟨_, _, hf' y, hf y⟩ := Units.ext h
  exact congr_arg Units.inv this

end Monoids

section Groups

variable [Group M] (c : Con M)

/-- Multiplicative congruence relations preserve inversion. -/
@[to_additive /-- Additive congruence relations preserve negation. -/]
/-
**Con.inv** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Group M] (c : Con M) {x y : M}, c x y → c x⁻¹ y⁻¹
参数：c : Con M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.map_of_mul_left_rel_one`：map_of_mul_left_rel_one [Monoid M] (c : Con
 M) (f : M -> M) (hf : forall x, c (f x * x) 1) {x y} (h : c x y) : c (f x) (f y
)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Con.refl`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) (x : M), c x x

--- 原说明 ---
Multiplicative congruence relations preserve inversion.
-/
protected theorem inv {x y} (h : c x y) : c x⁻¹ y⁻¹ :=
  c.map_of_mul_left_rel_one Inv.inv (fun x => by simp only [inv_mul_cancel, c.refl 1]) h

/-- Multiplicative congruence relations preserve division. -/
@[to_additive /-- Additive congruence relations preserve subtraction. -/]
/-
**Con.div** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Group M] (c : Con M) {w x y z : M}, c w x → c y z
 → c (w / y) (x / z)
参数：c : Con M；w / y；x / z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Con.mul`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {w x y z : M}, c w 
x → c y z → c (w * y) (x * z)
· 使用定理 `Con.inv`：∀ {M : Type u_1} [inst : Group M] (c : Con M) {x y : M}, c x y 
→ c x⁻¹ y⁻¹

--- 原说明 ---
Multiplicative congruence relations preserve division.
-/
protected theorem div : ∀ {w x y z}, c w x → c y z → c (w / y) (x / z) := @fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv h2)

/-- Multiplicative congruence relations preserve integer powers. -/
@[to_additive /-- Additive congruence relations preserve integer scaling. -/]
/-
**Con.zpow** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：∀ {M : Type u_1} [inst : Group M] (c : Con M) (n : ℤ) {w x : M}, c w x → c
 (w ^ n) (x ^ n)
参数：c : Con M；n : ℤ；w ^ n；x ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `Con.pow`：∀ {M : Type u_4} [inst : Monoid M] (c : Con M) (n : ℕ) {w x : M
}, c w x → c (w ^ n) (x ^ n)
· 使用定理 `zpow_negSucc`：zpow_negSucc (a : G) (n : Nat) : a ^ (Int.negSucc n) = (a 
^ (n + 1))⁻¹
· 使用定理 `Con.inv`：∀ {M : Type u_1} [inst : Group M] (c : Con M) {x y : M}, c x y 
→ c x⁻¹ y⁻¹

--- 原说明 ---
Multiplicative congruence relations preserve integer powers.
-/
protected theorem zpow : ∀ (n : ℤ) {w x}, c w x → c (w ^ n) (x ^ n)
  | Int.ofNat n, w, x, h => by simpa only [zpow_natCast, Int.ofNat_eq_natCast] using c.pow n h
  | Int.negSucc n, w, x, h => by simpa only [zpow_negSucc] using c.inv (c.pow _ h)

/-- The inversion induced on the quotient by a congruence relation on a type with an
inversion. -/
@[to_additive /-- The negation induced on the quotient by an additive congruence relation on a type
with a negation. -/]
/-
**Con.hasInv** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：hasInv : Inv c.Quotient
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Con.inv`：∀ {M : Type u_1} [inst : Group M] (c : Con M) {x y : M}, c x y 
→ c x⁻¹ y⁻¹
-/
instance hasInv : Inv c.Quotient :=
  ⟨(Quotient.map' Inv.inv) fun _ _ => c.inv⟩

/-- The division induced on the quotient by a congruence relation on a type with a
division. -/
@[to_additive /-- The subtraction induced on the quotient by an additive congruence relation on a
type with a subtraction. -/]
/-
**Con.hasDiv** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：hasDiv : Div c.Quotient
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.div`：∀ {M : Type u_1} [inst : Group M] (c : Con M) {w x y z : M}, c 
w x → c y z → c (w / y) (x / z)
-/
instance hasDiv : Div c.Quotient :=
  ⟨(Quotient.map₂ (· / ·)) fun _ _ h₁ _ _ h₂ => c.div h₁ h₂⟩

/-- The integer power induced on the quotient by a congruence relation on a type with a
division. -/
@[to_additive /-- The integer scaling induced on the quotient by a congruence relation on a type
with a subtraction. -/]
/-
**Con.instZPow** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：instZPow : Pow c.Quotient Int
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)
· 使用定理 `Con.zpow`：∀ {M : Type u_1} [inst : Group M] (c : Con M) (n : ℤ) {w x : M
}, c w x → c (w ^ n) (x ^ n)
-/
instance instZPow : Pow c.Quotient ℤ :=
  ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun _ _ h => c.zpow z h) x⟩

/-- The quotient of a group by a congruence relation is a group. -/
@[to_additive /-- The quotient of an `AddGroup` by an additive congruence relation is
an `AddGroup`. -/]
/-
**Con.group** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：group : Group c.Quotient
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance group : Group c.Quotient := fast_instance%
  Function.Surjective.group Quotient.mk'' Quotient.mk''_surjective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- The quotient of a `CommGroup` by a congruence relation is a `CommGroup`. -/
@[to_additive /-- The quotient of an `AddCommGroup` by an additive congruence
relation is an `AddCommGroup`. -/]
/-
**Con.commGroup** 是 Mathlib 中的一个实例，位于命名空间 `Con`。
形式化陈述：commGroup {M : Type*} [CommGroup M] (c : Con M) : CommGroup c.Quotient
参数：c : Con M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance commGroup {M : Type*} [CommGroup M] (c : Con M) : CommGroup c.Quotient := fast_instance%
  Function.Surjective.commGroup _ Quotient.mk''_surjective rfl (fun _ _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

end Groups

section Units

variable {α : Type*} [Monoid M] {c : Con M}

/-- In order to define a function `(Con.Quotient c)ˣ → α` on the units of `Con.Quotient c`,
where `c : Con M` is a multiplicative congruence on a monoid, it suffices to define a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, and returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`. -/
@[to_additive]
/-
**Con.liftOnUnits** 是 Mathlib 中的一个定义，位于命名空间 `Con`。
形式化陈述：liftOnUnits (u : Units c.Quotient) (f : forall x y : M, c (x * y) 1 -> c (
y * x) 1 -> α) (Hf : forall x y hxy hyx x' y' hxy' hyx', c x x' -> c y y' -> f x
 y hxy hyx = f x' y' hxy' hyx') : α
参数：u : Units c.Quotient；f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α；Hf :
 forall x y hxy hyx x' y' hxy' hyx', c x x' -> c y y' -> f x y hxy hyx = f x' y'
 hxy' hyx'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In order to define a function `(Con.Quotient c)ˣ → α` on the units of `Con.Quoti
ent c`,
where `c : Con M` is a multiplicative congruence on a monoid, it suffices to def
ine a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, an
d returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`.
-/
def liftOnUnits (u : Units c.Quotient) (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx',
      c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx') : α := by
  refine
    Con.hrecOn₂ (cN := c) (φ := fun x y => x * y = 1 → y * x = 1 → α) (u : c.Quotient)
      (↑u⁻¹ : c.Quotient)
      (fun (x y : M) (hxy : (x * y : c.Quotient) = 1) (hyx : (y * x : c.Quotient) = 1) =>
        f x y (c.eq.1 hxy) (c.eq.1 hyx))
      (fun x y x' y' hx hy => ?_) u.3 u.4
  refine Function.hfunext ?_ ?_
  · rw [c.eq.2 hx, c.eq.2 hy]
  · rintro Hxy Hxy' -
    refine Function.hfunext ?_ ?_
    · rw [c.eq.2 hx, c.eq.2 hy]
    · rintro Hyx Hyx' -
      exact heq_of_eq (Hf _ _ _ _ _ _ _ _ hx hy)

/-- In order to define a function `(Con.Quotient c)ˣ → α` on the units of `Con.Quotient c`,
where `c : Con M` is a multiplicative congruence on a monoid, it suffices to define a function `f`
that takes elements `x y : M` with proofs of `c (x * y) 1` and `c (y * x) 1`, and returns an element
of `α` provided that `f x y _ _ = f x' y' _ _` whenever `c x x'` and `c y y'`. -/
add_decl_doc AddCon.liftOnAddUnits

@[to_additive (attr := simp)]
/-
**Con.liftOnUnits_mk** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：liftOnUnits_mk (f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α) (Hf :
 forall x y hxy hyx x' y' hxy' hyx', c x x' -> c y y' -> f x y hxy hyx = f x' y'
 hxy' hyx') (x y : M) (hxy hyx) : liftOnUnits ⟨(x : c.Quotient), y, hxy, hyx⟩ f 
Hf = f x y (c.eq.1 hxy) (c.eq.1 hyx)
参数：f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α；Hf : forall x y hxy hyx x
' y' hxy' hyx', c x x' -> c y y' -> f x y hxy hyx = f x' y' hxy' hyx'；x y : M；hx
y hyx。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem liftOnUnits_mk (f : ∀ x y : M, c (x * y) 1 → c (y * x) 1 → α)
    (Hf : ∀ x y hxy hyx x' y' hxy' hyx', c x x' → c y y' → f x y hxy hyx = f x' y' hxy' hyx')
    (x y : M) (hxy hyx) :
    liftOnUnits ⟨(x : c.Quotient), y, hxy, hyx⟩ f Hf = f x y (c.eq.1 hxy) (c.eq.1 hyx) :=
  rfl

@[to_additive (attr := elab_as_elim)]
/-
**Con.induction_on_units** 是 Mathlib 中的一个定理，位于命名空间 `Con`。
形式化陈述：induction_on_units {p : Units c.Quotient -> Prop} (u : Units c.Quotient) (
H : forall (x y : M) (hxy : c (x * y) 1) (hyx : c (y * x) 1), p ⟨x, y, c.eq.2 hx
y, c.eq.2 hyx⟩) : p u
参数：u : Units c.Quotient；H : forall (x y : M) (hxy : c (x * y) 1) (hyx : c (y * x
) 1), p ⟨x, y, c.eq.2 hxy, c.eq.2 hyx⟩。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Con.eq`：∀ {M : Type u_1} [inst : Mul M] (c : Con M) {a b : M}, ↑a = ↑b ↔
 c a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem induction_on_units {p : Units c.Quotient → Prop} (u : Units c.Quotient)
    (H : ∀ (x y : M) (hxy : c (x * y) 1) (hyx : c (y * x) 1), p ⟨x, y, c.eq.2 hxy, c.eq.2 hyx⟩) :
    p u := by
  rcases u with ⟨⟨x⟩, ⟨y⟩, h₁, h₂⟩
  exact H x y (c.eq.1 h₁) (c.eq.1 h₂)

end Units

end Con

