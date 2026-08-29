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

/--
Definition of `AddCon` / `AddCon` 的定义

English:
structure AddCon
  parameters: [Add M]
  extends: Setoid M
  axioms and operations (1):
    - add' : forall {w x y z}, r w x -> r y z -> r (w + y) (x + z)

中文:
结构 加法Con
  参数: [加法 M]
  继承: 集合等价关系 M
  公理与运算 (1 个):
    - add' : 对任意 {w x y z}, r w x -> r y z -> r (w + y) (x + z)
-/
structure AddCon [Add M] extends Setoid M where
  /-- Additive congruence relations are closed under addition -/
  add' : forall {w x y z}, r w x -> r y z -> r (w + y) (x + z)

/-- A congruence relation on a type with a multiplication is an equivalence relation which
preserves multiplication. -/
@[to_additive AddCon]
/--
Definition of `Con` / `Con` 的定义

English:
structure Con
  parameters: [Mul M]
  extends: Setoid M
  axioms and operations (1):
    - mul' : forall {w x y z}, r w x -> r y z -> r (w * y) (x * z)

中文:
结构 Con
  参数: [乘法 M]
  继承: 集合等价关系 M
  公理与运算 (1 个):
    - mul' : 对任意 {w x y z}, r w x -> r y z -> r (w * y) (x * z)
-/
structure Con [Mul M] extends Setoid M where
  /-- Congruence relations are closed under multiplication -/
  mul' : forall {w x y z}, r w x -> r y z -> r (w * y) (x * z)

/-- The equivalence relation underlying an additive congruence relation. -/
add_decl_doc AddCon.toSetoid

/-- The equivalence relation underlying a multiplicative congruence relation. -/
add_decl_doc Con.toSetoid

variable {M}

/--
Inductive type `AddConGen.Rel` / 归纳类型 `AddConGen.Rel`

English:
inductive AddConGen.Rel
  parameters: [Add M] (r : M -> M -> Prop)
  constructors (5):
    - of: forall x y, r x y -> AddConGen.Rel r x y
    - refl: forall x, AddConGen.Rel r x x
    - symm: forall {x y}, AddConGen.Rel r x y -> AddConGen.Rel r y x
    - trans: forall {x y z}, AddConGen.Rel r x y -> AddConGen.Rel r y z -> AddConGen.Rel r x z
    - add: forall {w x y z}, AddConGen.Rel r w x -> AddConGen.Rel r y z -> AddConGen.Rel r (w + y) (x + z)

中文:
归纳类型 AddConGen.关系
  参数: [加法 M] (r : M -> M -> 命题)
  构造子 (5 个):
    - of: 对任意 x y, r x y -> AddConGen.关系 r x y
    - refl: 对任意 x, AddConGen.关系 r x x
    - symm: 对任意 {x y}, AddConGen.关系 r x y -> AddConGen.关系 r y x
    - trans: 对任意 {x y z}, AddConGen.关系 r x y -> AddConGen.关系 r y z -> AddConGen.关系 r x z
    - add: 对任意 {w x y z}, AddConGen.关系 r w x -> AddConGen.关系 r y z -> AddConGen.关系 r (w + y) (x + z)
-/
inductive AddConGen.Rel [Add M] (r : M -> M -> Prop) : M -> M -> Prop
  | of : forall x y, r x y -> AddConGen.Rel r x y
  | refl : forall x, AddConGen.Rel r x x
  | symm : forall {x y}, AddConGen.Rel r x y -> AddConGen.Rel r y x
  | trans : forall {x y z}, AddConGen.Rel r x y -> AddConGen.Rel r y z -> AddConGen.Rel r x z
  | add : forall {w x y z}, AddConGen.Rel r w x -> AddConGen.Rel r y z -> AddConGen.Rel r (w + y) (x + z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
relation. -/
@[to_additive AddConGen.Rel]
/--
Inductive type `ConGen.Rel` / 归纳类型 `ConGen.Rel`

English:
inductive ConGen.Rel
  parameters: [Mul M] (r : M -> M -> Prop)
  constructors (5):
    - of: forall x y, r x y -> ConGen.Rel r x y
    - refl: forall x, ConGen.Rel r x x
    - symm: forall {x y}, ConGen.Rel r x y -> ConGen.Rel r y x
    - trans: forall {x y z}, ConGen.Rel r x y -> ConGen.Rel r y z -> ConGen.Rel r x z
    - mul: forall {w x y z}, ConGen.Rel r w x -> ConGen.Rel r y z -> ConGen.Rel r (w * y) (x * z)

中文:
归纳类型 ConGen.关系
  参数: [乘法 M] (r : M -> M -> 命题)
  构造子 (5 个):
    - of: 对任意 x y, r x y -> ConGen.关系 r x y
    - refl: 对任意 x, ConGen.关系 r x x
    - symm: 对任意 {x y}, ConGen.关系 r x y -> ConGen.关系 r y x
    - trans: 对任意 {x y z}, ConGen.关系 r x y -> ConGen.关系 r y z -> ConGen.关系 r x z
    - mul: 对任意 {w x y z}, ConGen.关系 r w x -> ConGen.关系 r y z -> ConGen.关系 r (w * y) (x * z)
-/
inductive ConGen.Rel [Mul M] (r : M -> M -> Prop) : M -> M -> Prop
  | of : forall x y, r x y -> ConGen.Rel r x y
  | refl : forall x, ConGen.Rel r x x
  | symm : forall {x y}, ConGen.Rel r x y -> ConGen.Rel r y x
  | trans : forall {x y z}, ConGen.Rel r x y -> ConGen.Rel r y z -> ConGen.Rel r x z
  | mul : forall {w x y z}, ConGen.Rel r w x -> ConGen.Rel r y z -> ConGen.Rel r (w * y) (x * z)

/-- The inductively defined smallest multiplicative congruence relation containing a given binary
relation. -/
@[to_additive /-- The inductively defined smallest additive congruence relation containing
a given binary relation. -/]
/--
Definition of `conGen` / `conGen` 的定义

English:
definition conGen
  signature: [Mul M] (r : M -> M -> Prop)
  body: ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩

中文:
定义 conGen
  签名: [乘法 M] (r : M -> M -> 命题)
  定义体: ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩

Depends on / 依赖: ConGen, ConGen.Rel, ConGen.Rel.mul, ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans
-/
def conGen [Mul M] (r : M -> M -> Prop) : Con M :=
  ⟨⟨ConGen.Rel r, ⟨ConGen.Rel.refl, ConGen.Rel.symm, ConGen.Rel.trans⟩⟩, ConGen.Rel.mul⟩

namespace Con

section

variable [Mul M] [Mul N] [Mul P] {c d : Con M}

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Con M)
  body: ⟨conGen emptyRelation⟩

中文:
实例 :
  签名: 可居 (Con M)
  定义体: ⟨conGen emptyRelation⟩

Depends on / 依赖: conGen, emptyRelation
-/
instance : Inhabited (Con M) :=
  ⟨conGen emptyRelation⟩

/--
lemma `toSetoid_injective` / 引理 `toSetoid_injective`

English:
lemma toSetoid_injective
  statement: Injective (toSetoid (M := M))
  proof: fun c d => by cases c; congr!

中文:
引理 toSetoid_injective
  结论: 单射 (toSetoid (M := M))
  证明: fun c d => by cases c; congr!
-/
@[to_additive] lemma toSetoid_injective : Injective (toSetoid (M := M)) :=
  fun c d => by cases c; congr!

/--
lemma `toSetoid_inj` / 引理 `toSetoid_inj`

English:
lemma toSetoid_inj
  statement: c.toSetoid = d.toSetoid ↔ c = d
  proof: toSetoid_injective.eq_iff

中文:
引理 toSetoid_inj
  结论: c.toSetoid = d.toSetoid ↔ c = d
  证明: toSetoid_injective.eq_iff
-/
@[to_additive (attr := simp)] lemma toSetoid_inj : c.toSetoid = d.toSetoid ↔ c = d :=
  toSetoid_injective.eq_iff

/-- A coercion from a congruence relation to its underlying binary relation. -/
@[to_additive
/-- A coercion from an additive congruence relation to its underlying binary relation. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (Con M) M (M -> Prop)
  body: c.r
  coe_injective x y h := by
    rcases x with ⟨⟨x, _⟩, _⟩
    rcases y with ⟨⟨y, _⟩, _⟩
    have : x = y := h
    subst x; rfl

中文:
实例 :
  签名: 函数状 (Con M) M (M -> 命题)
  定义体: c.r
  coe_injective x y h := by
    rcases x with ⟨⟨x, _⟩, _⟩
    rcases y with ⟨⟨y, _⟩, _⟩
    have : x = y := h
    subst x; rfl
-/
instance : FunLike (Con M) M (M -> Prop) where
  coe c := c.r
  coe_injective x y h := by
    rcases x with ⟨⟨x, _⟩, _⟩
    rcases y with ⟨⟨y, _⟩, _⟩
    have : x = y := h
    subst x; rfl

variable (c)

@[to_additive (attr := simp)]
/--
theorem `rel_eq_coe` / 定理 `rel_eq_coe`

English:
theorem rel_eq_coe
  given: (c : Con M)
  statement: c.r = c
  proof: rfl

中文:
定理 rel_eq_coe
  条件: (c : Con M)
  结论: c.r = c
  证明: rfl
-/
theorem rel_eq_coe (c : Con M) : c.r = c :=
  rfl

/-- Congruence relations are reflexive. -/
@[to_additive /-- Additive congruence relations are reflexive. -/]
/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (x)
  statement: c x x
  proof: c.toSetoid.refl' x

中文:
定理 refl
  条件: (x)
  结论: c x x
  证明: c.toSetoid.refl' x
-/
protected theorem refl (x) : c x x :=
  c.toSetoid.refl' x

/-- Congruence relations are symmetric. -/
@[to_additive /-- Additive congruence relations are symmetric. -/]
/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {x y}
  statement: c x y -> c y x
  proof: c.toSetoid.symm'

中文:
定理 symm
  条件: {x y}
  结论: c x y -> c y x
  证明: c.toSetoid.symm'
-/
protected theorem symm {x y} : c x y -> c y x := c.toSetoid.symm'

/-- Congruence relations are transitive. -/
@[to_additive /-- Additive congruence relations are transitive. -/]
/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {x y z}
  statement: c x y -> c y z -> c x z
  proof: c.toSetoid.trans'

中文:
定理 trans
  条件: {x y z}
  结论: c x y -> c y z -> c x z
  证明: c.toSetoid.trans'
-/
protected theorem trans {x y z} : c x y -> c y z -> c x z := c.toSetoid.trans'

/-- Multiplicative congruence relations preserve multiplication. -/
@[to_additive /-- Additive congruence relations preserve addition. -/]
/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: {w x y z}
  statement: c w x -> c y z -> c (w * y) (x * z)
  proof: c.mul'

@[to_additive (attr := simp)]

中文:
定理 mul
  条件: {w x y z}
  结论: c w x -> c y z -> c (w * y) (x * z)
  证明: c.mul'

@[to_additive (attr := simp)]
-/
protected theorem mul {w x y z} : c w x -> c y z -> c (w * y) (x * z) := c.mul'

@[to_additive (attr := simp)]
/--
theorem `rel_mk` / 定理 `rel_mk`

English:
theorem rel_mk
  given: {s : Setoid M} {h a b}
  statement: Con.mk s h a b ↔ r a b
  proof: Iff.rfl

中文:
定理 rel_mk
  条件: {s : 集合等价关系 M} {h a b}
  结论: Con.mk s h a b ↔ r a b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem rel_mk {s : Setoid M} {h a b} : Con.mk s h a b ↔ r a b :=
  Iff.rfl

/-- Given a type `M` with a multiplication, a congruence relation `c` on `M`, and elements of `M`
`x, y`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/
@[to_additive instMembershipProd
  /-- Given a type `M` with an addition, `x, y ∈ M`, and an additive congruence relation
`c` on `M`, `(x, y) ∈ M × M` iff `x` is related to `y` by `c`. -/]
/--
Instance `instMembershipProd` / 实例 `instMembershipProd`

English:
instance instMembershipProd
  signature: : Membership (M × M) (Con M)
  body: ⟨fun c x => c x.1 x.2⟩

中文:
实例 instMembershipProd
  签名: : Membership (M × M) (Con M)
  定义体: ⟨fun c x => c x.1 x.2⟩
-/
instance instMembershipProd : Membership (M × M) (Con M) :=
  ⟨fun c x => c x.1 x.2⟩

variable {c}

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
@[to_additive /-- The map sending an additive congruence relation to its underlying binary relation
is injective. -/]
/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {c d : Con M} (H : ⇑c = ⇑d)
  statement: c = d
  proof: DFunLike.coe_injective H

中文:
定理 ext'
  条件: {c d : Con M} (H : ⇑c = ⇑d)
  结论: c = d
  证明: DFunLike.coe_injective H

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext' {c d : Con M} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
@[to_additive (attr := ext) /-- Extensionality rule for additive congruence relations. -/]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {c d : Con M} (H : forall x y, c x y ↔ d x y)
  statement: c = d
  proof: ext' by ext; apply H

中文:
定理 ext
  条件: {c d : Con M} (H : 对任意 x y, c x y ↔ d x y)
  结论: c = d
  证明: ext' by ext; apply H
-/
theorem ext {c d : Con M} (H : forall x y, c x y ↔ d x y) : c = d :=
ext' by ext; apply H

/-- Two congruence relations are equal iff their underlying binary relations are equal. -/
@[to_additive /-- Two additive congruence relations are equal iff their underlying binary relations
are equal. -/]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {c d : Con M}
  statement: ⇑c = ⇑d ↔ c = d
  proof: DFunLike.coe_injective.eq_iff

中文:
定理 coe_inj
  条件: {c d : Con M}
  结论: ⇑c = ⇑d ↔ c = d
  证明: DFunLike.coe_injective.eq_iff

Depends on / 依赖: DFunLike, DFunLike.coe_injective.eq_iff, coe_injective, eq_iff
-/
theorem coe_inj {c d : Con M} : ⇑c = ⇑d ↔ c = d := DFunLike.coe_injective.eq_iff

variable (c)

-- Quotients
/-- Defining the quotient by a congruence relation of a type with a multiplication. -/
@[to_additive /-- Defining the quotient by an additive congruence relation of a type with
an addition. -/]
/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  body: Quotient c.toSetoid

中文:
定义 商
  定义体: Quotient c.toSetoid
-/
protected def Quotient :=
  Quotient c.toSetoid

variable {c}

/-- The morphism into the quotient by a congruence relation -/
@[to_additive (attr := coe)
/-- The morphism into the quotient by an additive congruence relation -/]
/--
Definition of `toQuotient` / `toQuotient` 的定义

English:
definition toQuotient
  signature: : M -> c.Quotient
  body: Quotient.mk''

中文:
定义 toQuotient
  签名: : M -> c.商
  定义体: Quotient.mk''

Depends on / 依赖: Quotient, Quotient.mk
-/
def toQuotient : M -> c.Quotient :=
  Quotient.mk''

variable (c)

/-- Coercion from a type with a multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
@[to_additive /-- Coercion from a type with an addition to its quotient by an additive congruence
relation -/]
instance (priority := 10) : CoeTC M c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
@[to_additive
/-- The quotient by a decidable additive congruence relation has decidable equality. -/]
instance (priority := 500) [forall a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[to_additive (attr := simp)]
/--
theorem `quot_mk_eq_coe` / 定理 `quot_mk_eq_coe`

English:
theorem quot_mk_eq_coe
  given: {M : Type*} [Mul M] (c : Con M) (x : M)
  statement: Quot.mk c x = (x : c.Quotient)
  proof: rfl

中文:
定理 quot_mk_eq_coe
  条件: {M : 类型} [乘法 M] (c : Con M) (x : M)
  结论: 商.mk c x = (x : c.商)
  证明: rfl
-/
theorem quot_mk_eq_coe {M : Type*} [Mul M] (c : Con M) (x : M) : Quot.mk c x = (x : c.Quotient) :=
  rfl

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `elab_as_elim`
/-- The function on the quotient by a congruence relation `c` induced by a function that is
constant on `c`'s equivalence classes. -/
@[to_additive /-- The function on the quotient by a congruence relation `c`
induced by a function that is constant on `c`'s equivalence classes. -/]
/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: {β} {c : Con M} (q : c.Quotient) (f : M -> β) (h : forall a b, c a b -> f a = f b)
  body: Quotient.liftOn' q f h

中文:
定义 liftOn
  签名: {β} {c : Con M} (q : c.商) (f : M -> β) (h : 对任意 a b, c a b -> f a = f b)
  定义体: Quotient.liftOn' q f h
-/
protected def liftOn {β} {c : Con M} (q : c.Quotient) (f : M -> β) (h : forall a b, c a b -> f a = f b) :
    β :=
  Quotient.liftOn' q f h

-- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: restore `elab_as_elim`
/-- The binary function on the quotient by a congruence relation `c` induced by a binary function
that is constant on `c`'s equivalence classes. -/
@[to_additive /-- The binary function on the quotient by a congruence relation `c`
induced by a binary function that is constant on `c`'s equivalence classes. -/]
/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: {β} {c : Con M} (q r : c.Quotient) (f : M -> M -> β)
  body: Quotient.liftOn₂' q r f h

中文:
定义 liftOn₂
  签名: {β} {c : Con M} (q r : c.商) (f : M -> M -> β)
  定义体: Quotient.liftOn₂' q r f h
-/
protected def liftOn₂ {β} {c : Con M} (q r : c.Quotient) (f : M -> M -> β)
    (h : forall a₁ a₂ b₁ b₂, c a₁ b₁ -> c a₂ b₂ -> f a₁ a₂ = f b₁ b₂) : β :=
  Quotient.liftOn₂' q r f h

/-- A version of `Quotient.hrecOn₂'` for quotients by `Con`. -/
@[to_additive /-- A version of `Quotient.hrecOn₂'` for quotients by `AddCon`. -/]
/--
Definition of `hrecOn₂` / `hrecOn₂` 的定义

English:
definition hrecOn₂
  signature: {cM : Con M} {cN : Con N} {φ : cM.Quotient -> cN.Quotient -> Sort*}
  body: Quotient.hrecOn₂' a b f h

@[to_additive (attr := simp)]

中文:
定义 hrecOn₂
  签名: {cM : Con M} {cN : Con N} {φ : cM.商 -> cN.商 -> 类型层*}
  定义体: Quotient.hrecOn₂' a b f h

@[to_additive (attr := simp)]
-/
protected def hrecOn₂ {cM : Con M} {cN : Con N} {φ : cM.Quotient -> cN.Quotient -> Sort*}
    (a : cM.Quotient) (b : cN.Quotient) (f : forall (x : M) (y : N), φ x y)
    (h : forall x y x' y', cM x x' -> cN y y' -> f x y ≍ f x' y') : φ a b :=
  Quotient.hrecOn₂' a b f h

@[to_additive (attr := simp)]
/--
theorem `hrec_on₂_coe` / 定理 `hrec_on₂_coe`

English:
theorem hrec_on₂_coe
  statement: {cM : Con M} {cN : Con N} {φ : cM.Quotient -> cN.Quotient -> Sort*} (a : M)
  proof: rfl

中文:
定理 hrec_on₂_coe
  结论: {cM : Con M} {cN : Con N} {φ : cM.商 -> cN.商 -> 类型层*} (a : M)
  证明: rfl
-/
theorem hrec_on₂_coe {cM : Con M} {cN : Con N} {φ : cM.Quotient -> cN.Quotient -> Sort*} (a : M)
    (b : N) (f : forall (x : M) (y : N), φ x y)
    (h : forall x y x' y', cM x x' -> cN y y' -> f x y ≍ f x' y') :
    Con.hrecOn₂ (↑a) (↑b) f h = f a b :=
  rfl

variable {c}

/-- The inductive principle used to prove propositions about the elements of a quotient by a
congruence relation. -/
@[to_additive (attr := elab_as_elim) /-- The inductive principle used to prove propositions about
the elements of a quotient by an additive congruence relation. -/]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {C : c.Quotient -> Prop} (q : c.Quotient) (H : forall x : M, C x)
  statement: C q
  proof: Quotient.inductionOn' q H

中文:
定理 induction_on
  条件: {C : c.商 -> 命题} (q : c.商) (H : 对任意 x : M, C x)
  结论: C q
  证明: Quotient.inductionOn' q H
-/
protected theorem induction_on {C : c.Quotient -> Prop} (q : c.Quotient) (H : forall x : M, C x) : C q :=
  Quotient.inductionOn' q H

/-- A version of `Con.induction_on` for predicates which takes two arguments. -/
@[to_additive (attr := elab_as_elim)
/-- A version of `AddCon.induction_on` for predicates which takes two arguments. -/]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {d : Con N} {C : c.Quotient -> d.Quotient -> Prop} (p : c.Quotient)
  proof: Quotient.inductionOn₂' p q H

中文:
定理 induction_on₂
  结论: {d : Con N} {C : c.商 -> d.商 -> 命题} (p : c.商)
  证明: Quotient.inductionOn₂' p q H
-/
protected theorem induction_on₂ {d : Con N} {C : c.Quotient -> d.Quotient -> Prop} (p : c.Quotient)
    (q : d.Quotient) (H : forall (x : M) (y : N), C x y) : C p q :=
  Quotient.inductionOn₂' p q H

variable (c)

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[to_additive (attr := simp) /-- Two elements are related by an additive congruence relation `c` iff
they are represented by the same element of the quotient by `c`. -/]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {a b : M}
  statement: (a : c.Quotient) = (b : c.Quotient) ↔ c a b
  proof: Quotient.eq''

中文:
定理 eq
  条件: {a b : M}
  结论: (a : c.商) = (b : c.商) ↔ c a b
  证明: Quotient.eq''
-/
protected theorem eq {a b : M} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''

/-- The multiplication induced on the quotient by a congruence relation on a type with a
multiplication. -/
@[to_additive /-- The addition induced on the quotient by an additive congruence relation on a type
with an addition. -/]
/--
Instance `hasMul` / 实例 `hasMul`

English:
instance hasMul
  signature: : Mul c.Quotient
  body: ⟨Quotient.map₂ (· * ·) fun _ _ h1 _ _ h2 => c.mul h1 h2⟩

中文:
实例 hasMul
  签名: : 乘法 c.商
  定义体: ⟨Quotient.map₂ (· * ·) fun _ _ h1 _ _ h2 => c.mul h1 h2⟩

Depends on / 依赖: Quotient, Quotient.map, c.mul
-/
instance hasMul : Mul c.Quotient :=
  ⟨Quotient.map₂ (· * ·) fun _ _ h1 _ _ h2 => c.mul h1 h2⟩

variable {c}

/-- The coercion to the quotient of a congruence relation commutes with multiplication (by
definition). -/
@[to_additive (attr := simp) /-- The coercion to the quotient of an additive congruence relation
commutes with addition (by definition). -/]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : M)
  statement: (↑(x * y) : c.Quotient) = ↑x * ↑y
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : M)
  结论: (↑(x * y) : c.商) = ↑x * ↑y
  证明: rfl
-/
theorem coe_mul (x y : M) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl

/-- Definition of the function on the quotient by a congruence relation `c` induced by a function
that is constant on `c`'s equivalence classes. -/
@[to_additive (attr := simp) /-- Definition of the function on the quotient by an additive
congruence relation `c` induced by a function that is constant on `c`'s equivalence classes. -/]
/--
theorem `liftOn_coe` / 定理 `liftOn_coe`

English:
theorem liftOn_coe
  given: {β} (c : Con M) (f : M -> β) (h : forall a b, c a b -> f a = f b) (x : M)
  proof: rfl

中文:
定理 liftOn_coe
  条件: {β} (c : Con M) (f : M -> β) (h : 对任意 a b, c a b -> f a = f b) (x : M)
  证明: rfl
-/
protected theorem liftOn_coe {β} (c : Con M) (f : M -> β) (h : forall a b, c a b -> f a = f b) (x : M) :
    Con.liftOn (x : c.Quotient) f h = f x :=
  rfl

-- The complete lattice of congruence relations on a type
/-- For congruence relations `c, d` on a type `M` with a multiplication, `c ≤ d` iff `∀ x y ∈ M`,
`x` is related to `y` by `d` if `x` is related to `y` by `c`. -/
@[to_additive /-- For additive congruence relations `c, d` on a type `M` with an addition, `c ≤ d`
iff `∀ x y ∈ M`, `x` is related to `y` by `d` if `x` is related to `y` by `c`. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LE (Con M)
  body: forall ⦃x y⦄, c x y -> d x y

中文:
实例 :
  签名: LE (Con M)
  定义体: forall ⦃x y⦄, c x y -> d x y
-/
instance : LE (Con M) where
  le c d := forall ⦃x y⦄, c x y -> d x y

/-- Definition of `≤` for congruence relations. -/
@[to_additive /-- Definition of `≤` for additive congruence relations. -/]
/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: {c d : Con M}
  statement: c <= d ↔ forall {x y}, c x y -> d x y
  proof: Iff.rfl

中文:
定理 le_def
  条件: {c d : Con M}
  结论: c <= d ↔ 对任意 {x y}, c x y -> d x y
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem le_def {c d : Con M} : c <= d ↔ forall {x y}, c x y -> d x y :=
  Iff.rfl

/-- The infimum of a set of congruence relations on a given type with a multiplication. -/
@[to_additive /-- The infimum of a set of additive congruence relations on a given type with
an addition. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: InfSet (Con M)
  body: { r := fun x y => forall c : Con M, c in S -> c x y
iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm h c hc,
fun h1 h2 c hc => c.trans (h1 c hc) h2 c hc⟩
mul' := fun h1 h2 c hc => c.mul (h1 c hc) h2 c hc }

中文:
实例 :
  签名: 下确界集 (Con M)
  定义体: { r := fun x y => forall c : Con M, c in S -> c x y
iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm h c hc,
fun h1 h2 c hc => c.trans (h1 c hc) h2 c hc⟩
mul' := fun h1 h2 c hc => c.mul (h1 c hc) h2 c hc }

Depends on / 依赖: c.mul, c.refl, c.symm, c.trans
-/
instance : InfSet (Con M) where
  sInf S :=
    { r := fun x y => forall c : Con M, c in S -> c x y
iseqv := ⟨fun x c _ => c.refl x, fun h c hc => c.symm h c hc,
fun h1 h2 c hc => c.trans (h1 c hc) h2 c hc⟩
mul' := fun h1 h2 c hc => c.mul (h1 c hc) h2 c hc }

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying equivalence relation. -/
@[to_additive /-- The infimum of a set of additive congruence relations is the same as the infimum
of the set's image under the map to the underlying equivalence relation. -/]
/--
theorem `sInf_toSetoid` / 定理 `sInf_toSetoid`

English:
theorem sInf_toSetoid
  given: (S : Set (Con M))
  statement: (sInf S).toSetoid = sInf (toSetoid '' S)
  proof: Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

中文:
定理 sInf_toSetoid
  条件: (S : 集合 (Con M))
  结论: (sInf S).toSetoid = sInf (toSetoid '' S)
  证明: Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

Depends on / 依赖: Setoid, Setoid.ext, c.toSetoid, toSetoid
-/
theorem sInf_toSetoid (S : Set (Con M)) : (sInf S).toSetoid = sInf (toSetoid '' S) :=
  Setoid.ext fun x y =>
    ⟨fun h r ⟨c, hS, hr⟩ => by rw [← hr]; exact h c hS, fun h c hS => h c.toSetoid ⟨c, hS, rfl⟩⟩

/-- The infimum of a set of congruence relations is the same as the infimum of the set's image
under the map to the underlying binary relation. -/
@[to_additive (attr := simp, norm_cast)
  /-- The infimum of a set of additive congruence relations is the same as the infimum
  of the set's image under the map to the underlying binary relation. -/]
/--
theorem `coe_sInf` / 定理 `coe_sInf`

English:
theorem coe_sInf
  given: (S : Set (Con M))
  proof: by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_sInf
  条件: (S : 集合 (Con M))
  证明: by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

@[to_additive (attr := simp, norm_cast)]

Depends on / 依赖: iInf_Prop_eq, iInf_apply, sInf_image
-/
theorem coe_sInf (S : Set (Con M)) :
    ⇑(sInf S) = sInf ((⇑) '' S) := by
  ext
  simp only [sInf_image, iInf_apply, iInf_Prop_eq]
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_iInf` / 定理 `coe_iInf`

English:
theorem coe_iInf
  given: {ι : Sort*} (f : ι -> Con M)
  statement: ⇑(iInf f) = ⨅ i, ⇑(f i)
  proof: by
  rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rw [sInf_range]; rw [Function.comp_def]

@[to_additive]

中文:
定理 coe_iInf
  条件: {ι : 类型层*} (f : ι -> Con M)
  结论: ⇑(iInf f) = ⨅ i, ⇑(f i)
  证明: by
  rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rw [sInf_range]; rw [Function.comp_def]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, Set.range_comp, coe_sInf, comp_def, range_comp, sInf_range
-/
theorem coe_iInf {ι : Sort*} (f : ι -> Con M) : ⇑(iInf f) = ⨅ i, ⇑(f i) := by
  rw [iInf]; rw [coe_sInf]; rw [← Set.range_comp]; rw [sInf_range]; rw [Function.comp_def]

@[to_additive]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (Con M)
  body: id
le_trans _ _ _ h1 h2 _ _ h := h2 h1 h
  le_antisymm _ _ hc hd := ext fun _ _ => ⟨fun h => hc h, fun h => hd h⟩

中文:
实例 :
  签名: 偏序 (Con M)
  定义体: id
le_trans _ _ _ h1 h2 _ _ h := h2 h1 h
  le_antisymm _ _ hc hd := ext fun _ _ => ⟨fun h => hc h, fun h => hd h⟩
-/
instance : PartialOrder (Con M) where
  le_refl _ _ _ := id
le_trans _ _ _ h1 h2 _ _ h := h2 h1 h
  le_antisymm _ _ hc hd := ext fun _ _ => ⟨fun h => hc h, fun h => hd h⟩

/-- The complete lattice of congruence relations on a given type with a multiplication. -/
@[to_additive /-- The complete lattice of additive congruence relations on a given type with
an addition. -/]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompleteLattice (Con M)
  body: completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : forall r in s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
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

中文:
实例 :
  签名: 完备格 (Con M)
  定义体: completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : forall r in s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
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

Depends on / 依赖: completeLatticeOfInf
-/
instance : CompleteLattice (Con M) where
  __ := completeLatticeOfInf (Con M) fun s =>
      ⟨fun r hr x y h => (h : forall r in s, (r : Con M) x y) r hr, fun r hr x y h r' hr' =>
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
/--
theorem `coe_inf` / 定理 `coe_inf`

English:
theorem coe_inf
  given: {c d : Con M}
  statement: ⇑(c ⊓ d) = ⇑c ⊓ ⇑d
  proof: rfl

中文:
定理 coe_inf
  条件: {c d : Con M}
  结论: ⇑(c ⊓ d) = ⇑c ⊓ ⇑d
  证明: rfl
-/
theorem coe_inf {c d : Con M} : ⇑(c ⊓ d) = ⇑c ⊓ ⇑d :=
  rfl

/--
lemma `toSetoid_top` / 引理 `toSetoid_top`

English:
lemma toSetoid_top
  statement: (⊤ : Con M).toSetoid = ⊤
  proof: rfl

中文:
引理 toSetoid_top
  结论: (⊤ : Con M).toSetoid = ⊤
  证明: rfl
-/
@[to_additive (attr := simp)] lemma toSetoid_top : (⊤ : Con M).toSetoid = ⊤ := rfl
/--
lemma `toSetoid_bot` / 引理 `toSetoid_bot`

English:
lemma toSetoid_bot
  statement: (⊥ : Con M).toSetoid = ⊥
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 toSetoid_bot
  结论: (⊥ : Con M).toSetoid = ⊥
  证明: rfl

@[to_additive (attr := simp)]
-/
@[to_additive (attr := simp)] lemma toSetoid_bot : (⊥ : Con M).toSetoid = ⊥ := rfl

@[to_additive (attr := simp)]
/--
lemma `toSetoid_eq_top` / 引理 `toSetoid_eq_top`

English:
lemma toSetoid_eq_top
  statement: c.toSetoid = ⊤ ↔ c = ⊤
  proof: by rw [← toSetoid_top, toSetoid_inj]

@[to_additive (attr := simp)]

中文:
引理 toSetoid_eq_top
  结论: c.toSetoid = ⊤ ↔ c = ⊤
  证明: by rw [← toSetoid_top, toSetoid_inj]

@[to_additive (attr := simp)]

Depends on / 依赖: toSetoid_inj, toSetoid_top
-/
lemma toSetoid_eq_top : c.toSetoid = ⊤ ↔ c = ⊤ := by rw [← toSetoid_top, toSetoid_inj]

@[to_additive (attr := simp)]
/--
lemma `toSetoid_eq_bot` / 引理 `toSetoid_eq_bot`

English:
lemma toSetoid_eq_bot
  statement: c.toSetoid = ⊥ ↔ c = ⊥
  proof: by rw [← toSetoid_bot, toSetoid_inj]

中文:
引理 toSetoid_eq_bot
  结论: c.toSetoid = ⊥ ↔ c = ⊥
  证明: by rw [← toSetoid_bot, toSetoid_inj]

Depends on / 依赖: toSetoid_bot, toSetoid_inj
-/
lemma toSetoid_eq_bot : c.toSetoid = ⊥ ↔ c = ⊥ := by rw [← toSetoid_bot, toSetoid_inj]

/-- Definition of the infimum of two congruence relations. -/
@[to_additive /-- Definition of the infimum of two additive congruence relations. -/]
/--
theorem `inf_iff_and` / 定理 `inf_iff_and`

English:
theorem inf_iff_and
  given: {c d : Con M} {x y}
  statement: (c ⊓ d) x y ↔ c x y ∧ d x y
  proof: Iff.rfl

@[to_additive]

中文:
定理 inf_iff_and
  条件: {c d : Con M} {x y}
  结论: (c ⊓ d) x y ↔ c x y ∧ d x y
  证明: Iff.rfl

@[to_additive]

Depends on / 依赖: Iff.rfl
-/
theorem inf_iff_and {c d : Con M} {x y} : (c ⊓ d) x y ↔ c x y ∧ d x y :=
  Iff.rfl

@[to_additive]
/--
theorem `le_conGen` / 定理 `le_conGen`

English:
theorem le_conGen
  given: {r : M -> M -> Prop}
  statement: r <= ⇑(conGen r)
  proof: ConGen.Rel.of

中文:
定理 le_conGen
  条件: {r : M -> M -> 命题}
  结论: r <= ⇑(conGen r)
  证明: ConGen.Rel.of

Depends on / 依赖: ConGen, ConGen.Rel.of
-/
theorem le_conGen {r : M -> M -> Prop} : r <= ⇑(conGen r) := ConGen.Rel.of

/-- The inductively defined smallest congruence relation containing a binary relation `r` equals
the infimum of the set of congruence relations containing `r`. -/
@[to_additive /-- The inductively defined smallest additive congruence relation
containing a binary relation `r` equals the infimum of the set of additive congruence relations
containing `r`. -/]
/--
theorem `conGen_eq` / 定理 `conGen_eq`

English:
theorem conGen_eq
  given: (r : M -> M -> Prop)
  statement: conGen r = sInf { s : Con M | forall x y, r x y -> s x y }
  proof: le_antisymm
    (le_sInf (fun s hs x y (hxy : (conGen r) x y) =>
      show s x y by
        apply ConGen.Rel.recOn (motive := fun x y _ => s x y) hxy
        · exact fun x y h => hs x y h
        · exact s.refl'
        · exact fun _ => s.symm'
        · exact fun _ _ => s.trans'
        · exact fun _ _ => s.mul))
    (sInf_le ConGen.Rel.of)

中文:
定理 conGen_eq
  条件: (r : M -> M -> 命题)
  结论: conGen r = sInf { s : Con M | 对任意 x y, r x y -> s x y }
  证明: le_antisymm
    (le_sInf (fun s hs x y (hxy : (conGen r) x y) =>
      show s x y by
        apply ConGen.Rel.recOn (motive := fun x y _ => s x y) hxy
        · exact fun x y h => hs x y h
        · exact s.refl'
        · exact fun _ => s.symm'
        · exact fun _ _ => s.trans'
        · exact fun _ _ => s.mul))
    (sInf_le ConGen.Rel.of)

Depends on / 依赖: ConGen, ConGen.Rel.of, ConGen.Rel.recOn, conGen, le_antisymm, le_sInf, motive, s.mul, s.refl, s.symm, s.trans, sInf_le
-/
theorem conGen_eq (r : M -> M -> Prop) : conGen r = sInf { s : Con M | forall x y, r x y -> s x y } :=
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
/--
theorem `conGen_le` / 定理 `conGen_le`

English:
theorem conGen_le
  given: {r : M -> M -> Prop} {c : Con M}
  statement: conGen r <= c ↔ r <= ⇑c
  proof: ⟨le_trans le_conGen, conGen_eq r ▸ fun h => sInf_le h⟩

中文:
定理 conGen_le
  条件: {r : M -> M -> 命题} {c : Con M}
  结论: conGen r <= c ↔ r <= ⇑c
  证明: ⟨le_trans le_conGen, conGen_eq r ▸ fun h => sInf_le h⟩

Depends on / 依赖: conGen_eq, le_conGen, le_trans, sInf_le
-/
theorem conGen_le {r : M -> M -> Prop} {c : Con M} : conGen r <= c ↔ r <= ⇑c :=
  ⟨le_trans le_conGen, conGen_eq r ▸ fun h => sInf_le h⟩

variable (M) in
/-- There is a Galois insertion of congruence relations on a type with a multiplication `M` into
binary relations on `M`. -/
@[to_additive /-- There is a Galois insertion of additive congruence relations on a type with
an addition `M` into binary relations on `M`. -/]
/--
Definition of `gi` / `gi` 的定义

English:
definition gi
  signature: : GaloisInsertion (conGen (M := M)) DFunLike.coe where
  body: conGen r
  gc _ _ := conGen_le
  le_l_u _ := le_conGen
  choice_eq _ _ := rfl

@[to_additive]

中文:
定义 gi
  签名: : Galois嵌入 (conGen (M := M)) 依赖函数状.coe where
  定义体: conGen r
  gc _ _ := conGen_le
  le_l_u _ := le_conGen
  choice_eq _ _ := rfl

@[to_additive]
-/
protected def gi : GaloisInsertion (conGen (M := M)) DFunLike.coe where
  choice r _ := conGen r
  gc _ _ := conGen_le
  le_l_u _ := le_conGen
  choice_eq _ _ := rfl

@[to_additive]
/--
theorem `conGen_monotone` / 定理 `conGen_monotone`

English:
theorem conGen_monotone
  statement: Monotone (conGen (M := M))
  proof: .gc.monotone_l Con.gi M

中文:
定理 conGen_monotone
  结论: 递增 (conGen (M := M))
  证明: .gc.monotone_l Con.gi M
-/
theorem conGen_monotone : Monotone (conGen (M := M)) :=
.gc.monotone_l Con.gi M

/-- Given binary relations `r, s` with `r` contained in `s`, the smallest congruence relation
containing `s` contains the smallest congruence relation containing `r`. -/
@[to_additive /-- Given binary relations `r, s` with `r` contained in `s`, the
smallest additive congruence relation containing `s` contains the smallest additive congruence
relation containing `r`. -/]
/--
theorem `conGen_mono` / 定理 `conGen_mono`

English:
theorem conGen_mono
  given: {r s : M -> M -> Prop} (h : forall x y, r x y -> s x y)
  statement: conGen r <= conGen s
  proof: conGen_monotone h

中文:
定理 conGen_mono
  条件: {r s : M -> M -> 命题} (h : 对任意 x y, r x y -> s x y)
  结论: conGen r <= conGen s
  证明: conGen_monotone h

Depends on / 依赖: conGen_monotone
-/
theorem conGen_mono {r s : M -> M -> Prop} (h : forall x y, r x y -> s x y) : conGen r <= conGen s :=
  conGen_monotone h

/-- Congruence relations equal the smallest congruence relation in which they are contained. -/
@[to_additive (attr := simp) addConGen_of_addCon /-- Additive congruence relations equal the
smallest additive congruence relation in which they are contained. -/]
/--
theorem `conGen_of_con` / 定理 `conGen_of_con`

English:
theorem conGen_of_con
  given: (c : Con M)
  statement: conGen c = c
  proof: .l_u_eq _ Con.gi M

中文:
定理 conGen_of_con
  条件: (c : Con M)
  结论: conGen c = c
  证明: .l_u_eq _ Con.gi M

Depends on / 依赖: Con.gi, l_u_eq
-/
theorem conGen_of_con (c : Con M) : conGen c = c :=
.l_u_eq _ Con.gi M

/-- The map sending a binary relation to the smallest congruence relation in which it is
contained is idempotent. -/
@[to_additive /-- The map sending a binary relation to the smallest additive
congruence relation in which it is contained is idempotent. -/]
/--
theorem `conGen_idem` / 定理 `conGen_idem`

English:
theorem conGen_idem
  given: (r : M -> M -> Prop)
  statement: conGen (conGen r) = conGen r
  proof: .gc.l_u_l_eq_l _ Con.gi M

中文:
定理 conGen_idem
  条件: (r : M -> M -> 命题)
  结论: conGen (conGen r) = conGen r
  证明: .gc.l_u_l_eq_l _ Con.gi M

Depends on / 依赖: Con.gi, gc.l_u_l_eq_l, l_u_l_eq_l
-/
theorem conGen_idem (r : M -> M -> Prop) : conGen (conGen r) = conGen r :=
.gc.l_u_l_eq_l _ Con.gi M

/--
theorem `conGen_sup` / 定理 `conGen_sup`

English:
theorem conGen_sup
  given: (r s : M -> M -> Prop)
  statement: conGen (r ⊔ s) = conGen r ⊔ conGen s
  proof: .gc.l_sup Con.gi M

中文:
定理 conGen_sup
  条件: (r s : M -> M -> 命题)
  结论: conGen (r ⊔ s) = conGen r ⊔ conGen s
  证明: .gc.l_sup Con.gi M

Depends on / 依赖: Con.gi, gc.l_sup, l_sup
-/
theorem conGen_sup (r s : M -> M -> Prop) : conGen (r ⊔ s) = conGen r ⊔ conGen s :=
.gc.l_sup Con.gi M

/--
theorem `conGen_sSup` / 定理 `conGen_sSup`

English:
theorem conGen_sSup
  given: (rs : Set (M -> M -> Prop))
  statement: conGen (sSup rs) = ⨆ r in rs, conGen r
  proof: .gc.l_sSup Con.gi M

中文:
定理 conGen_sSup
  条件: (rs : 集合 (M -> M -> 命题))
  结论: conGen (sSup rs) = ⨆ r in rs, conGen r
  证明: .gc.l_sSup Con.gi M

Depends on / 依赖: Con.gi, gc.l_sSup, l_sSup
-/
theorem conGen_sSup (rs : Set (M -> M -> Prop)) : conGen (sSup rs) = ⨆ r in rs, conGen r :=
.gc.l_sSup Con.gi M

/--
theorem `conGen_iSup` / 定理 `conGen_iSup`

English:
theorem conGen_iSup
  given: {ι : Sort*} (r : ι -> M -> M -> Prop)
  statement: conGen (iSup r) = ⨆ i, conGen (r i)
  proof: .gc.l_iSup Con.gi M

中文:
定理 conGen_iSup
  条件: {ι : 类型层*} (r : ι -> M -> M -> 命题)
  结论: conGen (iSup r) = ⨆ i, conGen (r i)
  证明: .gc.l_iSup Con.gi M

Depends on / 依赖: Con.gi, gc.l_iSup, l_iSup
-/
theorem conGen_iSup {ι : Sort*} (r : ι -> M -> M -> Prop) : conGen (iSup r) = ⨆ i, conGen (r i) :=
.gc.l_iSup Con.gi M

/-- The supremum of two congruence relations equals the smallest congruence relation containing
the supremum of the underlying binary operations. -/
@[to_additive /-- The supremum of two additive congruence relations equals the smallest additive
congruence relation containing the supremum of the underlying binary operations. -/]
/--
theorem `sup_def` / 定理 `sup_def`

English:
theorem sup_def
  given: (c d : Con M)
  statement: c ⊔ d = conGen (⇑c ⊔ ⇑d)
  proof: .symm .l_sup_u _ _ Con.gi M

中文:
定理 sup_def
  条件: (c d : Con M)
  结论: c ⊔ d = conGen (⇑c ⊔ ⇑d)
  证明: .symm .l_sup_u _ _ Con.gi M

Depends on / 依赖: Con.gi, l_sup_u
-/
theorem sup_def (c d : Con M) : c ⊔ d = conGen (⇑c ⊔ ⇑d) :=
.symm .l_sup_u _ _ Con.gi M

/-- The supremum of congruence relations `c, d` equals the smallest congruence relation containing
the binary relation '`x` is related to `y` by `c` or `d`'. -/
@[to_additive /-- The supremum of additive congruence relations `c, d` equals the
smallest additive congruence relation containing the binary relation '`x` is related to `y`
by `c` or `d`'. -/]
/--
theorem `sup_eq_conGen` / 定理 `sup_eq_conGen`

English:
theorem sup_eq_conGen
  given: (c d : Con M)
  statement: c ⊔ d = conGen fun x y => c x y ∨ d x y
  proof: sup_def _ _

中文:
定理 sup_eq_conGen
  条件: (c d : Con M)
  结论: c ⊔ d = conGen fun x y => c x y ∨ d x y
  证明: sup_def _ _

Depends on / 依赖: sup_def
-/
theorem sup_eq_conGen (c d : Con M) : c ⊔ d = conGen fun x y => c x y ∨ d x y :=
  sup_def _ _

/-- The supremum of a set of congruence relations is the same as the smallest congruence relation
containing the supremum of the set's image under the map to the underlying binary relation. -/
@[to_additive /-- The supremum of a set of additive congruence relations is the same as the smallest
additive congruence relation containing the supremum of the set's image under the map to the
underlying binary relation. -/]
/--
theorem `sSup_def` / 定理 `sSup_def`

English:
theorem sSup_def
  given: (S : Set (Con M))
  statement: sSup S = conGen (sSup ((⇑) '' S))
  proof: .symm .l_sSup_u_image _ Con.gi M

中文:
定理 sSup_def
  条件: (S : 集合 (Con M))
  结论: sSup S = conGen (sSup ((⇑) '' S))
  证明: .symm .l_sSup_u_image _ Con.gi M

Depends on / 依赖: Con.gi, l_sSup_u_image
-/
theorem sSup_def (S : Set (Con M)) : sSup S = conGen (sSup ((⇑) '' S)) :=
.symm .l_sSup_u_image _ Con.gi M

/-- The supremum of a set of congruence relations `S` equals the smallest congruence relation
containing the binary relation 'there exists `c ∈ S` such that `x` is related to `y` by `c`'. -/
@[to_additive /-- The supremum of a set of additive congruence relations `S`
equals the smallest additive congruence relation containing the binary relation 'there exists
`c ∈ S` such that `x` is related to `y` by `c`'. -/]
/--
theorem `sSup_eq_conGen` / 定理 `sSup_eq_conGen`

English:
theorem sSup_eq_conGen
  given: (S : Set (Con M))
  proof: by
  rw [sSup_def]
  congr! with x y
  simp

中文:
定理 sSup_eq_conGen
  条件: (S : 集合 (Con M))
  证明: by
  rw [sSup_def]
  congr! with x y
  simp

Depends on / 依赖: sSup_def
-/
theorem sSup_eq_conGen (S : Set (Con M)) :
    sSup S = conGen fun x y => exists c : Con M, c in S ∧ c x y := by
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
/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : M -> N) (H : forall x y, f (x * y) = f x * f y) (c : Con N)
  body: { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }

@[to_additive (attr := simp)]

中文:
定义 comap
  签名: (f : M -> N) (H : 对任意 x y, f (x * y) = f x * f y) (c : Con N)
  定义体: { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }

@[to_additive (attr := simp)]

Depends on / 依赖: c.mul, c.toSetoid.comap, toSetoid
-/
def comap (f : M -> N) (H : forall x y, f (x * y) = f x * f y) (c : Con N) : Con M :=
  { c.toSetoid.comap f with
    mul' := @fun w x y z h1 h2 => show c (f (w * y)) (f (x * z)) by rw [H, H]; exact c.mul h1 h2 }

@[to_additive (attr := simp)]
/--
theorem `comap_rel` / 定理 `comap_rel`

English:
theorem comap_rel
  given: {f : M -> N} (H : forall x y, f (x * y) = f x * f y) {c : Con N} {x y : M}
  proof: Iff.rfl

@[to_additive (attr := simp)]

中文:
定理 comap_rel
  条件: {f : M -> N} (H : 对任意 x y, f (x * y) = f x * f y) {c : Con N} {x y : M}
  证明: Iff.rfl

@[to_additive (attr := simp)]

Depends on / 依赖: Iff.rfl
-/
theorem comap_rel {f : M -> N} (H : forall x y, f (x * y) = f x * f y) {c : Con N} {x y : M} :
    comap f H c x y ↔ c (f x) (f y) :=
  Iff.rfl

@[to_additive (attr := simp)]
/--
theorem `comap_id` / 定理 `comap_id`

English:
theorem comap_id
  given: (c : Con M)
  statement: c.comap id (by intros; rfl) = c
  proof: rfl

@[to_additive (attr := simp)]

中文:
定理 comap_id
  条件: (c : Con M)
  结论: c.comap id (by intros; rfl) = c
  证明: rfl

@[to_additive (attr := simp)]
-/
theorem comap_id (c : Con M) : c.comap id (by intros; rfl) = c := rfl

@[to_additive (attr := simp)]
/--
theorem `comap_comp` / 定理 `comap_comp`

English:
theorem comap_comp
  given: (c : Con P) (g : N -> P) (f : M -> N) (hg) (hf)
  proof: rfl

@[to_additive]

中文:
定理 comap_comp
  条件: (c : Con P) (g : N -> P) (f : M -> N) (hg) (hf)
  证明: rfl

@[to_additive]
-/
theorem comap_comp (c : Con P) (g : N -> P) (f : M -> N) (hg) (hf) :
    c.comap (g ∘ f) (by grind) = (c.comap g hg).comap f hf := rfl

@[to_additive]
/--
theorem `le_comap_conGen` / 定理 `le_comap_conGen`

English:
theorem le_comap_conGen
  given: (r : N -> N -> Prop) (f : M -> N) (hf)
  proof: conGen_le.2 fun _ _ h => ConGen.Rel.of _ _ h

@[to_additive]

中文:
定理 le_comap_conGen
  条件: (r : N -> N -> 命题) (f : M -> N) (hf)
  证明: conGen_le.2 fun _ _ h => ConGen.Rel.of _ _ h

@[to_additive]

Depends on / 依赖: ConGen, ConGen.Rel.of, conGen_le
-/
theorem le_comap_conGen (r : N -> N -> Prop) (f : M -> N) (hf) :
    conGen (r.onFun f) <= (conGen r).comap f hf :=
  conGen_le.2 fun _ _ h => ConGen.Rel.of _ _ h

@[to_additive]
/--
theorem `comap_injective` / 定理 `comap_injective`

English:
theorem comap_injective
  given: (f : M -> N) (hf : Function.Surjective f) (hf')
  proof: .of_comp (f := toSetoid) (Setoid.comap_injective f hf).comp toSetoid_injective

中文:
定理 comap_injective
  条件: (f : M -> N) (hf : 函数.满射 f) (hf')
  证明: .of_comp (f := toSetoid) (Setoid.comap_injective f hf).comp toSetoid_injective

Depends on / 依赖: Setoid, Setoid.comap_injective, comap_injective, of_comp, toSetoid, toSetoid_injective
-/
theorem comap_injective (f : M -> N) (hf : Function.Surjective f) (hf') :
    Function.Injective (comap f hf') :=
.of_comp (f := toSetoid) (Setoid.comap_injective f hf).comp toSetoid_injective

end

section

variable [Mul M] [One M] (c : Con M)

@[to_additive]
/--
Instance `one` / 实例 `one`

English:
instance one
  signature: : One c.Quotient where
  body: Quotient.mk'' (1 : M)
  -- one := ((1 : M) : c.Quotient)

中文:
实例 one
  签名: : 幺 c.商 where
  定义体: Quotient.mk'' (1 : M)
  -- one := ((1 : M) : c.Quotient)

Depends on / 依赖: Quotient, Quotient.mk
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
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ((1 : M) : c.Quotient) = 1
  proof: rfl

中文:
定理 coe_one
  结论: ((1 : M) : c.商) = 1
  证明: rfl
-/
theorem coe_one : ((1 : M) : c.Quotient) = 1 :=
  rfl

/-- There exists an element of the quotient of a monoid by a congruence relation (namely 1). -/
@[to_additive /-- There exists an element of the quotient of an `AddMonoid` by a congruence relation
(namely 0). -/]
/--
Instance `Quotient.inhabited` / 实例 `Quotient.inhabited`

English:
instance Quotient.inhabited
  signature: : Inhabited c.Quotient
  body: ⟨((1 : M) : c.Quotient)⟩

中文:
实例 商.inhabited
  签名: : 可居 c.商
  定义体: ⟨((1 : M) : c.Quotient)⟩

Depends on / 依赖: Quotient, c.Quotient
-/
instance Quotient.inhabited : Inhabited c.Quotient :=
  ⟨((1 : M) : c.Quotient)⟩

end

section MulOneClass

variable [MulOneClass M] (c : Con M)

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive /-- The quotient of an `AddMonoid` by an additive congruence relation is
an `AddMonoid`. -/]
/--
Instance `mulOneClass` / 实例 `mulOneClass`

English:
instance mulOneClass
  signature: : MulOneClass c.Quotient where
  body: Quotient.inductionOn' x fun _ => congr_arg ((↑) : M -> c.Quotient) mul_one _
one_mul x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M -> c.Quotient) one_mul _

中文:
实例 mulOneClass
  签名: : MulOne类 c.商 where
  定义体: Quotient.inductionOn' x fun _ => congr_arg ((↑) : M -> c.Quotient) mul_one _
one_mul x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M -> c.Quotient) one_mul _

Depends on / 依赖: Quotient, Quotient.inductionOn, c.Quotient, congr_arg, inductionOn, mul_one
-/
instance mulOneClass : MulOneClass c.Quotient where
mul_one x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M -> c.Quotient) mul_one _
one_mul x := Quotient.inductionOn' x fun _ => congr_arg ((↑) : M -> c.Quotient) one_mul _

end MulOneClass

section Monoids

/-- Multiplicative congruence relations preserve natural powers. -/
@[to_additive /-- Additive congruence relations preserve natural scaling. -/]
/--
theorem `pow` / 定理 `pow`

English:
theorem pow
  given: {M : Type*} [Monoid M] (c : Con M)

中文:
定理 pow
  条件: {M : 类型} [幺半群 M] (c : Con M)
-/
protected theorem pow {M : Type*} [Monoid M] (c : Con M) :
    forall (n : Nat) {w x}, c w x -> c (w ^ n) (x ^ n)
  | 0, w, x, _ => by simpa using c.refl _
  | Nat.succ n, w, x, h => by simpa [pow_succ] using c.mul (Con.pow c n h) h

@[to_additive]
instance {M : Type*} [Monoid M] (c : Con M) : Pow c.Quotient Nat where
  pow x n := Quotient.map' (fun x => x ^ n) (fun _ _ => c.pow n) x

/-- The quotient of a semigroup by a congruence relation is a semigroup. -/
@[to_additive /-- The quotient of an `AddSemigroup` by an additive congruence relation is
an `AddSemigroup`. -/]
/--
Instance `semigroup` / 实例 `semigroup`

English:
instance semigroup
  signature: {M : Type*} [Semigroup M] (c : Con M)
  body: fast_instance%
  Function.Surjective.semigroup _ Quotient.mk''_surjective fun _ _ => rfl

中文:
实例 semigroup
  签名: {M : 类型} [半群 M] (c : Con M)
  定义体: fast_instance%
  Function.Surjective.semigroup _ Quotient.mk''_surjective fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance semigroup {M : Type*} [Semigroup M] (c : Con M) : Semigroup c.Quotient := fast_instance%
  Function.Surjective.semigroup _ Quotient.mk''_surjective fun _ _ => rfl

/-- The quotient of a commutative magma by a congruence relation is a commutative magma. -/
@[to_additive /-- The quotient of an `AddCommMagma` by an additive congruence relation is
an `AddCommMagma`. -/]
/--
Instance `commMagma` / 实例 `commMagma`

English:
instance commMagma
  signature: {M : Type*} [CommMagma M] (c : Con M)
  body: fast_instance%
  Function.Surjective.commMagma _ Quotient.mk''_surjective fun _ _ => rfl

中文:
实例 commMagma
  签名: {M : 类型} [交换原群 M] (c : Con M)
  定义体: fast_instance%
  Function.Surjective.commMagma _ Quotient.mk''_surjective fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance commMagma {M : Type*} [CommMagma M] (c : Con M) : CommMagma c.Quotient := fast_instance%
  Function.Surjective.commMagma _ Quotient.mk''_surjective fun _ _ => rfl

/-- The quotient of a commutative semigroup by a congruence relation is a semigroup. -/
@[to_additive /-- The quotient of an `AddCommSemigroup` by an additive congruence relation is
an `AddCommSemigroup`. -/]
/--
Instance `commSemigroup` / 实例 `commSemigroup`

English:
instance commSemigroup
  signature: {M : Type*} [CommSemigroup M] (c : Con M)
  body: Function.Surjective.commSemigroup _ Quotient.mk''_surjective fun _ _ => rfl

中文:
实例 commSemigroup
  签名: {M : 类型} [交换半群 M] (c : Con M)
  定义体: Function.Surjective.commSemigroup _ Quotient.mk''_surjective fun _ _ => rfl

Depends on / 依赖: Function, Function.Surjective.commSemigroup, Quotient, Quotient.mk, Surjective, _surjective, commSemigroup
-/
instance commSemigroup {M : Type*} [CommSemigroup M] (c : Con M) : CommSemigroup c.Quotient :=
  Function.Surjective.commSemigroup _ Quotient.mk''_surjective fun _ _ => rfl

/-- The quotient of a monoid by a congruence relation is a monoid. -/
@[to_additive /-- The quotient of an `AddMonoid` by an additive congruence relation is
an `AddMonoid`. -/]
/--
Instance `monoid` / 实例 `monoid`

English:
instance monoid
  signature: {M : Type*} [Monoid M] (c : Con M)
  body: fast_instance%
  Function.Surjective.monoid _ Quotient.mk''_surjective rfl (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 monoid
  签名: {M : 类型} [幺半群 M] (c : Con M)
  定义体: fast_instance%
  Function.Surjective.monoid _ Quotient.mk''_surjective rfl (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance monoid {M : Type*} [Monoid M] (c : Con M) : Monoid c.Quotient := fast_instance%
  Function.Surjective.monoid _ Quotient.mk''_surjective rfl (fun _ _ => rfl) fun _ _ => rfl

/-- The quotient of a `CommMonoid` by a congruence relation is a `CommMonoid`. -/
@[to_additive /-- The quotient of an `AddCommMonoid` by an additive congruence
relation is an `AddCommMonoid`. -/]
/--
Instance `commMonoid` / 实例 `commMonoid`

English:
instance commMonoid
  signature: {M : Type*} [CommMonoid M] (c : Con M)
  body: fast_instance%
  fast_instance% Function.Surjective.commMonoid _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 commMonoid
  签名: {M : 类型} [交换幺半群 M] (c : Con M)
  定义体: fast_instance%
  fast_instance% Function.Surjective.commMonoid _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
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
/--
theorem `map_of_mul_left_rel_one` / 定理 `map_of_mul_left_rel_one`

English:
theorem map_of_mul_left_rel_one
  statement: [Monoid M] (c : Con M)
  proof: by
  simp only [← Con.eq, coe_one, coe_mul] at *
  have hf' : forall x : M, (x : c.Quotient) * f x = 1 := fun x =>
    calc
      (x : c.Quotient) * f x = f (f x) * f x * (x * f x) := by simp [hf]
      _ = f (f x) * (f x * x) * f x := by simp_rw [mul_assoc]
      _ = 1 := by simp [hf]
  have : (⟨_, _, hf' x, hf x⟩ : c.Quotientˣ) = ⟨_, _, hf' y, hf y⟩ := Units.ext h
  exact congr_arg Units.inv this

中文:
定理 map_of_mul_left_rel_one
  结论: [幺半群 M] (c : Con M)
  证明: by
  simp only [← Con.eq, coe_one, coe_mul] at *
  have hf' : forall x : M, (x : c.Quotient) * f x = 1 := fun x =>
    calc
      (x : c.Quotient) * f x = f (f x) * f x * (x * f x) := by simp [hf]
      _ = f (f x) * (f x * x) * f x := by simp_rw [mul_assoc]
      _ = 1 := by simp [hf]
  have : (⟨_, _, hf' x, hf x⟩ : c.Quotientˣ) = ⟨_, _, hf' y, hf y⟩ := Units.ext h
  exact congr_arg Units.inv this

Depends on / 依赖: Con.eq, Quotient, Units.ext, Units.inv, c.Quotient, coe_mul, coe_one, congr_arg, mul_assoc, simp_rw
-/
theorem map_of_mul_left_rel_one [Monoid M] (c : Con M)
    (f : M -> M) (hf : forall x, c (f x * x) 1) {x y} (h : c x y) : c (f x) (f y) := by
  simp only [← Con.eq, coe_one, coe_mul] at *
  have hf' : forall x : M, (x : c.Quotient) * f x = 1 := fun x =>
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
/--
theorem `inv` / 定理 `inv`

English:
theorem inv
  given: {x y} (h : c x y)
  statement: c x⁻¹ y⁻¹
  proof: c.map_of_mul_left_rel_one Inv.inv (fun x => by simp only [inv_mul_cancel, c.refl 1]) h

中文:
定理 inv
  条件: {x y} (h : c x y)
  结论: c x⁻¹ y⁻¹
  证明: c.map_of_mul_left_rel_one Inv.inv (fun x => by simp only [inv_mul_cancel, c.refl 1]) h
-/
protected theorem inv {x y} (h : c x y) : c x⁻¹ y⁻¹ :=
  c.map_of_mul_left_rel_one Inv.inv (fun x => by simp only [inv_mul_cancel, c.refl 1]) h

/-- Multiplicative congruence relations preserve division. -/
@[to_additive /-- Additive congruence relations preserve subtraction. -/]
/--
theorem `div` / 定理 `div`

English:
theorem div
  statement: forall {w x y z}, c w x -> c y z -> c (w / y) (x / z)
  proof: @fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv h2)

中文:
定理 div
  结论: 对任意 {w x y z}, c w x -> c y z -> c (w / y) (x / z)
  证明: @fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv h2)
-/
protected theorem div : forall {w x y z}, c w x -> c y z -> c (w / y) (x / z) := @fun w x y z h1 h2 => by
  simpa only [div_eq_mul_inv] using c.mul h1 (c.inv h2)

/-- Multiplicative congruence relations preserve integer powers. -/
@[to_additive /-- Additive congruence relations preserve integer scaling. -/]
/--
theorem `zpow` / 定理 `zpow`

English:
theorem zpow
  statement: forall (n : Int) {w x}, c w x -> c (w ^ n) (x ^ n)

中文:
定理 zpow
  结论: 对任意 (n : 整数) {w x}, c w x -> c (w ^ n) (x ^ n)
-/
protected theorem zpow : forall (n : Int) {w x}, c w x -> c (w ^ n) (x ^ n)
  | Int.ofNat n, w, x, h => by simpa only [zpow_natCast, Int.ofNat_eq_natCast] using c.pow n h
  | Int.negSucc n, w, x, h => by simpa only [zpow_negSucc] using c.inv (c.pow _ h)

/-- The inversion induced on the quotient by a congruence relation on a type with an
inversion. -/
@[to_additive /-- The negation induced on the quotient by an additive congruence relation on a type
with a negation. -/]
/--
Instance `hasInv` / 实例 `hasInv`

English:
instance hasInv
  signature: : Inv c.Quotient
  body: ⟨(Quotient.map' Inv.inv) fun _ _ => c.inv⟩

中文:
实例 hasInv
  签名: : 取逆 c.商
  定义体: ⟨(Quotient.map' Inv.inv) fun _ _ => c.inv⟩

Depends on / 依赖: Inv.inv, Quotient, Quotient.map, c.inv
-/
instance hasInv : Inv c.Quotient :=
  ⟨(Quotient.map' Inv.inv) fun _ _ => c.inv⟩

/-- The division induced on the quotient by a congruence relation on a type with a
division. -/
@[to_additive /-- The subtraction induced on the quotient by an additive congruence relation on a
type with a subtraction. -/]
/--
Instance `hasDiv` / 实例 `hasDiv`

English:
instance hasDiv
  signature: : Div c.Quotient
  body: ⟨(Quotient.map₂ (· / ·)) fun _ _ h₁ _ _ h₂ => c.div h₁ h₂⟩

中文:
实例 hasDiv
  签名: : 除法 c.商
  定义体: ⟨(Quotient.map₂ (· / ·)) fun _ _ h₁ _ _ h₂ => c.div h₁ h₂⟩

Depends on / 依赖: Quotient, Quotient.map, c.div
-/
instance hasDiv : Div c.Quotient :=
  ⟨(Quotient.map₂ (· / ·)) fun _ _ h₁ _ _ h₂ => c.div h₁ h₂⟩

/-- The integer power induced on the quotient by a congruence relation on a type with a
division. -/
@[to_additive /-- The integer scaling induced on the quotient by a congruence relation on a type
with a subtraction. -/]
/--
Instance `instZPow` / 实例 `instZPow`

English:
instance instZPow
  signature: : Pow c.Quotient Int
  body: ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun _ _ h => c.zpow z h) x⟩

中文:
实例 instZPow
  签名: : 幂 c.商 整数
  定义体: ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun _ _ h => c.zpow z h) x⟩

Depends on / 依赖: Quotient, Quotient.map, c.zpow
-/
instance instZPow : Pow c.Quotient Int :=
  ⟨fun x z => Quotient.map' (fun x => x ^ z) (fun _ _ h => c.zpow z h) x⟩

/-- The quotient of a group by a congruence relation is a group. -/
@[to_additive /-- The quotient of an `AddGroup` by an additive congruence relation is
an `AddGroup`. -/]
/--
Instance `group` / 实例 `group`

English:
instance group
  signature: : Group c.Quotient
  body: fast_instance%
  Function.Surjective.group Quotient.mk'' Quotient.mk''_surjective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 group
  签名: : 群 c.商
  定义体: fast_instance%
  Function.Surjective.group Quotient.mk'' Quotient.mk''_surjective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance group : Group c.Quotient := fast_instance%
  Function.Surjective.group Quotient.mk'' Quotient.mk''_surjective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/-- The quotient of a `CommGroup` by a congruence relation is a `CommGroup`. -/
@[to_additive /-- The quotient of an `AddCommGroup` by an additive congruence
relation is an `AddCommGroup`. -/]
/--
Instance `commGroup` / 实例 `commGroup`

English:
instance commGroup
  signature: {M : Type*} [CommGroup M] (c : Con M)
  body: fast_instance%
  Function.Surjective.commGroup _ Quotient.mk''_surjective rfl (fun _ _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

中文:
实例 commGroup
  签名: {M : 类型} [交换群 M] (c : Con M)
  定义体: fast_instance%
  Function.Surjective.commGroup _ Quotient.mk''_surjective rfl (fun _ _ => rfl) (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

Depends on / 依赖: fast_instance
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
/--
Definition of `liftOnUnits` / `liftOnUnits` 的定义

English:
definition liftOnUnits
  signature: (u : Units c.Quotient) (f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α)
  body: by
  refine
    Con.hrecOn₂ (cN := c) (φ := fun x y => x * y = 1 -> y * x = 1 -> α) (u : c.Quotient)
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

中文:
定义 liftOnUnits
  签名: (u : 单位群 c.商) (f : 对任意 x y : M, c (x * y) 1 -> c (y * x) 1 -> α)
  定义体: by
  refine
    Con.hrecOn₂ (cN := c) (φ := fun x y => x * y = 1 -> y * x = 1 -> α) (u : c.Quotient)
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

Depends on / 依赖: Con.hrecOn, Function, Function.hfunext, Quotient, c.Quotient, c.eq, heq_of_eq, hfunext
-/
def liftOnUnits (u : Units c.Quotient) (f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α)
    (Hf : forall x y hxy hyx x' y' hxy' hyx',
      c x x' -> c y y' -> f x y hxy hyx = f x' y' hxy' hyx') : α := by
  refine
    Con.hrecOn₂ (cN := c) (φ := fun x y => x * y = 1 -> y * x = 1 -> α) (u : c.Quotient)
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
/--
theorem `liftOnUnits_mk` / 定理 `liftOnUnits_mk`

English:
theorem liftOnUnits_mk
  statement: (f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α)
  proof: rfl

@[to_additive (attr := elab_as_elim)]

中文:
定理 liftOnUnits_mk
  结论: (f : 对任意 x y : M, c (x * y) 1 -> c (y * x) 1 -> α)
  证明: rfl

@[to_additive (attr := elab_as_elim)]
-/
theorem liftOnUnits_mk (f : forall x y : M, c (x * y) 1 -> c (y * x) 1 -> α)
    (Hf : forall x y hxy hyx x' y' hxy' hyx', c x x' -> c y y' -> f x y hxy hyx = f x' y' hxy' hyx')
    (x y : M) (hxy hyx) :
    liftOnUnits ⟨(x : c.Quotient), y, hxy, hyx⟩ f Hf = f x y (c.eq.1 hxy) (c.eq.1 hyx) :=
  rfl

@[to_additive (attr := elab_as_elim)]
/--
theorem `induction_on_units` / 定理 `induction_on_units`

English:
theorem induction_on_units
  statement: {p : Units c.Quotient -> Prop} (u : Units c.Quotient)
  proof: by
  rcases u with ⟨⟨x⟩, ⟨y⟩, h₁, h₂⟩
  exact H x y (c.eq.1 h₁) (c.eq.1 h₂)

中文:
定理 induction_on_units
  结论: {p : 单位群 c.商 -> 命题} (u : 单位群 c.商)
  证明: by
  rcases u with ⟨⟨x⟩, ⟨y⟩, h₁, h₂⟩
  exact H x y (c.eq.1 h₁) (c.eq.1 h₂)

Depends on / 依赖: c.eq
-/
theorem induction_on_units {p : Units c.Quotient -> Prop} (u : Units c.Quotient)
    (H : forall (x y : M) (hxy : c (x * y) 1) (hyx : c (y * x) 1), p ⟨x, y, c.eq.2 hxy, c.eq.2 hyx⟩) :
    p u := by
  rcases u with ⟨⟨x⟩, ⟨y⟩, h₁, h₂⟩
  exact H x y (c.eq.1 h₁) (c.eq.1 h₂)

end Units

end Con
