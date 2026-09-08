/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Ring.Hom.Defs
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.GroupTheory.Congruence.Defs
public import Mathlib.Tactic.FastInstance

/-!
# Congruence relations on rings

This file defines congruence relations on rings, which extend `Con` and `AddCon` on monoids and
additive monoids.

Most of the time you likely want to use the `Ideal.Quotient` API that is built on top of this.

## Main Definitions

* `RingCon R`: the type of congruence relations respecting `+` and `*`.
* `RingConGen r`: the inductively defined smallest ring congruence relation containing a given
  binary relation.

## TODO

* Copy across more API from `Con` and `AddCon` in `Mathlib/GroupTheory/Congruence/`.
-/

@[expose] public section

open Function

/-- A congruence relation on a type with an addition and multiplication is an equivalence relation
which preserves both. -/
/-
**RingCon** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) → [Add R] → [Mul R] → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A congruence relation on a type with an addition and multiplication is an equiva
lence relation
which preserves both.
-/
structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where

/-- The induced multiplicative congruence from a `RingCon`. -/
add_decl_doc RingCon.toCon

/-- The induced additive congruence from a `RingCon`. -/
add_decl_doc RingCon.toAddCon

variable {R : Type*}

/-- The inductively defined smallest ring congruence relation containing a given binary
relation. -/
/-
**RingConGen.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `RingConGen`。
形式化陈述：{R : Type u_1} → [Add R] → [Mul R] → (R → R → Prop) → R → R → Prop
参数：R → R → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inductively defined smallest ring congruence relation containing a given bin
ary
relation.
-/
inductive RingConGen.Rel [Add R] [Mul R] (r : R → R → Prop) : R → R → Prop
  | of : ∀ x y, r x y → RingConGen.Rel r x y
  | refl : ∀ x, RingConGen.Rel r x x
  | symm : ∀ {x y}, RingConGen.Rel r x y → RingConGen.Rel r y x
  | trans : ∀ {x y z}, RingConGen.Rel r x y → RingConGen.Rel r y z → RingConGen.Rel r x z
  | add : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w + y) (x + z)
  | mul : ∀ {w x y z}, RingConGen.Rel r w x → RingConGen.Rel r y z →
      RingConGen.Rel r (w * y) (x * z)

/-- The inductively defined smallest ring congruence relation containing a given binary
relation. -/
/-
**ringConGen** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ringConGen [Add R] [Mul R] (r : R -> R -> Prop) : RingCon R where r
参数：r : R -> R -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inductively defined smallest ring congruence relation containing a given bin
ary
relation.
-/
def ringConGen [Add R] [Mul R] (r : R → R → Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul

namespace RingCon

section Basic

variable [Add R] [Mul R] {c d : RingCon R}

/-
**RingCon.toCon_injective** 是 Mathlib 中的一个引理，位于命名空间 `RingCon`。
形式化陈述：toCon_injective : Injective fun c : RingCon R => c.toCon
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `RingCon.add'`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (self : R
ingCon R) {w x y z : R},   self.toSetoid w x → self.toSetoid y z → self.toSetoid
 (…
-/
lemma toCon_injective : Injective fun c : RingCon R ↦ c.toCon := fun c d ↦ by cases c; congr!
/-
**RingCon.toCon_inj** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] {c d : RingCon R}, c.toCo
n = d.toCon ↔ c = d
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `RingCon.toCon_injective`：toCon_injective : Injective fun c : RingCon R =
> c.toCon
-/
@[simp] lemma toCon_inj : c.toCon = d.toCon ↔ c = d := toCon_injective.eq_iff

/-- A coercion from a congruence relation to its underlying binary relation. -/
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A coercion from a congruence relation to its underlying binary relation.
-/
instance : FunLike (RingCon R) R (R → Prop) where
  coe c := c.r
  coe_injective := DFunLike.coe_injective.comp toCon_injective

variable (c)

@[simp]
/-
**RingCon.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_mk (s : Con R) (h) : ⇑(mk s h) = s
参数：s : Con R；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (s : Con R) (h) : ⇑(mk s h) = s := rfl
/-
**RingCon.rel_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：rel_eq_coe : c.r = c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem rel_eq_coe : c.r = c :=
  rfl

@[simp]
/-
**RingCon.toCon_coe_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：toCon_coe_eq_coe : (c.toCon : R -> R -> Prop) = c
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toCon_coe_eq_coe : (c.toCon : R → R → Prop) = c :=
  rfl
/-
**RingCon.refl** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingCon R) (x : R), 
c x x
参数：c : RingCon R；x : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.refl'`：refl' (r : Setoid α) (x) : r x x
-/
protected theorem refl (x) : c x x :=
  c.refl' x
/-
**RingCon.symm** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingCon R) {x y : R}
, c x y → c y x
参数：c : RingCon R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.symm'`：symm' (r : Setoid α) : forall {x y}, r x y -> r y x
-/
protected theorem symm {x y} : c x y → c y x :=
  c.symm'
/-
**RingCon.trans** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingCon R) {x y z : 
R}, c x y → c y z → c x z
参数：c : RingCon R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.trans'`：trans' (r : Setoid α) : forall {x y z}, r x y -> r y z ->
 r x z
-/
protected theorem trans {x y z} : c x y → c y z → c x z :=
  c.trans'
/-
**RingCon.add** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingCon R) {w x y z 
: R}, c w x → c y z → c (w + y) (x + z)
参数：c : RingCon R；w + y；x + z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.add'`：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (self : R
ingCon R) {w x y z : R},   self.toSetoid w x → self.toSetoid y z → self.toSetoid
 (…
-/
protected theorem add {w x y z} : c w x → c y z → c (w + y) (x + z) :=
  c.add'
/-
**RingCon.mul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingCon R) {w x y z 
: R}, c w x → c y z → c (w * y) (x * z)
参数：c : RingCon R；w * y；x * z。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Con.mul'`：∀ {M : Type u_1} [inst : Mul M] (self : Con M) {w x y z : M}, 
  self.toSetoid w x → self.toSetoid y z → self.toSetoid (w * y) (x * z)
-/
protected theorem mul {w x y z} : c w x → c y z → c (w * y) (x * z) :=
  c.mul'
/-
**RingCon.sub** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {S : Type u_2} [inst : AddGroup S] [inst_1 : Mul S] (t : RingCon S) {a b
 c d : S}, t a b → t c d → t (a - c) (b - d)
参数：t : RingCon S；a - c；b - d。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.sub`：∀ {M : Type u_1} [inst : AddGroup M] (c : AddCon M) {w x y z
 : M}, c w x → c y z → c (w - y) (x - z)
-/
protected theorem sub {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    {a b c d : S} (h : t a b) (h' : t c d) : t (a - c) (b - d) := t.toAddCon.sub h h'
/-
**RingCon.neg** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {S : Type u_2} [inst : AddGroup S] [inst_1 : Mul S] (t : RingCon S) {a b
 : S}, t a b → t (-a) (-b)
参数：t : RingCon S；-a；-b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.neg`：∀ {M : Type u_1} [inst : AddGroup M] (c : AddCon M) {x y : M
}, c x y → c (-x) (-y)
-/
protected theorem neg {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    {a b} (h : t a b) : t (-a) (-b) := t.toAddCon.neg h
/-
**RingCon.nsmul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {S : Type u_2} [inst : AddMonoid S] [inst_1 : Mul S] (t : RingCon S) (m 
: ℕ) {x y : S}, t x y → t (m • x) (m • y)
参数：t : RingCon S；m : ℕ；m • x；m • y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.nsmul`：∀ {M : Type u_4} [inst : AddMonoid M] (c : AddCon M) (n : 
ℕ) {w x : M}, c w x → c (n • w) (n • x)
-/
protected theorem nsmul {S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
    (m : ℕ) {x y : S} (hx : t x y) : t (m • x) (m • y) := t.toAddCon.nsmul m hx
/-
**RingCon.zsmul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {S : Type u_2} [inst : AddGroup S] [inst_1 : Mul S] (t : RingCon S) (z :
 ℤ) {x y : S}, t x y → t (z • x) (z • y)
参数：t : RingCon S；z : ℤ；z • x；z • y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.zsmul`：∀ {M : Type u_1} [inst : AddGroup M] (c : AddCon M) (n : ℤ
) {w x : M}, c w x → c (n • w) (n • x)
-/
protected theorem zsmul {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    (z : ℤ) {x y : S} (hx : t x y) : t (z • x) (z • y) := t.toAddCon.zsmul z hx
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (RingCon R) :=
  ⟨ringConGen emptyRelation⟩

@[simp]
/-
**RingCon.rel_mk** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：rel_mk {s : Con R} {h a b} : RingCon.mk s h a b ↔ s a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_mk {s : Con R} {h a b} : RingCon.mk s h a b ↔ s a b :=
  Iff.rfl

/-- The map sending a congruence relation to its underlying binary relation is injective. -/
/-
**RingCon.ext'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d
参数：H : ⇑c = ⇑d。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
The map sending a congruence relation to its underlying binary relation is injec
tive.
-/
theorem ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
@[ext]
/-
**RingCon.ext** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c = d
参数：H : forall x y, c x y ↔ d x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext'`：ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g

--- 原说明 ---
Extensionality rule for congruence relations.
-/
theorem ext {c d : RingCon R} (H : ∀ x y, c x y ↔ d x y) : c = d :=
  ext' <| by ext; apply H

/-- The map sending a ring congruence relation to its underlying equivalence
relation is injective. -/
/-
**RingCon.ext''** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：ext'' {c d : RingCon R} (H : c.toSetoid = d.toSetoid) : c = d
参数：H : c.toSetoid = d.toSetoid。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.ext`：ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c =
 d
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Setoid.ext_iff`：∀ {α : Sort u_3} {s t : Setoid α}, s = t ↔ ∀ (a b : α), 
s a b ↔ t a b

--- 原说明 ---
The map sending a ring congruence relation to its underlying equivalence
relation is injective.
-/
theorem ext'' {c d : RingCon R} (H : c.toSetoid = d.toSetoid) : c = d :=
  ext <| Setoid.ext_iff.1 H

/-- Two ring congruence relations are equal iff their underlying binary
relations are equal. -/
/-
**RingCon.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_inj {c d : RingCon R} : ⇑c = ⇑d ↔ c = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Two ring congruence relations are equal iff their underlying binary
relations are equal.
-/
theorem coe_inj {c d : RingCon R} : ⇑c = ⇑d ↔ c = d := by simp

variable {R R' F : Type*} [Add R] [Add R']
    [FunLike F R R'] [AddHomClass F R R'] [Mul R] [Mul R'] [MulHomClass F R R']

/--
Pulling back a `RingCon` across a ring homomorphism.
-/
/-
**RingCon.comap** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：comap (J : RingCon R') (f : F) : RingCon R where __
参数：J : RingCon R'；f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddCon.add'`：∀ {M : Type u_1} [inst : Add M] (self : AddCon M) {w x y z 
: M},   self.toSetoid w x → self.toSetoid y z → self.toSetoid (w + y) (x + z)

--- 原说明 ---
Pulling back a `RingCon` across a ring homomorphism.
-/
def comap (J : RingCon R') (f : F) :
    RingCon R where
  __ := J.toCon.comap f (map_mul f)
  __ := J.toAddCon.comap f (map_add f)

@[simp]
/-
**RingCon.comap_rel** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_rel {J : RingCon R'} {f : F} {x y : R} : J.comap f x y ↔ J (f x) (f 
y)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem comap_rel {J : RingCon R'} {f : F} {x y : R} :
    J.comap f x y ↔ J (f x) (f y) := Iff.rfl

@[simp]
/-
**RingCon.comap_nonUnitalRingHomId** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_nonUnitalRingHomId {R} [NonUnitalNonAssocSemiring R] (J : RingCon R)
 : J.comap (NonUnitalRingHom.id _) = J
参数：J : RingCon R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
-/
theorem comap_nonUnitalRingHomId {R} [NonUnitalNonAssocSemiring R] (J : RingCon R) :
    J.comap (NonUnitalRingHom.id _) = J := rfl

@[simp]
/-
**RingCon.comap_nonUnitalRingHomComp** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_nonUnitalRingHomComp {R R' R''} [NonUnitalNonAssocSemiring R] [NonUn
italNonAssocSemiring R'] [NonUnitalNonAssocSemiring R''] (J : RingCon R) (g : R'
 ->ₙ+* R) (f : R'' ->ₙ+* R') : J.comap (g.comp f) = (J.comap g).comap f
参数：J : RingCon R；g : R' ->ₙ+* R；f : R'' ->ₙ+* R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `NonUnitalRingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outPara
m (Type u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {
inst_1 : NonUnitalNonAssocSemir…
· 使用定理 `NonUnitalRingHom.instNonUnitalRingHomClass`：∀ {α : Type u_2} {β : Type u
_3} [inst : NonUnitalNonAssocSemiring α] [inst_1 : NonUnitalNonAssocSemiring β],
   NonUnitalRingHomClass (α →ₙ+*…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
-/
theorem comap_nonUnitalRingHomComp {R R' R''}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring R'']
    (J : RingCon R) (g : R' →ₙ+* R) (f : R'' →ₙ+* R') :
    J.comap (g.comp f) = (J.comap g).comap f := rfl

@[simp]
/-
**RingCon.comap_ringHomId** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_ringHomId {R} [NonAssocSemiring R] (J : RingCon R) : J.comap (RingHo
m.id _) = J
参数：J : RingCon R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem comap_ringHomId {R} [NonAssocSemiring R] (J : RingCon R) :
    J.comap (RingHom.id _) = J := rfl

@[simp]
/-
**RingCon.comap_ringHomComp** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：comap_ringHomComp {R R' R''} [NonAssocSemiring R] [NonAssocSemiring R'] [N
onAssocSemiring R''] (J : RingCon R) (g : R' ->+* R) (f : R'' ->+* R') : J.comap
 (g.comp f) = (J.comap g).comap f
参数：J : RingCon R；g : R' ->+* R；f : R'' ->+* R'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
-/
theorem comap_ringHomComp {R R' R''}
    [NonAssocSemiring R] [NonAssocSemiring R'] [NonAssocSemiring R'']
    (J : RingCon R) (g : R' →+* R) (f : R'' →+* R') :
    J.comap (g.comp f) = (J.comap g).comap f := rfl

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

/-- Defining the quotient by a congruence relation of a type with addition and multiplication. -/
/-
**RingCon.Quotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：{R : Type u_1} → [inst : Add R] → [inst_1 : Mul R] → RingCon R → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defining the quotient by a congruence relation of a type with addition and multi
plication.
-/
protected def Quotient :=
  Quotient c.toSetoid

variable {c}

/-- The morphism into the quotient by a congruence relation -/
/-
**RingCon.toQuotient** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：{R : Type u_1} → [inst : Add R] → [inst_1 : Mul R] → {c : RingCon R} → R →
 c.Quotient
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)

--- 原说明 ---
The morphism into the quotient by a congruence relation
-/
@[coe] def toQuotient (r : R) : c.Quotient :=
  @Quotient.mk'' _ c.toSetoid r

variable (c)

/-- Coercion from a type with addition and multiplication to its quotient by a congruence relation.

See Note [use has_coe_t]. -/
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from a type with addition and multiplication to its quotient by a congr
uence relation.

See Note [use has_coe_t].
-/
instance : CoeTC R c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient by a decidable congruence relation has decidable equality.
-/
instance (priority := 500) [_d : ∀ a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[simp]
/-
**RingCon.quot_mk_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient)
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
/-
**RingCon.eq** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : Add R] [inst_1 : Mul R] (c : RingCon R) {a b : R}
, ↑a = ↑b ↔ c a b
参数：c : RingCon R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b

--- 原说明 ---
Two elements are related by a congruence relation `c` iff they are represented b
y the same
element of the quotient by `c`.
-/
protected theorem eq {a b : R} : (a : c.Quotient) = (b : c.Quotient) ↔ c a b :=
  Quotient.eq''

end Basic

/-! ### Basic notation

The basic algebraic notation, `0`, `1`, `+`, `*`, `-`, `^`, descend naturally under the quotient
-/


section Data

section add_mul

variable [Add R] [Mul R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add c.Quotient := inferInstanceAs (Add c.toAddCon.Quotient)

@[simp, norm_cast]
/-
**RingCon.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul c.Quotient := inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]
/-
**RingCon.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero c.Quotient := inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]
/-
**RingCon.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_zero : (↑(0 : R) : c.Quotient) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One c.Quotient := inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]
/-
**RingCon.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_one : (↑(1 : R) : c.Quotient) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl

end One

/-- A function used to define scalar actions on `RingCon.Quotient`. To make sure such actions coming
from different sources are reducibly defeq, they should all go through this function. -/
/-
**RingCon.smulAux** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：smulAux [Add R] [Mul R] {α : Type*} [SMul α R] (c : RingCon R) (h : forall
 (a : α) (x y : R), c x y -> c (a • x) (a • y)) (a : α) (x : c.Quotient) : c.Quo
tient
参数：c : RingCon R；h : forall (a : α) (x y : R), c x y -> c (a • x) (a • y)；a : α；
x : c.Quotient。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
A function used to define scalar actions on `RingCon.Quotient`. To make sure suc
h actions coming
from different sources are reducibly defeq, they should all go through this func
tion.
-/
def smulAux [Add R] [Mul R] {α : Type*} [SMul α R]
    (c : RingCon R) (h : ∀ (a : α) (x y : R), c x y → c (a • x) (a • y))
    (a : α) (x : c.Quotient) : c.Quotient :=
  Quotient.map' (a • ·) (h a) x

section NegSubZSMul

variable [AddGroup R] [Mul R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg c.Quotient := inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]
/-
**RingCon.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_neg (x : R) : (↑(-x) : c.Quotient) = -x
参数：x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub c.Quotient := inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]
/-
**RingCon.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y
参数：x y : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl
/-
**RingCon.hasZSMul** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
形式化陈述：hasZSMul : SMul Int c.Quotient
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.zsmul`：∀ {S : Type u_2} [inst : AddGroup S] [inst_1 : Mul S] (t 
: RingCon S) (z : ℤ) {x y : S}, t x y → t (z • x) (z • y)
-/
instance hasZSMul : SMul ℤ c.Quotient := ⟨c.smulAux (RingCon.zsmul c)⟩

@[simp, norm_cast]
/-
**RingCon.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_zsmul (z : Int) (x : R) : (↑(z • x) : c.Quotient) = z • (x : c.Quotien
t)
参数：z : Int；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul (z : ℤ) (x : R) : (↑(z • x) : c.Quotient) = z • (x : c.Quotient) :=
  rfl

end NegSubZSMul

section NSMul

variable [AddMonoid R] [Mul R] (c : RingCon R)

/-
**RingCon.hasNSMul** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
形式化陈述：hasNSMul : SMul Nat c.Quotient
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingCon.nsmul`：∀ {S : Type u_2} [inst : AddMonoid S] [inst_1 : Mul S] (t
 : RingCon S) (m : ℕ) {x y : S}, t x y → t (m • x) (m • y)
-/
instance hasNSMul : SMul ℕ c.Quotient := ⟨c.smulAux (RingCon.nsmul c)⟩

@[simp, norm_cast]
/-
**RingCon.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_nsmul (n : Nat) (x : R) : (↑(n • x) : c.Quotient) = n • (x : c.Quotien
t)
参数：n : Nat；x : R。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul (n : ℕ) (x : R) : (↑(n • x) : c.Quotient) = n • (x : c.Quotient) :=
  rfl

end NSMul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Pow c.Quotient ℕ := inferInstanceAs (Pow c.toCon.Quotient ℕ)

@[simp, norm_cast]
/-
**RingCon.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_pow (x : R) (n : Nat) : (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n
参数：x : R；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow (x : R) (n : ℕ) : (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n :=
  rfl

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]
/-
**RingCon.coe_natCast** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_natCast (n : Nat) : (↑(n : R) : c.Quotient) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_natCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]
/-
**RingCon.coe_intCast** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_intCast (n : Nat) : (↑(n : R) : c.Quotient) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_intCast (n : ℕ) : (↑(n : R) : c.Quotient) = n :=
  rfl

end IntCast

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : RingCon R` preserve the algebraic structure of `R`.
-/


section Algebraic

section Add

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddZeroClass R] [Mul R] (c : RingCon R) : AddZeroClass c.Quotient :=
  inferInstanceAs <| AddZeroClass c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddSemigroup R] [Mul R] (c : RingCon R) : AddSemigroup c.Quotient :=
  inferInstanceAs <| AddSemigroup c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMagma R] [Mul R] (c : RingCon R) : AddCommMagma c.Quotient :=
  inferInstanceAs <| AddCommMagma c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommSemigroup R] [Mul R] (c : RingCon R) : AddCommSemigroup c.Quotient :=
  inferInstanceAs <| AddCommSemigroup c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddMonoid R] [Mul R] (c : RingCon R) : AddMonoid c.Quotient where
  nsmul n x := n • x
  __ : AddMonoid c.Quotient := inferInstanceAs <| AddMonoid c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommMonoid R] [Mul R] (c : RingCon R) : AddCommMonoid c.Quotient :=
  inferInstanceAs <| AddCommMonoid c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddGroup R] [Mul R] (c : RingCon R) : AddGroup c.Quotient where
  zsmul n x := n • x
  __ : AddGroup c.Quotient := inferInstanceAs <| AddGroup c.toAddCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [AddCommGroup R] [Mul R] (c : RingCon R) : AddCommGroup c.Quotient :=
  inferInstanceAs <| AddCommGroup c.toAddCon.Quotient

end Add

section Mul

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [MulOneClass R] (c : RingCon R) : MulOneClass c.Quotient :=
  inferInstanceAs <| MulOneClass c.toCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [Semigroup R] (c : RingCon R) : Semigroup c.Quotient :=
  inferInstanceAs <| Semigroup c.toCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [CommMagma R] (c : RingCon R) : CommMagma c.Quotient :=
  inferInstanceAs <| CommMagma c.toCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [CommSemigroup R] (c : RingCon R) : CommSemigroup c.Quotient :=
  inferInstanceAs <| CommSemigroup c.toCon.Quotient
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [Monoid R] (c : RingCon R) : Monoid c.Quotient := fast_instance%
  { __ : Monoid c.toCon.Quotient := inferInstanceAs _
    -- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/inferInstanceAs.20creates.20non-reducible.20diamonds/near/603969174
    npow n x := x ^ n }
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Add R] [CommMonoid R] (c : RingCon R) : CommMonoid c.Quotient :=
  inferInstanceAs <| CommMonoid c.toCon.Quotient

end Mul

/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocSemiring R] (c : RingCon R) :
    NonUnitalNonAssocSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocCommSemiring R] (c : RingCon R) :
    NonUnitalNonAssocCommSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocCommSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient := fast_instance%
  Function.Surjective.nonAssocSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocCommSemiring R] (c : RingCon R) :
    NonAssocCommSemiring c.Quotient := fast_instance%
  Function.Surjective.nonAssocCommSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommSemiring R] (c : RingCon R) :
    NonUnitalCommSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalCommSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] (c : RingCon R) : Semiring c.Quotient := fast_instance%
  Function.Surjective.semiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient := fast_instance%
  Function.Surjective.commSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocRing R] (c : RingCon R) :
    NonUnitalNonAssocRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalNonAssocCommRing R] (c : RingCon R) :
    NonUnitalNonAssocCommRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient := fast_instance%
  Function.Surjective.nonAssocRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonAssocCommRing R] (c : RingCon R) : NonAssocCommRing c.Quotient := fast_instance%
  Function.Surjective.nonAssocCommRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [NonUnitalCommRing R] (c : RingCon R) : NonUnitalCommRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Ring R] (c : RingCon R) : Ring c.Quotient := fast_instance%
  Function.Surjective.ring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl
/-
**RingCon.** 是 Mathlib 中的一个实例，位于命名空间 `RingCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CommRing R] (c : RingCon R) : CommRing c.Quotient := fast_instance%
  Function.Surjective.commRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

end Algebraic

variable [NonAssocSemiring R] (c : RingCon R)

/-- The natural homomorphism from a ring to its quotient by a ring congruence relation. -/
/-
**RingCon.mk'** 是 Mathlib 中的一个定义，位于命名空间 `RingCon`。
形式化陈述：mk' : R ->+* c.Quotient where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural homomorphism from a ring to its quotient by a ring congruence relati
on.
-/
def mk' : R →+* c.Quotient where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl
/-
**RingCon.mk'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：∀ {R : Type u_1} [inst : NonAssocSemiring R] (c : RingCon R), Function.Sur
jective ⇑c.mk'
参数：c : RingCon R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
-/
theorem mk'_surjective : Function.Surjective c.mk' :=
  Quotient.mk''_surjective

@[simp]
/-
**RingCon.coe_mk'** 是 Mathlib 中的一个定理，位于命名空间 `RingCon`。
形式化陈述：coe_mk' : (c.mk' : R -> c.Quotient) = ((↑) : R -> c.Quotient)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk' : (c.mk' : R → c.Quotient) = ((↑) : R → c.Quotient) :=
  rfl

end Quotient

end RingCon

