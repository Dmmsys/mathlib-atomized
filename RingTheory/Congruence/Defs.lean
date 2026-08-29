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

/--
Definition of `RingCon` / `RingCon` 的定义

English:
structure RingCon
  parameters: (R : Type*) [Add R] [Mul R]
  extends: Con R, AddCon R
  (no additional axioms)

中文:
结构 RingCon
  参数: (R : 类型) [加法 R] [乘法 R]
  继承: Con R, 加法Con R
  (无附加公理)
-/
structure RingCon (R : Type*) [Add R] [Mul R] extends Con R, AddCon R where

/-- The induced multiplicative congruence from a `RingCon`. -/
add_decl_doc RingCon.toCon

/-- The induced additive congruence from a `RingCon`. -/
add_decl_doc RingCon.toAddCon

variable {R : Type*}

/--
Inductive type `RingConGen.Rel` / 归纳类型 `RingConGen.Rel`

English:
inductive RingConGen.Rel
  parameters: [Add R] [Mul R] (r : R -> R -> Prop)
  constructors (6):
    - of: forall x y, r x y -> RingConGen.Rel r x y
    - refl: forall x, RingConGen.Rel r x x
    - symm: forall {x y}, RingConGen.Rel r x y -> RingConGen.Rel r y x
    - trans: forall {x y z}, RingConGen.Rel r x y -> RingConGen.Rel r y z -> RingConGen.Rel r x z
    - add: forall {w x y z}, RingConGen.Rel r w x -> RingConGen.Rel r y z -> RingConGen.Rel r (w + y) (x + z)
    - mul: forall {w x y z}, RingConGen.Rel r w x -> RingConGen.Rel r y z -> RingConGen.Rel r (w * y) (x * z)

中文:
归纳类型 RingConGen.关系
  参数: [加法 R] [乘法 R] (r : R -> R -> 命题)
  构造子 (6 个):
    - of: 对任意 x y, r x y -> RingConGen.关系 r x y
    - refl: 对任意 x, RingConGen.关系 r x x
    - symm: 对任意 {x y}, RingConGen.关系 r x y -> RingConGen.关系 r y x
    - trans: 对任意 {x y z}, RingConGen.关系 r x y -> RingConGen.关系 r y z -> RingConGen.关系 r x z
    - add: 对任意 {w x y z}, RingConGen.关系 r w x -> RingConGen.关系 r y z -> RingConGen.关系 r (w + y) (x + z)
    - mul: 对任意 {w x y z}, RingConGen.关系 r w x -> RingConGen.关系 r y z -> RingConGen.关系 r (w * y) (x * z)
-/
inductive RingConGen.Rel [Add R] [Mul R] (r : R -> R -> Prop) : R -> R -> Prop
  | of : forall x y, r x y -> RingConGen.Rel r x y
  | refl : forall x, RingConGen.Rel r x x
  | symm : forall {x y}, RingConGen.Rel r x y -> RingConGen.Rel r y x
  | trans : forall {x y z}, RingConGen.Rel r x y -> RingConGen.Rel r y z -> RingConGen.Rel r x z
  | add : forall {w x y z}, RingConGen.Rel r w x -> RingConGen.Rel r y z ->
      RingConGen.Rel r (w + y) (x + z)
  | mul : forall {w x y z}, RingConGen.Rel r w x -> RingConGen.Rel r y z ->
      RingConGen.Rel r (w * y) (x * z)

/--
Definition of `ringConGen` / `ringConGen` 的定义

English:
definition ringConGen
  signature: [Add R] [Mul R] (r : R -> R -> Prop)
  body: RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul

中文:
定义 ringConGen
  签名: [加法 R] [乘法 R] (r : R -> R -> 命题)
  定义体: RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul

Depends on / 依赖: RingConGen, RingConGen.Rel
-/
def ringConGen [Add R] [Mul R] (r : R -> R -> Prop) : RingCon R where
  r := RingConGen.Rel r
  iseqv := ⟨RingConGen.Rel.refl, @RingConGen.Rel.symm _ _ _ _, @RingConGen.Rel.trans _ _ _ _⟩
  add' := RingConGen.Rel.add
  mul' := RingConGen.Rel.mul

namespace RingCon

section Basic

variable [Add R] [Mul R] {c d : RingCon R}

/--
lemma `toCon_injective` / 引理 `toCon_injective`

English:
lemma toCon_injective
  statement: Injective fun c : RingCon R => c.toCon
  proof: fun c d => by cases c; congr!

中文:
引理 toCon_injective
  结论: 单射 fun c : RingCon R => c.toCon
  证明: fun c d => by cases c; congr!
-/
lemma toCon_injective : Injective fun c : RingCon R => c.toCon := fun c d => by cases c; congr!

/--
lemma `toCon_inj` / 引理 `toCon_inj`

English:
lemma toCon_inj
  statement: c.toCon = d.toCon ↔ c = d
  proof: toCon_injective.eq_iff

中文:
引理 toCon_inj
  结论: c.toCon = d.toCon ↔ c = d
  证明: toCon_injective.eq_iff
-/
@[simp] lemma toCon_inj : c.toCon = d.toCon ↔ c = d := toCon_injective.eq_iff

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (RingCon R) R (R -> Prop)
  body: c.r
  coe_injective := DFunLike.coe_injective.comp toCon_injective

中文:
实例 :
  签名: 函数状 (RingCon R) R (R -> 命题)
  定义体: c.r
  coe_injective := DFunLike.coe_injective.comp toCon_injective
-/
instance : FunLike (RingCon R) R (R -> Prop) where
  coe c := c.r
  coe_injective := DFunLike.coe_injective.comp toCon_injective

variable (c)

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (s : Con R) (h)
  statement: ⇑(mk s h) = s
  proof: rfl

中文:
定理 coe_mk
  条件: (s : Con R) (h)
  结论: ⇑(mk s h) = s
  证明: rfl
-/
theorem coe_mk (s : Con R) (h) : ⇑(mk s h) = s := rfl

/--
theorem `rel_eq_coe` / 定理 `rel_eq_coe`

English:
theorem rel_eq_coe
  statement: c.r = c
  proof: rfl

@[simp]

中文:
定理 rel_eq_coe
  结论: c.r = c
  证明: rfl

@[simp]
-/
theorem rel_eq_coe : c.r = c :=
  rfl

@[simp]
/--
theorem `toCon_coe_eq_coe` / 定理 `toCon_coe_eq_coe`

English:
theorem toCon_coe_eq_coe
  statement: (c.toCon : R -> R -> Prop) = c
  proof: rfl

中文:
定理 toCon_coe_eq_coe
  结论: (c.toCon : R -> R -> 命题) = c
  证明: rfl
-/
theorem toCon_coe_eq_coe : (c.toCon : R -> R -> Prop) = c :=
  rfl

/--
theorem `refl` / 定理 `refl`

English:
theorem refl
  given: (x)
  statement: c x x
  proof: c.refl' x

中文:
定理 refl
  条件: (x)
  结论: c x x
  证明: c.refl' x
-/
protected theorem refl (x) : c x x :=
  c.refl' x

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: {x y}
  statement: c x y -> c y x
  proof: c.symm'

中文:
定理 symm
  条件: {x y}
  结论: c x y -> c y x
  证明: c.symm'
-/
protected theorem symm {x y} : c x y -> c y x :=
  c.symm'

/--
theorem `trans` / 定理 `trans`

English:
theorem trans
  given: {x y z}
  statement: c x y -> c y z -> c x z
  proof: c.trans'

中文:
定理 trans
  条件: {x y z}
  结论: c x y -> c y z -> c x z
  证明: c.trans'
-/
protected theorem trans {x y z} : c x y -> c y z -> c x z :=
  c.trans'

/--
theorem `add` / 定理 `add`

English:
theorem add
  given: {w x y z}
  statement: c w x -> c y z -> c (w + y) (x + z)
  proof: c.add'

中文:
定理 add
  条件: {w x y z}
  结论: c w x -> c y z -> c (w + y) (x + z)
  证明: c.add'
-/
protected theorem add {w x y z} : c w x -> c y z -> c (w + y) (x + z) :=
  c.add'

/--
theorem `mul` / 定理 `mul`

English:
theorem mul
  given: {w x y z}
  statement: c w x -> c y z -> c (w * y) (x * z)
  proof: c.mul'

中文:
定理 mul
  条件: {w x y z}
  结论: c w x -> c y z -> c (w * y) (x * z)
  证明: c.mul'
-/
protected theorem mul {w x y z} : c w x -> c y z -> c (w * y) (x * z) :=
  c.mul'

/--
theorem `sub` / 定理 `sub`

English:
theorem sub
  statement: {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.sub h h'

中文:
定理 sub
  结论: {S : 类型} [加法群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.sub h h'
-/
protected theorem sub {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    {a b c d : S} (h : t a b) (h' : t c d) : t (a - c) (b - d) := t.toAddCon.sub h h'

/--
theorem `neg` / 定理 `neg`

English:
theorem neg
  statement: {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.neg h

中文:
定理 neg
  结论: {S : 类型} [加法群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.neg h
-/
protected theorem neg {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    {a b} (h : t a b) : t (-a) (-b) := t.toAddCon.neg h

/--
theorem `nsmul` / 定理 `nsmul`

English:
theorem nsmul
  statement: {S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.nsmul m hx

中文:
定理 nsmul
  结论: {S : 类型} [加法幺半群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.nsmul m hx
-/
protected theorem nsmul {S : Type*} [AddMonoid S] [Mul S] (t : RingCon S)
    (m : Nat) {x y : S} (hx : t x y) : t (m • x) (m • y) := t.toAddCon.nsmul m hx

/--
theorem `zsmul` / 定理 `zsmul`

English:
theorem zsmul
  statement: {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
  proof: t.toAddCon.zsmul z hx

中文:
定理 zsmul
  结论: {S : 类型} [加法群 S] [乘法 S] (t : RingCon S)
  证明: t.toAddCon.zsmul z hx
-/
protected theorem zsmul {S : Type*} [AddGroup S] [Mul S] (t : RingCon S)
    (z : Int) {x y : S} (hx : t x y) : t (z • x) (z • y) := t.toAddCon.zsmul z hx

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RingCon R)
  body: ⟨ringConGen emptyRelation⟩

@[simp]

中文:
实例 :
  签名: 可居 (RingCon R)
  定义体: ⟨ringConGen emptyRelation⟩

@[simp]

Depends on / 依赖: emptyRelation, ringConGen
-/
instance : Inhabited (RingCon R) :=
  ⟨ringConGen emptyRelation⟩

@[simp]
/--
theorem `rel_mk` / 定理 `rel_mk`

English:
theorem rel_mk
  given: {s : Con R} {h a b}
  statement: RingCon.mk s h a b ↔ s a b
  proof: Iff.rfl

中文:
定理 rel_mk
  条件: {s : Con R} {h a b}
  结论: RingCon.mk s h a b ↔ s a b
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem rel_mk {s : Con R} {h a b} : RingCon.mk s h a b ↔ s a b :=
  Iff.rfl

/--
theorem `ext'` / 定理 `ext'`

English:
theorem ext'
  given: {c d : RingCon R} (H : ⇑c = ⇑d)
  statement: c = d
  proof: DFunLike.coe_injective H

中文:
定理 ext'
  条件: {c d : RingCon R} (H : ⇑c = ⇑d)
  结论: c = d
  证明: DFunLike.coe_injective H

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem ext' {c d : RingCon R} (H : ⇑c = ⇑d) : c = d := DFunLike.coe_injective H

/-- Extensionality rule for congruence relations. -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {c d : RingCon R} (H : forall x y, c x y ↔ d x y)
  statement: c = d
  proof: ext' by ext; apply H

中文:
定理 ext
  条件: {c d : RingCon R} (H : 对任意 x y, c x y ↔ d x y)
  结论: c = d
  证明: ext' by ext; apply H
-/
theorem ext {c d : RingCon R} (H : forall x y, c x y ↔ d x y) : c = d :=
ext' by ext; apply H

/--
theorem `ext''` / 定理 `ext''`

English:
theorem ext''
  given: {c d : RingCon R} (H : c.toSetoid = d.toSetoid)
  statement: c = d
  proof: ext Setoid.ext_iff.1 H

中文:
定理 ext''
  条件: {c d : RingCon R} (H : c.toSetoid = d.toSetoid)
  结论: c = d
  证明: ext Setoid.ext_iff.1 H

Depends on / 依赖: Setoid, Setoid.ext_iff, ext_iff
-/
theorem ext'' {c d : RingCon R} (H : c.toSetoid = d.toSetoid) : c = d :=
ext Setoid.ext_iff.1 H

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {c d : RingCon R}
  statement: ⇑c = ⇑d ↔ c = d
  proof: by simp

中文:
定理 coe_inj
  条件: {c d : RingCon R}
  结论: ⇑c = ⇑d ↔ c = d
  证明: by simp
-/
theorem coe_inj {c d : RingCon R} : ⇑c = ⇑d ↔ c = d := by simp

variable {R R' F : Type*} [Add R] [Add R']
    [FunLike F R R'] [AddHomClass F R R'] [Mul R] [Mul R'] [MulHomClass F R R']

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (J : RingCon R') (f : F)
  body: J.toCon.comap f (map_mul f)
  __ := J.toAddCon.comap f (map_add f)

@[simp]

中文:
定义 comap
  签名: (J : RingCon R') (f : F)
  定义体: J.toCon.comap f (map_mul f)
  __ := J.toAddCon.comap f (map_add f)

@[simp]

Depends on / 依赖: J.toCon.comap, map_mul
-/
def comap (J : RingCon R') (f : F) :
    RingCon R where
  __ := J.toCon.comap f (map_mul f)
  __ := J.toAddCon.comap f (map_add f)

@[simp]
/--
theorem `comap_rel` / 定理 `comap_rel`

English:
theorem comap_rel
  given: {J : RingCon R'} {f : F} {x y : R}
  proof: Iff.rfl

@[simp]

中文:
定理 comap_rel
  条件: {J : RingCon R'} {f : F} {x y : R}
  证明: Iff.rfl

@[simp]

Depends on / 依赖: Iff.rfl
-/
theorem comap_rel {J : RingCon R'} {f : F} {x y : R} :
    J.comap f x y ↔ J (f x) (f y) := Iff.rfl

@[simp]
/--
theorem `comap_nonUnitalRingHomId` / 定理 `comap_nonUnitalRingHomId`

English:
theorem comap_nonUnitalRingHomId
  given: {R} [NonUnitalNonAssocSemiring R] (J : RingCon R)
  proof: rfl

@[simp]

中文:
定理 comap_nonUnitalRingHomId
  条件: {R} [非幺非结合半环 R] (J : RingCon R)
  证明: rfl

@[simp]
-/
theorem comap_nonUnitalRingHomId {R} [NonUnitalNonAssocSemiring R] (J : RingCon R) :
    J.comap (NonUnitalRingHom.id _) = J := rfl

@[simp]
/--
theorem `comap_nonUnitalRingHomComp` / 定理 `comap_nonUnitalRingHomComp`

English:
theorem comap_nonUnitalRingHomComp
  statement: {R R' R''}
  proof: rfl

@[simp]

中文:
定理 comap_nonUnitalRingHomComp
  结论: {R R' R''}
  证明: rfl

@[simp]
-/
theorem comap_nonUnitalRingHomComp {R R' R''}
    [NonUnitalNonAssocSemiring R] [NonUnitalNonAssocSemiring R'] [NonUnitalNonAssocSemiring R'']
    (J : RingCon R) (g : R' ->ₙ+* R) (f : R'' ->ₙ+* R') :
    J.comap (g.comp f) = (J.comap g).comap f := rfl

@[simp]
/--
theorem `comap_ringHomId` / 定理 `comap_ringHomId`

English:
theorem comap_ringHomId
  given: {R} [NonAssocSemiring R] (J : RingCon R)
  proof: rfl

@[simp]

中文:
定理 comap_ringHomId
  条件: {R} [非结合半环 R] (J : RingCon R)
  证明: rfl

@[simp]
-/
theorem comap_ringHomId {R} [NonAssocSemiring R] (J : RingCon R) :
    J.comap (RingHom.id _) = J := rfl

@[simp]
/--
theorem `comap_ringHomComp` / 定理 `comap_ringHomComp`

English:
theorem comap_ringHomComp
  statement: {R R' R''}
  proof: rfl

中文:
定理 comap_ringHomComp
  结论: {R R' R''}
  证明: rfl
-/
theorem comap_ringHomComp {R R' R''}
    [NonAssocSemiring R] [NonAssocSemiring R'] [NonAssocSemiring R'']
    (J : RingCon R) (g : R' ->+* R) (f : R'' ->+* R') :
    J.comap (g.comp f) = (J.comap g).comap f := rfl

end Basic

section Quotient

section Basic

variable [Add R] [Mul R] (c : RingCon R)

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

/--
Definition of `toQuotient` / `toQuotient` 的定义

English:
definition toQuotient
  signature: (r : R)
  body: @Quotient.mk'' _ c.toSetoid r

中文:
定义 toQuotient
  签名: (r : R)
  定义体: @Quotient.mk'' _ c.toSetoid r
-/
@[coe] def toQuotient (r : R) : c.Quotient :=
  @Quotient.mk'' _ c.toSetoid r

variable (c)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC R c.Quotient
  body: ⟨toQuotient⟩

中文:
实例 :
  签名: CoeTC R c.商
  定义体: ⟨toQuotient⟩

Depends on / 依赖: toQuotient
-/
instance : CoeTC R c.Quotient :=
  ⟨toQuotient⟩

-- Lower the priority since it unifies with any quotient type.
/-- The quotient by a decidable congruence relation has decidable equality. -/
instance (priority := 500) [_d : forall a b, Decidable (c a b)] : DecidableEq c.Quotient :=
  inferInstanceAs (DecidableEq (Quotient c.toSetoid))

@[simp]
/--
theorem `quot_mk_eq_coe` / 定理 `quot_mk_eq_coe`

English:
theorem quot_mk_eq_coe
  given: (x : R)
  statement: Quot.mk c x = (x : c.Quotient)
  proof: rfl

中文:
定理 quot_mk_eq_coe
  条件: (x : R)
  结论: 商.mk c x = (x : c.商)
  证明: rfl
-/
theorem quot_mk_eq_coe (x : R) : Quot.mk c x = (x : c.Quotient) :=
  rfl

/-- Two elements are related by a congruence relation `c` iff they are represented by the same
element of the quotient by `c`. -/
@[simp]
/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: {a b : R}
  statement: (a : c.Quotient) = (b : c.Quotient) ↔ c a b
  proof: Quotient.eq''

中文:
定理 eq
  条件: {a b : R}
  结论: (a : c.商) = (b : c.商) ↔ c a b
  证明: Quotient.eq''
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

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add c.Quotient
  body: inferInstanceAs (Add c.toAddCon.Quotient)

@[simp, norm_cast]

中文:
实例 :
  签名: 加法 c.商
  定义体: inferInstanceAs (Add c.toAddCon.Quotient)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toAddCon.Quotient, toAddCon
-/
instance : Add c.Quotient := inferInstanceAs (Add c.toAddCon.Quotient)

@[simp, norm_cast]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (x y : R)
  statement: (↑(x + y) : c.Quotient) = ↑x + ↑y
  proof: rfl

中文:
定理 coe_add
  条件: (x y : R)
  结论: (↑(x + y) : c.商) = ↑x + ↑y
  证明: rfl
-/
theorem coe_add (x y : R) : (↑(x + y) : c.Quotient) = ↑x + ↑y :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul c.Quotient
  body: inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]

中文:
实例 :
  签名: 乘法 c.商
  定义体: inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toCon.Quotient
-/
instance : Mul c.Quotient := inferInstanceAs (Mul c.toCon.Quotient)

@[simp, norm_cast]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (x y : R)
  statement: (↑(x * y) : c.Quotient) = ↑x * ↑y
  proof: rfl

中文:
定理 coe_mul
  条件: (x y : R)
  结论: (↑(x * y) : c.商) = ↑x * ↑y
  证明: rfl
-/
theorem coe_mul (x y : R) : (↑(x * y) : c.Quotient) = ↑x * ↑y :=
  rfl

end add_mul

section Zero

variable [AddZeroClass R] [Mul R] (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero c.Quotient
  body: inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]

中文:
实例 :
  签名: 零 c.商
  定义体: inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toAddCon.Quotient, toAddCon
-/
instance : Zero c.Quotient := inferInstanceAs (Zero c.toAddCon.Quotient)

@[simp, norm_cast]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: (↑(0 : R) : c.Quotient) = 0
  proof: rfl

中文:
定理 coe_zero
  结论: (↑(0 : R) : c.商) = 0
  证明: rfl
-/
theorem coe_zero : (↑(0 : R) : c.Quotient) = 0 :=
  rfl

end Zero

section One

variable [Add R] [MulOneClass R] (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One c.Quotient
  body: inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]

中文:
实例 :
  签名: 幺 c.商
  定义体: inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toCon.Quotient
-/
instance : One c.Quotient := inferInstanceAs (One c.toCon.Quotient)

@[simp, norm_cast]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: (↑(1 : R) : c.Quotient) = 1
  proof: rfl

中文:
定理 coe_one
  结论: (↑(1 : R) : c.商) = 1
  证明: rfl
-/
theorem coe_one : (↑(1 : R) : c.Quotient) = 1 :=
  rfl

end One

/--
Definition of `smulAux` / `smulAux` 的定义

English:
definition smulAux
  signature: [Add R] [Mul R] {α : Type*} [SMul α R]
  body: Quotient.map' (a • ·) (h a) x

中文:
定义 smulAux
  签名: [加法 R] [乘法 R] {α : 类型} [标量乘法 α R]
  定义体: Quotient.map' (a • ·) (h a) x

Depends on / 依赖: Quotient, Quotient.map
-/
def smulAux [Add R] [Mul R] {α : Type*} [SMul α R]
    (c : RingCon R) (h : forall (a : α) (x y : R), c x y -> c (a • x) (a • y))
    (a : α) (x : c.Quotient) : c.Quotient :=
  Quotient.map' (a • ·) (h a) x

section NegSubZSMul

variable [AddGroup R] [Mul R] (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg c.Quotient
  body: inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]

中文:
实例 :
  签名: 取负 c.商
  定义体: inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toAddCon.Quotient, toAddCon
-/
instance : Neg c.Quotient := inferInstanceAs (Neg c.toAddCon.Quotient)

@[simp, norm_cast]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (x : R)
  statement: (↑(-x) : c.Quotient) = -x
  proof: rfl

中文:
定理 coe_neg
  条件: (x : R)
  结论: (↑(-x) : c.商) = -x
  证明: rfl
-/
theorem coe_neg (x : R) : (↑(-x) : c.Quotient) = -x :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub c.Quotient
  body: inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]

中文:
实例 :
  签名: 减法 c.商
  定义体: inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toAddCon.Quotient, toAddCon
-/
instance : Sub c.Quotient := inferInstanceAs (Sub c.toAddCon.Quotient)

@[simp, norm_cast]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (x y : R)
  statement: (↑(x - y) : c.Quotient) = x - y
  proof: rfl

中文:
定理 coe_sub
  条件: (x y : R)
  结论: (↑(x - y) : c.商) = x - y
  证明: rfl
-/
theorem coe_sub (x y : R) : (↑(x - y) : c.Quotient) = x - y :=
  rfl

/--
Instance `hasZSMul` / 实例 `hasZSMul`

English:
instance hasZSMul
  signature: : SMul Int c.Quotient
  body: ⟨c.smulAux (RingCon.zsmul c)⟩

@[simp, norm_cast]

中文:
实例 hasZSMul
  签名: : 标量乘法 整数 c.商
  定义体: ⟨c.smulAux (RingCon.zsmul c)⟩

@[simp, norm_cast]

Depends on / 依赖: RingCon, RingCon.zsmul, c.smulAux, smulAux
-/
instance hasZSMul : SMul Int c.Quotient := ⟨c.smulAux (RingCon.zsmul c)⟩

@[simp, norm_cast]
/--
theorem `coe_zsmul` / 定理 `coe_zsmul`

English:
theorem coe_zsmul
  given: (z : Int) (x : R)
  statement: (↑(z • x) : c.Quotient) = z • (x : c.Quotient)
  proof: rfl

中文:
定理 coe_zsmul
  条件: (z : 整数) (x : R)
  结论: (↑(z • x) : c.商) = z • (x : c.商)
  证明: rfl
-/
theorem coe_zsmul (z : Int) (x : R) : (↑(z • x) : c.Quotient) = z • (x : c.Quotient) :=
  rfl

end NegSubZSMul

section NSMul

variable [AddMonoid R] [Mul R] (c : RingCon R)

/--
Instance `hasNSMul` / 实例 `hasNSMul`

English:
instance hasNSMul
  signature: : SMul Nat c.Quotient
  body: ⟨c.smulAux (RingCon.nsmul c)⟩

@[simp, norm_cast]

中文:
实例 hasNSMul
  签名: : 标量乘法 自然数 c.商
  定义体: ⟨c.smulAux (RingCon.nsmul c)⟩

@[simp, norm_cast]

Depends on / 依赖: RingCon, RingCon.nsmul, c.smulAux, smulAux
-/
instance hasNSMul : SMul Nat c.Quotient := ⟨c.smulAux (RingCon.nsmul c)⟩

@[simp, norm_cast]
/--
theorem `coe_nsmul` / 定理 `coe_nsmul`

English:
theorem coe_nsmul
  given: (n : Nat) (x : R)
  statement: (↑(n • x) : c.Quotient) = n • (x : c.Quotient)
  proof: rfl

中文:
定理 coe_nsmul
  条件: (n : 自然数) (x : R)
  结论: (↑(n • x) : c.商) = n • (x : c.商)
  证明: rfl
-/
theorem coe_nsmul (n : Nat) (x : R) : (↑(n • x) : c.Quotient) = n • (x : c.Quotient) :=
  rfl

end NSMul

section Pow

variable [Add R] [Monoid R] (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow c.Quotient Nat
  body: inferInstanceAs (Pow c.toCon.Quotient Nat)

@[simp, norm_cast]

中文:
实例 :
  签名: 幂 c.商 自然数
  定义体: inferInstanceAs (Pow c.toCon.Quotient Nat)

@[simp, norm_cast]

Depends on / 依赖: Quotient, c.toCon.Quotient
-/
instance : Pow c.Quotient Nat := inferInstanceAs (Pow c.toCon.Quotient Nat)

@[simp, norm_cast]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: (x : R) (n : Nat)
  statement: (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n
  proof: rfl

中文:
定理 coe_pow
  条件: (x : R) (n : 自然数)
  结论: (↑(x ^ n) : c.商) = (x : c.商) ^ n
  证明: rfl
-/
theorem coe_pow (x : R) (n : Nat) : (↑(x ^ n) : c.Quotient) = (x : c.Quotient) ^ n :=
  rfl

end Pow

section NatCast

variable [AddMonoidWithOne R] [Mul R] (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast c.Quotient
  body: ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 自然数嵌入 c.商
  定义体: ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]
-/
instance : NatCast c.Quotient :=
  ⟨fun n => ↑(n : R)⟩

@[simp, norm_cast]
/--
theorem `coe_natCast` / 定理 `coe_natCast`

English:
theorem coe_natCast
  given: (n : Nat)
  statement: (↑(n : R) : c.Quotient) = n
  proof: rfl

中文:
定理 coe_natCast
  条件: (n : 自然数)
  结论: (↑(n : R) : c.商) = n
  证明: rfl
-/
theorem coe_natCast (n : Nat) : (↑(n : R) : c.Quotient) = n :=
  rfl

end NatCast

section IntCast

variable [AddGroupWithOne R] [Mul R] (c : RingCon R)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast c.Quotient
  body: ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]

中文:
实例 :
  签名: 整数嵌入 c.商
  定义体: ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]
-/
instance : IntCast c.Quotient :=
  ⟨fun z => ↑(z : R)⟩

@[simp, norm_cast]
/--
theorem `coe_intCast` / 定理 `coe_intCast`

English:
theorem coe_intCast
  given: (n : Nat)
  statement: (↑(n : R) : c.Quotient) = n
  proof: rfl

中文:
定理 coe_intCast
  条件: (n : 自然数)
  结论: (↑(n : R) : c.商) = n
  证明: rfl
-/
theorem coe_intCast (n : Nat) : (↑(n : R) : c.Quotient) = n :=
  rfl

end IntCast

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: R] [Add R] [Mul R] (c
  body: ⟨↑(default : R)⟩

中文:
实例 [可居
  签名: R] [加法 R] [乘法 R] (c
  定义体: ⟨↑(default : R)⟩
-/
instance [Inhabited R] [Add R] [Mul R] (c : RingCon R) : Inhabited c.Quotient :=
  ⟨↑(default : R)⟩

end Data

/-! ### Algebraic structure

The operations above on the quotient by `c : RingCon R` preserve the algebraic structure of `R`.
-/


section Algebraic

section Add

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: R] [Mul R] (c
  body: inferInstanceAs AddZeroClass c.toAddCon.Quotient

中文:
实例 [加法零类
  签名: R] [乘法 R] (c
  定义体: inferInstanceAs AddZeroClass c.toAddCon.Quotient

Depends on / 依赖: AddZeroClass, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [AddZeroClass R] [Mul R] (c : RingCon R) : AddZeroClass c.Quotient :=
inferInstanceAs AddZeroClass c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddSemigroup
  signature: R] [Mul R] (c
  body: inferInstanceAs AddSemigroup c.toAddCon.Quotient

中文:
实例 [加法半群
  签名: R] [乘法 R] (c
  定义体: inferInstanceAs AddSemigroup c.toAddCon.Quotient

Depends on / 依赖: AddSemigroup, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [AddSemigroup R] [Mul R] (c : RingCon R) : AddSemigroup c.Quotient :=
inferInstanceAs AddSemigroup c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMagma
  signature: R] [Mul R] (c
  body: inferInstanceAs AddCommMagma c.toAddCon.Quotient

中文:
实例 [加法交换原群
  签名: R] [乘法 R] (c
  定义体: inferInstanceAs AddCommMagma c.toAddCon.Quotient

Depends on / 依赖: AddCommMagma, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [AddCommMagma R] [Mul R] (c : RingCon R) : AddCommMagma c.Quotient :=
inferInstanceAs AddCommMagma c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommSemigroup
  signature: R] [Mul R] (c
  body: inferInstanceAs AddCommSemigroup c.toAddCon.Quotient

中文:
实例 [加法交换半群
  签名: R] [乘法 R] (c
  定义体: inferInstanceAs AddCommSemigroup c.toAddCon.Quotient

Depends on / 依赖: AddCommSemigroup, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [AddCommSemigroup R] [Mul R] (c : RingCon R) : AddCommSemigroup c.Quotient :=
inferInstanceAs AddCommSemigroup c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddMonoid
  signature: R] [Mul R] (c
  body: n • x
__ : AddMonoid c.Quotient := inferInstanceAs AddMonoid c.toAddCon.Quotient

中文:
实例 [加法幺半群
  签名: R] [乘法 R] (c
  定义体: n • x
__ : AddMonoid c.Quotient := inferInstanceAs AddMonoid c.toAddCon.Quotient
-/
instance [AddMonoid R] [Mul R] (c : RingCon R) : AddMonoid c.Quotient where
  nsmul n x := n • x
__ : AddMonoid c.Quotient := inferInstanceAs AddMonoid c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommMonoid
  signature: R] [Mul R] (c
  body: inferInstanceAs AddCommMonoid c.toAddCon.Quotient

中文:
实例 [加法交换幺半群
  签名: R] [乘法 R] (c
  定义体: inferInstanceAs AddCommMonoid c.toAddCon.Quotient

Depends on / 依赖: AddCommMonoid, Quotient, bfamilyOfFamily, c.toAddCon.Quotient, enum_typein, toAddCon
-/
instance [AddCommMonoid R] [Mul R] (c : RingCon R) : AddCommMonoid c.Quotient :=
inferInstanceAs AddCommMonoid c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddGroup
  signature: R] [Mul R] (c
  body: n • x
__ : AddGroup c.Quotient := inferInstanceAs AddGroup c.toAddCon.Quotient

中文:
实例 [加法群
  签名: R] [乘法 R] (c
  定义体: n • x
__ : AddGroup c.Quotient := inferInstanceAs AddGroup c.toAddCon.Quotient
-/
instance [AddGroup R] [Mul R] (c : RingCon R) : AddGroup c.Quotient where
  zsmul n x := n • x
__ : AddGroup c.Quotient := inferInstanceAs AddGroup c.toAddCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddCommGroup
  signature: R] [Mul R] (c
  body: inferInstanceAs AddCommGroup c.toAddCon.Quotient

中文:
实例 [加法交换群
  签名: R] [乘法 R] (c
  定义体: inferInstanceAs AddCommGroup c.toAddCon.Quotient

Depends on / 依赖: AddCommGroup, Quotient, c.toAddCon.Quotient, familyOfBFamily, toAddCon, typein_enum
-/
instance [AddCommGroup R] [Mul R] (c : RingCon R) : AddCommGroup c.Quotient :=
inferInstanceAs AddCommGroup c.toAddCon.Quotient

end Add

section Mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [MulOneClass R] (c
  body: inferInstanceAs MulOneClass c.toCon.Quotient

中文:
实例 [加法
  签名: R] [MulOne类 R] (c
  定义体: inferInstanceAs MulOneClass c.toCon.Quotient

Depends on / 依赖: MulOneClass, Quotient, c.toCon.Quotient
-/
instance [Add R] [MulOneClass R] (c : RingCon R) : MulOneClass c.Quotient :=
inferInstanceAs MulOneClass c.toCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [Semigroup R] (c
  body: inferInstanceAs Semigroup c.toCon.Quotient

中文:
实例 [加法
  签名: R] [半群 R] (c
  定义体: inferInstanceAs Semigroup c.toCon.Quotient

Depends on / 依赖: Quotient, Semigroup, c.toCon.Quotient
-/
instance [Add R] [Semigroup R] (c : RingCon R) : Semigroup c.Quotient :=
inferInstanceAs Semigroup c.toCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [CommMagma R] (c
  body: inferInstanceAs CommMagma c.toCon.Quotient

中文:
实例 [加法
  签名: R] [交换原群 R] (c
  定义体: inferInstanceAs CommMagma c.toCon.Quotient

Depends on / 依赖: CommMagma, Quotient, c.toCon.Quotient
-/
instance [Add R] [CommMagma R] (c : RingCon R) : CommMagma c.Quotient :=
inferInstanceAs CommMagma c.toCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [CommSemigroup R] (c
  body: inferInstanceAs CommSemigroup c.toCon.Quotient

中文:
实例 [加法
  签名: R] [交换半群 R] (c
  定义体: inferInstanceAs CommSemigroup c.toCon.Quotient

Depends on / 依赖: CommSemigroup, Quotient, c.toCon.Quotient
-/
instance [Add R] [CommSemigroup R] (c : RingCon R) : CommSemigroup c.Quotient :=
inferInstanceAs CommSemigroup c.toCon.Quotient

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [Monoid R] (c
  body: fast_instance%
  { __ : Monoid c.toCon.Quotient := inferInstanceAs _
    -- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/inferInstanceAs.20creates.20non-reducible.20diamonds/near/603969174
    npow n x := x ^ n }

中文:
实例 [加法
  签名: R] [幺半群 R] (c
  定义体: fast_instance%
  { __ : Monoid c.toCon.Quotient := inferInstanceAs _
    -- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/inferInstanceAs.20creates.20non-reducible.20diamonds/near/603969174
    npow n x := x ^ n }

Depends on / 依赖: fast_instance
-/
instance [Add R] [Monoid R] (c : RingCon R) : Monoid c.Quotient := fast_instance%
  { __ : Monoid c.toCon.Quotient := inferInstanceAs _
    -- see https://leanprover.zulipchat.com/#narrow/channel/287929-mathlib4/topic/inferInstanceAs.20creates.20non-reducible.20diamonds/near/603969174
    npow n x := x ^ n }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Add
  signature: R] [CommMonoid R] (c
  body: inferInstanceAs CommMonoid c.toCon.Quotient

中文:
实例 [加法
  签名: R] [交换幺半群 R] (c
  定义体: inferInstanceAs CommMonoid c.toCon.Quotient

Depends on / 依赖: CommMonoid, Quotient, c.toCon.Quotient
-/
instance [Add R] [CommMonoid R] (c : RingCon R) : CommMonoid c.Quotient :=
inferInstanceAs CommMonoid c.toCon.Quotient

end Mul

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺非结合半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalNonAssocSemiring R] (c : RingCon R) :
    NonUnitalNonAssocSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocCommSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalNonAssocCommSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺非结合交换半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalNonAssocCommSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalNonAssocCommSemiring R] (c : RingCon R) :
    NonUnitalNonAssocCommSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocCommSemiring _ Quotient.mk''_surjective rfl
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonAssocSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [非结合半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonAssocSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonAssocSemiring R] (c : RingCon R) : NonAssocSemiring c.Quotient := fast_instance%
  Function.Surjective.nonAssocSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocCommSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonAssocCommSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [非结合交换半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonAssocCommSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonAssocCommSemiring R] (c : RingCon R) :
    NonAssocCommSemiring c.Quotient := fast_instance%
  Function.Surjective.nonAssocCommSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalSemiring R] (c : RingCon R) : NonUnitalSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalCommSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺交换半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalCommSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalCommSemiring R] (c : RingCon R) :
    NonUnitalCommSemiring c.Quotient := fast_instance%
  Function.Surjective.nonUnitalCommSemiring _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.semiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.semiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [Semiring R] (c : RingCon R) : Semiring c.Quotient := fast_instance%
  Function.Surjective.semiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommSemiring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.commSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

中文:
实例 [交换半环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.commSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [CommSemiring R] (c : RingCon R) : CommSemiring c.Quotient := fast_instance%
  Function.Surjective.commSemiring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺非结合环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalNonAssocRing R] (c : RingCon R) :
    NonUnitalNonAssocRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalNonAssocCommRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalNonAssocCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺非结合交换环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalNonAssocCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalNonAssocCommRing R] (c : RingCon R) :
    NonUnitalNonAssocCommRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalNonAssocCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonAssocRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

中文:
实例 [非结合环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonAssocRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonAssocRing R] (c : RingCon R) : NonAssocRing c.Quotient := fast_instance%
  Function.Surjective.nonAssocRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonAssocCommRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonAssocCommRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

中文:
实例 [非结合交换环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonAssocCommRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonAssocCommRing R] (c : RingCon R) : NonAssocCommRing c.Quotient := fast_instance%
  Function.Surjective.nonAssocCommRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalRing R] (c : RingCon R) : NonUnitalRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [NonUnitalCommRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.nonUnitalCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

中文:
实例 [非幺交换环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.nonUnitalCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [NonUnitalCommRing R] (c : RingCon R) : NonUnitalCommRing c.Quotient := fast_instance%
  Function.Surjective.nonUnitalCommRing _ Quotient.mk''_surjective rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Ring
  signature: R] (c
  body: fast_instance%
  Function.Surjective.ring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

中文:
实例 [环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.ring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [Ring R] (c : RingCon R) : Ring c.Quotient := fast_instance%
  Function.Surjective.ring _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [CommRing
  signature: R] (c
  body: fast_instance%
  Function.Surjective.commRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

中文:
实例 [交换环
  签名: R] (c
  定义体: fast_instance%
  Function.Surjective.commRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

Depends on / 依赖: fast_instance
-/
instance [CommRing R] (c : RingCon R) : CommRing c.Quotient := fast_instance%
  Function.Surjective.commRing _ Quotient.mk''_surjective rfl rfl (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ => rfl) fun _ => rfl

end Algebraic

variable [NonAssocSemiring R] (c : RingCon R)

/--
Definition of `mk'` / `mk'` 的定义

English:
definition mk'
  signature: : R ->+* c.Quotient where
  body: toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

中文:
定义 mk'
  签名: : R ->+* c.商 where
  定义体: toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

Depends on / 依赖: toQuotient
-/
def mk' : R ->+* c.Quotient where
  toFun := toQuotient
  map_zero' := rfl
  map_one' := rfl
  map_add' _ _ := rfl
  map_mul' _ _ := rfl

/--
theorem `mk'_surjective` / 定理 `mk'_surjective`

English:
theorem mk'_surjective
  statement: Function.Surjective c.mk'
  proof: Quotient.mk''_surjective

@[simp]

中文:
定理 mk'_surjective
  结论: 函数.满射 c.mk'
  证明: Quotient.mk''_surjective

@[simp]
-/
theorem mk'_surjective : Function.Surjective c.mk' :=
  Quotient.mk''_surjective

@[simp]
/--
theorem `coe_mk'` / 定理 `coe_mk'`

English:
theorem coe_mk'
  statement: (c.mk' : R -> c.Quotient) = ((↑) : R -> c.Quotient)
  proof: rfl

中文:
定理 coe_mk'
  结论: (c.mk' : R -> c.商) = ((↑) : R -> c.商)
  证明: rfl
-/
theorem coe_mk' : (c.mk' : R -> c.Quotient) = ((↑) : R -> c.Quotient) :=
  rfl

end Quotient

end RingCon
