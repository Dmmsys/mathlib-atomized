/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.CauSeq.Basic
public import Mathlib.Algebra.Ring.Action.Rat
public import Mathlib.Tactic.FastInstance

/-!
# Cauchy completion

This file generalizes the Cauchy completion of `(ℚ, abs)` to the completion of a ring
with absolute value.
-/

@[expose] public section


namespace CauSeq.Completion

open CauSeq

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Ring β] (abv : β -> α) [IsAbsoluteValue abv]

-- TODO: rename this to `CauSeq.Completion` instead of `CauSeq.Completion.Cauchy`.
/--
Definition of `Cauchy` / `Cauchy` 的定义

English:
definition Cauchy
  body: @Quotient (CauSeq _ abv) CauSeq.equiv

中文:
定义 Cauchy
  定义体: @Quotient (CauSeq _ abv) CauSeq.equiv

Depends on / 依赖: CauSeq, CauSeq.equiv, Quotient
-/
def Cauchy :=
  @Quotient (CauSeq _ abv) CauSeq.equiv

variable {abv}

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : CauSeq _ abv -> Cauchy abv
  body: Quotient.mk''

@[simp]

中文:
定义 mk
  签名: : CauSeq _ abv -> Cauchy abv
  定义体: Quotient.mk''

@[simp]

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk : CauSeq _ abv -> Cauchy abv :=
  Quotient.mk''

@[simp]
/--
theorem `mk_eq_mk` / 定理 `mk_eq_mk`

English:
theorem mk_eq_mk
  given: (f : CauSeq _ abv)
  statement: @Eq (Cauchy abv) ⟦f⟧ (mk f)
  proof: rfl

中文:
定理 mk_eq_mk
  条件: (f : CauSeq _ abv)
  结论: @相等 (Cauchy abv) ⟦f⟧ (mk f)
  证明: rfl
-/
theorem mk_eq_mk (f : CauSeq _ abv) : @Eq (Cauchy abv) ⟦f⟧ (mk f) :=
  rfl

/--
theorem `mk_eq` / 定理 `mk_eq`

English:
theorem mk_eq
  given: {f g : CauSeq _ abv}
  statement: mk f = mk g ↔ LimZero (f - g)
  proof: Quotient.eq

中文:
定理 mk_eq
  条件: {f g : CauSeq _ abv}
  结论: mk f = mk g ↔ LimZero (f - g)
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem mk_eq {f g : CauSeq _ abv} : mk f = mk g ↔ LimZero (f - g) :=
  Quotient.eq

/--
Definition of `ofRat` / `ofRat` 的定义

English:
definition ofRat
  signature: (x : β)
  body: mk (const abv x)

中文:
定义 ofRat
  签名: (x : β)
  定义体: mk (const abv x)
-/
def ofRat (x : β) : Cauchy abv :=
  mk (const abv x)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Cauchy abv)
  body: ⟨ofRat 0⟩

中文:
实例 :
  签名: 零 (Cauchy abv)
  定义体: ⟨ofRat 0⟩
-/
instance : Zero (Cauchy abv) :=
  ⟨ofRat 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Cauchy abv)
  body: ⟨ofRat 1⟩

中文:
实例 :
  签名: 幺 (Cauchy abv)
  定义体: ⟨ofRat 1⟩
-/
instance : One (Cauchy abv) :=
  ⟨ofRat 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (Cauchy abv)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (Cauchy abv)
  定义体: ⟨0⟩
-/
instance : Inhabited (Cauchy abv) :=
  ⟨0⟩

/--
theorem `ofRat_zero` / 定理 `ofRat_zero`

English:
theorem ofRat_zero
  statement: (ofRat 0 : Cauchy abv) = 0
  proof: rfl

中文:
定理 ofRat_zero
  结论: (ofRat 0 : Cauchy abv) = 0
  证明: rfl
-/
theorem ofRat_zero : (ofRat 0 : Cauchy abv) = 0 :=
  rfl

/--
theorem `ofRat_one` / 定理 `ofRat_one`

English:
theorem ofRat_one
  statement: (ofRat 1 : Cauchy abv) = 1
  proof: rfl

@[simp]

中文:
定理 ofRat_one
  结论: (ofRat 1 : Cauchy abv) = 1
  证明: rfl

@[simp]
-/
theorem ofRat_one : (ofRat 1 : Cauchy abv) = 1 :=
  rfl

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: {f : CauSeq _ abv}
  statement: mk f = 0 ↔ LimZero f
  proof: by
  have : mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this

中文:
定理 mk_eq_zero
  条件: {f : CauSeq _ abv}
  结论: mk f = 0 ↔ LimZero f
  证明: by
  have : mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this

Depends on / 依赖: LimZero, Quotient, Quotient.eq, sub_zero
-/
theorem mk_eq_zero {f : CauSeq _ abv} : mk f = 0 ↔ LimZero f := by
  have : mk f = 0 ↔ LimZero (f - 0) := Quotient.eq
  rwa [sub_zero] at this

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Cauchy abv)
  body: ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]

中文:
实例 :
  签名: 加法 (Cauchy abv)
  定义体: ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.map, add_equiv_add
-/
instance : Add (Cauchy abv) :=
  ⟨(Quotient.map₂ (· + ·)) fun _ _ hf _ _ hg => add_equiv_add hf hg⟩

@[simp]
/--
theorem `mk_add` / 定理 `mk_add`

English:
theorem mk_add
  given: (f g : CauSeq β abv)
  statement: mk f + mk g = mk (f + g)
  proof: rfl

中文:
定理 mk_add
  条件: (f g : CauSeq β abv)
  结论: mk f + mk g = mk (f + g)
  证明: rfl
-/
theorem mk_add (f g : CauSeq β abv) : mk f + mk g = mk (f + g) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (Cauchy abv)
  body: ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]

中文:
实例 :
  签名: 取负 (Cauchy abv)
  定义体: ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]

Depends on / 依赖: Neg.neg, Quotient, Quotient.map, neg_equiv_neg
-/
instance : Neg (Cauchy abv) :=
  ⟨(Quotient.map Neg.neg) fun _ _ hf => neg_equiv_neg hf⟩

@[simp]
/--
theorem `mk_neg` / 定理 `mk_neg`

English:
theorem mk_neg
  given: (f : CauSeq β abv)
  statement: -mk f = mk (-f)
  proof: rfl

中文:
定理 mk_neg
  条件: (f : CauSeq β abv)
  结论: -mk f = mk (-f)
  证明: rfl
-/
theorem mk_neg (f : CauSeq β abv) : -mk f = mk (-f) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Cauchy abv)
  body: ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[simp]

中文:
实例 :
  签名: 乘法 (Cauchy abv)
  定义体: ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.map, mul_equiv_mul
-/
instance : Mul (Cauchy abv) :=
  ⟨(Quotient.map₂ (· * ·)) fun _ _ hf _ _ hg => mul_equiv_mul hf hg⟩

@[simp]
/--
theorem `mk_mul` / 定理 `mk_mul`

English:
theorem mk_mul
  given: (f g : CauSeq β abv)
  statement: mk f * mk g = mk (f * g)
  proof: rfl

中文:
定理 mk_mul
  条件: (f g : CauSeq β abv)
  结论: mk f * mk g = mk (f * g)
  证明: rfl
-/
theorem mk_mul (f g : CauSeq β abv) : mk f * mk g = mk (f * g) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (Cauchy abv)
  body: ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[simp]

中文:
实例 :
  签名: 减法 (Cauchy abv)
  定义体: ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.map, Sub.sub, sub_equiv_sub
-/
instance : Sub (Cauchy abv) :=
  ⟨(Quotient.map₂ Sub.sub) fun _ _ hf _ _ hg => sub_equiv_sub hf hg⟩

@[simp]
/--
theorem `mk_sub` / 定理 `mk_sub`

English:
theorem mk_sub
  given: (f g : CauSeq β abv)
  statement: mk f - mk g = mk (f - g)
  proof: rfl

中文:
定理 mk_sub
  条件: (f g : CauSeq β abv)
  结论: mk f - mk g = mk (f - g)
  证明: rfl
-/
theorem mk_sub (f g : CauSeq β abv) : mk f - mk g = mk (f - g) :=
  rfl

instance {γ : Type*} [SMul γ β] [IsScalarTower γ β β] : SMul γ (Cauchy abv) :=
  ⟨fun c => (Quotient.map (c • ·)) fun _ _ hf => smul_equiv_smul _ hf⟩

@[simp]
/--
theorem `mk_smul` / 定理 `mk_smul`

English:
theorem mk_smul
  given: {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv)
  proof: rfl

中文:
定理 mk_smul
  条件: {γ : 类型} [标量乘法 γ β] [标量塔 γ β β] (c : γ) (f : CauSeq β abv)
  证明: rfl
-/
theorem mk_smul {γ : Type*} [SMul γ β] [IsScalarTower γ β β] (c : γ) (f : CauSeq β abv) :
    c • mk f = mk (c • f) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Pow (Cauchy abv) Nat
  body: ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]

中文:
实例 :
  签名: 幂 (Cauchy abv) 自然数
  定义体: ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.map, pow_equiv_pow
-/
instance : Pow (Cauchy abv) Nat :=
  ⟨fun x n => Quotient.map (· ^ n) (fun _ _ hf => pow_equiv_pow hf _) x⟩

@[simp]
/--
theorem `mk_pow` / 定理 `mk_pow`

English:
theorem mk_pow
  given: (n : Nat) (f : CauSeq β abv)
  statement: mk f ^ n = mk (f ^ n)
  proof: rfl

中文:
定理 mk_pow
  条件: (n : 自然数) (f : CauSeq β abv)
  结论: mk f ^ n = mk (f ^ n)
  证明: rfl
-/
theorem mk_pow (n : Nat) (f : CauSeq β abv) : mk f ^ n = mk (f ^ n) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast (Cauchy abv)
  body: ⟨fun n => mk n⟩

中文:
实例 :
  签名: 自然数嵌入 (Cauchy abv)
  定义体: ⟨fun n => mk n⟩
-/
instance : NatCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IntCast (Cauchy abv)
  body: ⟨fun n => mk n⟩

@[simp]

中文:
实例 :
  签名: 整数嵌入 (Cauchy abv)
  定义体: ⟨fun n => mk n⟩

@[simp]
-/
instance : IntCast (Cauchy abv) :=
  ⟨fun n => mk n⟩

@[simp]
/--
theorem `ofRat_natCast` / 定理 `ofRat_natCast`

English:
theorem ofRat_natCast
  given: (n : Nat)
  statement: (ofRat n : Cauchy abv) = n
  proof: rfl

@[simp]

中文:
定理 ofRat_natCast
  条件: (n : 自然数)
  结论: (ofRat n : Cauchy abv) = n
  证明: rfl

@[simp]
-/
theorem ofRat_natCast (n : Nat) : (ofRat n : Cauchy abv) = n :=
  rfl

@[simp]
/--
theorem `ofRat_intCast` / 定理 `ofRat_intCast`

English:
theorem ofRat_intCast
  given: (z : Int)
  statement: (ofRat z : Cauchy abv) = z
  proof: rfl

中文:
定理 ofRat_intCast
  条件: (z : 整数)
  结论: (ofRat z : Cauchy abv) = z
  证明: rfl
-/
theorem ofRat_intCast (z : Int) : (ofRat z : Cauchy abv) = z :=
  rfl

/--
theorem `ofRat_add` / 定理 `ofRat_add`

English:
theorem ofRat_add
  given: (x y : β)
  proof: congr_arg mk (const_add _ _)

中文:
定理 ofRat_add
  条件: (x y : β)
  证明: congr_arg mk (const_add _ _)

Depends on / 依赖: congr_arg, const_add
-/
theorem ofRat_add (x y : β) :
    ofRat (x + y) = (ofRat x + ofRat y : Cauchy abv) :=
  congr_arg mk (const_add _ _)

/--
theorem `ofRat_neg` / 定理 `ofRat_neg`

English:
theorem ofRat_neg
  given: (x : β)
  statement: ofRat (-x) = (-ofRat x : Cauchy abv)
  proof: congr_arg mk (const_neg _)

中文:
定理 ofRat_neg
  条件: (x : β)
  结论: ofRat (-x) = (-ofRat x : Cauchy abv)
  证明: congr_arg mk (const_neg _)

Depends on / 依赖: congr_arg, const_neg
-/
theorem ofRat_neg (x : β) : ofRat (-x) = (-ofRat x : Cauchy abv) :=
  congr_arg mk (const_neg _)

/--
theorem `ofRat_mul` / 定理 `ofRat_mul`

English:
theorem ofRat_mul
  given: (x y : β)
  proof: congr_arg mk (const_mul _ _)

中文:
定理 ofRat_mul
  条件: (x y : β)
  证明: congr_arg mk (const_mul _ _)

Depends on / 依赖: congr_arg, const_mul
-/
theorem ofRat_mul (x y : β) :
    ofRat (x * y) = (ofRat x * ofRat y : Cauchy abv) :=
  congr_arg mk (const_mul _ _)

/--
theorem `ofRat_injective` / 定理 `ofRat_injective`

English:
theorem ofRat_injective
  statement: Function.Injective (ofRat : β -> Cauchy abv)
  proof: fun x y h => by
  simpa [ofRat, mk_eq, ← const_sub, const_limZero, sub_eq_zero] using h

中文:
定理 ofRat_injective
  结论: 函数.单射 (ofRat : β -> Cauchy abv)
  证明: fun x y h => by
  simpa [ofRat, mk_eq, ← const_sub, const_limZero, sub_eq_zero] using h

Depends on / 依赖: const_limZero, const_sub, mk_eq, sub_eq_zero
-/
theorem ofRat_injective : Function.Injective (ofRat : β -> Cauchy abv) := fun x y h => by
  simpa [ofRat, mk_eq, ← const_sub, const_limZero, sub_eq_zero] using h

/--
Instance `Cauchy.ring` / 实例 `Cauchy.ring`

English:
instance Cauchy.ring
  signature: : Ring (Cauchy abv)
  body: fast_instance%
  Function.Surjective.ring mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).sy

中文:
实例 Cauchy.ring
  签名: : 环 (Cauchy abv)
  定义体: fast_instance%
  Function.Surjective.ring mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).sy

Depends on / 依赖: fast_instance
-/
instance Cauchy.ring : Ring (Cauchy abv) := fast_instance%
  Function.Surjective.ring mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

/-- `CauSeq.Completion.ofRat` as a `RingHom` -/
@[simps]
/--
Definition of `ofRatRingHom` / `ofRatRingHom` 的定义

English:
definition ofRatRingHom
  signature: : β ->+* (Cauchy abv) where
  body: ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul

中文:
定义 ofRatRingHom
  签名: : β ->+* (Cauchy abv) where
  定义体: ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul
-/
def ofRatRingHom : β ->+* (Cauchy abv) where
  toFun := ofRat
  map_zero' := ofRat_zero
  map_one' := ofRat_one
  map_add' := ofRat_add
  map_mul' := ofRat_mul

/--
theorem `ofRat_sub` / 定理 `ofRat_sub`

English:
theorem ofRat_sub
  given: (x y : β)
  statement: ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv)
  proof: congr_arg mk (const_sub _ _)

中文:
定理 ofRat_sub
  条件: (x y : β)
  结论: ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv)
  证明: congr_arg mk (const_sub _ _)

Depends on / 依赖: congr_arg, const_sub
-/
theorem ofRat_sub (x y : β) : ofRat (x - y) = (ofRat x - ofRat y : Cauchy abv) :=
  congr_arg mk (const_sub _ _)

/--
Instance `Cauchy.instNonTrivial` / 实例 `Cauchy.instNonTrivial`

English:
instance Cauchy.instNonTrivial
  signature: [Nontrivial β]
  body: ofRat_injective.nontrivial

中文:
实例 Cauchy.instNonTrivial
  签名: [非平凡 β]
  定义体: ofRat_injective.nontrivial

Depends on / 依赖: nontrivial, ofRat_injective, ofRat_injective.nontrivial
-/
noncomputable instance Cauchy.instNonTrivial [Nontrivial β] : Nontrivial (Cauchy abv) :=
  ofRat_injective.nontrivial

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [CommRing β] {abv : β -> α} [IsAbsoluteValue abv]

/--
Instance `Cauchy.commRing` / 实例 `Cauchy.commRing`

English:
instance Cauchy.commRing
  signature: : CommRing (Cauchy abv)
  body: fast_instance%
  Function.Surjective.commRing mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _

中文:
实例 Cauchy.commRing
  签名: : 交换环 (Cauchy abv)
  定义体: fast_instance%
  Function.Surjective.commRing mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _

Depends on / 依赖: fast_instance
-/
instance Cauchy.commRing : CommRing (Cauchy abv) := fast_instance%
  Function.Surjective.commRing mk Quotient.mk'_surjective rfl rfl
    (fun _ _ => (mk_add _ _).symm) (fun _ _ => (mk_mul _ _).symm) (fun _ => (mk_neg _).symm)
    (fun _ _ => (mk_sub _ _).symm) (fun _ _ => (mk_smul _ _).symm) (fun _ _ => (mk_smul _ _).symm)
    (fun _ _ => (mk_pow _ _).symm) (fun _ => rfl) fun _ => rfl

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [DivisionRing β] {abv : β -> α} [IsAbsoluteValue abv]

/--
Instance `instNNRatCast` / 实例 `instNNRatCast`

English:
instance instNNRatCast
  signature: : NNRatCast (Cauchy abv) where nnratCast q
  body: ofRat q

中文:
实例 instNNRatCast
  签名: : 非负有理数嵌入 (Cauchy abv) where nnratCast q
  定义体: ofRat q
-/
instance instNNRatCast : NNRatCast (Cauchy abv) where nnratCast q := ofRat q
/--
Instance `instRatCast` / 实例 `instRatCast`

English:
instance instRatCast
  signature: : RatCast (Cauchy abv) where ratCast q
  body: ofRat q

中文:
实例 instRatCast
  签名: : 有理数嵌入 (Cauchy abv) where ratCast q
  定义体: ofRat q
-/
instance instRatCast : RatCast (Cauchy abv) where ratCast q := ofRat q

/--
lemma `ofRat_nnratCast` / 引理 `ofRat_nnratCast`

English:
lemma ofRat_nnratCast
  given: (q : Rat>=0)
  statement: ofRat (q : β) = (q : Cauchy abv)
  proof: rfl

中文:
引理 ofRat_nnratCast
  条件: (q : 有理数>=0)
  结论: ofRat (q : β) = (q : Cauchy abv)
  证明: rfl
-/
@[simp, norm_cast] lemma ofRat_nnratCast (q : Rat>=0) : ofRat (q : β) = (q : Cauchy abv) := rfl
/--
lemma `ofRat_ratCast` / 引理 `ofRat_ratCast`

English:
lemma ofRat_ratCast
  given: (q : Rat)
  statement: ofRat (q : β) = (q : Cauchy abv)
  proof: rfl

中文:
引理 ofRat_ratCast
  条件: (q : 有理数)
  结论: ofRat (q : β) = (q : Cauchy abv)
  证明: rfl
-/
@[simp, norm_cast] lemma ofRat_ratCast (q : Rat) : ofRat (q : β) = (q : Cauchy abv) := rfl

open scoped Classical in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inv (Cauchy abv)
  body: ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk

中文:
实例 :
  签名: 取逆 (Cauchy abv)
  定义体: ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk

Depends on / 依赖: LimZero, Quotient, Quotient.liftOn, dite_false, inv_mul_cancel, liftOn, limZero_congr, mk_eq, mul_inv_cancel, mul_one
-/
noncomputable instance : Inv (Cauchy abv) :=
  ⟨fun x =>
    (Quotient.liftOn x fun f => mk <| if h : LimZero f then 0 else inv f h) fun f g fg => by
      have := limZero_congr fg
      by_cases hf : LimZero f
      · simp [hf, this.1 hf]
      · have hg := mt this.2 hf
        simp only [hf, dite_false, hg]
        have If : mk (inv f hf) * mk f = 1 := mk_eq.2 (inv_mul_cancel hf)
        have Ig : mk (inv g hg) * mk g = 1 := mk_eq.2 (inv_mul_cancel hg)
        have Ig' : mk g * mk (inv g hg) = 1 := mk_eq.2 (mul_inv_cancel hg)
        rw [mk_eq.2 fg]; rw [← Ig] at If
        rw [← mul_one (mk (inv f hf))]; rw [← Ig']; rw [← mul_assoc]; rw [If]; rw [mul_assoc]; rw [Ig']; rw [mul_one]⟩

/--
theorem `inv_zero` / 定理 `inv_zero`

English:
theorem inv_zero
  statement: (0 : (Cauchy abv))⁻¹ = 0
  proof: congr_arg mk by rw [dif_pos] <;> [rfl; exact zero_limZero]

@[simp]

中文:
定理 inv_zero
  结论: (0 : (Cauchy abv))⁻¹ = 0
  证明: congr_arg mk by rw [dif_pos] <;> [rfl; exact zero_limZero]

@[simp]

Depends on / 依赖: congr_arg, dif_pos, zero_limZero
-/
theorem inv_zero : (0 : (Cauchy abv))⁻¹ = 0 :=
congr_arg mk by rw [dif_pos] <;> [rfl; exact zero_limZero]

@[simp]
/--
theorem `inv_mk` / 定理 `inv_mk`

English:
theorem inv_mk
  given: {f} (hf)
  statement: (mk (abv := abv) f)⁻¹ = mk (inv f hf)
  proof: congr_arg mk by rw [dif_neg]

中文:
定理 inv_mk
  条件: {f} (hf)
  结论: (mk (abv := abv) f)⁻¹ = mk (inv f hf)
  证明: congr_arg mk by rw [dif_neg]
-/
theorem inv_mk {f} (hf) : (mk (abv := abv) f)⁻¹ = mk (inv f hf) :=
congr_arg mk by rw [dif_neg]

/--
theorem `cau_seq_zero_ne_one` / 定理 `cau_seq_zero_ne_one`

English:
theorem cau_seq_zero_ne_one
  statement: ¬(0 : CauSeq _ abv) ≈ 1
  proof: fun h =>
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero (1 : CauSeq _ abv) := by simpa
one_ne_zero const_limZero.1 this

中文:
定理 cau_seq_zero_ne_one
  结论: ¬(0 : CauSeq _ abv) ≈ 1
  证明: fun h =>
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero (1 : CauSeq _ abv) := by simpa
one_ne_zero const_limZero.1 this
-/
theorem cau_seq_zero_ne_one : ¬(0 : CauSeq _ abv) ≈ 1 := fun h =>
  have : LimZero (1 - 0 : CauSeq _ abv) := Setoid.symm h
  have : LimZero (1 : CauSeq _ abv) := by simpa
one_ne_zero const_limZero.1 this

/--
theorem `zero_ne_one` / 定理 `zero_ne_one`

English:
theorem zero_ne_one
  statement: (0 : (Cauchy abv)) != 1
  proof: fun h => cau_seq_zero_ne_one mk_eq.1 h

中文:
定理 zero_ne_one
  结论: (0 : (Cauchy abv)) != 1
  证明: fun h => cau_seq_zero_ne_one mk_eq.1 h

Depends on / 依赖: cau_seq_zero_ne_one, mk_eq
-/
theorem zero_ne_one : (0 : (Cauchy abv)) != 1 := fun h => cau_seq_zero_ne_one mk_eq.1 h

/--
theorem `inv_mul_cancel` / 定理 `inv_mul_cancel`

English:
theorem inv_mul_cancel
  given: {x : (Cauchy abv)}
  statement: x != 0 -> x⁻¹ * x = 1
  proof: Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)

中文:
定理 inv_mul_cancel
  条件: {x : (Cauchy abv)}
  结论: x != 0 -> x⁻¹ * x = 1
  证明: Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)
-/
protected theorem inv_mul_cancel {x : (Cauchy abv)} : x != 0 -> x⁻¹ * x = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.inv_mul_cancel hf)

/--
theorem `mul_inv_cancel` / 定理 `mul_inv_cancel`

English:
theorem mul_inv_cancel
  given: {x : (Cauchy abv)}
  statement: x != 0 -> x * x⁻¹ = 1
  proof: Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)

中文:
定理 mul_inv_cancel
  条件: {x : (Cauchy abv)}
  结论: x != 0 -> x * x⁻¹ = 1
  证明: Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)
-/
protected theorem mul_inv_cancel {x : (Cauchy abv)} : x != 0 -> x * x⁻¹ = 1 :=
  Quotient.inductionOn x fun f hf => by
    simp only [mk_eq_mk, ne_eq, mk_eq_zero] at hf
    simp only [mk_eq_mk, hf, not_false_eq_true, inv_mk, mk_mul]
    exact Quotient.sound (CauSeq.mul_inv_cancel hf)

/--
theorem `ofRat_inv` / 定理 `ofRat_inv`

English:
theorem ofRat_inv
  given: (x : β)
  statement: ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv))
  proof: congr_arg mk by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]

中文:
定理 ofRat_inv
  条件: (x : β)
  结论: ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv))
  证明: congr_arg mk by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]

Depends on / 依赖: GroupWithZero, GroupWithZero.inv_zero, congr_arg, const_limZero, const_zero, inv_zero, split_ifs
-/
theorem ofRat_inv (x : β) : ofRat x⁻¹ = ((ofRat x)⁻¹ : (Cauchy abv)) :=
congr_arg mk by split_ifs with h <;>
    [simp only [const_limZero.1 h, GroupWithZero.inv_zero, const_zero]; rfl]

/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: : DivInvMonoid (Cauchy abv) where

中文:
实例 instDivInvMonoid
  签名: : 除逆幺半群 (Cauchy abv) where
-/
noncomputable instance instDivInvMonoid : DivInvMonoid (Cauchy abv) where

/--
lemma `ofRat_div` / 引理 `ofRat_div`

English:
lemma ofRat_div
  given: (x y : β)
  statement: ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv)
  proof: by
  simp only [div_eq_mul_inv, ofRat_inv, ofRat_mul]

中文:
引理 ofRat_div
  条件: (x y : β)
  结论: ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv)
  证明: by
  simp only [div_eq_mul_inv, ofRat_inv, ofRat_mul]

Depends on / 依赖: div_eq_mul_inv, ofRat_inv, ofRat_mul
-/
lemma ofRat_div (x y : β) : ofRat (x / y) = (ofRat x / ofRat y : Cauchy abv) := by
  simp only [div_eq_mul_inv, ofRat_inv, ofRat_mul]

/--
Instance `Cauchy.divisionRing` / 实例 `Cauchy.divisionRing`

English:
instance Cauchy.divisionRing
  signature: : DivisionRing (Cauchy abv) where
  body: inv_zero
  mul_inv_cancel _ := CauSeq.Completion.mul_inv_cancel
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by simp_rw [← ofRat_nnratCast, NNRat.cast_def, ofRat_div, ofRat_natCast]
  ratCast_def q := by rw [← ofRat_ratCast, Rat.cast_def, ofRat_div, ofRat_natCast, ofRat_intCast]
nnqs

中文:
实例 Cauchy.divisionRing
  签名: : 除环 (Cauchy abv) where
  定义体: inv_zero
  mul_inv_cancel _ := CauSeq.Completion.mul_inv_cancel
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by simp_rw [← ofRat_nnratCast, NNRat.cast_def, ofRat_div, ofRat_natCast]
  ratCast_def q := by rw [← ofRat_ratCast, Rat.cast_def, ofRat_div, ofRat_natCast, ofRat_intCast]
nnqs

Depends on / 依赖: inv_zero
-/
noncomputable instance Cauchy.divisionRing : DivisionRing (Cauchy abv) where
  inv_zero := inv_zero
  mul_inv_cancel _ := CauSeq.Completion.mul_inv_cancel
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  nnratCast_def q := by simp_rw [← ofRat_nnratCast, NNRat.cast_def, ofRat_div, ofRat_natCast]
  ratCast_def q := by rw [← ofRat_ratCast, Rat.cast_def, ofRat_div, ofRat_natCast, ofRat_intCast]
nnqsmul_def _ x := Quotient.inductionOn x fun _ => congr_arg mk ext fun _ => NNRat.smul_def _ _
qsmul_def _ x := Quotient.inductionOn x fun _ => congr_arg mk ext fun _ => Rat.smul_def _ _

/-- Show the first 10 items of a representative of this equivalence class of Cauchy sequences.

The representative chosen is the one passed in the VM to `Quot.mk`, so two Cauchy sequences
converging to the same number may be printed differently.
-/
unsafe instance [Repr β] : Repr (Cauchy abv) where
  reprPrec r _ :=
    let N := 10
    let seq := r.unquot
    "(sorry /- " ++ Std.Format.joinSep ((List.range N).map <| repr ∘ seq) ", " ++ ", ... -/)"

end

section

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]
variable {β : Type*} [Field β] {abv : β -> α} [IsAbsoluteValue abv]

/--
Instance `Cauchy.field` / 实例 `Cauchy.field`

English:
instance Cauchy.field
  signature: : Field (Cauchy abv)
  body: { Cauchy.divisionRing, Cauchy.commRing with }

中文:
实例 Cauchy.field
  签名: : 域 (Cauchy abv)
  定义体: { Cauchy.divisionRing, Cauchy.commRing with }

Depends on / 依赖: Cauchy, Cauchy.commRing, Cauchy.divisionRing, commRing, divisionRing
-/
noncomputable instance Cauchy.field : Field (Cauchy abv) :=
  { Cauchy.divisionRing, Cauchy.commRing with }

end

end CauSeq.Completion

variable {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

namespace CauSeq

section

variable (β : Type*) [Ring β] (abv : β -> α) [IsAbsoluteValue abv]

/--
Definition of `IsComplete` / `IsComplete` 的定义

English:
class IsComplete
  parameters: : Prop where
  axioms and operations (1):
    - isComplete : forall s : CauSeq β abv, exists b : β, s ≈ const abv b

中文:
类 是完备
  参数: : 命题 where
  公理与运算 (1 个):
    - isComplete : 对任意 s : CauSeq β abv, 存在 b : β, s ≈ const abv b
-/
class IsComplete : Prop where
  /-- Every Cauchy sequence has a limit. -/
  isComplete : forall s : CauSeq β abv, exists b : β, s ≈ const abv b

end

section

variable {β : Type*} [Ring β] {abv : β -> α} [IsAbsoluteValue abv]
variable [IsComplete β abv]

/--
theorem `complete` / 定理 `complete`

English:
theorem complete
  statement: forall s : CauSeq β abv, exists b : β, s ≈ const abv b
  proof: IsComplete.isComplete

中文:
定理 complete
  结论: 对任意 s : CauSeq β abv, 存在 b : β, s ≈ const abv b
  证明: IsComplete.isComplete

Depends on / 依赖: IsComplete, IsComplete.isComplete, isComplete
-/
theorem complete : forall s : CauSeq β abv, exists b : β, s ≈ const abv b :=
  IsComplete.isComplete

/--
Definition of `lim` / `lim` 的定义

English:
definition lim
  signature: (s : CauSeq β abv)
  body: Classical.choose (complete s)

中文:
定义 lim
  签名: (s : CauSeq β abv)
  定义体: Classical.choose (complete s)

Depends on / 依赖: Classical, Classical.choose, complete
-/
noncomputable def lim (s : CauSeq β abv) : β :=
  Classical.choose (complete s)

/--
theorem `equiv_lim` / 定理 `equiv_lim`

English:
theorem equiv_lim
  given: (s : CauSeq β abv)
  statement: s ≈ const abv (lim s)
  proof: Classical.choose_spec (complete s)

中文:
定理 equiv_lim
  条件: (s : CauSeq β abv)
  结论: s ≈ const abv (lim s)
  证明: Classical.choose_spec (complete s)

Depends on / 依赖: Classical, Classical.choose_spec, choose_spec, complete
-/
theorem equiv_lim (s : CauSeq β abv) : s ≈ const abv (lim s) :=
  Classical.choose_spec (complete s)

/--
theorem `eq_lim_of_const_equiv` / 定理 `eq_lim_of_const_equiv`

English:
theorem eq_lim_of_const_equiv
  given: {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f)
  statement: x = lim f
  proof: const_equiv.mp Setoid.trans h equiv_lim f

中文:
定理 eq_lim_of_const_equiv
  条件: {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f)
  结论: x = lim f
  证明: const_equiv.mp Setoid.trans h equiv_lim f

Depends on / 依赖: Setoid, Setoid.trans, const_equiv, const_equiv.mp, equiv_lim
-/
theorem eq_lim_of_const_equiv {f : CauSeq β abv} {x : β} (h : CauSeq.const abv x ≈ f) : x = lim f :=
const_equiv.mp Setoid.trans h equiv_lim f

/--
theorem `lim_eq_of_equiv_const` / 定理 `lim_eq_of_equiv_const`

English:
theorem lim_eq_of_equiv_const
  given: {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x)
  statement: lim f = x
  proof: (eq_lim_of_const_equiv <| Setoid.symm h).symm

中文:
定理 lim_eq_of_equiv_const
  条件: {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x)
  结论: lim f = x
  证明: (eq_lim_of_const_equiv <| Setoid.symm h).symm

Depends on / 依赖: Setoid, Setoid.symm, eq_lim_of_const_equiv
-/
theorem lim_eq_of_equiv_const {f : CauSeq β abv} {x : β} (h : f ≈ CauSeq.const abv x) : lim f = x :=
  (eq_lim_of_const_equiv <| Setoid.symm h).symm

/--
theorem `lim_eq_lim_of_equiv` / 定理 `lim_eq_lim_of_equiv`

English:
theorem lim_eq_lim_of_equiv
  given: {f g : CauSeq β abv} (h : f ≈ g)
  statement: lim f = lim g
  proof: lim_eq_of_equiv_const Setoid.trans h equiv_lim g

@[simp]

中文:
定理 lim_eq_lim_of_equiv
  条件: {f g : CauSeq β abv} (h : f ≈ g)
  结论: lim f = lim g
  证明: lim_eq_of_equiv_const Setoid.trans h equiv_lim g

@[simp]

Depends on / 依赖: Setoid, Setoid.trans, equiv_lim, lim_eq_of_equiv_const
-/
theorem lim_eq_lim_of_equiv {f g : CauSeq β abv} (h : f ≈ g) : lim f = lim g :=
lim_eq_of_equiv_const Setoid.trans h equiv_lim g

@[simp]
/--
theorem `lim_const` / 定理 `lim_const`

English:
theorem lim_const
  given: (x : β)
  statement: lim (const abv x) = x
  proof: lim_eq_of_equiv_const Setoid.refl _

中文:
定理 lim_const
  条件: (x : β)
  结论: lim (const abv x) = x
  证明: lim_eq_of_equiv_const Setoid.refl _

Depends on / 依赖: Setoid, Setoid.refl, lim_eq_of_equiv_const
-/
theorem lim_const (x : β) : lim (const abv x) = x :=
lim_eq_of_equiv_const Setoid.refl _

/--
theorem `lim_add` / 定理 `lim_add`

English:
theorem lim_add
  given: (f g : CauSeq β abv)
  statement: lim f + lim g = lim (f + g)
  proof: eq_lim_of_const_equiv
    show LimZero (const abv (lim f + lim g) - (f + g)) by
      rw [const_add]; rw [add_sub_add_comm]
      exact add_limZero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))

中文:
定理 lim_add
  条件: (f g : CauSeq β abv)
  结论: lim f + lim g = lim (f + g)
  证明: eq_lim_of_const_equiv
    show LimZero (const abv (lim f + lim g) - (f + g)) by
      rw [const_add]; rw [add_sub_add_comm]
      exact add_limZero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))

Depends on / 依赖: LimZero, Setoid, Setoid.symm, add_limZero, add_sub_add_comm, const_add, eq_lim_of_const_equiv, equiv_lim
-/
theorem lim_add (f g : CauSeq β abv) : lim f + lim g = lim (f + g) :=
eq_lim_of_const_equiv
    show LimZero (const abv (lim f + lim g) - (f + g)) by
      rw [const_add]; rw [add_sub_add_comm]
      exact add_limZero (Setoid.symm (equiv_lim f)) (Setoid.symm (equiv_lim g))

/--
theorem `lim_mul_lim` / 定理 `lim_mul_lim`

English:
theorem lim_mul_lim
  given: (f g : CauSeq β abv)
  statement: lim f * lim g = lim (f * g)
  proof: eq_lim_of_const_equiv
    show LimZero (const abv (lim f * lim g) - f * g) by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              

中文:
定理 lim_mul_lim
  条件: (f g : CauSeq β abv)
  结论: lim f * lim g = lim (f * g)
  证明: eq_lim_of_const_equiv
    show LimZero (const abv (lim f * lim g) - f * g) by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              

Depends on / 依赖: LimZero, Setoid, Setoid.symm, Subtype, Subtype.ext, add_limZero, coe_add, eq_lim_of_const_equiv, equiv_lim, mul_limZero_left, mul_limZero_right, mul_sub, sub_mul
-/
theorem lim_mul_lim (f g : CauSeq β abv) : lim f * lim g = lim (f * g) :=
eq_lim_of_const_equiv
    show LimZero (const abv (lim f * lim g) - f * g) by
      have h :
        const abv (lim f * lim g) - f * g =
          (const abv (lim f) - f) * g + const abv (lim f) * (const abv (lim g) - g) := by
              apply Subtype.ext
              rw [coe_add]
              simp [sub_mul, mul_sub]
      rw [h]
      exact
        add_limZero (mul_limZero_left _ (Setoid.symm (equiv_lim _)))
          (mul_limZero_right _ (Setoid.symm (equiv_lim _)))

/--
theorem `lim_mul` / 定理 `lim_mul`

English:
theorem lim_mul
  given: (f : CauSeq β abv) (x : β)
  statement: lim f * x = lim (f * const abv x)
  proof: by
  rw [← lim_mul_lim]; rw [lim_const]

中文:
定理 lim_mul
  条件: (f : CauSeq β abv) (x : β)
  结论: lim f * x = lim (f * const abv x)
  证明: by
  rw [← lim_mul_lim]; rw [lim_const]

Depends on / 依赖: lim_const, lim_mul_lim
-/
theorem lim_mul (f : CauSeq β abv) (x : β) : lim f * x = lim (f * const abv x) := by
  rw [← lim_mul_lim]; rw [lim_const]

/--
theorem `lim_neg` / 定理 `lim_neg`

English:
theorem lim_neg
  given: (f : CauSeq β abv)
  statement: lim (-f) = -lim f
  proof: lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg]; rw [sub_neg_eq_add]; rw [add_comm]; rw [← sub_eq_add_neg]
      exact Setoid.symm (equiv_lim f))

中文:
定理 lim_neg
  条件: (f : CauSeq β abv)
  结论: lim (-f) = -lim f
  证明: lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg]; rw [sub_neg_eq_add]; rw [add_comm]; rw [← sub_eq_add_neg]
      exact Setoid.symm (equiv_lim f))

Depends on / 依赖: LimZero, Setoid, Setoid.symm, add_comm, const_neg, equiv_lim, lim_eq_of_equiv_const, sub_eq_add_neg, sub_neg_eq_add
-/
theorem lim_neg (f : CauSeq β abv) : lim (-f) = -lim f :=
  lim_eq_of_equiv_const
    (show LimZero (-f - const abv (-lim f)) by
      rw [const_neg]; rw [sub_neg_eq_add]; rw [add_comm]; rw [← sub_eq_add_neg]
      exact Setoid.symm (equiv_lim f))

/--
theorem `lim_sub` / 定理 `lim_sub`

English:
theorem lim_sub
  given: (f g : CauSeq β abv)
  statement: lim f - lim g = lim (f - g)
  proof: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add f (-g)]

中文:
定理 lim_sub
  条件: (f g : CauSeq β abv)
  结论: lim f - lim g = lim (f - g)
  证明: by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add f (-g)]

Depends on / 依赖: lim_add, lim_neg, sub_eq_add_neg
-/
theorem lim_sub (f g : CauSeq β abv) : lim f - lim g = lim (f - g) := by
  rw [sub_eq_add_neg]; rw [sub_eq_add_neg]; rw [← lim_neg]; rw [lim_add f (-g)]

/--
theorem `lim_eq_zero_iff` / 定理 `lim_eq_zero_iff`

English:
theorem lim_eq_zero_iff
  given: (f : CauSeq β abv)
  statement: lim f = 0 ↔ LimZero f
  proof: ⟨fun h => by
    have hf := equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp
    rw [h₁] at h
    exact lim_eq_of_equiv_const h⟩

中文:
定理 lim_eq_zero_iff
  条件: (f : CauSeq β abv)
  结论: lim f = 0 ↔ LimZero f
  证明: ⟨fun h => by
    have hf := equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp
    rw [h₁] at h
    exact lim_eq_of_equiv_const h⟩

Depends on / 依赖: const_limZero, const_limZero.mpr, equiv_lim, limZero_congr, lim_eq_of_equiv_const
-/
theorem lim_eq_zero_iff (f : CauSeq β abv) : lim f = 0 ↔ LimZero f :=
  ⟨fun h => by
    have hf := equiv_lim f
    rw [h] at hf
    exact (limZero_congr hf).mpr (const_limZero.mpr rfl),
   fun h => by
    have h₁ : f = f - const abv 0 := ext fun n => by simp
    rw [h₁] at h
    exact lim_eq_of_equiv_const h⟩

end

section

variable {β : Type*} [Field β] {abv : β -> α} [IsAbsoluteValue abv] [IsComplete β abv]

/--
theorem `lim_inv` / 定理 `lim_inv`

English:
theorem lim_inv
  given: {f : CauSeq β abv} (hf : ¬LimZero f)
  statement: lim (inv f hf) = (lim f)⁻¹
  proof: have hl : lim f != 0 := by rwa [← lim_eq_zero_iff] at hf
lim_eq_of_equiv_const
    show LimZero (inv f hf - const abv (lim f)⁻¹) from
      have h₁ : forall (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
          have h₂ : g - f * inv f hf * g = 1

中文:
定理 lim_inv
  条件: {f : CauSeq β abv} (hf : ¬LimZero f)
  结论: lim (inv f hf) = (lim f)⁻¹
  证明: have hl : lim f != 0 := by rwa [← lim_eq_zero_iff] at hf
lim_eq_of_equiv_const
    show LimZero (inv f hf - const abv (lim f)⁻¹) from
      have h₁ : forall (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
          have h₂ : g - f * inv f hf * g = 1

Depends on / 依赖: CauSeq, LimZero, lim_eq_of_equiv_const, lim_eq_zero_iff, mul_assoc, one_mul, sub_mul
-/
theorem lim_inv {f : CauSeq β abv} (hf : ¬LimZero f) : lim (inv f hf) = (lim f)⁻¹ :=
  have hl : lim f != 0 := by rwa [← lim_eq_zero_iff] at hf
lim_eq_of_equiv_const
    show LimZero (inv f hf - const abv (lim f)⁻¹) from
      have h₁ : forall (g f : CauSeq β abv) (hf : ¬LimZero f), LimZero (g - f * inv f hf * g) :=
        fun g f hf => by
          have h₂ : g - f * inv f hf * g = 1 * g - f * inv f hf * g := by rw [one_mul g]
          have h₃ : f * inv f hf * g = (f * inv f hf) * g := by simp [mul_assoc]
          have h₄ : g - f * inv f hf * g = (1 - f * inv f hf) * g := by rw [h₂, h₃, ← sub_mul]
          have h₅ : g - f * inv f hf * g = g * (1 - f * inv f hf) := by rw [h₄, mul_comm]
          have h₆ : g - f * inv f hf * g = g * (1 - inv f hf * f) := by rw [h₅, mul_comm f]
          rw [h₆]; exact mul_limZero_right _ (Setoid.symm (CauSeq.inv_mul_cancel _))
      have h₂ :
        LimZero
          (inv f hf - const abv (lim f)⁻¹ -
            (const abv (lim f) - f) * (inv f hf * const abv (lim f)⁻¹)) := by
              rw [sub_mul]; rw [← sub_add]; rw [sub_sub]; rw [sub_add_eq_sub_sub]; rw [sub_right_comm]; rw [sub_add]
              change LimZero
                (inv f hf - const abv (lim f) * (inv f hf * const abv (lim f)⁻¹) -
                  (const abv (lim f)⁻¹ - f * (inv f hf * const abv (lim f)⁻¹)))
              exact sub_limZero
                (by rw [← mul_assoc, mul_right_comm, const_inv hl]; exact h₁ _ _ _)
                (by rw [← mul_assoc]; exact h₁ _ _ _)
(limZero_congr h₂).mpr mul_limZero_left _ (Setoid.symm (equiv_lim f))

end

section

variable [IsComplete α abs]

/--
theorem `lim_le` / 定理 `lim_le`

English:
theorem lim_le
  given: {f : CauSeq α abs} {x : α} (h : f <= CauSeq.const abs x)
  statement: lim f <= x
  proof: CauSeq.const_le.1 CauSeq.le_of_eq_of_le (Setoid.symm (equiv_lim f)) h

中文:
定理 lim_le
  条件: {f : CauSeq α abs} {x : α} (h : f <= CauSeq.const abs x)
  结论: lim f <= x
  证明: CauSeq.const_le.1 CauSeq.le_of_eq_of_le (Setoid.symm (equiv_lim f)) h

Depends on / 依赖: CauSeq, CauSeq.const_le, CauSeq.le_of_eq_of_le, Setoid, Setoid.symm, const_le, equiv_lim, le_of_eq_of_le
-/
theorem lim_le {f : CauSeq α abs} {x : α} (h : f <= CauSeq.const abs x) : lim f <= x :=
CauSeq.const_le.1 CauSeq.le_of_eq_of_le (Setoid.symm (equiv_lim f)) h

/--
theorem `le_lim` / 定理 `le_lim`

English:
theorem le_lim
  given: {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x <= f)
  statement: x <= lim f
  proof: CauSeq.const_le.1 CauSeq.le_of_le_of_eq h (equiv_lim f)

中文:
定理 le_lim
  条件: {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x <= f)
  结论: x <= lim f
  证明: CauSeq.const_le.1 CauSeq.le_of_le_of_eq h (equiv_lim f)

Depends on / 依赖: CauSeq, CauSeq.const_le, CauSeq.le_of_le_of_eq, const_le, equiv_lim, le_of_le_of_eq
-/
theorem le_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x <= f) : x <= lim f :=
CauSeq.const_le.1 CauSeq.le_of_le_of_eq h (equiv_lim f)

/--
theorem `lt_lim` / 定理 `lt_lim`

English:
theorem lt_lim
  given: {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f)
  statement: x < lim f
  proof: CauSeq.const_lt.1 CauSeq.lt_of_lt_of_eq h (equiv_lim f)

中文:
定理 lt_lim
  条件: {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f)
  结论: x < lim f
  证明: CauSeq.const_lt.1 CauSeq.lt_of_lt_of_eq h (equiv_lim f)

Depends on / 依赖: CauSeq, CauSeq.const_lt, CauSeq.lt_of_lt_of_eq, const_lt, equiv_lim, lt_of_lt_of_eq
-/
theorem lt_lim {f : CauSeq α abs} {x : α} (h : CauSeq.const abs x < f) : x < lim f :=
CauSeq.const_lt.1 CauSeq.lt_of_lt_of_eq h (equiv_lim f)

/--
theorem `lim_lt` / 定理 `lim_lt`

English:
theorem lim_lt
  given: {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x)
  statement: lim f < x
  proof: CauSeq.const_lt.1 CauSeq.lt_of_eq_of_lt (Setoid.symm (equiv_lim f)) h

中文:
定理 lim_lt
  条件: {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x)
  结论: lim f < x
  证明: CauSeq.const_lt.1 CauSeq.lt_of_eq_of_lt (Setoid.symm (equiv_lim f)) h

Depends on / 依赖: CauSeq, CauSeq.const_lt, CauSeq.lt_of_eq_of_lt, Setoid, Setoid.symm, const_lt, equiv_lim, lt_of_eq_of_lt
-/
theorem lim_lt {f : CauSeq α abs} {x : α} (h : f < CauSeq.const abs x) : lim f < x :=
CauSeq.const_lt.1 CauSeq.lt_of_eq_of_lt (Setoid.symm (equiv_lim f)) h

end

end CauSeq
