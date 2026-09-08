/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Yury Kudryashov, Neil Strickland
-/
module

public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Opposites
public import Mathlib.Algebra.GroupWithZero.InjSurj
public import Mathlib.Data.Int.Cast.Basic

/-!
# Pulling back rings along injective maps, and pushing them forward along surjective maps

## Implementation note

The `nsmul` and `zsmul` assumptions on any transfer definition for an algebraic structure involving
both addition and multiplication (e.g. `AddMonoidWithOne`) is `∀ n x, f (n • x) = n • f x`, which is
what we would expect.
However, we cannot do the same for transfer definitions built using `to_additive` (e.g. `AddMonoid`)
as we want the multiplicative versions to be `∀ x n, f (x ^ n) = f x ^ n`.
As a result, we must use `Function.swap` when using additivised transfer definitions in
non-additivised ones.
-/

public section

variable {R S : Type*}

namespace Function.Injective
variable (f : S → R) (hf : Injective f)
include hf

variable [Add S] [Mul S]

/-- Pullback a `LeftDistribClass` instance along an injective function. -/
/-
**Function.Injective.leftDistribClass** 是 Mathlib 中的一个定理，位于命名空间 `Function.Inject
ive`。
形式化陈述：leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : forall x y, f
 (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y) : LeftDistribCla
ss S where left_distrib x y z
参数：add : forall x y, f (x + y) = f x + f y；mul : forall x y, f (x * y) = f x * f
 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullback a `LeftDistribClass` instance along an injective function.
-/
theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib x y z := hf <| by simp only [*, left_distrib]

/-- Pullback a `RightDistribClass` instance along an injective function. -/
/-
**Function.Injective.rightDistribClass** 是 Mathlib 中的一个定理，位于命名空间 `Function.Injec
tive`。
形式化陈述：rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : forall x y,
 f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y) : RightDistrib
Class S where right_distrib x y z
参数：add : forall x y, f (x + y) = f x + f y；mul : forall x y, f (x * y) = f x * f
 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pullback a `RightDistribClass` instance along an injective function.
-/
theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib x y z := hf <| by simp only [*, right_distrib]

variable [Zero S] [One S] [Neg S] [Sub S] [SMul ℕ S] [SMul ℤ S]
  [Pow S ℕ] [NatCast S] [IntCast S]

/-- Pullback a `Distrib` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.distrib** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Distrib R] →               (∀ (x y : S), f (x + y) = f x + f y) → (∀ (x y :
 S), f (x * y) = f x * f y) → Distrib S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LeftDistribClass.left_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1 :
 Add R} [self : LeftDistribClass R] (a b c : R), a * (b + c) = a * b + a * c
· 使用定理 `RightDistribClass.right_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1
 : Add R} [self : RightDistribClass R] (a b c : R), (a + b) * c = a * c + b * c
-/
protected abbrev distrib [Distrib R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib S where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

/-- A type endowed with `-` and `*` has distributive negation, if it admits an injective map that
preserves `-` and `*` to a type which has distributive negation. -/
-- See note [reducible non-instances]
/-
**Function.Injective.hasDistribNeg** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Mul S] →       [inst_1 : N
eg S] →         (f : S → R) →           Function.Injective f →             [inst
_2 : Mul R] →               [inst_3 : HasDistribNeg R] →                 (∀ (a :
 S), f (-a) = -f a) → (∀ (a b : S), f (a * b) = f a * f b) → HasDistribNeg S
参数：f : S → R；∀ (a : S), f (-a) = -f a；∀ (a b : S), f (a * b) = f a * f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev hasDistribNeg (f : S → R) (hf : Injective f) [Mul R] [HasDistribNeg R]
    (neg : ∀ a, f (-a) = -f a)
    (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg S :=
  { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := fun x y => hf <| by rw [neg, mul, neg, neg_mul, mul],
    mul_neg := fun x y => hf <| by rw [neg, mul, neg, mul_neg, mul] }

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive monoid with one.
See note [reducible non-instances]. -/
/-
**Function.Injective.addMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : Z
ero S] →         [inst_2 : One S] →           [inst_3 : SMul ℕ S] →             
[inst_4 : NatCast S] →               [inst_5 : AddMonoidWithOne R] →            
     (f : S → R) →                   Function.Injective f →                     
f 0 = 0 →                       f 1 = 1 →                         (∀ (x y : S), 
f (x + y) = f x + f y) →                           (∀ (n : ℕ) (x : S), f (n • x)
 = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → AddMonoidWithOne S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (n : ℕ) (x : S), f (n • x) = n
 • f x；∀ (n : ℕ), f ↑n = ↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits an injective map that preserves `0`, `1` and `+` to an additive mon
oid with one.
See note [reducible non-instances].
-/
protected abbrev addMonoidWithOne [AddMonoidWithOne R]
    (f : S → R) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne S :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := hf (by rw [natCast, Nat.cast_zero, zero]),
    natCast_succ := fun n => hf (by rw [natCast, Nat.cast_succ, add, one, natCast]) }

/-- A type endowed with `0`, `1` and `+` is an additive commutative monoid with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative monoid with one.
See note [reducible non-instances]. -/
/-
**Function.Injective.addCommMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.In
jective`。
形式化陈述：{R : Type u_1} →   {S : Type u_3} →     [inst : Zero S] →       [inst_1 : 
One S] →         [inst_2 : Add S] →           [inst_3 : SMul ℕ S] →             
[inst_4 : NatCast S] →               [inst_5 : AddCommMonoidWithOne R] →        
         (f : S → R) →                   Function.Injective f →                 
    f 0 = 0 →                       f 1 = 1 →                         (∀ (x y : 
S), f (x + y) = f x + f y) →                           (∀ (n : ℕ) (x : S), f (n 
• x) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → AddCommMonoidWithOne S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (n : ℕ) (x : S), f (n • x) = n
 • f x；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a

--- 原说明 ---
A type endowed with `0`, `1` and `+` is an additive commutative monoid with one,
 if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative monoid 
with one.
See note [reducible non-instances].
-/
protected abbrev addCommMonoidWithOne {S} [Zero S] [One S] [Add S] [SMul ℕ S] [NatCast S]
    [AddCommMonoidWithOne R] (f : S → R) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne S where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

/-- A type endowed with `0`, `1` and `+` is an additive group with one, if it admits an injective
map that preserves `0`, `1` and `+` to an additive group with one.  See note
[reducible non-instances]. -/
/-
**Function.Injective.addGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injecti
ve`。
形式化陈述：{R : Type u_1} →   {S : Type u_3} →     [inst : Zero S] →       [inst_1 : 
One S] →         [inst_2 : Add S] →           [inst_3 : SMul ℕ S] →             
[inst_4 : Neg S] →               [inst_5 : Sub S] →                 [inst_6 : SM
ul ℤ S] →                   [inst_7 : NatCast S] →                     [inst_8 :
 IntCast S] →                       [inst_9 : AddGroupWithOne R] →              
           (f : S → R) →                           Function.Injective f →       
                      f 0 = 0 →                               f 1 = 1 →         
                        (∀ (x y : S), f (x + y) = f x + f y) →                  
                 (∀ (x : S), f (-x) = -f x) →                                   
  (∀ (x y : S), f (x - y) = f x - f y) →                                       (
∀ (n : ℕ) (x : S), f (n • x) = n • f x) →                                       
  (∀ (n : ℤ) (x : S), f (n • x) = n • f x) →                                    
       (∀ (n : ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → AddGroupWithOne S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x : S), f (-x) = -f x；∀ (x y 
: S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S), f (n • x) = n • f x；∀ (n : ℤ) (x 
: S), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `AddGroup.neg_add_cancel`：∀ {A : Type u} [self : AddGroup A] (a : A), -a 
+ a = 0

--- 原说明 ---
A type endowed with `0`, `1` and `+` is an additive group with one, if it admits
 an injective
map that preserves `0`, `1` and `+` to an additive group with one.  See note
[reducible non-instances].
-/
protected abbrev addGroupWithOne {S} [Zero S] [One S] [Add S] [SMul ℕ S] [Neg S] [Sub S]
    [SMul ℤ S] [NatCast S] [IntCast S] [AddGroupWithOne R] (f : S → R) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne S :=
  { hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul),
    hf.addMonoidWithOne f zero one add nsmul natCast with
    intCast := Int.cast,
    intCast_ofNat := fun n => hf (by rw [natCast, intCast, Int.cast_natCast]),
    intCast_negSucc := fun n => hf (by rw [intCast, neg, natCast, Int.cast_negSucc]) }

/-- A type endowed with `0`, `1` and `+` is an additive commutative group with one, if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
/-
**Function.Injective.addCommGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inj
ective`。
形式化陈述：{R : Type u_1} →   {S : Type u_3} →     [inst : Zero S] →       [inst_1 : 
One S] →         [inst_2 : Add S] →           [inst_3 : SMul ℕ S] →             
[inst_4 : Neg S] →               [inst_5 : Sub S] →                 [inst_6 : SM
ul ℤ S] →                   [inst_7 : NatCast S] →                     [inst_8 :
 IntCast S] →                       [inst_9 : AddCommGroupWithOne R] →          
               (f : S → R) →                           Function.Injective f →   
                          f 0 = 0 →                               f 1 = 1 →     
                            (∀ (x y : S), f (x + y) = f x + f y) →              
                     (∀ (x : S), f (-x) = -f x) →                               
      (∀ (x y : S), f (x - y) = f x - f y) →                                    
   (∀ (n : ℕ) (x : S), f (n • x) = n • f x) →                                   
      (∀ (n : ℤ) (x : S), f (n • x) = n • f x) →                                
           (∀ (n : ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → AddCommGroupWithOne
 S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x : S), f (-x) = -f x；∀ (x y 
: S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S), f (n • x) = n • f x；∀ (n : ℤ) (x 
: S), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `AddGroupWithOne.zsmul_zero'`：∀ {R : Type u} [self : AddGroupWithOne R] (
a : R), 0 • a = 0
· 使用定理 `AddGroupWithOne.zsmul_succ'`：∀ {R : Type u} [self : AddGroupWithOne R] (
n : ℕ) (a : R), ↑n.succ • a = ↑n • a + a
· 使用定理 `AddGroupWithOne.zsmul_neg'`：∀ {R : Type u} [self : AddGroupWithOne R] (n
 : ℕ) (a : R), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroupWithOne.neg_add_cancel`：∀ {R : Type u} [self : AddGroupWithOne R
] (a : R), -a + a = 0
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)

--- 原说明 ---
A type endowed with `0`, `1` and `+` is an additive commutative group with one, 
if it admits an
injective map that preserves `0`, `1` and `+` to an additive commutative group w
ith one.
See note [reducible non-instances].
-/
protected abbrev addCommGroupWithOne {S} [Zero S] [One S] [Add S] [SMul ℕ S] [Neg S] [Sub S]
    [SMul ℤ S] [NatCast S] [IntCast S] [AddCommGroupWithOne R] (f : S → R) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne S :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

/-- Pullback a `NonUnitalNonAssocSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalNonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Functi
on.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : Non
UnitalNonAssocSemiring R] →                   f 0 = 0 →                     (∀ (
x y : S), f (x + y) = f x + f y) →                       (∀ (x y : S), f (x * y)
 = f x * f y) →                         (∀ (n : ℕ) (x : S), f (n • x) = n • f x)
 → NonUnitalNonAssocSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Distrib.left_distrib`：∀ {R : Type u_1} [self : Distrib R] (a b c : R), a
 * (b + c) = a * b + a * c
· 使用定理 `Distrib.right_distrib`：∀ {R : Type u_1} [self : Distrib R] (a b c : R), 
(a + b) * c = a * c + b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring S where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

/-- Pullback a `NonUnitalSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injec
tive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : Non
UnitalSemiring R] →                   f 0 = 0 →                     (∀ (x y : S)
, f (x + y) = f x + f y) →                       (∀ (x y : S), f (x * y) = f x *
 f y) →                         (∀ (n : ℕ) (x : S), f (n • x) = n • f x) → NonUn
italSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev nonUnitalSemiring [NonUnitalSemiring R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

/-- Pullback a `NonAssocSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul ℕ
 S] →                   [inst_5 : NatCast S] →                     [inst_6 : Non
AssocSemiring R] →                       f 0 = 0 →                         f 1 =
 1 →                           (∀ (x y : S), f (x + y) = f x + f y) →           
                  (∀ (x y : S), f (x * y) = f x * f y) →                        
       (∀ (n : ℕ) (x : S), f (n • x) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → NonAs
socSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
protected abbrev nonAssocSemiring [NonAssocSemiring R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

/-- Pullback a `Semiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.semiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul ℕ
 S] →                   [inst_5 : Pow S ℕ] →                     [inst_6 : NatCa
st S] →                       [inst_7 : Semiring R] →                         f 
0 = 0 →                           f 1 = 1 →                             (∀ (x y 
: S), f (x + y) = f x + f y) →                               (∀ (x y : S), f (x 
* y) = f x * f y) →                                 (∀ (n : ℕ) (x : S), f (n • x
) = n • f x) →                                   (∀ (x : S) (n : ℕ), f (x ^ n) =
 f x ^ n) → (∀ (n : ℕ), f ↑n = ↑n) → Semiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x；∀ (x : S) (n : ℕ), f (x ^ n) = f x ^ n
；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSemiring.mul_assoc`：∀ {α : Type u} [self : NonUnitalSemiring α]
 (a b c : α), a * b * c = a * (b * c)
· 使用定理 `NonAssocSemiring.one_mul`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), 1 * a = a
· 使用定理 `NonAssocSemiring.mul_one`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), a * 1 = a
· 使用定理 `NonAssocSemiring.natCast_zero`：∀ {α : Type u} [self : NonAssocSemiring α
], ↑0 = 0
· 使用定理 `NonAssocSemiring.natCast_succ`：∀ {α : Type u} [self : NonAssocSemiring α
] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
protected abbrev semiring [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : Semiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

/-- Pullback a `NonUnitalNonAssocRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalNonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.I
njective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : M
ul S] →         [inst_2 : Zero S] →           [inst_3 : Neg S] →             [in
st_4 : Sub S] →               [inst_5 : SMul ℕ S] →                 [inst_6 : SM
ul ℤ S] →                   [inst_7 : NonUnitalNonAssocRing R] →                
     (f : S → R) →                       Function.Injective f →                 
        f 0 = 0 →                           (∀ (x y : S), f (x + y) = f x + f y)
 →                             (∀ (x y : S), f (x * y) = f x * f y) →           
                    (∀ (x : S), f (-x) = -f x) →                                
 (∀ (x y : S), f (x - y) = f x - f y) →                                   (∀ (n 
: ℕ) (x : S), f (n • x) = n • f x) →                                     (∀ (n :
 ℤ) (x : S), f (n • x) = n • f x) → NonUnitalNonAssocRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocSemiring.left_distrib`：∀ {α : Type u} [self : NonUnital
NonAssocSemiring α] (a b c : α), a * (b + c) = a * b + a * c
· 使用定理 `NonUnitalNonAssocSemiring.right_distrib`：∀ {α : Type u} [self : NonUnita
lNonAssocSemiring α] (a b c : α), (a + b) * c = a * c + b * c
· 使用定理 `NonUnitalNonAssocSemiring.zero_mul`：∀ {α : Type u} [self : NonUnitalNonA
ssocSemiring α] (a : α), 0 * a = 0
· 使用定理 `NonUnitalNonAssocSemiring.mul_zero`：∀ {α : Type u} [self : NonUnitalNonA
ssocSemiring α] (a : α), a * 0 = 0
-/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocRing S where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective
`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S]
 →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ 
S] →                       [inst_7 : NonUnitalRing R] →                         
f 0 = 0 →                           (∀ (x y : S), f (x + y) = f x + f y) →      
                       (∀ (x y : S), f (x * y) = f x * f y) →                   
            (∀ (x : S), f (-x) = -f x) →                                 (∀ (x y
 : S), f (x - y) = f x - f y) →                                   (∀ (n : ℕ) (x 
: S), f (n • x) = n • f x) →                                     (∀ (n : ℤ) (x :
 S), f (n • x) = n • f x) → NonUnitalRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSemiring.mul_assoc`：∀ {α : Type u} [self : NonUnitalSemiring α]
 (a b c : α), a * b * c = a * (b * c)
-/
protected abbrev nonUnitalRing [NonUnitalRing R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

/-- Pullback a `NonAssocRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`
。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S]
 →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S] 
→                       [inst_7 : SMul ℤ S] →                         [inst_8 : 
NatCast S] →                           [inst_9 : IntCast S] →                   
          [inst_10 : NonAssocRing R] →                               f 0 = 0 →  
                               f 1 = 1 →                                   (∀ (x
 y : S), f (x + y) = f x + f y) →                                     (∀ (x y : 
S), f (x * y) = f x * f y) →                                       (∀ (x : S), f
 (-x) = -f x) →                                         (∀ (x y : S), f (x - y) 
= f x - f y) →                                           (∀ (n : ℕ) (x : S), f (
n • x) = n • f x) →                                             (∀ (n : ℤ) (x : 
S), f (n • x) = n • f x) →                                               (∀ (n :
 ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → NonAssocRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑
n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonAssocSemiring.one_mul`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), 1 * a = a
· 使用定理 `NonAssocSemiring.mul_one`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), a * 1 = a
· 使用定理 `NonAssocSemiring.natCast_zero`：∀ {α : Type u} [self : NonAssocSemiring α
], ↑0 = 0
· 使用定理 `NonAssocSemiring.natCast_succ`：∀ {α : Type u} [self : NonAssocSemiring α
] (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `AddCommGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddCommGroupWi
thOne R] (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddCommGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddCommGroup
WithOne R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
-/
protected abbrev nonAssocRing [NonAssocRing R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : NonAssocRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

/-- Pullback a `Ring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.ring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S]
 →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S] 
→                       [inst_7 : SMul ℤ S] →                         [inst_8 : 
Pow S ℕ] →                           [inst_9 : NatCast S] →                     
        [inst_10 : IntCast S] →                               [inst_11 : Ring R]
 →                                 f 0 = 0 →                                   f
 1 = 1 →                                     (∀ (x y : S), f (x + y) = f x + f y
) →                                       (∀ (x y : S), f (x * y) = f x * f y) →
                                         (∀ (x : S), f (-x) = -f x) →           
                                (∀ (x y : S), f (x - y) = f x - f y) →          
                                   (∀ (n : ℕ) (x : S), f (n • x) = n • f x) →   
                                            (∀ (n : ℤ) (x : S), f (n • x) = n • 
f x) →                                                 (∀ (x : S) (n : ℕ), f (x 
^ n) = f x ^ n) →                                                   (∀ (n : ℕ), 
f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → Ring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x；∀ (x : S) (n : ℕ), 
f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `AddGroupWithOne.zsmul_zero'`：∀ {R : Type u} [self : AddGroupWithOne R] (
a : R), 0 • a = 0
· 使用定理 `AddGroupWithOne.zsmul_succ'`：∀ {R : Type u} [self : AddGroupWithOne R] (
n : ℕ) (a : R), ↑n.succ • a = ↑n • a + a
· 使用定理 `AddGroupWithOne.zsmul_neg'`：∀ {R : Type u} [self : AddGroupWithOne R] (n
 : ℕ) (a : R), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroupWithOne.neg_add_cancel`：∀ {R : Type u} [self : AddGroupWithOne R
] (a : R), -a + a = 0
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
-/
protected abbrev ring [Ring R] (zero : f 0 = 0)
    (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : Ring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  -- zsmul included here explicitly to make sure it's picked correctly by `fast_instance%`.
  zsmul := fun n x ↦ n • x
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

/-- Pullback a `NonUnitalNonAssocCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalNonAssocCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Fu
nction.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : Non
UnitalNonAssocCommSemiring R] →                   f 0 = 0 →                     
(∀ (x y : S), f (x + y) = f x + f y) →                       (∀ (x y : S), f (x 
* y) = f x * f y) →                         (∀ (n : ℕ) (x : S), f (n • x) = n • 
f x) → NonUnitalNonAssocCommSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMagma.mul_comm`：∀ {G : Type u} [self : CommMagma G] (a b : G), a * b
 = b * a
-/
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocCommSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pullback a `NonUnitalCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.I
njective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : M
ul S] →         [inst_2 : Zero S] →           [inst_3 : SMul ℕ S] →             
[inst_4 : NonUnitalCommSemiring R] →               (f : S → R) →                
 Function.Injective f →                   f 0 = 0 →                     (∀ (x y 
: S), f (x + y) = f x + f y) →                       (∀ (x y : S), f (x * y) = f
 x * f y) →                         (∀ (n : ℕ) (x : S), f (n • x) = n • f x) → N
onUnitalCommSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemigroup.mul_comm`：∀ {G : Type u} [self : CommSemigroup G] (a b : G
), a * b = b * a
-/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) :
    NonUnitalCommSemiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

/-- Pullback a `NonAssocCommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonAssocCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.In
jective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : M
ul S] →         [inst_2 : Zero S] →           [inst_3 : One S] →             [in
st_4 : SMul ℕ S] →               [inst_5 : NatCast S] →                 [inst_6 
: NonAssocCommSemiring R] →                   (f : S → R) →                     
Function.Injective f →                       f 0 = 0 →                         f
 1 = 1 →                           (∀ (x y : S), f (x + y) = f x + f y) →       
                      (∀ (x y : S), f (x * y) = f x * f y) →                    
           (∀ (n : ℕ) (x : S), f (n • x) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → N
onAssocCommSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMagma.mul_comm`：∀ {G : Type u} [self : CommMagma G] (a b : G), a * b
 = b * a
-/
protected abbrev nonAssocCommSemiring [NonAssocCommSemiring R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocCommSemiring S where
  toNonAssocSemiring := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

/-- Pullback a `CommSemiring` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.commSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`
。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul ℕ
 S] →                   [inst_5 : Pow S ℕ] →                     [inst_6 : NatCa
st S] →                       [inst_7 : CommSemiring R] →                       
  f 0 = 0 →                           f 1 = 1 →                             (∀ (
x y : S), f (x + y) = f x + f y) →                               (∀ (x y : S), f
 (x * y) = f x * f y) →                                 (∀ (n : ℕ) (x : S), f (n
 • x) = n • f x) →                                   (∀ (x : S) (n : ℕ), f (x ^ 
n) = f x ^ n) → (∀ (n : ℕ), f ↑n = ↑n) → CommSemiring S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : S), f (n • x) = n • f x；∀ (x : S) (n : ℕ), f (x ^ n) = f x ^ n
；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemigroup.mul_comm`：∀ {G : Type u} [self : CommSemigroup G] (a b : G
), a * b = b * a
-/
protected abbrev commSemiring [CommSemiring R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n) :
    CommSemiring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

/-- Pullback a `NonUnitalNonAssocCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalNonAssocCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Functi
on.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : M
ul S] →         [inst_2 : Zero S] →           [inst_3 : Neg S] →             [in
st_4 : Sub S] →               [inst_5 : SMul ℕ S] →                 [inst_6 : SM
ul ℤ S] →                   [inst_7 : NonUnitalNonAssocCommRing R] →            
         (f : S → R) →                       Function.Injective f →             
            f 0 = 0 →                           (∀ (x y : S), f (x + y) = f x + 
f y) →                             (∀ (x y : S), f (x * y) = f x * f y) →       
                        (∀ (x : S), f (-x) = -f x) →                            
     (∀ (x y : S), f (x - y) = f x - f y) →                                   (∀
 (n : ℕ) (x : S), f (n • x) = n • f x) →                                     (∀ 
(n : ℤ) (x : S), f (n • x) = n • f x) → NonUnitalNonAssocCommRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommSemiring.mul_comm`：∀ {α : Type u} [self : NonUnital
NonAssocCommSemiring α] (a b : α), a * b = b * a
-/
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pullback a `NonUnitalCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonUnitalCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injec
tive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : M
ul S] →         [inst_2 : Zero S] →           [inst_3 : Neg S] →             [in
st_4 : Sub S] →               [inst_5 : SMul ℕ S] →                 [inst_6 : SM
ul ℤ S] →                   [inst_7 : NonUnitalCommRing R] →                    
 (f : S → R) →                       Function.Injective f →                     
    f 0 = 0 →                           (∀ (x y : S), f (x + y) = f x + f y) →  
                           (∀ (x y : S), f (x * y) = f x * f y) →               
                (∀ (x : S), f (-x) = -f x) →                                 (∀ 
(x y : S), f (x - y) = f x - f y) →                                   (∀ (n : ℕ)
 (x : S), f (n • x) = n • f x) →                                     (∀ (n : ℤ) 
(x : S), f (n • x) = n • f x) → NonUnitalCommRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommRing.mul_comm`：∀ {α : Type u} [self : NonUnitalNonA
ssocCommRing α] (a b : α), a * b = b * a
-/
protected abbrev nonUnitalCommRing [NonUnitalCommRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalCommRing S where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

/-- Pullback a `NonAssocCommRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.nonAssocCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Inject
ive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     [inst : Add S] →       [inst_1 : M
ul S] →         [inst_2 : Zero S] →           [inst_3 : One S] →             [in
st_4 : Neg S] →               [inst_5 : Sub S] →                 [inst_6 : SMul 
ℕ S] →                   [inst_7 : SMul ℤ S] →                     [inst_8 : Nat
Cast S] →                       [inst_9 : IntCast S] →                         [
inst_10 : NonAssocCommRing R] →                           (f : S → R) →         
                    Function.Injective f →                               f 0 = 0
 →                                 f 1 = 1 →                                   (
∀ (x y : S), f (x + y) = f x + f y) →                                     (∀ (x 
y : S), f (x * y) = f x * f y) →                                       (∀ (x : S
), f (-x) = -f x) →                                         (∀ (x y : S), f (x -
 y) = f x - f y) →                                           (∀ (n : ℕ) (x : S),
 f (n • x) = n • f x) →                                             (∀ (n : ℤ) (
x : S), f (n • x) = n • f x) →                                               (∀ 
(n : ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → NonAssocCommRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑
n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommRing.mul_comm`：∀ {α : Type u} [self : NonUnitalNonA
ssocCommRing α] (a b : α), a * b = b * a
-/
protected abbrev nonAssocCommRing [NonAssocCommRing R] (f : S → R)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocCommRing S where
  toNonAssocRing := hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

/-- Pullback a `CommRing` instance along an injective function. -/
-- See note [reducible non-instances]
/-
**Function.Injective.commRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Injective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : S → R) →       Function.Injec
tive f →         [inst : Add S] →           [inst_1 : Mul S] →             [inst
_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S]
 →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S] 
→                       [inst_7 : SMul ℤ S] →                         [inst_8 : 
Pow S ℕ] →                           [inst_9 : NatCast S] →                     
        [inst_10 : IntCast S] →                               [inst_11 : CommRin
g R] →                                 f 0 = 0 →                                
   f 1 = 1 →                                     (∀ (x y : S), f (x + y) = f x +
 f y) →                                       (∀ (x y : S), f (x * y) = f x * f 
y) →                                         (∀ (x : S), f (-x) = -f x) →       
                                    (∀ (x y : S), f (x - y) = f x - f y) →      
                                       (∀ (n : ℕ) (x : S), f (n • x) = n • f x) 
→                                               (∀ (n : ℤ) (x : S), f (n • x) = 
n • f x) →                                                 (∀ (x : S) (n : ℕ), f
 (x ^ n) = f x ^ n) →                                                   (∀ (n : 
ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → CommRing S
参数：f : S → R；∀ (x y : S), f (x + y) = f x + f y；∀ (x y : S), f (x * y) = f x * f
 y；∀ (x : S), f (-x) = -f x；∀ (x y : S), f (x - y) = f x - f y；∀ (n : ℕ) (x : S)
, f (n • x) = n • f x；∀ (n : ℤ) (x : S), f (n • x) = n • f x；∀ (x : S) (n : ℕ), 
f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.mul_comm`：∀ {M : Type u} [self : CommMonoid M] (a b : M), a *
 b = b * a
-/
protected abbrev commRing [CommRing R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : CommRing S where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

end Function.Injective

namespace Function.Surjective
variable (f : R → S) (hf : Surjective f)
include hf

variable [Add S] [Mul S]

/-- Pushforward a `LeftDistribClass` instance along a surjective function. -/
/-
**Function.Surjective.leftDistribClass** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surje
ctive`。
形式化陈述：leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : forall x y, f
 (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y) : LeftDistribCla
ss S where left_distrib
参数：add : forall x y, f (x + y) = f x + f y；mul : forall x y, f (x * y) = f x * f
 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₃`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f →     ∀ {p : β → β → β → Prop}, (∀ (y₁ y₂ y₃ : β), p y
₁ y₂ y₃) ↔ ∀ (x₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `left_distrib`：left_distrib [Mul R] [Add R] [LeftDistribClass R] (a b c :
 R) : a * (b + c) = a * b + a * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pushforward a `LeftDistribClass` instance along a surjective function.
-/
theorem leftDistribClass [Mul R] [Add R] [LeftDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : LeftDistribClass S where
  left_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, left_distrib]

/-- Pushforward a `RightDistribClass` instance along a surjective function. -/
/-
**Function.Surjective.rightDistribClass** 是 Mathlib 中的一个定理，位于命名空间 `Function.Surj
ective`。
形式化陈述：rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : forall x y,
 f (x + y) = f x + f y) (mul : forall x y, f (x * y) = f x * f y) : RightDistrib
Class S where right_distrib
参数：add : forall x y, f (x + y) = f x + f y；mul : forall x y, f (x * y) = f x * f
 y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.Surjective.forall₃`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}
,   Function.Surjective f →     ∀ {p : β → β → β → Prop}, (∀ (y₁ y₂ y₃ : β), p y
₁ y₂ y₃) ↔ ∀ (x₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `right_distrib`：right_distrib [Mul R] [Add R] [RightDistribClass R] (a b 
c : R) : (a + b) * c = a * c + b * c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Pushforward a `RightDistribClass` instance along a surjective function.
-/
theorem rightDistribClass [Mul R] [Add R] [RightDistribClass R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : RightDistribClass S where
  right_distrib := hf.forall₃.2 fun x y z => by simp only [← add, ← mul, right_distrib]

/-- Pushforward a `Distrib` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.distrib** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Distrib R] →               (∀ (x y : R), f (x + y) = f x + f y) → (∀ (x y 
: R), f (x * y) = f x * f y) → Distrib S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LeftDistribClass.left_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1 :
 Add R} [self : LeftDistribClass R] (a b c : R), a * (b + c) = a * b + a * c
· 使用定理 `RightDistribClass.right_distrib`：∀ {R : Type u_1} {inst : Mul R} {inst_1
 : Add R} [self : RightDistribClass R] (a b c : R), (a + b) * c = a * c + b * c
-/
protected abbrev distrib [Distrib R] (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) : Distrib S where
  __ := hf.leftDistribClass f add mul
  __ := hf.rightDistribClass f add mul

variable [Zero S] [One S] [Neg S] [Sub S] [SMul ℕ S] [SMul ℤ S]
  [Pow S ℕ] [NatCast S] [IntCast S]

/-- A type endowed with `-` and `*` has distributive negation, if it admits a surjective map that
preserves `-` and `*` from a type which has distributive negation. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.hasDistribNeg** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjecti
ve`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Mul S] →           [inst_1 : Neg S] →             [ins
t_2 : Mul R] →               [inst_3 : HasDistribNeg R] →                 (∀ (a 
: R), f (-a) = -f a) → (∀ (a b : R), f (a * b) = f a * f b) → HasDistribNeg S
参数：f : R → S；∀ (a : R), f (-a) = -f a；∀ (a b : R), f (a * b) = f a * f b。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev hasDistribNeg [Mul R] [HasDistribNeg R]
    (neg : ∀ a, f (-a) = -f a) (mul : ∀ a b, f (a * b) = f a * f b) : HasDistribNeg S :=
  { hf.involutiveNeg _ neg, ‹Mul S› with
    neg_mul := hf.forall₂.2 fun x y => by rw [← neg, ← mul, neg_mul, neg, mul]
    mul_neg := hf.forall₂.2 fun x y => by rw [← neg, ← mul, mul_neg, neg, mul] }


/-- A type endowed with `0`, `1` and `+` is an additive monoid with one, if it admits a surjective
map that preserves `0`, `1` and `*` from an additive monoid with one. See note
[reducible non-instances]. -/
/-
**Function.Surjective.addMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surje
ctive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Zero S] →             [in
st_2 : One S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : Na
tCast S] →                   [inst_5 : AddMonoidWithOne R] →                    
 f 0 = 0 →                       f 1 = 1 →                         (∀ (x y : R),
 f (x + y) = f x + f y) →                           (∀ (n : ℕ) (x : R), f (n • x
) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → AddMonoidWithOne S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (n : ℕ) (x : R), f (n • x) = n
 • f x；∀ (n : ℕ), f ↑n = ↑n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type endowed with `0`, `1` and `+` is an additive monoid with one, if it admit
s a surjective
map that preserves `0`, `1` and `*` from an additive monoid with one. See note
[reducible non-instances].
-/
protected abbrev addMonoidWithOne [AddMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddMonoidWithOne S :=
  { hf.addMonoid f zero add (swap nsmul) with
    natCast := Nat.cast,
    natCast_zero := by rw [← natCast, Nat.cast_zero, zero]
    natCast_succ := fun n => by rw [← natCast, Nat.cast_succ, add, one, natCast] }

/-- A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits a surjective map that preserves `0`, `1` and `*` from an additive monoid with one.
See note [reducible non-instances]. -/
/-
**Function.Surjective.addCommMonoidWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.S
urjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Zero S] →             [in
st_2 : One S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : Na
tCast S] →                   [inst_5 : AddCommMonoidWithOne R] →                
     f 0 = 0 →                       f 1 = 1 →                         (∀ (x y :
 R), f (x + y) = f x + f y) →                           (∀ (n : ℕ) (x : R), f (n
 • x) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → AddCommMonoidWithOne S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (n : ℕ) (x : R), f (n • x) = n
 • f x；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a

--- 原说明 ---
A type endowed with `0`, `1` and `+` is an additive monoid with one,
if it admits a surjective map that preserves `0`, `1` and `*` from an additive m
onoid with one.
See note [reducible non-instances].
-/
protected abbrev addCommMonoidWithOne [AddCommMonoidWithOne R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : AddCommMonoidWithOne S where
  __ := hf.addMonoidWithOne f zero one add nsmul natCast
  __ := hf.addCommMonoid _ zero add (swap nsmul)

/-- A type endowed with `0`, `1`, `+` is an additive group with one,
if it admits a surjective map that preserves `0`, `1`, and `+` to an additive group with one.
See note [reducible non-instances]. -/
/-
**Function.Surjective.addGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjec
tive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Zero S] →             [in
st_2 : One S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S
] →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ
 S] →                       [inst_7 : NatCast S] →                         [inst
_8 : IntCast S] →                           [inst_9 : AddGroupWithOne R] →      
                       f 0 = 0 →                               f 1 = 1 →        
                         (∀ (x y : R), f (x + y) = f x + f y) →                 
                  (∀ (x : R), f (-x) = -f x) →                                  
   (∀ (x y : R), f (x - y) = f x - f y) →                                       
(∀ (n : ℕ) (x : R), f (n • x) = n • f x) →                                      
   (∀ (n : ℤ) (x : R), f (n • x) = n • f x) →                                   
        (∀ (n : ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → AddGroupWithOne S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x : R), f (-x) = -f x；∀ (x y 
: R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R), f (n • x) = n • f x；∀ (n : ℤ) (x 
: R), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroup.neg_add_cancel`：∀ {A : Type u} [self : AddGroup A] (a : A), -a 
+ a = 0

--- 原说明 ---
A type endowed with `0`, `1`, `+` is an additive group with one,
if it admits a surjective map that preserves `0`, `1`, and `+` to an additive gr
oup with one.
See note [reducible non-instances].
-/
protected abbrev addGroupWithOne [AddGroupWithOne R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddGroupWithOne S :=
  { hf.addMonoidWithOne f zero one add nsmul natCast,
    hf.addGroup f zero add neg sub (swap nsmul) (swap zsmul) with
    intCast := Int.cast,
    intCast_ofNat := fun n => by rw [← intCast, Int.cast_natCast, natCast],
    intCast_negSucc := fun n => by
      rw [← intCast, Int.cast_negSucc, neg, natCast] }

/-- A type endowed with `0`, `1`, `+` is an additive commutative group with one, if it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group with one.
See note [reducible non-instances]. -/
/-
**Function.Surjective.addCommGroupWithOne** 是 Mathlib 中的一个定义，位于命名空间 `Function.Su
rjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Zero S] →             [in
st_2 : One S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S
] →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ
 S] →                       [inst_7 : NatCast S] →                         [inst
_8 : IntCast S] →                           [inst_9 : AddCommGroupWithOne R] →  
                           f 0 = 0 →                               f 1 = 1 →    
                             (∀ (x y : R), f (x + y) = f x + f y) →             
                      (∀ (x : R), f (-x) = -f x) →                              
       (∀ (x y : R), f (x - y) = f x - f y) →                                   
    (∀ (n : ℕ) (x : R), f (n • x) = n • f x) →                                  
       (∀ (n : ℤ) (x : R), f (n • x) = n • f x) →                               
            (∀ (n : ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → AddCommGroupWithOn
e S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x : R), f (-x) = -f x；∀ (x y 
: R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R), f (n • x) = n • f x；∀ (n : ℤ) (x 
: R), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `AddGroupWithOne.zsmul_zero'`：∀ {R : Type u} [self : AddGroupWithOne R] (
a : R), 0 • a = 0
· 使用定理 `AddGroupWithOne.zsmul_succ'`：∀ {R : Type u} [self : AddGroupWithOne R] (
n : ℕ) (a : R), ↑n.succ • a = ↑n • a + a
· 使用定理 `AddGroupWithOne.zsmul_neg'`：∀ {R : Type u} [self : AddGroupWithOne R] (n
 : ℕ) (a : R), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroupWithOne.neg_add_cancel`：∀ {R : Type u} [self : AddGroupWithOne R
] (a : R), -a + a = 0
· 使用定理 `AddCommMonoid.add_comm`：∀ {M : Type u} [self : AddCommMonoid M] (a b : M
), a + b = b + a
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)

--- 原说明 ---
A type endowed with `0`, `1`, `+` is an additive commutative group with one, if 
it admits a
surjective map that preserves `0`, `1`, and `+` to an additive commutative group
 with one.
See note [reducible non-instances].
-/
protected abbrev addCommGroupWithOne [AddCommGroupWithOne R]
    (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : AddCommGroupWithOne S :=
  { hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast,
    hf.addCommMonoid _ zero add (swap nsmul) with }

/-- Pushforward a `NonUnitalNonAssocSemiring` instance along a surjective function.
See note [reducible non-instances]. -/
/-
**Function.Surjective.nonUnitalNonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Funct
ion.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : No
nUnitalNonAssocSemiring R] →                   f 0 = 0 →                     (∀ 
(x y : R), f (x + y) = f x + f y) →                       (∀ (x y : R), f (x * y
) = f x * f y) →                         (∀ (n : ℕ) (x : R), f (n • x) = n • f x
) → NonUnitalNonAssocSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Distrib.left_distrib`：∀ {R : Type u_1} [self : Distrib R] (a b c : R), a
 * (b + c) = a * b + a * c
· 使用定理 `Distrib.right_distrib`：∀ {R : Type u_1} [self : Distrib R] (a b c : R), 
(a + b) * c = a * c + b * c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Pushforward a `NonUnitalNonAssocSemiring` instance along a surjective function.
See note [reducible non-instances].
-/
protected abbrev nonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocSemiring S where
  toAddCommMonoid := hf.addCommMonoid f zero add (swap nsmul)
  __ := hf.distrib f add mul
  __ := hf.mulZeroClass f zero mul

/-- Pushforward a `NonUnitalSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surj
ective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : No
nUnitalSemiring R] →                   f 0 = 0 →                     (∀ (x y : R
), f (x + y) = f x + f y) →                       (∀ (x y : R), f (x * y) = f x 
* f y) →                         (∀ (n : ℕ) (x : R), f (n • x) = n • f x) → NonU
nitalSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected abbrev nonUnitalSemiring [NonUnitalSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.semigroupWithZero f zero mul

/-- Pushforward a `NonAssocSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonAssocSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surje
ctive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul 
ℕ S] →                   [inst_5 : NatCast S] →                     [inst_6 : No
nAssocSemiring R] →                       f 0 = 0 →                         f 1 
= 1 →                           (∀ (x y : R), f (x + y) = f x + f y) →          
                   (∀ (x y : R), f (x * y) = f x * f y) →                       
        (∀ (n : ℕ) (x : R), f (n • x) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → NonA
ssocSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidWithOne.natCast_zero`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R], ↑0 = 0
· 使用定理 `AddMonoidWithOne.natCast_succ`：∀ {R : Type u_2} [self : AddMonoidWithOne
 R] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
protected abbrev nonAssocSemiring [NonAssocSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.mulZeroOneClass f zero one mul
  __ := hf.addMonoidWithOne f zero one add nsmul natCast

/-- Pushforward a `Semiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.semiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul 
ℕ S] →                   [inst_5 : Pow S ℕ] →                     [inst_6 : NatC
ast S] →                       [inst_7 : Semiring R] →                         f
 0 = 0 →                           f 1 = 1 →                             (∀ (x y
 : R), f (x + y) = f x + f y) →                               (∀ (x y : R), f (x
 * y) = f x * f y) →                                 (∀ (n : ℕ) (x : R), f (n • 
x) = n • f x) →                                   (∀ (x : R) (n : ℕ), f (x ^ n) 
= f x ^ n) → (∀ (n : ℕ), f ↑n = ↑n) → Semiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x；∀ (x : R) (n : ℕ), f (x ^ n) = f x ^ n
；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSemiring.mul_assoc`：∀ {α : Type u} [self : NonUnitalSemiring α]
 (a b c : α), a * b * c = a * (b * c)
· 使用定理 `NonAssocSemiring.one_mul`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), 1 * a = a
· 使用定理 `NonAssocSemiring.mul_one`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), a * 1 = a
· 使用定理 `NonAssocSemiring.natCast_zero`：∀ {α : Type u} [self : NonAssocSemiring α
], ↑0 = 0
· 使用定理 `NonAssocSemiring.natCast_succ`：∀ {α : Type u} [self : NonAssocSemiring α
] (n : ℕ), ↑(n + 1) = ↑n + 1
-/
protected abbrev semiring [Semiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n) : Semiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.monoidWithZero f zero one mul npow

/-- Pushforward a `NonUnitalNonAssocRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalNonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.
Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S
] →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ
 S] →                       [inst_7 : NonUnitalNonAssocRing R] →                
         f 0 = 0 →                           (∀ (x y : R), f (x + y) = f x + f y
) →                             (∀ (x y : R), f (x * y) = f x * f y) →          
                     (∀ (x : R), f (-x) = -f x) →                               
  (∀ (x y : R), f (x - y) = f x - f y) →                                   (∀ (n
 : ℕ) (x : R), f (n • x) = n • f x) →                                     (∀ (n 
: ℤ) (x : R), f (n • x) = n • f x) → NonUnitalNonAssocRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocSemiring.left_distrib`：∀ {α : Type u} [self : NonUnital
NonAssocSemiring α] (a b c : α), a * (b + c) = a * b + a * c
· 使用定理 `NonUnitalNonAssocSemiring.right_distrib`：∀ {α : Type u} [self : NonUnita
lNonAssocSemiring α] (a b c : α), (a + b) * c = a * c + b * c
· 使用定理 `NonUnitalNonAssocSemiring.zero_mul`：∀ {α : Type u} [self : NonUnitalNonA
ssocSemiring α] (a : α), 0 * a = 0
· 使用定理 `NonUnitalNonAssocSemiring.mul_zero`：∀ {α : Type u} [self : NonUnitalNonA
ssocSemiring α] (a : α), a * 0 = 0
-/
protected abbrev nonUnitalNonAssocRing [NonUnitalNonAssocRing R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalNonAssocRing S where
  toAddCommGroup := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)
  __ := hf.nonUnitalNonAssocSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjecti
ve`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S
] →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ
 S] →                       [inst_7 : NonUnitalRing R] →                        
 f 0 = 0 →                           (∀ (x y : R), f (x + y) = f x + f y) →     
                        (∀ (x y : R), f (x * y) = f x * f y) →                  
             (∀ (x : R), f (-x) = -f x) →                                 (∀ (x 
y : R), f (x - y) = f x - f y) →                                   (∀ (n : ℕ) (x
 : R), f (n • x) = n • f x) →                                     (∀ (n : ℤ) (x 
: R), f (n • x) = n • f x) → NonUnitalRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSemiring.mul_assoc`：∀ {α : Type u} [self : NonUnitalSemiring α]
 (a b c : α), a * b * c = a * (b * c)
-/
protected abbrev nonUnitalRing [NonUnitalRing R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalSemiring f zero add mul nsmul

/-- Pushforward a `NonAssocRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S
] →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S]
 →                       [inst_7 : SMul ℤ S] →                         [inst_8 :
 NatCast S] →                           [inst_9 : IntCast S] →                  
           [inst_10 : NonAssocRing R] →                               f 0 = 0 → 
                                f 1 = 1 →                                   (∀ (
x y : R), f (x + y) = f x + f y) →                                     (∀ (x y :
 R), f (x * y) = f x * f y) →                                       (∀ (x : R), 
f (-x) = -f x) →                                         (∀ (x y : R), f (x - y)
 = f x - f y) →                                           (∀ (n : ℕ) (x : R), f 
(n • x) = n • f x) →                                             (∀ (n : ℤ) (x :
 R), f (n • x) = n • f x) →                                               (∀ (n 
: ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → NonAssocRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑
n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonAssocSemiring.one_mul`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), 1 * a = a
· 使用定理 `NonAssocSemiring.mul_one`：∀ {α : Type u} [self : NonAssocSemiring α] (a 
: α), a * 1 = a
· 使用定理 `NonAssocSemiring.natCast_zero`：∀ {α : Type u} [self : NonAssocSemiring α
], ↑0 = 0
· 使用定理 `NonAssocSemiring.natCast_succ`：∀ {α : Type u} [self : NonAssocSemiring α
] (n : ℕ), ↑(n + 1) = ↑n + 1
· 使用定理 `AddCommGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddCommGroupWi
thOne R] (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddCommGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddCommGroup
WithOne R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
-/
protected abbrev nonAssocRing [NonAssocRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.addCommGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast

/-- Pushforward a `Ring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.ring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S
] →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S]
 →                       [inst_7 : SMul ℤ S] →                         [inst_8 :
 Pow S ℕ] →                           [inst_9 : NatCast S] →                    
         [inst_10 : IntCast S] →                               [inst_11 : Ring R
] →                                 f 0 = 0 →                                   
f 1 = 1 →                                     (∀ (x y : R), f (x + y) = f x + f 
y) →                                       (∀ (x y : R), f (x * y) = f x * f y) 
→                                         (∀ (x : R), f (-x) = -f x) →          
                                 (∀ (x y : R), f (x - y) = f x - f y) →         
                                    (∀ (n : ℕ) (x : R), f (n • x) = n • f x) →  
                                             (∀ (n : ℤ) (x : R), f (n • x) = n •
 f x) →                                                 (∀ (x : R) (n : ℕ), f (x
 ^ n) = f x ^ n) →                                                   (∀ (n : ℕ),
 f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → Ring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x；∀ (x : R) (n : ℕ), 
f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AddGroupWithOne.sub_eq_add_neg`：∀ {R : Type u} [self : AddGroupWithOne R
] (a b : R), a - b = a + -b
· 使用定理 `AddGroupWithOne.zsmul_zero'`：∀ {R : Type u} [self : AddGroupWithOne R] (
a : R), 0 • a = 0
· 使用定理 `AddGroupWithOne.zsmul_succ'`：∀ {R : Type u} [self : AddGroupWithOne R] (
n : ℕ) (a : R), ↑n.succ • a = ↑n • a + a
· 使用定理 `AddGroupWithOne.zsmul_neg'`：∀ {R : Type u} [self : AddGroupWithOne R] (n
 : ℕ) (a : R), Int.negSucc n • a = -(↑n.succ • a)
· 使用定理 `AddGroupWithOne.neg_add_cancel`：∀ {R : Type u} [self : AddGroupWithOne R
] (a : R), -a + a = 0
· 使用定理 `AddGroupWithOne.intCast_ofNat`：∀ {R : Type u} [self : AddGroupWithOne R]
 (n : ℕ), IntCast.intCast ↑n = ↑n
· 使用定理 `AddGroupWithOne.intCast_negSucc`：∀ {R : Type u} [self : AddGroupWithOne 
R] (n : ℕ), IntCast.intCast (Int.negSucc n) = -↑(n + 1)
-/
protected abbrev ring [Ring R] (zero : f 0 = 0) (one : f 1 = 1) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (natCast : ∀ n : ℕ, f n = n)
    (intCast : ∀ n : ℤ, f n = n) : Ring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.addGroupWithOne f zero one add neg sub nsmul zsmul natCast intCast
  __ := hf.addCommGroup f zero add neg sub (swap nsmul) (swap zsmul)

/-- Pushforward a `NonUnitalNonAssocCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalNonAssocCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `F
unction.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : No
nUnitalNonAssocCommSemiring R] →                   f 0 = 0 →                    
 (∀ (x y : R), f (x + y) = f x + f y) →                       (∀ (x y : R), f (x
 * y) = f x * f y) →                         (∀ (n : ℕ) (x : R), f (n • x) = n •
 f x) → NonUnitalNonAssocCommSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMagma.mul_comm`：∀ {G : Type u} [self : CommMagma G] (a b : G), a * b
 = b * a
-/
protected abbrev nonUnitalNonAssocCommSemiring [NonUnitalNonAssocCommSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommSemiring S where
  toNonUnitalNonAssocSemiring := hf.nonUnitalNonAssocSemiring f zero add mul nsmul
  __ := hf.commMagma f mul

/-- Pushforward a `NonUnitalCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.
Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : SMul ℕ S] →                 [inst_4 : No
nUnitalCommSemiring R] →                   f 0 = 0 →                     (∀ (x y
 : R), f (x + y) = f x + f y) →                       (∀ (x y : R), f (x * y) = 
f x * f y) →                         (∀ (n : ℕ) (x : R), f (n • x) = n • f x) → 
NonUnitalCommSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemigroup.mul_comm`：∀ {G : Type u} [self : CommSemigroup G] (a b : G
), a * b = b * a
-/
protected abbrev nonUnitalCommSemiring [NonUnitalCommSemiring R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) : NonUnitalCommSemiring S where
  toNonUnitalSemiring := hf.nonUnitalSemiring f zero add mul nsmul
  __ := hf.commSemigroup f mul

/-- Pushforward a `NonAssocCommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonAssocCommSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.S
urjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul 
ℕ S] →                   [inst_5 : NatCast S] →                     [inst_6 : No
nAssocCommSemiring R] →                       f 0 = 0 →                         
f 1 = 1 →                           (∀ (x y : R), f (x + y) = f x + f y) →      
                       (∀ (x y : R), f (x * y) = f x * f y) →                   
            (∀ (n : ℕ) (x : R), f (n • x) = n • f x) → (∀ (n : ℕ), f ↑n = ↑n) → 
NonAssocCommSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMagma.mul_comm`：∀ {G : Type u} [self : CommMagma G] (a b : G), a * b
 = b * a
-/
protected abbrev nonAssocCommSemiring [NonAssocCommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) : NonAssocCommSemiring S where
  toNonAssocSemiring := hf.nonAssocSemiring f zero one add mul nsmul natCast
  __ := hf.commMagma f mul

/-- Pushforward a `CommSemiring` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.commSemiring** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjectiv
e`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : SMul 
ℕ S] →                   [inst_5 : Pow S ℕ] →                     [inst_6 : NatC
ast S] →                       [inst_7 : CommSemiring R] →                      
   f 0 = 0 →                           f 1 = 1 →                             (∀ 
(x y : R), f (x + y) = f x + f y) →                               (∀ (x y : R), 
f (x * y) = f x * f y) →                                 (∀ (n : ℕ) (x : R), f (
n • x) = n • f x) →                                   (∀ (x : R) (n : ℕ), f (x ^
 n) = f x ^ n) → (∀ (n : ℕ), f ↑n = ↑n) → CommSemiring S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (n : ℕ) (x : R), f (n • x) = n • f x；∀ (x : R) (n : ℕ), f (x ^ n) = f x ^ n
；∀ (n : ℕ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommSemigroup.mul_comm`：∀ {G : Type u} [self : CommSemigroup G] (a b : G
), a * b = b * a
-/
protected abbrev commSemiring [CommSemiring R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) : CommSemiring S where
  toSemiring := hf.semiring f zero one add mul nsmul npow natCast
  __ := hf.commSemigroup f mul

/-- Pushforward a `NonUnitalNonAssocCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalNonAssocCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Funct
ion.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S
] →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ
 S] →                       [inst_7 : NonUnitalNonAssocCommRing R] →            
             f 0 = 0 →                           (∀ (x y : R), f (x + y) = f x +
 f y) →                             (∀ (x y : R), f (x * y) = f x * f y) →      
                         (∀ (x : R), f (-x) = -f x) →                           
      (∀ (x y : R), f (x - y) = f x - f y) →                                   (
∀ (n : ℕ) (x : R), f (n • x) = n • f x) →                                     (∀
 (n : ℤ) (x : R), f (n • x) = n • f x) → NonUnitalNonAssocCommRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommSemiring.mul_comm`：∀ {α : Type u} [self : NonUnital
NonAssocCommSemiring α] (a b : α), a * b = b * a
-/
protected abbrev nonUnitalNonAssocCommRing [NonUnitalNonAssocCommRing R]
    (zero : f 0 = 0) (add : ∀ x y, f (x + y) = f x + f y)
    (mul : ∀ x y, f (x * y) = f x * f y) (neg : ∀ x, f (-x) = -f x)
    (sub : ∀ x y, f (x - y) = f x - f y) (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x)
    (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) : NonUnitalNonAssocCommRing S where
  toNonUnitalNonAssocRing := hf.nonUnitalNonAssocRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommSemiring f zero add mul nsmul

/-- Pushforward a `NonUnitalCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonUnitalCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surj
ective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : Neg S] →                 [inst_4 : Sub S
] →                   [inst_5 : SMul ℕ S] →                     [inst_6 : SMul ℤ
 S] →                       [inst_7 : NonUnitalCommRing R] →                    
     f 0 = 0 →                           (∀ (x y : R), f (x + y) = f x + f y) → 
                            (∀ (x y : R), f (x * y) = f x * f y) →              
                 (∀ (x : R), f (-x) = -f x) →                                 (∀
 (x y : R), f (x - y) = f x - f y) →                                   (∀ (n : ℕ
) (x : R), f (n • x) = n • f x) →                                     (∀ (n : ℤ)
 (x : R), f (n • x) = n • f x) → NonUnitalCommRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalNonAssocCommRing.mul_comm`：∀ {α : Type u} [self : NonUnitalNonA
ssocCommRing α] (a b : α), a * b = b * a
-/
protected abbrev nonUnitalCommRing [NonUnitalCommRing R] (zero : f 0 = 0)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x) :
    NonUnitalCommRing S where
  toNonUnitalRing := hf.nonUnitalRing f zero add mul neg sub nsmul zsmul
  __ := hf.nonUnitalNonAssocCommRing f zero add mul neg sub nsmul zsmul

/-- Pushforward a `NonAssocCommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.nonAssocCommRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surje
ctive`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S
] →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S]
 →                       [inst_7 : SMul ℤ S] →                         [inst_8 :
 NatCast S] →                           [inst_9 : IntCast S] →                  
           [inst_10 : NonAssocCommRing R] →                               f 0 = 
0 →                                 f 1 = 1 →                                   
(∀ (x y : R), f (x + y) = f x + f y) →                                     (∀ (x
 y : R), f (x * y) = f x * f y) →                                       (∀ (x : 
R), f (-x) = -f x) →                                         (∀ (x y : R), f (x 
- y) = f x - f y) →                                           (∀ (n : ℕ) (x : R)
, f (n • x) = n • f x) →                                             (∀ (n : ℤ) 
(x : R), f (n • x) = n • f x) →                                               (∀
 (n : ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → NonAssocCommRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x；∀ (n : ℕ), f ↑n = ↑
n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `NonAssocCommSemiring.mul_comm`：∀ {α : Type u} [self : NonAssocCommSemiri
ng α] (a b : α), a * b = b * a
-/
protected abbrev nonAssocCommRing [NonAssocCommRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : NonAssocCommRing S where
  toNonAssocRing := hf.nonAssocRing f zero one add mul neg sub nsmul zsmul natCast intCast
  __ := hf.nonAssocCommSemiring f zero one add mul nsmul natCast

/-- Pushforward a `CommRing` instance along a surjective function. -/
-- See note [reducible non-instances]
/-
**Function.Surjective.commRing** 是 Mathlib 中的一个定义，位于命名空间 `Function.Surjective`。
形式化陈述：{R : Type u_1} →   {S : Type u_2} →     (f : R → S) →       Function.Surje
ctive f →         [inst : Add S] →           [inst_1 : Mul S] →             [ins
t_2 : Zero S] →               [inst_3 : One S] →                 [inst_4 : Neg S
] →                   [inst_5 : Sub S] →                     [inst_6 : SMul ℕ S]
 →                       [inst_7 : SMul ℤ S] →                         [inst_8 :
 Pow S ℕ] →                           [inst_9 : NatCast S] →                    
         [inst_10 : IntCast S] →                               [inst_11 : CommRi
ng R] →                                 f 0 = 0 →                               
    f 1 = 1 →                                     (∀ (x y : R), f (x + y) = f x 
+ f y) →                                       (∀ (x y : R), f (x * y) = f x * f
 y) →                                         (∀ (x : R), f (-x) = -f x) →      
                                     (∀ (x y : R), f (x - y) = f x - f y) →     
                                        (∀ (n : ℕ) (x : R), f (n • x) = n • f x)
 →                                               (∀ (n : ℤ) (x : R), f (n • x) =
 n • f x) →                                                 (∀ (x : R) (n : ℕ), 
f (x ^ n) = f x ^ n) →                                                   (∀ (n :
 ℕ), f ↑n = ↑n) → (∀ (n : ℤ), f ↑n = ↑n) → CommRing S
参数：f : R → S；∀ (x y : R), f (x + y) = f x + f y；∀ (x y : R), f (x * y) = f x * f
 y；∀ (x : R), f (-x) = -f x；∀ (x y : R), f (x - y) = f x - f y；∀ (n : ℕ) (x : R)
, f (n • x) = n • f x；∀ (n : ℤ) (x : R), f (n • x) = n • f x；∀ (x : R) (n : ℕ), 
f (x ^ n) = f x ^ n；∀ (n : ℕ), f ↑n = ↑n；∀ (n : ℤ), f ↑n = ↑n。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CommMonoid.mul_comm`：∀ {M : Type u} [self : CommMonoid M] (a b : M), a *
 b = b * a
-/
protected abbrev commRing [CommRing R] (zero : f 0 = 0) (one : f 1 = 1)
    (add : ∀ x y, f (x + y) = f x + f y) (mul : ∀ x y, f (x * y) = f x * f y)
    (neg : ∀ x, f (-x) = -f x) (sub : ∀ x y, f (x - y) = f x - f y)
    (nsmul : ∀ (n : ℕ) (x), f (n • x) = n • f x) (zsmul : ∀ (n : ℤ) (x), f (n • x) = n • f x)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (natCast : ∀ n : ℕ, f n = n) (intCast : ∀ n : ℤ, f n = n) : CommRing S where
  toRing := hf.ring f zero one add mul neg sub nsmul zsmul npow natCast intCast
  __ := hf.commMonoid f one mul npow

end Function.Surjective

variable [Mul R] [HasDistribNeg R]

/-
**AddOpposite.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AddOpposite.instHasDistribNeg : HasDistribNeg Rᵃᵒᵖ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AddOpposite.unop_injective`：∀ {α : Type u_1}, Function.Injective AddOppo
site.unop
· 使用定理 `AddOpposite.unop_mul`：∀ {α : Type u_1} [inst : Mul α] (a b : αᵃᵒᵖ), AddO
pposite.unop (a * b) = AddOpposite.unop a * AddOpposite.unop b
-/
instance AddOpposite.instHasDistribNeg : HasDistribNeg Rᵃᵒᵖ :=
  unop_injective.hasDistribNeg _ unop_neg unop_mul
