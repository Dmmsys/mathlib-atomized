/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Data.PFun
public import Mathlib.Data.Vector3
public import Mathlib.NumberTheory.PellMatiyasevic

/-!
# Diophantine functions and Matiyasevic's theorem

Hilbert's tenth problem asked whether there exists an algorithm which for a given integer polynomial
determines whether this polynomial has integer solutions. It was answered in the negative in 1970,
the final step being completed by Matiyasevic who showed that the power function is Diophantine.

Here a function is called Diophantine if its graph is Diophantine as a set. A subset `S ⊆ ℕ ^ α` in
turn is called Diophantine if there exists an integer polynomial on `α ⊕ β` such that `v ∈ S` iff
there exists `t : ℕ^β` with `p (v, t) = 0`.

## Main definitions

* `IsPoly`: a predicate stating that a function is a multivariate integer polynomial.
* `Poly`: the type of multivariate integer polynomial functions.
* `Dioph`: a predicate stating that a set is Diophantine, i.e. a set `S ⊆ ℕ^α` is
  Diophantine if there exists a polynomial on `α ⊕ β` such that `v ∈ S` iff there
  exists `t : ℕ^β` with `p (v, t) = 0`.
* `DiophFn`: a predicate on a function stating that it is Diophantine in the sense that its graph
  is Diophantine as a set.

## Main statements

* `pell_dioph` states that solutions to Pell's equation form a Diophantine set.
* `pow_dioph` states that the power function is Diophantine, a version of Matiyasevic's theorem.

## References

* [M. Carneiro, _A Lean formalization of Matiyasevic's theorem_][carneiro2018matiyasevic]
* [M. Davis, _Hilbert's tenth problem is unsolvable_][MR317916]

## Tags

Matiyasevic's theorem, Hilbert's tenth problem

## TODO

* Finish the solution of Hilbert's tenth problem.
* Connect `Poly` to `MvPolynomial`
-/

@[expose] public section


open Fin2 Function Nat Sum

local infixr:67 " ::ₒ " => Option.elim'

local infixr:65 " otimes " => Sum.elim

universe u

/-!
### Multivariate integer polynomials

Note that this duplicates `MvPolynomial`.
-/


section Polynomials

variable {α β : Type*}

/--
Inductive type `IsPoly` / 归纳类型 `IsPoly`

English:
inductive IsPoly
  parameters: : ((α -> Nat) -> Int) -> Prop
  constructors (4):
    - proj: forall i, IsPoly fun x : α -> Nat => x i
    - const: forall n : Int, IsPoly fun _ : α -> Nat => n
    - sub: forall {f g : (α -> Nat) -> Int}, IsPoly f -> IsPoly g -> IsPoly fun x => f x - g x
    - mul: forall {f g : (α -> Nat) -> Int}, IsPoly f -> IsPoly g -> IsPoly fun x => f x * g x

中文:
归纳类型 IsPoly
  参数: : ((α -> 自然数) -> 整数) -> 命题
  构造子 (4 个):
    - proj: 对任意 i, IsPoly fun x : α -> 自然数 => x i
    - const: 对任意 n : 整数, IsPoly fun _ : α -> 自然数 => n
    - sub: 对任意 {f g : (α -> 自然数) -> 整数}, IsPoly f -> IsPoly g -> IsPoly fun x => f x - g x
    - mul: 对任意 {f g : (α -> 自然数) -> 整数}, IsPoly f -> IsPoly g -> IsPoly fun x => f x * g x
-/
inductive IsPoly : ((α -> Nat) -> Int) -> Prop
  | proj : forall i, IsPoly fun x : α -> Nat => x i
  | const : forall n : Int, IsPoly fun _ : α -> Nat => n
  | sub : forall {f g : (α -> Nat) -> Int}, IsPoly f -> IsPoly g -> IsPoly fun x => f x - g x
  | mul : forall {f g : (α -> Nat) -> Int}, IsPoly f -> IsPoly g -> IsPoly fun x => f x * g x

/--
theorem `IsPoly.neg` / 定理 `IsPoly.neg`

English:
theorem IsPoly.neg
  given: {f : (α -> Nat) -> Int}
  statement: IsPoly f -> IsPoly (-f)
  proof: by
  rw [← zero_sub]; exact (IsPoly.const 0).sub

中文:
定理 IsPoly.neg
  条件: {f : (α -> 自然数) -> 整数}
  结论: IsPoly f -> IsPoly (-f)
  证明: by
  rw [← zero_sub]; exact (IsPoly.const 0).sub

Depends on / 依赖: IsPoly, IsPoly.const, zero_sub
-/
theorem IsPoly.neg {f : (α -> Nat) -> Int} : IsPoly f -> IsPoly (-f) := by
  rw [← zero_sub]; exact (IsPoly.const 0).sub

/--
theorem `IsPoly.add` / 定理 `IsPoly.add`

English:
theorem IsPoly.add
  given: {f g : (α -> Nat) -> Int} (hf : IsPoly f) (hg : IsPoly g)
  statement: IsPoly (f + g)
  proof: by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg

中文:
定理 IsPoly.add
  条件: {f g : (α -> 自然数) -> 整数} (hf : IsPoly f) (hg : IsPoly g)
  结论: IsPoly (f + g)
  证明: by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg

Depends on / 依赖: hf.sub, hg.neg, sub_neg_eq_add
-/
theorem IsPoly.add {f g : (α -> Nat) -> Int} (hf : IsPoly f) (hg : IsPoly g) : IsPoly (f + g) := by
  rw [← sub_neg_eq_add]; exact hf.sub hg.neg

/--
Definition of `Poly` / `Poly` 的定义

English:
definition Poly
  signature: (α : Type u)
  body: { f : (α -> Nat) -> Int // IsPoly f }

中文:
定义 Poly
  签名: (α : 类型u)
  定义体: { f : (α -> Nat) -> Int // IsPoly f }

Depends on / 依赖: IsPoly
-/
def Poly (α : Type u) := { f : (α -> Nat) -> Int // IsPoly f }

namespace Poly

section

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (Poly α) (α -> Nat) Int
  body: ⟨Subtype.val, Subtype.val_injective⟩

中文:
实例 instFunLike
  签名: : FunLike (Poly α) (α -> 自然数) 整数
  定义体: ⟨Subtype.val, Subtype.val_injective⟩

Depends on / 依赖: Subtype, Subtype.val, Subtype.val_injective, val_injective
-/
instance instFunLike : FunLike (Poly α) (α -> Nat) Int :=
  ⟨Subtype.val, Subtype.val_injective⟩

/--
theorem `isPoly` / 定理 `isPoly`

English:
theorem isPoly
  given: (f : Poly α)
  statement: IsPoly f
  proof: f.2

中文:
定理 isPoly
  条件: (f : Poly α)
  结论: IsPoly f
  证明: f.2
-/
protected theorem isPoly (f : Poly α) : IsPoly f := f.2

/-- Extensionality for `Poly α` -/
@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {f g : Poly α}
  statement: (forall x, f x = g x) -> f = g
  proof: DFunLike.ext _ _

中文:
定理 ext
  条件: {f g : Poly α}
  结论: (对任意 x, f x = g x) -> f = g
  证明: DFunLike.ext _ _

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {f g : Poly α} : (forall x, f x = g x) -> f = g := DFunLike.ext _ _

/--
Definition of `proj` / `proj` 的定义

English:
definition proj
  signature: (i : α)
  body: ⟨_, IsPoly.proj i⟩

@[simp]

中文:
定义 proj
  签名: (i : α)
  定义体: ⟨_, IsPoly.proj i⟩

@[simp]

Depends on / 依赖: IsPoly, IsPoly.proj
-/
def proj (i : α) : Poly α := ⟨_, IsPoly.proj i⟩

@[simp]
/--
theorem `proj_apply` / 定理 `proj_apply`

English:
theorem proj_apply
  given: (i : α) (x)
  statement: proj i x = x i
  proof: rfl

中文:
定理 proj_apply
  条件: (i : α) (x)
  结论: proj i x = x i
  证明: rfl
-/
theorem proj_apply (i : α) (x) : proj i x = x i := rfl

/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: (n : Int)
  body: ⟨_, IsPoly.const n⟩

@[simp]

中文:
定义 const
  签名: (n : 整数)
  定义体: ⟨_, IsPoly.const n⟩

@[simp]

Depends on / 依赖: IsPoly, IsPoly.const
-/
def const (n : Int) : Poly α := ⟨_, IsPoly.const n⟩

@[simp]
/--
theorem `const_apply` / 定理 `const_apply`

English:
theorem const_apply
  given: (n) (x : α -> Nat)
  statement: const n x = n
  proof: rfl

中文:
定理 const_apply
  条件: (n) (x : α -> 自然数)
  结论: const n x = n
  证明: rfl
-/
theorem const_apply (n) (x : α -> Nat) : const n x = n := rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero (Poly α)
  body: ⟨const 0⟩

中文:
实例 :
  签名: Zero (Poly α)
  定义体: ⟨const 0⟩
-/
instance : Zero (Poly α) := ⟨const 0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One (Poly α)
  body: ⟨const 1⟩

中文:
实例 :
  签名: One (Poly α)
  定义体: ⟨const 1⟩
-/
instance : One (Poly α) := ⟨const 1⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Neg (Poly α)
  body: ⟨fun f => ⟨-f, f.2.neg⟩⟩

中文:
实例 :
  签名: Neg (Poly α)
  定义体: ⟨fun f => ⟨-f, f.2.neg⟩⟩
-/
instance : Neg (Poly α) := ⟨fun f => ⟨-f, f.2.neg⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add (Poly α)
  body: ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

中文:
实例 :
  签名: Add (Poly α)
  定义体: ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩
-/
instance : Add (Poly α) := ⟨fun f g => ⟨f + g, f.2.add g.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Sub (Poly α)
  body: ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

中文:
实例 :
  签名: Sub (Poly α)
  定义体: ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩
-/
instance : Sub (Poly α) := ⟨fun f g => ⟨f - g, f.2.sub g.2⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul (Poly α)
  body: ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp]

中文:
实例 :
  签名: Mul (Poly α)
  定义体: ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp]
-/
instance : Mul (Poly α) := ⟨fun f g => ⟨f * g, f.2.mul g.2⟩⟩

@[simp]
/--
theorem `coe_zero` / 定理 `coe_zero`

English:
theorem coe_zero
  statement: ⇑(0 : Poly α) = const 0
  proof: rfl

@[simp]

中文:
定理 coe_zero
  结论: ⇑(0 : Poly α) = const 0
  证明: rfl

@[simp]

Depends on / 依赖: RelEmbedding, RelEmbedding.instFunLike, instFunLike
-/
theorem coe_zero : ⇑(0 : Poly α) = const 0 := rfl

@[simp]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  statement: ⇑(1 : Poly α) = const 1
  proof: rfl

@[simp]

中文:
定理 coe_one
  结论: ⇑(1 : Poly α) = const 1
  证明: rfl

@[simp]

Depends on / 依赖: RelIso, RelIso.instFunLike, instFunLike
-/
theorem coe_one : ⇑(1 : Poly α) = const 1 := rfl

@[simp]
/--
theorem `coe_neg` / 定理 `coe_neg`

English:
theorem coe_neg
  given: (f : Poly α)
  statement: ⇑(-f) = -f
  proof: rfl

@[simp]

中文:
定理 coe_neg
  条件: (f : Poly α)
  结论: ⇑(-f) = -f
  证明: rfl

@[simp]
-/
theorem coe_neg (f : Poly α) : ⇑(-f) = -f := rfl

@[simp]
/--
theorem `coe_add` / 定理 `coe_add`

English:
theorem coe_add
  given: (f g : Poly α)
  statement: ⇑(f + g) = f + g
  proof: rfl

@[simp]

中文:
定理 coe_add
  条件: (f g : Poly α)
  结论: ⇑(f + g) = f + g
  证明: rfl

@[simp]
-/
theorem coe_add (f g : Poly α) : ⇑(f + g) = f + g := rfl

@[simp]
/--
theorem `coe_sub` / 定理 `coe_sub`

English:
theorem coe_sub
  given: (f g : Poly α)
  statement: ⇑(f - g) = f - g
  proof: rfl

@[simp]

中文:
定理 coe_sub
  条件: (f g : Poly α)
  结论: ⇑(f - g) = f - g
  证明: rfl

@[simp]

Depends on / 依赖: OrderIsoClass, OrderIsoClass.toOrderIso, toOrderIso
-/
theorem coe_sub (f g : Poly α) : ⇑(f - g) = f - g := rfl

@[simp]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: (f g : Poly α)
  statement: ⇑(f * g) = f * g
  proof: rfl

@[simp]

中文:
定理 coe_mul
  条件: (f g : Poly α)
  结论: ⇑(f * g) = f * g
  证明: rfl

@[simp]

Depends on / 依赖: OrderIsoClass, OrderIsoClass.toOrderHomClass, toOrderHomClass
-/
theorem coe_mul (f g : Poly α) : ⇑(f * g) = f * g := rfl

@[simp]
/--
theorem `zero_apply` / 定理 `zero_apply`

English:
theorem zero_apply
  given: (x)
  statement: (0 : Poly α) x = 0
  proof: rfl

@[simp]

中文:
定理 zero_apply
  条件: (x)
  结论: (0 : Poly α) x = 0
  证明: rfl

@[simp]
-/
theorem zero_apply (x) : (0 : Poly α) x = 0 := rfl

@[simp]
/--
theorem `one_apply` / 定理 `one_apply`

English:
theorem one_apply
  given: (x)
  statement: (1 : Poly α) x = 1
  proof: rfl

@[simp]

中文:
定理 one_apply
  条件: (x)
  结论: (1 : Poly α) x = 1
  证明: rfl

@[simp]
-/
theorem one_apply (x) : (1 : Poly α) x = 1 := rfl

@[simp]
/--
theorem `neg_apply` / 定理 `neg_apply`

English:
theorem neg_apply
  given: (f : Poly α) (x)
  statement: (-f) x = -f x
  proof: rfl

@[simp]

中文:
定理 neg_apply
  条件: (f : Poly α) (x)
  结论: (-f) x = -f x
  证明: rfl

@[simp]
-/
theorem neg_apply (f : Poly α) (x) : (-f) x = -f x := rfl

@[simp]
/--
theorem `add_apply` / 定理 `add_apply`

English:
theorem add_apply
  given: (f g : Poly α) (x : α -> Nat)
  statement: (f + g) x = f x + g x
  proof: rfl

@[simp]

中文:
定理 add_apply
  条件: (f g : Poly α) (x : α -> 自然数)
  结论: (f + g) x = f x + g x
  证明: rfl

@[simp]
-/
theorem add_apply (f g : Poly α) (x : α -> Nat) : (f + g) x = f x + g x := rfl

@[simp]
/--
theorem `sub_apply` / 定理 `sub_apply`

English:
theorem sub_apply
  given: (f g : Poly α) (x : α -> Nat)
  statement: (f - g) x = f x - g x
  proof: rfl

@[simp]

中文:
定理 sub_apply
  条件: (f g : Poly α) (x : α -> 自然数)
  结论: (f - g) x = f x - g x
  证明: rfl

@[simp]
-/
theorem sub_apply (f g : Poly α) (x : α -> Nat) : (f - g) x = f x - g x := rfl

@[simp]
/--
theorem `mul_apply` / 定理 `mul_apply`

English:
theorem mul_apply
  given: (f g : Poly α) (x : α -> Nat)
  statement: (f * g) x = f x * g x
  proof: rfl

中文:
定理 mul_apply
  条件: (f g : Poly α) (x : α -> 自然数)
  结论: (f * g) x = f x * g x
  证明: rfl
-/
theorem mul_apply (f g : Poly α) (x : α -> Nat) : (f * g) x = f x * g x := rfl

instance (α : Type*) : Inhabited (Poly α) := ⟨0⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddCommGroup (Poly α)
  body: @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩)
  add_zero _ := by ext; simp_rw [add_apply, zero_apply, add_zero]
  zero_add _ := by ext; simp_rw [add_apply, zero_apply, zero_add]
  add_comm _ _ := by ext; simp_rw 

中文:
实例 :
  签名: AddCommGroup (Poly α)
  定义体: @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩)
  add_zero _ := by ext; simp_rw [add_apply, zero_apply, add_zero]
  zero_add _ := by ext; simp_rw [add_apply, zero_apply, zero_add]
  add_comm _ _ := by ext; simp_rw 

Depends on / 依赖: nsmulRec
-/
instance : AddCommGroup (Poly α) where
  nsmul := @nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩
  zsmul := @zsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec _ ⟨(0 : Poly α)⟩ ⟨(· + ·)⟩)
  add_zero _ := by ext; simp_rw [add_apply, zero_apply, add_zero]
  zero_add _ := by ext; simp_rw [add_apply, zero_apply, zero_add]
  add_comm _ _ := by ext; simp_rw [add_apply, add_comm]
  add_assoc _ _ _ := by ext; simp_rw [add_apply, ← add_assoc]
  neg_add_cancel _ := by ext; simp_rw [add_apply, neg_apply, neg_add_cancel, zero_apply]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: AddGroupWithOne (Poly α)
  body: fun n => Poly.const n
  intCast := Poly.const

中文:
实例 :
  签名: AddGroupWithOne (Poly α)
  定义体: fun n => Poly.const n
  intCast := Poly.const

Depends on / 依赖: Poly.const
-/
instance : AddGroupWithOne (Poly α) where
  natCast := fun n => Poly.const n
  intCast := Poly.const

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CommRing (Poly α)
  body: (inferInstance : AddCommGroup (Poly α))
  __ := (inferInstance : AddGroupWithOne (Poly α))
  npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨(· * ·)⟩
  mul_zero _ := by ext; rw [mul_apply, zero_apply, mul_zero]
  zero_mul _ := by ext; rw [mul_apply, zero_apply, zero_mul]
  mul_one _ := by ext; rw [mul_apply, one

中文:
实例 :
  签名: CommRing (Poly α)
  定义体: (inferInstance : AddCommGroup (Poly α))
  __ := (inferInstance : AddGroupWithOne (Poly α))
  npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨(· * ·)⟩
  mul_zero _ := by ext; rw [mul_apply, zero_apply, mul_zero]
  zero_mul _ := by ext; rw [mul_apply, zero_apply, zero_mul]
  mul_one _ := by ext; rw [mul_apply, one

Depends on / 依赖: AddCommGroup
-/
instance : CommRing (Poly α) where
  __ := (inferInstance : AddCommGroup (Poly α))
  __ := (inferInstance : AddGroupWithOne (Poly α))
  npow := @npowRec _ ⟨(1 : Poly α)⟩ ⟨(· * ·)⟩
  mul_zero _ := by ext; rw [mul_apply, zero_apply, mul_zero]
  zero_mul _ := by ext; rw [mul_apply, zero_apply, zero_mul]
  mul_one _ := by ext; rw [mul_apply, one_apply, mul_one]
  one_mul _ := by ext; rw [mul_apply, one_apply, one_mul]
  mul_comm _ _ := by ext; simp_rw [mul_apply, mul_comm]
  mul_assoc _ _ _ := by ext; simp_rw [mul_apply, mul_assoc]
  left_distrib _ _ _ := by ext; simp_rw [add_apply, mul_apply]; apply mul_add
  right_distrib _ _ _ := by ext; simp only [add_apply, mul_apply]; apply add_mul

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {C : Poly α -> Prop} (H1 : forall i, C (proj i)) (H2 : forall n, C (const n))
  proof: by
  obtain ⟨f, pf⟩ := f
  induction pf with
  | proj => apply H1
  | const => apply H2
  | sub _ _ ihf ihg => apply H3 _ _ ihf ihg
  | mul _ _ ihf ihg => apply H4 _ _ ihf ihg

中文:
定理 induction
  结论: {C : Poly α -> 命题} (H1 : 对任意 i, C (proj i)) (H2 : 对任意 n, C (const n))
  证明: by
  obtain ⟨f, pf⟩ := f
  induction pf with
  | proj => apply H1
  | const => apply H2
  | sub _ _ ihf ihg => apply H3 _ _ ihf ihg
  | mul _ _ ihf ihg => apply H4 _ _ ihf ihg
-/
theorem induction {C : Poly α -> Prop} (H1 : forall i, C (proj i)) (H2 : forall n, C (const n))
    (H3 : forall f g, C f -> C g -> C (f - g)) (H4 : forall f g, C f -> C g -> C (f * g)) (f : Poly α) : C f := by
  obtain ⟨f, pf⟩ := f
  induction pf with
  | proj => apply H1
  | const => apply H2
  | sub _ _ ihf ihg => apply H3 _ _ ihf ihg
  | mul _ _ ihf ihg => apply H4 _ _ ihf ihg

/--
Definition of `sumsq` / `sumsq` 的定义

English:
definition sumsq
  signature: : List (Poly α) -> Poly α

中文:
定义 sumsq
  签名: : List (Poly α) -> Poly α
-/
def sumsq : List (Poly α) -> Poly α
  | [] => 0
  | p::ps => p * p + sumsq ps

/--
theorem `sumsq_nonneg` / 定理 `sumsq_nonneg`

English:
theorem sumsq_nonneg
  given: (x : α -> Nat)
  statement: forall l, 0 <= sumsq l x

中文:
定理 sumsq_nonneg
  条件: (x : α -> 自然数)
  结论: 对任意 l, 0 <= sumsq l x
-/
@[simp] theorem sumsq_nonneg (x : α -> Nat) : forall l, 0 <= sumsq l x
  | [] => le_refl 0
  | p::ps => by
    rw [sumsq]
    exact add_nonneg (mul_self_nonneg _) (sumsq_nonneg _ ps)

/--
theorem `sumsq_eq_zero` / 定理 `sumsq_eq_zero`

English:
theorem sumsq_eq_zero
  given: (x)
  statement: forall l, sumsq l x = 0 ↔ l.Forall fun a : Poly α => a x = 0

中文:
定理 sumsq_eq_zero
  条件: (x)
  结论: 对任意 l, sumsq l x = 0 ↔ l.Forall fun a : Poly α => a x = 0
-/
theorem sumsq_eq_zero (x) : forall l, sumsq l x = 0 ↔ l.Forall fun a : Poly α => a x = 0
  | [] => eq_self_iff_true _
  | p::ps => by simp [sumsq, add_eq_zero_iff_of_nonneg, mul_self_nonneg, sumsq_eq_zero]

end

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: {α β} (f : α -> β) (g : Poly α)
  body: ⟨fun v => g v ∘ f, Poly.induction (C := fun g => IsPoly (fun v => g (v ∘ f)))
    (fun i => by simpa using IsPoly.proj _) (fun n => by simpa using IsPoly.const _)
    (fun f g pf pg => by simpa using IsPoly.sub pf pg)
    (fun f g pf pg => by simpa using IsPoly.mul pf pg) _⟩

@[simp]

中文:
定义 map
  签名: {α β} (f : α -> β) (g : Poly α)
  定义体: ⟨fun v => g v ∘ f, Poly.induction (C := fun g => IsPoly (fun v => g (v ∘ f)))
    (fun i => by simpa using IsPoly.proj _) (fun n => by simpa using IsPoly.const _)
    (fun f g pf pg => by simpa using IsPoly.sub pf pg)
    (fun f g pf pg => by simpa using IsPoly.mul pf pg) _⟩

@[simp]

Depends on / 依赖: IsPoly, IsPoly.const, IsPoly.mul, IsPoly.proj, IsPoly.sub, Poly.induction
-/
def map {α β} (f : α -> β) (g : Poly α) : Poly β :=
⟨fun v => g v ∘ f, Poly.induction (C := fun g => IsPoly (fun v => g (v ∘ f)))
    (fun i => by simpa using IsPoly.proj _) (fun n => by simpa using IsPoly.const _)
    (fun f g pf pg => by simpa using IsPoly.sub pf pg)
    (fun f g pf pg => by simpa using IsPoly.mul pf pg) _⟩

@[simp]
/--
theorem `map_apply` / 定理 `map_apply`

English:
theorem map_apply
  given: {α β} (f : α -> β) (g : Poly α) (v)
  statement: map f g v = g (v ∘ f)
  proof: rfl

中文:
定理 map_apply
  条件: {α β} (f : α -> β) (g : Poly α) (v)
  结论: map f g v = g (v ∘ f)
  证明: rfl
-/
theorem map_apply {α β} (f : α -> β) (g : Poly α) (v) : map f g v = g (v ∘ f) := rfl

end Poly

end Polynomials

/-! ### Diophantine sets -/


/--
Definition of `Dioph` / `Dioph` 的定义

English:
definition Dioph
  signature: {α : Type u} (S : Set (α -> Nat))
  body: exists (β : Type u) (p : Poly (α oplus β)), forall v, v in S ↔ exists t, p (v otimes t) = 0

中文:
定义 Dioph
  签名: {α : 类型u} (S : Set (α -> 自然数))
  定义体: exists (β : Type u) (p : Poly (α oplus β)), forall v, v in S ↔ exists t, p (v otimes t) = 0

Depends on / 依赖: otimes
-/
def Dioph {α : Type u} (S : Set (α -> Nat)) : Prop :=
  exists (β : Type u) (p : Poly (α oplus β)), forall v, v in S ↔ exists t, p (v otimes t) = 0

namespace Dioph

section

variable {α β γ : Type u} {S S' : Set (α -> Nat)}

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: (d : Dioph S) (H : forall v, v in S ↔ v in S')
  statement: Dioph S'
  proof: by rwa [← Set.ext H]

中文:
定理 ext
  条件: (d : Dioph S) (H : 对任意 v, v in S ↔ v in S')
  结论: Dioph S'
  证明: by rwa [← Set.ext H]

Depends on / 依赖: Set.ext
-/
theorem ext (d : Dioph S) (H : forall v, v in S ↔ v in S') : Dioph S' := by rwa [← Set.ext H]

/--
theorem `of_no_dummies` / 定理 `of_no_dummies`

English:
theorem of_no_dummies
  given: (S : Set (α -> Nat)) (p : Poly α) (h : forall v, v in S ↔ p v = 0)
  statement: Dioph S
  proof: ⟨PEmpty, ⟨p.map inl, fun v => (h v).trans ⟨fun h => ⟨PEmpty.elim, h⟩, fun ⟨_, ht⟩ => ht⟩⟩⟩

中文:
定理 of_no_dummies
  条件: (S : Set (α -> 自然数)) (p : Poly α) (h : 对任意 v, v in S ↔ p v = 0)
  结论: Dioph S
  证明: ⟨PEmpty, ⟨p.map inl, fun v => (h v).trans ⟨fun h => ⟨PEmpty.elim, h⟩, fun ⟨_, ht⟩ => ht⟩⟩⟩

Depends on / 依赖: PEmpty, PEmpty.elim, p.map
-/
theorem of_no_dummies (S : Set (α -> Nat)) (p : Poly α) (h : forall v, v in S ↔ p v = 0) : Dioph S :=
  ⟨PEmpty, ⟨p.map inl, fun v => (h v).trans ⟨fun h => ⟨PEmpty.elim, h⟩, fun ⟨_, ht⟩ => ht⟩⟩⟩

/--
theorem `inject_dummies_lem` / 定理 `inject_dummies_lem`

English:
theorem inject_dummies_lem
  statement: (f : β -> γ) (g : γ -> Option β) (inv : forall x, g (f x) = some x)
  proof: by
  dsimp; refine ⟨fun t => ?_, fun t => ?_⟩ <;> obtain ⟨t, ht⟩ := t
  · have : (v otimes (0 ::ₒ t) ∘ g) ∘ (inl otimes inr ∘ f) = v otimes t :=
      funext fun s => by rcases s with a | b <;> dsimp [(· ∘ ·)]; try rw [inv]; rfl
    exact ⟨(0 ::ₒ t) ∘ g, by rwa [this]⟩
  · have : v otimes t ∘ f = (v

中文:
定理 inject_dummies_lem
  结论: (f : β -> γ) (g : γ -> Option β) (inv : 对任意 x, g (f x) = some x)
  证明: by
  dsimp; refine ⟨fun t => ?_, fun t => ?_⟩ <;> obtain ⟨t, ht⟩ := t
  · have : (v otimes (0 ::ₒ t) ∘ g) ∘ (inl otimes inr ∘ f) = v otimes t :=
      funext fun s => by rcases s with a | b <;> dsimp [(· ∘ ·)]; try rw [inv]; rfl
    exact ⟨(0 ::ₒ t) ∘ g, by rwa [this]⟩
  · have : v otimes t ∘ f = (v

Depends on / 依赖: PartialOrder, PartialOrder.lift, otimes
-/
theorem inject_dummies_lem (f : β -> γ) (g : γ -> Option β) (inv : forall x, g (f x) = some x)
    (p : Poly (α oplus β)) (v : α -> Nat) :
    (exists t, p (v otimes t) = 0) ↔ exists t, p.map (inl otimes inr ∘ f) (v otimes t) = 0 := by
  dsimp; refine ⟨fun t => ?_, fun t => ?_⟩ <;> obtain ⟨t, ht⟩ := t
  · have : (v otimes (0 ::ₒ t) ∘ g) ∘ (inl otimes inr ∘ f) = v otimes t :=
      funext fun s => by rcases s with a | b <;> dsimp [(· ∘ ·)]; try rw [inv]; rfl
    exact ⟨(0 ::ₒ t) ∘ g, by rwa [this]⟩
  · have : v otimes t ∘ f = (v otimes t) ∘ (inl otimes inr ∘ f) := funext fun s => by rcases s with a | b <;> rfl
    exact ⟨t ∘ f, by rwa [this]⟩

/--
theorem `inject_dummies` / 定理 `inject_dummies`

English:
theorem inject_dummies
  statement: (f : β -> γ) (g : γ -> Option β) (inv : forall x, g (f x) = some x)
  proof: ⟨p.map (inl otimes inr ∘ f), fun v => (h v).trans inject_dummies_lem f g inv _ _⟩

中文:
定理 inject_dummies
  结论: (f : β -> γ) (g : γ -> Option β) (inv : 对任意 x, g (f x) = some x)
  证明: ⟨p.map (inl otimes inr ∘ f), fun v => (h v).trans inject_dummies_lem f g inv _ _⟩

Depends on / 依赖: inject_dummies_lem, otimes, p.map
-/
theorem inject_dummies (f : β -> γ) (g : γ -> Option β) (inv : forall x, g (f x) = some x)
    (p : Poly (α oplus β)) (h : forall v, v in S ↔ exists t, p (v otimes t) = 0) :
    exists q : Poly (α oplus γ), forall v, v in S ↔ exists t, q (v otimes t) = 0 :=
⟨p.map (inl otimes inr ∘ f), fun v => (h v).trans inject_dummies_lem f g inv _ _⟩

variable (β) in
/--
theorem `reindex_dioph` / 定理 `reindex_dioph`

English:
theorem reindex_dioph
  given: (f : α -> β)
  statement: Dioph S -> Dioph {v | v ∘ f in S}

中文:
定理 reindex_dioph
  条件: (f : α -> β)
  结论: Dioph S -> Dioph {v | v ∘ f in S}
-/
theorem reindex_dioph (f : α -> β) : Dioph S -> Dioph {v | v ∘ f in S}
  | ⟨γ, p, pe⟩ => ⟨γ, p.map (inl ∘ f otimes inr), fun v =>
(pe _).trans
        exists_congr fun t =>
          suffices v ∘ f otimes t = (v otimes t) ∘ (inl ∘ f otimes inr) by simp [this]
          funext fun s => by rcases s with a | b <;> rfl⟩

/--
theorem `DiophList.forall` / 定理 `DiophList.forall`

English:
theorem DiophList.forall
  given: (l : List (Set <| α -> Nat)) (d : l.Forall Dioph)
  proof: by
  suffices exists (β : _) (pl : List (Poly (α oplus β))), forall v, List.Forall (fun S : Set _ => v in S) l ↔
          exists t, List.Forall (fun p : Poly (α oplus β) => p (v otimes t) = 0) pl
    from
    let ⟨β, pl, h⟩ := this
⟨β, Poly.sumsq pl, fun v => (h v).trans exists_congr fun t => (Poly

中文:
定理 DiophList.forall
  条件: (l : List (Set <| α -> 自然数)) (d : l.Forall Dioph)
  证明: by
  suffices exists (β : _) (pl : List (Poly (α oplus β))), forall v, List.Forall (fun S : Set _ => v in S) l ↔
          exists t, List.Forall (fun p : Poly (α oplus β) => p (v otimes t) = 0) pl
    from
    let ⟨β, pl, h⟩ := this
⟨β, Poly.sumsq pl, fun v => (h v).trans exists_congr fun t => (Poly

Depends on / 依赖: Forall, List.Forall, List.forall_cons, Poly.sumsq, Poly.sumsq_eq_zero, exists_congr, forall_cons, otimes, p.map, sumsq_eq_zero
-/
theorem DiophList.forall (l : List (Set <| α -> Nat)) (d : l.Forall Dioph) :
    Dioph {v | l.Forall fun S : Set (α -> Nat) => v in S} := by
  suffices exists (β : _) (pl : List (Poly (α oplus β))), forall v, List.Forall (fun S : Set _ => v in S) l ↔
          exists t, List.Forall (fun p : Poly (α oplus β) => p (v otimes t) = 0) pl
    from
    let ⟨β, pl, h⟩ := this
⟨β, Poly.sumsq pl, fun v => (h v).trans exists_congr fun t => (Poly.sumsq_eq_zero _ _).symm⟩
  induction l with | nil => exact ⟨ULift Empty, [], fun _ => by simp⟩ | cons S l IH =>
  obtain ⟨⟨β, p, pe⟩, dl⟩ := (List.forall_cons _ _ _).mp d
  exact
    let ⟨γ, pl, ple⟩ := IH dl
    ⟨β oplus γ, p.map (inl otimes inr ∘ inl)::pl.map fun q => q.map (inl otimes inr ∘ inr),
      fun v => by
      simpa using
        Iff.trans (and_congr (pe v) (ple v))
          ⟨fun ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ =>
            ⟨m otimes n, by
              rw [show (v otimes m otimes n) ∘ (inl otimes inr ∘ inl) = v otimes m from
                    funext fun s => by rcases s with a | b <;> rfl]; exact hm, by
              refine List.Forall.imp (fun q hq => ?_) hn; dsimp [Function.comp_def]
              rw [show
                    (fun x : α oplus γ => (v otimes m otimes n) ((inl otimes fun x : γ => inr (inr x)) x)) = v otimes n
                    from funext fun s => by rcases s with a | b <;> rfl]; exact hq⟩,
            fun ⟨t, hl, hr⟩ =>
            ⟨⟨t ∘ inl, by
                rwa [show (v otimes t) ∘ (inl otimes inr ∘ inl) = v otimes t ∘ inl from
                    funext fun s => by rcases s with a | b <;> rfl] at hl⟩,
              ⟨t ∘ inr, by
                refine List.Forall.imp (fun q hq => ?_) hr; dsimp [Function.comp_def] at hq
                rwa [show
                    (fun x : α oplus γ => (v otimes t) ((inl otimes fun x : γ => inr (inr x)) x)) =
                      v otimes t ∘ inr
                    from funext fun s => by rcases s with a | b <;> rfl] at hq ⟩⟩⟩⟩

/--
theorem `inter` / 定理 `inter`

English:
theorem inter
  given: (d : Dioph S) (d' : Dioph S')
  statement: Dioph (S inter S')
  proof: DiophList.forall [S, S'] ⟨d, d'⟩

中文:
定理 inter
  条件: (d : Dioph S) (d' : Dioph S')
  结论: Dioph (S inter S')
  证明: DiophList.forall [S, S'] ⟨d, d'⟩

Depends on / 依赖: DiophList, DiophList.forall
-/
theorem inter (d : Dioph S) (d' : Dioph S') : Dioph (S inter S') := DiophList.forall [S, S'] ⟨d, d'⟩

/--
theorem `union` / 定理 `union`

English:
theorem union
  statement: forall (_ : Dioph S) (_ : Dioph S'), Dioph (S union S')

中文:
定理 union
  结论: 对任意 (_ : Dioph S) (_ : Dioph S'), Dioph (S union S')
-/
theorem union : forall (_ : Dioph S) (_ : Dioph S'), Dioph (S union S')
  | ⟨β, p, pe⟩, ⟨γ, q, qe⟩ =>
    ⟨β oplus γ, p.map (inl otimes inr ∘ inl) * q.map (inl otimes inr ∘ inr), fun v => by
      refine
        Iff.trans (or_congr ((pe v).trans ?_) ((qe v).trans ?_))
          (exists_or.symm.trans
            (exists_congr fun t =>
              (@mul_eq_zero _ _ _ (p ((v otimes t) ∘ (inl otimes inr ∘ inl)))
                  (q ((v otimes t) ∘ (inl otimes inr ∘ inr)))).symm))
      · -- Porting note: putting everything on the same line fails
        refine inject_dummies_lem _ (some otimes fun _ => none) ?_ _ _
        exact fun _ => by simp only [elim_inl]
      · -- Porting note: putting everything on the same line fails
        refine inject_dummies_lem _ ((fun _ => none) otimes some) ?_ _ _
        exact fun _ => by simp only [elim_inr]⟩

/--
Definition of `DiophPFun` / `DiophPFun` 的定义

English:
definition DiophPFun
  signature: (f : (α -> Nat) ->. Nat)
  body: Dioph {v : Option α -> Nat | (v ∘ some, v none) in f.graph}

中文:
定义 DiophPFun
  签名: (f : (α -> 自然数) ->. 自然数)
  定义体: Dioph {v : Option α -> Nat | (v ∘ some, v none) in f.graph}

Depends on / 依赖: f.graph
-/
def DiophPFun (f : (α -> Nat) ->. Nat) : Prop :=
  Dioph {v : Option α -> Nat | (v ∘ some, v none) in f.graph}

/--
Definition of `DiophFn` / `DiophFn` 的定义

English:
definition DiophFn
  signature: (f : (α -> Nat) -> Nat)
  body: Dioph {v : Option α -> Nat | f (v ∘ some) = v none}

中文:
定义 DiophFn
  签名: (f : (α -> 自然数) -> 自然数)
  定义体: Dioph {v : Option α -> Nat | f (v ∘ some) = v none}
-/
def DiophFn (f : (α -> Nat) -> Nat) : Prop :=
  Dioph {v : Option α -> Nat | f (v ∘ some) = v none}

/--
theorem `reindex_diophFn` / 定理 `reindex_diophFn`

English:
theorem reindex_diophFn
  given: {f : (α -> Nat) -> Nat} (g : α -> β) (d : DiophFn f)
  proof: by convert! reindex_dioph (Option β) (Option.map g) d

中文:
定理 reindex_diophFn
  条件: {f : (α -> 自然数) -> 自然数} (g : α -> β) (d : DiophFn f)
  证明: by convert! reindex_dioph (Option β) (Option.map g) d

Depends on / 依赖: Option.map, convert, reindex_dioph
-/
theorem reindex_diophFn {f : (α -> Nat) -> Nat} (g : α -> β) (d : DiophFn f) :
    DiophFn fun v => f (v ∘ g) := by convert! reindex_dioph (Option β) (Option.map g) d

/--
theorem `ex_dioph` / 定理 `ex_dioph`

English:
theorem ex_dioph
  given: {S : Set (α oplus β -> Nat)}
  statement: Dioph S -> Dioph {v | exists x, v otimes x in S}
  proof: (pe _).1 hx
        ⟨x otimes t, by
          simp only [Poly.map_apply]
          rw [show (v otimes x otimes t) ∘ ((inl otimes inr ∘ inl) otimes inr ∘ inr) = (v otimes x) otimes t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl]
          exact ht⟩,
       

中文:
定理 ex_dioph
  条件: {S : Set (α oplus β -> 自然数)}
  结论: Dioph S -> Dioph {v | 存在 x, v otimes x in S}
  证明: (pe _).1 hx
        ⟨x otimes t, by
          simp only [Poly.map_apply]
          rw [show (v otimes x otimes t) ∘ ((inl otimes inr ∘ inl) otimes inr ∘ inr) = (v otimes x) otimes t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl]
          exact ht⟩,
       
-/
theorem ex_dioph {S : Set (α oplus β -> Nat)} : Dioph S -> Dioph {v | exists x, v otimes x in S}
  | ⟨γ, p, pe⟩ =>
    ⟨β oplus γ, p.map ((inl otimes inr ∘ inl) otimes inr ∘ inr), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x otimes t, by
          simp only [Poly.map_apply]
          rw [show (v otimes x otimes t) ∘ ((inl otimes inr ∘ inl) otimes inr ∘ inr) = (v otimes x) otimes t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
        ⟨t ∘ inl,
          (pe _).2
            ⟨t ∘ inr, by
              simp only [Poly.map_apply] at ht
              rwa [show (v otimes t) ∘ ((inl otimes inr ∘ inl) otimes inr ∘ inr) = (v otimes t ∘ inl) otimes t ∘ inr from
                funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl] at ht⟩⟩⟩⟩

/--
theorem `ex1_dioph` / 定理 `ex1_dioph`

English:
theorem ex1_dioph
  given: {S : Set (Option α -> Nat)}
  statement: Dioph S -> Dioph {v | exists x, x ::ₒ v in S}
  proof: (pe _).1 hx
        ⟨x ::ₒ t, by
          simp only [Poly.map_apply]
          rw [show (v otimes x ::ₒ t) ∘ (inr none ::ₒ inl otimes inr ∘ some) = x ::ₒ v otimes t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl}; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
 

中文:
定理 ex1_dioph
  条件: {S : Set (Option α -> 自然数)}
  结论: Dioph S -> Dioph {v | 存在 x, x ::ₒ v in S}
  证明: (pe _).1 hx
        ⟨x ::ₒ t, by
          simp only [Poly.map_apply]
          rw [show (v otimes x ::ₒ t) ∘ (inr none ::ₒ inl otimes inr ∘ some) = x ::ₒ v otimes t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl}; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
 
-/
theorem ex1_dioph {S : Set (Option α -> Nat)} : Dioph S -> Dioph {v | exists x, x ::ₒ v in S}
  | ⟨β, p, pe⟩ =>
    ⟨Option β, p.map (inr none ::ₒ inl otimes inr ∘ some), fun v =>
      ⟨fun ⟨x, hx⟩ =>
        let ⟨t, ht⟩ := (pe _).1 hx
        ⟨x ::ₒ t, by
          simp only [Poly.map_apply]
          rw [show (v otimes x ::ₒ t) ∘ (inr none ::ₒ inl otimes inr ∘ some) = x ::ₒ v otimes t from
            funext fun s => by rcases s with a | b <;> try { cases a <;> rfl}; rfl]
          exact ht⟩,
        fun ⟨t, ht⟩ =>
        ⟨t none,
          (pe _).2
            ⟨t ∘ some, by
              simp only [Poly.map_apply] at ht
              rwa [show (v otimes t) ∘ (inr none ::ₒ inl otimes inr ∘ some) = t none ::ₒ v otimes t ∘ some from
                funext fun s => by rcases s with a | b <;> try { cases a <;> rfl }; rfl] at ht ⟩⟩⟩⟩

/--
theorem `dom_dioph` / 定理 `dom_dioph`

English:
theorem dom_dioph
  given: {f : (α -> Nat) ->. Nat} (d : DiophPFun f)
  statement: Dioph f.Dom
  proof: cast (congr_arg Dioph <| Set.ext fun _ => (PFun.dom_iff_graph _ _).symm) (ex1_dioph d)

中文:
定理 dom_dioph
  条件: {f : (α -> 自然数) ->. 自然数} (d : DiophPFun f)
  结论: Dioph f.Dom
  证明: cast (congr_arg Dioph <| Set.ext fun _ => (PFun.dom_iff_graph _ _).symm) (ex1_dioph d)

Depends on / 依赖: PFun.dom_iff_graph, Set.ext, congr_arg, dom_iff_graph, ex1_dioph
-/
theorem dom_dioph {f : (α -> Nat) ->. Nat} (d : DiophPFun f) : Dioph f.Dom :=
  cast (congr_arg Dioph <| Set.ext fun _ => (PFun.dom_iff_graph _ _).symm) (ex1_dioph d)

/--
theorem `diophFn_iff_pFun` / 定理 `diophFn_iff_pFun`

English:
theorem diophFn_iff_pFun
  given: (f : (α -> Nat) -> Nat)
  statement: DiophFn f = @DiophPFun α f
  proof: by
  refine congr_arg Dioph (Set.ext fun v => ?_); exact PFun.lift_graph.symm

中文:
定理 diophFn_iff_pFun
  条件: (f : (α -> 自然数) -> 自然数)
  结论: DiophFn f = @DiophPFun α f
  证明: by
  refine congr_arg Dioph (Set.ext fun v => ?_); exact PFun.lift_graph.symm

Depends on / 依赖: PFun.lift_graph.symm, Set.ext, congr_arg, lift_graph
-/
theorem diophFn_iff_pFun (f : (α -> Nat) -> Nat) : DiophFn f = @DiophPFun α f := by
  refine congr_arg Dioph (Set.ext fun v => ?_); exact PFun.lift_graph.symm

/--
theorem `abs_poly_dioph` / 定理 `abs_poly_dioph`

English:
theorem abs_poly_dioph
  given: (p : Poly α)
  statement: DiophFn fun v => (p v).natAbs
  proof: of_no_dummies _ ((p.map some - Poly.proj none) * (p.map some + Poly.proj none))
    fun v => (by dsimp; exact Int.natAbs_eq_iff_mul_eq_zero)

中文:
定理 abs_poly_dioph
  条件: (p : Poly α)
  结论: DiophFn fun v => (p v).natAbs
  证明: of_no_dummies _ ((p.map some - Poly.proj none) * (p.map some + Poly.proj none))
    fun v => (by dsimp; exact Int.natAbs_eq_iff_mul_eq_zero)

Depends on / 依赖: Int.natAbs_eq_iff_mul_eq_zero, Poly.proj, natAbs_eq_iff_mul_eq_zero, of_no_dummies, p.map
-/
theorem abs_poly_dioph (p : Poly α) : DiophFn fun v => (p v).natAbs :=
  of_no_dummies _ ((p.map some - Poly.proj none) * (p.map some + Poly.proj none))
    fun v => (by dsimp; exact Int.natAbs_eq_iff_mul_eq_zero)

/--
theorem `proj_dioph` / 定理 `proj_dioph`

English:
theorem proj_dioph
  given: (i : α)
  statement: DiophFn fun v => v i
  proof: abs_poly_dioph (Poly.proj i)

中文:
定理 proj_dioph
  条件: (i : α)
  结论: DiophFn fun v => v i
  证明: abs_poly_dioph (Poly.proj i)

Depends on / 依赖: Poly.proj, abs_poly_dioph
-/
theorem proj_dioph (i : α) : DiophFn fun v => v i :=
  abs_poly_dioph (Poly.proj i)

/--
theorem `diophPFun_comp1` / 定理 `diophPFun_comp1`

English:
theorem diophPFun_comp1
  given: {S : Set (Option α -> Nat)} (d : Dioph S) {f} (df : DiophPFun f)
  proof: ext (ex1_dioph (d.inter df)) fun v =>
    ⟨fun ⟨x, hS, (h : Exists _)⟩ => by
      rw [show (x ::ₒ v) ∘ some = v from funext fun s => rfl] at h
      obtain ⟨hf, h⟩ := h; refine ⟨hf, ?_⟩; rw [PFun.fn, h]; exact hS,
    fun ⟨x, hS⟩ =>
      ⟨f.fn v x, hS, show Exists _ by
        rw [show (f.fn v x :

中文:
定理 diophPFun_comp1
  条件: {S : Set (Option α -> 自然数)} (d : Dioph S) {f} (df : DiophPFun f)
  证明: ext (ex1_dioph (d.inter df)) fun v =>
    ⟨fun ⟨x, hS, (h : Exists _)⟩ => by
      rw [show (x ::ₒ v) ∘ some = v from funext fun s => rfl] at h
      obtain ⟨hf, h⟩ := h; refine ⟨hf, ?_⟩; rw [PFun.fn, h]; exact hS,
    fun ⟨x, hS⟩ =>
      ⟨f.fn v x, hS, show Exists _ by
        rw [show (f.fn v x :

Depends on / 依赖: Exists, PFun.fn, d.inter, ex1_dioph, f.fn
-/
theorem diophPFun_comp1 {S : Set (Option α -> Nat)} (d : Dioph S) {f} (df : DiophPFun f) :
    Dioph {v : α -> Nat | exists h : v in f.Dom, f.fn v h ::ₒ v in S} :=
  ext (ex1_dioph (d.inter df)) fun v =>
    ⟨fun ⟨x, hS, (h : Exists _)⟩ => by
      rw [show (x ::ₒ v) ∘ some = v from funext fun s => rfl] at h
      obtain ⟨hf, h⟩ := h; refine ⟨hf, ?_⟩; rw [PFun.fn, h]; exact hS,
    fun ⟨x, hS⟩ =>
      ⟨f.fn v x, hS, show Exists _ by
        rw [show (f.fn v x ::ₒ v) ∘ some = v from funext fun s => rfl]; exact ⟨x, rfl⟩⟩⟩

/--
theorem `diophFn_comp1` / 定理 `diophFn_comp1`

English:
theorem diophFn_comp1
  given: {S : Set (Option α -> Nat)} (d : Dioph S) {f : (α -> Nat) -> Nat} (df : DiophFn f)
  proof: ext (diophPFun_comp1 d <| cast (diophFn_iff_pFun f) df)
    fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

中文:
定理 diophFn_comp1
  条件: {S : Set (Option α -> 自然数)} (d : Dioph S) {f : (α -> 自然数) -> 自然数} (df : DiophFn f)
  证明: ext (diophPFun_comp1 d <| cast (diophFn_iff_pFun f) df)
    fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

Depends on / 依赖: diophFn_iff_pFun, diophPFun_comp1
-/
theorem diophFn_comp1 {S : Set (Option α -> Nat)} (d : Dioph S) {f : (α -> Nat) -> Nat} (df : DiophFn f) :
    Dioph {v | f v ::ₒ v in S} :=
  ext (diophPFun_comp1 d <| cast (diophFn_iff_pFun f) df)
    fun _ => ⟨fun ⟨_, h⟩ => h, fun h => ⟨trivial, h⟩⟩

end

section

variable {α : Type} {n : Nat}

open Vector3

open scoped Vector3

/--
theorem `diophFn_vec_comp1` / 定理 `diophFn_vec_comp1`

English:
theorem diophFn_vec_comp1
  statement: {S : Set (Vector3 Nat (succ n))} (d : Dioph S) {f : Vector3 Nat n -> Nat}
  proof: Dioph.ext (diophFn_comp1 (reindex_dioph _ (none :: some) d) df) (fun v => by
    dsimp
    -- TODO: `apply iff_of_eq` is required here, even though `congr!` works on iff below.
    apply iff_of_eq
    congr 1
    ext x; cases x <;> rfl)

中文:
定理 diophFn_vec_comp1
  结论: {S : Set (Vector3 自然数 (succ n))} (d : Dioph S) {f : Vector3 自然数 n -> 自然数}
  证明: Dioph.ext (diophFn_comp1 (reindex_dioph _ (none :: some) d) df) (fun v => by
    dsimp
    -- TODO: `apply iff_of_eq` is required here, even though `congr!` works on iff below.
    apply iff_of_eq
    congr 1
    ext x; cases x <;> rfl)

Depends on / 依赖: Dioph.ext, diophFn_comp1, reindex_dioph
-/
theorem diophFn_vec_comp1 {S : Set (Vector3 Nat (succ n))} (d : Dioph S) {f : Vector3 Nat n -> Nat}
    (df : DiophFn f) : Dioph {v : Vector3 Nat n | (f v :: v) in S} :=
  Dioph.ext (diophFn_comp1 (reindex_dioph _ (none :: some) d) df) (fun v => by
    dsimp
    -- TODO: `apply iff_of_eq` is required here, even though `congr!` works on iff below.
    apply iff_of_eq
    congr 1
    ext x; cases x <;> rfl)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `vec_ex1_dioph` / 定理 `vec_ex1_dioph`

English:
theorem vec_ex1_dioph
  given: (n) {S : Set (Vector3 Nat (succ n))} (d : Dioph S)
  proof: ext (ex1_dioph <| reindex_dioph _ (none :: some) d) fun v =>
    exists_congr fun x => by
      dsimp
      rw [show Option.elim' x v ∘ cons none some = x :: v from
          funext fun s => by rcases s with a | b <;> rfl]

中文:
定理 vec_ex1_dioph
  条件: (n) {S : Set (Vector3 自然数 (succ n))} (d : Dioph S)
  证明: ext (ex1_dioph <| reindex_dioph _ (none :: some) d) fun v =>
    exists_congr fun x => by
      dsimp
      rw [show Option.elim' x v ∘ cons none some = x :: v from
          funext fun s => by rcases s with a | b <;> rfl]

Depends on / 依赖: Option.elim, ex1_dioph, exists_congr, reindex_dioph
-/
theorem vec_ex1_dioph (n) {S : Set (Vector3 Nat (succ n))} (d : Dioph S) :
    Dioph {v : Fin2 n -> Nat | exists x, (x :: v) in S} :=
  ext (ex1_dioph <| reindex_dioph _ (none :: some) d) fun v =>
    exists_congr fun x => by
      dsimp
      rw [show Option.elim' x v ∘ cons none some = x :: v from
          funext fun s => by rcases s with a | b <;> rfl]

/--
theorem `diophFn_vec` / 定理 `diophFn_vec`

English:
theorem diophFn_vec
  given: (f : Vector3 Nat n -> Nat)
  statement: DiophFn f ↔ Dioph {v | f (v ∘ fs) = v fz}
  proof: ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

中文:
定理 diophFn_vec
  条件: (f : Vector3 自然数 n -> 自然数)
  结论: DiophFn f ↔ Dioph {v | f (v ∘ fs) = v fz}
  证明: ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

Depends on / 依赖: reindex_dioph
-/
theorem diophFn_vec (f : Vector3 Nat n -> Nat) : DiophFn f ↔ Dioph {v | f (v ∘ fs) = v fz} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

/--
theorem `diophPFun_vec` / 定理 `diophPFun_vec`

English:
theorem diophPFun_vec
  given: (f : Vector3 Nat n ->. Nat)
  statement: DiophPFun f ↔ Dioph {v | (v ∘ fs, v fz) in f.graph}
  proof: ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

中文:
定理 diophPFun_vec
  条件: (f : Vector3 自然数 n ->. 自然数)
  结论: DiophPFun f ↔ Dioph {v | (v ∘ fs, v fz) in f.graph}
  证明: ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

Depends on / 依赖: reindex_dioph
-/
theorem diophPFun_vec (f : Vector3 Nat n ->. Nat) : DiophPFun f ↔ Dioph {v | (v ∘ fs, v fz) in f.graph} :=
  ⟨reindex_dioph _ (fz ::ₒ fs), reindex_dioph _ (none::some)⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `diophFn_compn` / 定理 `diophFn_compn`

English:
theorem diophFn_compn
  proof: x; rfl
  | succ n, S, d, f =>
    f.consElim fun f fl => by
        simp only [vectorAllP_cons, and_imp]
        exact fun df dfl =>
          have : Dioph {v | (v ∘ inl otimes f (v ∘ inl)::v ∘ inr) in S} :=
            ext (diophFn_comp1 (reindex_dioph _ (some ∘ inl otimes none :: some ∘ inr) d) <|

中文:
定理 diophFn_compn
  证明: x; rfl
  | succ n, S, d, f =>
    f.consElim fun f fl => by
        simp only [vectorAllP_cons, and_imp]
        exact fun df dfl =>
          have : Dioph {v | (v ∘ inl otimes f (v ∘ inl)::v ∘ inr) in S} :=
            ext (diophFn_comp1 (reindex_dioph _ (some ∘ inl otimes none :: some ∘ inr) d) <|
-/
theorem diophFn_compn :
    forall {n} {S : Set (α oplus (Fin2 n) -> Nat)} (_ : Dioph S) {f : Vector3 ((α -> Nat) -> Nat) n}
      (_ : VectorAllP DiophFn f), Dioph {v : α -> Nat | (v otimes fun i => f i v) in S}
  | 0, S, d, f => fun _ =>
    ext (reindex_dioph _ (id otimes Fin2.elim0) d) fun v => by
      dsimp
      -- TODO: `congr! 1; ext` should be equivalent to `congr! 1 with x` but that does not work.
      congr! 1
      ext x; obtain _ | _ | _ := x; rfl
  | succ n, S, d, f =>
    f.consElim fun f fl => by
        simp only [vectorAllP_cons, and_imp]
        exact fun df dfl =>
          have : Dioph {v | (v ∘ inl otimes f (v ∘ inl)::v ∘ inr) in S} :=
            ext (diophFn_comp1 (reindex_dioph _ (some ∘ inl otimes none :: some ∘ inr) d) <|
                reindex_diophFn inl df)
              fun v => by
                dsimp
                -- TODO: `congr! 1; ext` should be equivalent to `congr! 1 with x`
                -- but that does not work.
                congr! 1
                ext x; obtain _ | _ | _ := x <;> rfl
          have : Dioph {v | (v otimes f v::fun i : Fin2 n => fl i v) in S} :=
            @diophFn_compn n {v | (v ∘ inl otimes f (v ∘ inl) :: v ∘ inr) in S} this _ dfl
          ext this fun v => by
            dsimp
            congr! 3 with x
            obtain _ | _ | _ := x <;> rfl

/--
theorem `dioph_comp` / 定理 `dioph_comp`

English:
theorem dioph_comp
  statement: {S : Set (Vector3 Nat n)} (d : Dioph S) (f : Vector3 ((α -> Nat) -> Nat) n)
  proof: diophFn_compn (reindex_dioph _ inr d) df

中文:
定理 dioph_comp
  结论: {S : Set (Vector3 自然数 n)} (d : Dioph S) (f : Vector3 ((α -> 自然数) -> 自然数) n)
  证明: diophFn_compn (reindex_dioph _ inr d) df

Depends on / 依赖: diophFn_compn, reindex_dioph
-/
theorem dioph_comp {S : Set (Vector3 Nat n)} (d : Dioph S) (f : Vector3 ((α -> Nat) -> Nat) n)
    (df : VectorAllP DiophFn f) : Dioph {v | (fun i => f i v) in S} :=
  diophFn_compn (reindex_dioph _ inr d) df

set_option backward.isDefEq.respectTransparency false in
/--
theorem `diophFn_comp` / 定理 `diophFn_comp`

English:
theorem diophFn_comp
  statement: {f : Vector3 Nat n -> Nat} (df : DiophFn f) (g : Vector3 ((α -> Nat) -> Nat) n)
  proof: dioph_comp ((diophFn_vec _).1 df) ((fun v => v none) :: fun i v => g i (v ∘ some)) by
    simp only [vectorAllP_cons]
    exact ⟨proj_dioph none, (vectorAllP_iff_forall _ _).2 fun i =>
reindex_diophFn _ (vectorAllP_iff_forall _ _).1 dg _⟩

@[inherit_doc]
scoped notation:35 x " D∧ " y => Dioph.inter 

中文:
定理 diophFn_comp
  结论: {f : Vector3 自然数 n -> 自然数} (df : DiophFn f) (g : Vector3 ((α -> 自然数) -> 自然数) n)
  证明: dioph_comp ((diophFn_vec _).1 df) ((fun v => v none) :: fun i v => g i (v ∘ some)) by
    simp only [vectorAllP_cons]
    exact ⟨proj_dioph none, (vectorAllP_iff_forall _ _).2 fun i =>
reindex_diophFn _ (vectorAllP_iff_forall _ _).1 dg _⟩

@[inherit_doc]
scoped notation:35 x " D∧ " y => Dioph.inter 

Depends on / 依赖: diophFn_vec, dioph_comp, proj_dioph, reindex_diophFn, vectorAllP_cons, vectorAllP_iff_forall
-/
theorem diophFn_comp {f : Vector3 Nat n -> Nat} (df : DiophFn f) (g : Vector3 ((α -> Nat) -> Nat) n)
    (dg : VectorAllP DiophFn g) : DiophFn fun v => f fun i => g i v :=
dioph_comp ((diophFn_vec _).1 df) ((fun v => v none) :: fun i v => g i (v ∘ some)) by
    simp only [vectorAllP_cons]
    exact ⟨proj_dioph none, (vectorAllP_iff_forall _ _).2 fun i =>
reindex_diophFn _ (vectorAllP_iff_forall _ _).1 dg _⟩

@[inherit_doc]
scoped notation:35 x " D∧ " y => Dioph.inter x y

@[inherit_doc]
scoped notation:35 x " D∨ " y => Dioph.union x y

@[inherit_doc]
scoped notation:30 "Dexists" => Dioph.vec_ex1_dioph

/-- Local abbreviation for `Fin2.ofNat'` -/
scoped prefix:arg "&" => Fin2.ofNat'

/--
theorem `proj_dioph_of_nat` / 定理 `proj_dioph_of_nat`

English:
theorem proj_dioph_of_nat
  given: {n : Nat} (m : Nat) [IsLT m n]
  statement: DiophFn fun v : Vector3 Nat n => v &m
  proof: proj_dioph &m

中文:
定理 proj_dioph_of_nat
  条件: {n : 自然数} (m : 自然数) [IsLT m n]
  结论: DiophFn fun v : Vector3 自然数 n => v &m
  证明: proj_dioph &m

Depends on / 依赖: proj_dioph
-/
theorem proj_dioph_of_nat {n : Nat} (m : Nat) [IsLT m n] : DiophFn fun v : Vector3 Nat n => v &m :=
  proj_dioph &m

/-- Projection preserves Diophantine functions. -/
scoped prefix:100 "D&" => Dioph.proj_dioph_of_nat

/--
theorem `const_dioph` / 定理 `const_dioph`

English:
theorem const_dioph
  given: (n : Nat)
  statement: DiophFn (const (α -> Nat) n)
  proof: abs_poly_dioph (Poly.const n)

中文:
定理 const_dioph
  条件: (n : 自然数)
  结论: DiophFn (const (α -> 自然数) n)
  证明: abs_poly_dioph (Poly.const n)

Depends on / 依赖: Poly.const, abs_poly_dioph
-/
theorem const_dioph (n : Nat) : DiophFn (const (α -> Nat) n) :=
  abs_poly_dioph (Poly.const n)

/-- The constant function is Diophantine. -/
scoped prefix:100 "D." => Dioph.const_dioph

section
variable {f g : (α -> Nat) -> Nat} (df : DiophFn f) (dg : DiophFn g)
include df dg

/--
theorem `dioph_comp2` / 定理 `dioph_comp2`

English:
theorem dioph_comp2
  given: {S : Nat -> Nat -> Prop} (d : Dioph {v : Vector3 Nat 2 | S (v &0) (v &1)})
  proof: dioph_comp d [f, g] ⟨df, dg⟩

中文:
定理 dioph_comp2
  条件: {S : 自然数 -> 自然数 -> 命题} (d : Dioph {v : Vector3 自然数 2 | S (v &0) (v &1)})
  证明: dioph_comp d [f, g] ⟨df, dg⟩

Depends on / 依赖: dioph_comp
-/
theorem dioph_comp2 {S : Nat -> Nat -> Prop} (d : Dioph {v : Vector3 Nat 2 | S (v &0) (v &1)}) :
    Dioph {v | S (f v) (g v)} := dioph_comp d [f, g] ⟨df, dg⟩

/--
theorem `diophFn_comp2` / 定理 `diophFn_comp2`

English:
theorem diophFn_comp2
  given: {h : Nat -> Nat -> Nat} (d : DiophFn fun v : Vector3 Nat 2 => h (v &0) (v &1))
  proof: diophFn_comp d [f, g] ⟨df, dg⟩

中文:
定理 diophFn_comp2
  条件: {h : 自然数 -> 自然数 -> 自然数} (d : DiophFn fun v : Vector3 自然数 2 => h (v &0) (v &1))
  证明: diophFn_comp d [f, g] ⟨df, dg⟩

Depends on / 依赖: diophFn_comp
-/
theorem diophFn_comp2 {h : Nat -> Nat -> Nat} (d : DiophFn fun v : Vector3 Nat 2 => h (v &0) (v &1)) :
    DiophFn fun v => h (f v) (g v) := diophFn_comp d [f, g] ⟨df, dg⟩

/--
theorem `eq_dioph` / 定理 `eq_dioph`

English:
theorem eq_dioph
  statement: Dioph {v | f v = g v}
  proof: dioph_comp2 df dg
    of_no_dummies _ (Poly.proj &0 - Poly.proj &1) fun v => by
      exact Int.ofNat_inj.symm.trans ⟨@sub_eq_zero_of_eq Int _ (v &0) (v &1), eq_of_sub_eq_zero⟩

@[inherit_doc]
scoped infixl:50 " D= " => Dioph.eq_dioph

中文:
定理 eq_dioph
  结论: Dioph {v | f v = g v}
  证明: dioph_comp2 df dg
    of_no_dummies _ (Poly.proj &0 - Poly.proj &1) fun v => by
      exact Int.ofNat_inj.symm.trans ⟨@sub_eq_zero_of_eq Int _ (v &0) (v &1), eq_of_sub_eq_zero⟩

@[inherit_doc]
scoped infixl:50 " D= " => Dioph.eq_dioph

Depends on / 依赖: Int.ofNat_inj.symm.trans, Poly.proj, dioph_comp2, eq_of_sub_eq_zero, ofNat_inj, of_no_dummies, sub_eq_zero_of_eq
-/
theorem eq_dioph : Dioph {v | f v = g v} :=
dioph_comp2 df dg
    of_no_dummies _ (Poly.proj &0 - Poly.proj &1) fun v => by
      exact Int.ofNat_inj.symm.trans ⟨@sub_eq_zero_of_eq Int _ (v &0) (v &1), eq_of_sub_eq_zero⟩

@[inherit_doc]
scoped infixl:50 " D= " => Dioph.eq_dioph

/--
theorem `add_dioph` / 定理 `add_dioph`

English:
theorem add_dioph
  statement: DiophFn fun v => f v + g v
  proof: diophFn_comp2 df dg abs_poly_dioph (@Poly.proj (Fin2 2) &0 + @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:80 " D+ " => Dioph.add_dioph

中文:
定理 add_dioph
  结论: DiophFn fun v => f v + g v
  证明: diophFn_comp2 df dg abs_poly_dioph (@Poly.proj (Fin2 2) &0 + @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:80 " D+ " => Dioph.add_dioph

Depends on / 依赖: Poly.proj, abs_poly_dioph, diophFn_comp2
-/
theorem add_dioph : DiophFn fun v => f v + g v :=
diophFn_comp2 df dg abs_poly_dioph (@Poly.proj (Fin2 2) &0 + @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:80 " D+ " => Dioph.add_dioph

/--
theorem `mul_dioph` / 定理 `mul_dioph`

English:
theorem mul_dioph
  statement: DiophFn fun v => f v * g v
  proof: diophFn_comp2 df dg abs_poly_dioph (@Poly.proj (Fin2 2) &0 * @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:90 " D* " => Dioph.mul_dioph

中文:
定理 mul_dioph
  结论: DiophFn fun v => f v * g v
  证明: diophFn_comp2 df dg abs_poly_dioph (@Poly.proj (Fin2 2) &0 * @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:90 " D* " => Dioph.mul_dioph

Depends on / 依赖: Poly.proj, abs_poly_dioph, diophFn_comp2
-/
theorem mul_dioph : DiophFn fun v => f v * g v :=
diophFn_comp2 df dg abs_poly_dioph (@Poly.proj (Fin2 2) &0 * @Poly.proj (Fin2 2) &1)

@[inherit_doc]
scoped infixl:90 " D* " => Dioph.mul_dioph

/--
theorem `le_dioph` / 定理 `le_dioph`

English:
theorem le_dioph
  statement: Dioph {v | f v <= g v}
  proof: dioph_comp2 df dg
    ext ((Dexists) 2 <| D&1 D+ D&0 D= D&2) fun _ => ⟨fun ⟨_, hx⟩ => le.intro hx, le.dest⟩

@[inherit_doc]
scoped infixl:50 " D<= " => Dioph.le_dioph

中文:
定理 le_dioph
  结论: Dioph {v | f v <= g v}
  证明: dioph_comp2 df dg
    ext ((Dexists) 2 <| D&1 D+ D&0 D= D&2) fun _ => ⟨fun ⟨_, hx⟩ => le.intro hx, le.dest⟩

@[inherit_doc]
scoped infixl:50 " D<= " => Dioph.le_dioph

Depends on / 依赖: Dexists, dioph_comp2, le.dest, le.intro
-/
theorem le_dioph : Dioph {v | f v <= g v} :=
dioph_comp2 df dg
    ext ((Dexists) 2 <| D&1 D+ D&0 D= D&2) fun _ => ⟨fun ⟨_, hx⟩ => le.intro hx, le.dest⟩

@[inherit_doc]
scoped infixl:50 " D<= " => Dioph.le_dioph

/--
theorem `lt_dioph` / 定理 `lt_dioph`

English:
theorem lt_dioph
  statement: Dioph {v | f v < g v}
  proof: df D+ D.1 D<= dg

@[inherit_doc]
scoped infixl:50 " D< " => Dioph.lt_dioph

中文:
定理 lt_dioph
  结论: Dioph {v | f v < g v}
  证明: df D+ D.1 D<= dg

@[inherit_doc]
scoped infixl:50 " D< " => Dioph.lt_dioph
-/
theorem lt_dioph : Dioph {v | f v < g v} := df D+ D.1 D<= dg

@[inherit_doc]
scoped infixl:50 " D< " => Dioph.lt_dioph

/--
theorem `ne_dioph` / 定理 `ne_dioph`

English:
theorem ne_dioph
  statement: Dioph {v | f v != g v}
  proof: ext (df D< dg D∨ dg D< df) fun v => by dsimp; exact lt_or_lt_iff_ne (α := Nat)

@[inherit_doc]
scoped infixl:50 " D!= " => Dioph.ne_dioph

中文:
定理 ne_dioph
  结论: Dioph {v | f v != g v}
  证明: ext (df D< dg D∨ dg D< df) fun v => by dsimp; exact lt_or_lt_iff_ne (α := Nat)

@[inherit_doc]
scoped infixl:50 " D!= " => Dioph.ne_dioph

Depends on / 依赖: lt_or_lt_iff_ne
-/
theorem ne_dioph : Dioph {v | f v != g v} :=
  ext (df D< dg D∨ dg D< df) fun v => by dsimp; exact lt_or_lt_iff_ne (α := Nat)

@[inherit_doc]
scoped infixl:50 " D!= " => Dioph.ne_dioph

/--
theorem `sub_dioph` / 定理 `sub_dioph`

English:
theorem sub_dioph
  statement: DiophFn fun v => f v - g v
  proof: diophFn_comp2 df dg
(diophFn_vec _).2
ext (D&1 D= D&0 D+ D&2 D∨ D&1 D<= D&2 D∧ D&0 D= D.0)
        (vectorAll_iff_forall _).1 fun x y z =>
          show y = x + z ∨ y <= z ∧ x = 0 ↔ y - z = x by grind

@[inherit_doc]
scoped infixl:80 " D- " => Dioph.sub_dioph

中文:
定理 sub_dioph
  结论: DiophFn fun v => f v - g v
  证明: diophFn_comp2 df dg
(diophFn_vec _).2
ext (D&1 D= D&0 D+ D&2 D∨ D&1 D<= D&2 D∧ D&0 D= D.0)
        (vectorAll_iff_forall _).1 fun x y z =>
          show y = x + z ∨ y <= z ∧ x = 0 ↔ y - z = x by grind

@[inherit_doc]
scoped infixl:80 " D- " => Dioph.sub_dioph

Depends on / 依赖: diophFn_comp2, diophFn_vec, vectorAll_iff_forall
-/
theorem sub_dioph : DiophFn fun v => f v - g v :=
diophFn_comp2 df dg
(diophFn_vec _).2
ext (D&1 D= D&0 D+ D&2 D∨ D&1 D<= D&2 D∧ D&0 D= D.0)
        (vectorAll_iff_forall _).1 fun x y z =>
          show y = x + z ∨ y <= z ∧ x = 0 ↔ y - z = x by grind

@[inherit_doc]
scoped infixl:80 " D- " => Dioph.sub_dioph

/--
theorem `dvd_dioph` / 定理 `dvd_dioph`

English:
theorem dvd_dioph
  statement: Dioph {v | f v ∣ g v}
  proof: dioph_comp ((Dexists) 2 <| D&2 D= D&1 D* D&0) [f, g] ⟨df, dg⟩

@[inherit_doc]
scoped infixl:50 " D∣ " => Dioph.dvd_dioph

中文:
定理 dvd_dioph
  结论: Dioph {v | f v ∣ g v}
  证明: dioph_comp ((Dexists) 2 <| D&2 D= D&1 D* D&0) [f, g] ⟨df, dg⟩

@[inherit_doc]
scoped infixl:50 " D∣ " => Dioph.dvd_dioph

Depends on / 依赖: Dexists, dioph_comp
-/
theorem dvd_dioph : Dioph {v | f v ∣ g v} :=
  dioph_comp ((Dexists) 2 <| D&2 D= D&1 D* D&0) [f, g] ⟨df, dg⟩

@[inherit_doc]
scoped infixl:50 " D∣ " => Dioph.dvd_dioph

/--
theorem `mod_dioph` / 定理 `mod_dioph`

English:
theorem mod_dioph
  statement: DiophFn fun v => f v % g v
  proof: have : Dioph {v : Vector3 Nat 3 | (v &2 = 0 ∨ v &0 < v &2) ∧ exists x : Nat, v &0 + v &2 * x = v &1} :=
(D&2 D= D.0 D∨ D&0 D< D&2) D∧ (Dexists) 3 D&1 D+ D&3 D* D&0 D= D&2
diophFn_comp2 df dg
(diophFn_vec _).2
ext this
        (vectorAll_iff_forall _).1 fun z x y =>
          show ((y = 0 ∨ z < y) ∧ 

中文:
定理 mod_dioph
  结论: DiophFn fun v => f v % g v
  证明: have : Dioph {v : Vector3 Nat 3 | (v &2 = 0 ∨ v &0 < v &2) ∧ exists x : Nat, v &0 + v &2 * x = v &1} :=
(D&2 D= D.0 D∨ D&0 D< D&2) D∧ (Dexists) 3 D&1 D+ D&3 D* D&0 D= D&2
diophFn_comp2 df dg
(diophFn_vec _).2
ext this
        (vectorAll_iff_forall _).1 fun z x y =>
          show ((y = 0 ∨ z < y) ∧ 

Depends on / 依赖: Dexists, Vector3, add_mul_mod_self_left, diophFn_comp2, diophFn_vec, mod_eq_of_lt, mod_zero, or_iff_not_imp_, vectorAll_iff_forall
-/
theorem mod_dioph : DiophFn fun v => f v % g v :=
  have : Dioph {v : Vector3 Nat 3 | (v &2 = 0 ∨ v &0 < v &2) ∧ exists x : Nat, v &0 + v &2 * x = v &1} :=
(D&2 D= D.0 D∨ D&0 D< D&2) D∧ (Dexists) 3 D&1 D+ D&3 D* D&0 D= D&2
diophFn_comp2 df dg
(diophFn_vec _).2
ext this
        (vectorAll_iff_forall _).1 fun z x y =>
          show ((y = 0 ∨ z < y) ∧ exists c, z + y * c = x) ↔ x % y = z from
            ⟨fun ⟨h, c, hc⟩ => by
              rw [← hc]; simp only [add_mul_mod_self_left]; rcases h with x0 | hl
              · rw [x0, mod_zero]
              exact mod_eq_of_lt hl, fun e => by
                rw [← e]
                exact ⟨or_iff_not_imp_left.2 fun h => mod_lt _ (Nat.pos_of_ne_zero h), x / y,
                  mod_add_div _ _⟩⟩

@[inherit_doc]
scoped infixl:80 " D% " => Dioph.mod_dioph

/--
theorem `modEq_dioph` / 定理 `modEq_dioph`

English:
theorem modEq_dioph
  given: {h : (α -> Nat) -> Nat} (dh : DiophFn h)
  statement: Dioph {v | f v ≡ g v [MOD h v]}
  proof: df D% dh D= dg D% dh

@[inherit_doc]
scoped notation "D≡ " => Dioph.modEq_dioph

中文:
定理 modEq_dioph
  条件: {h : (α -> 自然数) -> 自然数} (dh : DiophFn h)
  结论: Dioph {v | f v ≡ g v [MOD h v]}
  证明: df D% dh D= dg D% dh

@[inherit_doc]
scoped notation "D≡ " => Dioph.modEq_dioph
-/
theorem modEq_dioph {h : (α -> Nat) -> Nat} (dh : DiophFn h) : Dioph {v | f v ≡ g v [MOD h v]} :=
  df D% dh D= dg D% dh

@[inherit_doc]
scoped notation "D≡ " => Dioph.modEq_dioph

/--
theorem `div_dioph` / 定理 `div_dioph`

English:
theorem div_dioph
  statement: DiophFn fun v => f v / g v
  proof: have :
    Dioph {v : Vector3 Nat 3 | v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 <= v &1 ∧ v &1 < (v &0 + 1) * v &2} :=
    (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D<= D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2
diophFn_comp2 df dg
(diophFn_vec _).2
ext this
        (vectorAll_iff_forall _).1 fun z x y =>
          s

中文:
定理 div_dioph
  结论: DiophFn fun v => f v / g v
  证明: have :
    Dioph {v : Vector3 Nat 3 | v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 <= v &1 ∧ v &1 < (v &0 + 1) * v &2} :=
    (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D<= D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2
diophFn_comp2 df dg
(diophFn_vec _).2
ext this
        (vectorAll_iff_forall _).1 fun z x y =>
          s

Depends on / 依赖: Nat.div_eq_iff, Nat.succ_mul, Vector3, diophFn_comp2, diophFn_vec, div_eq_iff, eq_comm, eq_zero_or_pos, succ_mul, vectorAll_iff_forall, y.eq_zero_or_pos
-/
theorem div_dioph : DiophFn fun v => f v / g v :=
  have :
    Dioph {v : Vector3 Nat 3 | v &2 = 0 ∧ v &0 = 0 ∨ v &0 * v &2 <= v &1 ∧ v &1 < (v &0 + 1) * v &2} :=
    (D&2 D= D.0 D∧ D&0 D= D.0) D∨ D&0 D* D&2 D<= D&1 D∧ D&1 D< (D&0 D+ D.1) D* D&2
diophFn_comp2 df dg
(diophFn_vec _).2
ext this
        (vectorAll_iff_forall _).1 fun z x y =>
          show y = 0 ∧ z = 0 ∨ z * y <= x ∧ x < (z + 1) * y ↔ x / y = z by
            rcases y.eq_zero_or_pos with rfl | hy
            · simp [eq_comm]
            · rw [Nat.div_eq_iff hy, Nat.succ_mul]
              grind

end

@[inherit_doc]
scoped infixl:80 " D/ " => Dioph.div_dioph

open Pell

/--
theorem `pell_dioph` / 定理 `pell_dioph`

English:
theorem pell_dioph
  proof: by
  have : Dioph {v : Vector3 Nat 4 |
    1 < v &0 ∧ v &1 <= v &3 ∧
    (v &2 = 1 ∧ v &3 = 0 ∨
    exists u w s t b : Nat,
      v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
      u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
      s * s - (b * b - 1) * t * t = 1 ∧
      1 < b ∧ b ≡ 1 [MOD 4 * v &

中文:
定理 pell_dioph
  证明: by
  have : Dioph {v : Vector3 Nat 4 |
    1 < v &0 ∧ v &1 <= v &3 ∧
    (v &2 = 1 ∧ v &3 = 0 ∨
    exists u w s t b : Nat,
      v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
      u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
      s * s - (b * b - 1) * t * t = 1 ∧
      1 < b ∧ b ≡ 1 [MOD 4 * v &

Depends on / 依赖: Dexists, Vector3
-/
theorem pell_dioph :
    Dioph {v : Vector3 Nat 4 | exists h : 1 < v &0, xn h (v &1) = v &2 ∧ yn h (v &1) = v &3} := by
  have : Dioph {v : Vector3 Nat 4 |
    1 < v &0 ∧ v &1 <= v &3 ∧
    (v &2 = 1 ∧ v &3 = 0 ∨
    exists u w s t b : Nat,
      v &2 * v &2 - (v &0 * v &0 - 1) * v &3 * v &3 = 1 ∧
      u * u - (v &0 * v &0 - 1) * w * w = 1 ∧
      s * s - (b * b - 1) * t * t = 1 ∧
      1 < b ∧ b ≡ 1 [MOD 4 * v &3] ∧ b ≡ v &0 [MOD u] ∧
      0 < w ∧ v &3 * v &3 ∣ w ∧
      s ≡ v &2 [MOD u] ∧
      t ≡ v &1 [MOD 4 * v &3])} :=
  (D.1 D< D&0 D∧ D&1 D<= D&3 D∧
    ((D&2 D= D.1 D∧ D&3 D= D.0) D∨
    ((Dexists) 4 <| (Dexists) 5 <| (Dexists) 6 <| (Dexists) 7 <| (Dexists) 8 <|
    D&7 D* D&7 D- (D&5 D* D&5 D- D.1) D* D&8 D* D&8 D= D.1 D∧
    D&4 D* D&4 D- (D&5 D* D&5 D- D.1) D* D&3 D* D&3 D= D.1 D∧
    D&2 D* D&2 D- (D&0 D* D&0 D- D.1) D* D&1 D* D&1 D= D.1 D∧
    D.1 D< D&0 D∧ (D≡ (D&0) (D.1) (D.4 D* D&8)) D∧ (D≡ (D&0) (D&5) (D&4)) D∧
    D.0 D< D&3 D∧ D&8 D* D&8 D∣ D&3 D∧
    (D≡ (D&2) (D&7) (D&4)) D∧
    (D≡ (D&1) (D&6) (D.4 D* (D&8))))) :)
  exact Dioph.ext this fun v => matiyasevic.symm

/--
theorem `xn_dioph` / 定理 `xn_dioph`

English:
theorem xn_dioph
  statement: DiophPFun fun v : Vector3 Nat 2 => ⟨1 < v &0, fun h => xn h (v &1)⟩
  proof: have : Dioph {v : Vector3 Nat 3 | exists y, exists h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y} :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 4) [&2, &3, &1, &0]
    (Dexists) 3 D_pell
(diophPFun_vec _).2
    Dioph.ext this fun _ => ⟨fun ⟨_, h, xe, _⟩ => ⟨h, xe⟩, fun ⟨h, xe⟩ => ⟨_, h, x

中文:
定理 xn_dioph
  结论: DiophPFun fun v : Vector3 自然数 2 => ⟨1 < v &0, fun h => xn h (v &1)⟩
  证明: have : Dioph {v : Vector3 Nat 3 | exists y, exists h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y} :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 4) [&2, &3, &1, &0]
    (Dexists) 3 D_pell
(diophPFun_vec _).2
    Dioph.ext this fun _ => ⟨fun ⟨_, h, xe, _⟩ => ⟨h, xe⟩, fun ⟨h, xe⟩ => ⟨_, h, x

Depends on / 依赖: D_pell, Dexists, Dioph.ext, Vector3, diophPFun_vec, pell_dioph, pell_dioph.reindex_dioph, reindex_dioph
-/
theorem xn_dioph : DiophPFun fun v : Vector3 Nat 2 => ⟨1 < v &0, fun h => xn h (v &1)⟩ :=
  have : Dioph {v : Vector3 Nat 3 | exists y, exists h : 1 < v &1, xn h (v &2) = v &0 ∧ yn h (v &2) = y} :=
    let D_pell := pell_dioph.reindex_dioph (Fin2 4) [&2, &3, &1, &0]
    (Dexists) 3 D_pell
(diophPFun_vec _).2
    Dioph.ext this fun _ => ⟨fun ⟨_, h, xe, _⟩ => ⟨h, xe⟩, fun ⟨h, xe⟩ => ⟨_, h, xe, rfl⟩⟩

/--
theorem `pow_dioph` / 定理 `pow_dioph`

English:
theorem pow_dioph
  given: {f g : (α -> Nat) -> Nat} (df : DiophFn f) (dg : DiophFn g)
  proof: by
  have : Dioph {v : Vector3 Nat 3 |
    v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
    (v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
    exists w a t z x y : Nat,
      (exists a1 : 1 < a, xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
      x ≡ y * (a - v &1) + v &0 [MOD t] ∧
      2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
    

中文:
定理 pow_dioph
  条件: {f g : (α -> 自然数) -> 自然数} (df : DiophFn f) (dg : DiophFn g)
  证明: by
  have : Dioph {v : Vector3 Nat 3 |
    v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
    (v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
    exists w a t z x y : Nat,
      (exists a1 : 1 < a, xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
      x ≡ y * (a - v &1) + v &0 [MOD t] ∧
      2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
    

Depends on / 依赖: Dexists, Vector3
-/
theorem pow_dioph {f g : (α -> Nat) -> Nat} (df : DiophFn f) (dg : DiophFn g) :
    DiophFn fun v => f v ^ g v := by
  have : Dioph {v : Vector3 Nat 3 |
    v &2 = 0 ∧ v &0 = 1 ∨ 0 < v &2 ∧
    (v &1 = 0 ∧ v &0 = 0 ∨ 0 < v &1 ∧
    exists w a t z x y : Nat,
      (exists a1 : 1 < a, xn a1 (v &2) = x ∧ yn a1 (v &2) = y) ∧
      x ≡ y * (a - v &1) + v &0 [MOD t] ∧
      2 * a * v &1 = t + (v &1 * v &1 + 1) ∧
      v &0 < t ∧ v &1 <= w ∧ v &2 <= w ∧
      a * a - ((w + 1) * (w + 1) - 1) * (w * z) * (w * z) = 1)} :=
  (D&2 D= D.0 D∧ D&0 D= D.1) D∨ (D.0 D< D&2 D∧
    ((D&1 D= D.0 D∧ D&0 D= D.0) D∨ (D.0 D< D&1 D∧
    ((Dexists) 3 <| (Dexists) 4 <| (Dexists) 5 <| (Dexists) 6 <| (Dexists) 7 <| (Dexists) 8 <|
    pell_dioph.reindex_dioph (Fin2 9) [&4, &8, &1, &0] D∧
    (D≡ (D&1) (D&0 D* (D&4 D- D&7) D+ D&6) (D&3)) D∧
    D.2 D* D&4 D* D&7 D= D&3 D+ (D&7 D* D&7 D+ D.1) D∧
    D&6 D< D&3 D∧ D&7 D<= D&5 D∧ D&8 D<= D&5 D∧
    D&4 D* D&4 D- ((D&5 D+ D.1) D* (D&5 D+ D.1) D- D.1) D* (D&5 D* D&2) D* (D&5 D* D&2) D= D.1))) :)
exact diophFn_comp2 df dg (diophFn_vec _).2 Dioph.ext this fun v => Iff.symm
eq_pow_of_pell.trans or_congr Iff.rfl and_congr Iff.rfl or_congr Iff.rfl
and_congr Iff.rfl
        ⟨fun ⟨w, a, t, z, a1, h⟩ => ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩,
        fun ⟨w, a, t, z, _, _, ⟨a1, rfl, rfl⟩, h⟩ => ⟨w, a, t, z, a1, h⟩⟩

end

end Dioph
