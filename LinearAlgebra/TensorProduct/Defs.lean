/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.Algebra.Module.Submodule.Bilinear
public import Mathlib.GroupTheory.Congruence.Hom
public import Mathlib.Tactic.Abel

/-!
# Tensor product of modules over commutative semirings

This file constructs the tensor product of modules over commutative semirings. Given a semiring `R`
and modules over it `M` and `N`, the standard construction of the tensor product is
`TensorProduct R M N`. It is also a module over `R`.

It comes with a canonical bilinear map
`TensorProduct.mk R M N : M →ₗ[R] N →ₗ[R] TensorProduct R M N`.

## Notation

* This file introduces the notation `M ⊗ N` and `M ⊗[R] N` for the tensor product space
  `TensorProduct R M N`.
* It introduces the notation `m ⊗ₜ n` and `m ⊗ₜ[R] n` for the tensor product of two elements,
  otherwise written as `TensorProduct.tmul R m n`.

## Tags

bilinear, tensor, tensor product
-/

@[expose] public section

section Semiring

variable {R R₂ R₃ R' R'' : Type*}
variable [CommSemiring R] [CommSemiring R₂] [CommSemiring R₃] [Monoid R'] [Semiring R'']
variable {σ₁₂ : R →+* R₂} {σ₂₃ : R₂ →+* R₃} {σ₁₃ : R →+* R₃}
variable {A M N P Q S : Type*}
variable {M₂ M₃ N₂ N₃ P' P₂ P₃ Q' Q₂ Q₃ : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P] [AddCommMonoid Q] [AddCommMonoid S]
variable [AddCommMonoid P'] [AddCommMonoid Q']
variable [AddCommMonoid M₂] [AddCommMonoid N₂] [AddCommMonoid P₂] [AddCommMonoid Q₂]
variable [AddCommMonoid M₃] [AddCommMonoid N₃] [AddCommMonoid P₃] [AddCommMonoid Q₃]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable [Module R M] [Module R N] [Module R S]
variable [Module R P'] [Module R Q']
variable [Module R₂ M₂] [Module R₂ N₂] [Module R₂ P₂] [Module R₂ Q₂]
variable [Module R₃ M₃] [Module R₃ N₃] [Module R₃ P₃] [Module R₃ Q₃]

variable (M N)

namespace TensorProduct

section

variable (R)

/-- The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotient is
the tensor product. -/
/-
**TensorProduct.Eqv** 是 Mathlib 中的一个归纳类型，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     (M : Type u_7) →       (N
 : Type u_8) →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddCommM
onoid N] →             [_root_.Module R M] → [_root_.Module R N] → FreeAddMonoid
 (M × N) → FreeAddMonoid (M × N) → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relation on `FreeAddMonoid (M × N)` that generates a congruence whose quotie
nt is
the tensor product.
-/
inductive Eqv : FreeAddMonoid (M × N) → FreeAddMonoid (M × N) → Prop
  | of_zero_left : ∀ n : N, Eqv (.of (0, n)) 0
  | of_zero_right : ∀ m : M, Eqv (.of (m, 0)) 0
  | of_add_left : ∀ (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : ∀ (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : ∀ (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
  | add_comm : ∀ x y, Eqv (x + y) (y + x)

end

end TensorProduct

variable (R) in
/-- The tensor product of two modules `M` and `N` over the same commutative semiring `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped TensorProduct`. -/
/-
**TensorProduct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：TensorProduct : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of two modules `M` and `N` over the same commutative semiring
 `R`.
The localized notations are `M ⊗ N` and `M ⊗[R] N`, accessed by `open scoped Ten
sorProduct`.
-/
def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient
deriving Zero, Add, AddZeroClass, AddSemigroup

set_option quotPrecheck false in
@[inherit_doc TensorProduct] scoped[TensorProduct] infixl:100 " ⊗ " => TensorProduct _

@[inherit_doc] scoped[TensorProduct] notation:100 M:100 " ⊗[" R "] " N:101 => TensorProduct R M N

namespace TensorProduct

section Module

/-
**TensorProduct.addCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：addCommSemigroup : AddCommSemigroup (M otimes[R] N) where add_comm
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommSemigroup : AddCommSemigroup (M ⊗[R] N) where
  add_comm := fun x y =>
    AddCon.induction_on₂ x y fun _ _ =>
      Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.add_comm _ _
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ⊗[R] N) :=
  ⟨0⟩

variable {M N}

variable (R) in
/-- The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and `m ⊗ₜ[R] n`,
accessed by `open scoped TensorProduct`. -/
/-
**TensorProduct.tmul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：tmul (m : M) (n : N) : M otimes[R] N
参数：m : M；n : N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical function `M → N → M ⊗ N`. The localized notations are `m ⊗ₜ n` and
 `m ⊗ₜ[R] n`,
accessed by `open scoped TensorProduct`.
-/
def tmul (m : M) (n : N) : M ⊗[R] N :=
  AddCon.mk' _ <| FreeAddMonoid.of (m, n)

/-- The canonical function `M → N → M ⊗ N`. -/
infixl:100 " ⊗ₜ " => tmul _

/-- The canonical function `M → N → M ⊗ N`. -/
notation:100 x:100 " ⊗ₜ[" R "] " y:101 => tmul R x y

/-- Produces an arbitrary representation of the form `mₒ ⊗ₜ n₀ + ...`. -/
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Produces an arbitrary representation of the form `mₒ ⊗ₜ n₀ + ...`.
-/
unsafe instance [Repr M] [Repr N] : Repr (M ⊗[R] N) where
  reprPrec mn p :=
    let parts := mn.unquot.toList.map fun (mi, ni) =>
      Std.Format.group f!"{reprPrec mi 100} ⊗ₜ {reprPrec ni 101}"
    match parts with
    | [] => f!"0"
    | [part] => if p > 100 then Std.Format.bracketFill "(" part ")" else .fill part
    | parts =>
      (if p > 65 then (Std.Format.bracketFill "(" · ")") else (.fill ·)) <|
        .joinSep parts f!" +{Std.Format.line}"

@[elab_as_elim, induction_eliminator]
/-
**TensorProduct.induction_on** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N]   {motive : TensorProduct R M N → Prop} (z : Tens
orProduct R M N),   motive 0 →     (∀ (x : M) (y : N), motive (x ⊗ₜ[R] y)) →    
   (∀ (x y : TensorProduct R M N), motive x → motive y → motive (x + y)) → motiv
e z
参数：z : TensorProduct R M N；∀ (x : M) (y : N), motive (x ⊗ₜ[R] y)；∀ (x y : Tensor
Product R M N), motive x → motive y → motive (x + y)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddCon.induction_on`：∀ {M : Type u_1} [inst : Add M] {c : AddCon M} {C :
 c.Quotient → Prop} (q : c.Quotient), (∀ (x : M), C ↑x) → C q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddCon.coe_add`：∀ {M : Type u_1} [inst : Add M] {c : AddCon M} (x y : M)
, ↑(x + y) = ↑x + ↑y
-/
protected theorem induction_on {motive : M ⊗[R] N → Prop} (z : M ⊗[R] N)
    (zero : motive 0)
    (tmul : ∀ x y, motive <| x ⊗ₜ[R] y)
    (add : ∀ x y, motive x → motive y → motive (x + y)) : motive z :=
  AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih

variable (M) in
@[simp]
/-
**TensorProduct.zero_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
参数：n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem zero_tmul (n : N) : (0 : M) ⊗ₜ[R] n = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_left _
/-
**TensorProduct.add_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ n = m₁ otimesₜ n + m₂ oti
mesₜ[R] n
参数：m₁ m₂ : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) ⊗ₜ n = m₁ ⊗ₜ n + m₂ ⊗ₜ[R] n :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_left _ _ _

variable (N) in
@[simp]
/-
**TensorProduct.tmul_zero** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem tmul_zero (m : M) : m ⊗ₜ[R] (0 : N) = 0 :=
  Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_zero_right _
/-
**TensorProduct.tmul_add** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n₂) = m otimesₜ n₁ + m otim
esₜ[R] n₂
参数：m : M；n₁ n₂ : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quotient.sound'`：sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Qu
otient.mk'' b
-/
theorem tmul_add (m : M) (n₁ n₂ : N) : m ⊗ₜ (n₁ + n₂) = m ⊗ₜ n₁ + m ⊗ₜ[R] n₂ :=
  Eq.symm <| Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_add_right _ _ _
/-
**TensorProduct.uniqueLeft** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：uniqueLeft [Subsingleton M] : Unique (M otimes[R] N) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueLeft [Subsingleton M] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim x 0, zero_tmul]) <| by
    rintro _ _ rfl rfl; apply add_zero
/-
**TensorProduct.uniqueRight** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：uniqueRight [Subsingleton N] : Unique (M otimes[R] N) where default
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance uniqueRight [Subsingleton N] : Unique (M ⊗[R] N) where
  default := 0
  uniq z := z.induction_on rfl (fun x y ↦ by rw [Subsingleton.elim y 0, tmul_zero]) <| by
    rintro _ _ rfl rfl; apply add_zero

section

variable (R R' M N)

/-- A typeclass for `SMul` structures which can be moved across a tensor product.

This typeclass is generated automatically from an `IsScalarTower` instance, but exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be moved even if
`R` does not support negation.

Note that `Module R' (M ⊗[R] N)` is available even without this typeclass on `R'`; it's only
needed if `TensorProduct.smul_tmul`, `TensorProduct.smul_tmul'`, or `TensorProduct.tmul_smul` is
used.
-/
/-
**TensorProduct.CompatibleSMul** 是 Mathlib 中的一个归纳类型，位于命名空间 `TensorProduct`。
形式化陈述：(R : Type u_1) →   (R' : Type u_4) →     [inst : CommSemiring R] →       [
inst_1 : Monoid R'] →         (M : Type u_7) →           (N : Type u_8) →       
      [inst_2 : AddCommMonoid M] →               [inst_3 : AddCommMonoid N] →   
              [DistribMulAction R' M] → [_root_.Module R M] → [_root_.Module R N
] → [DistribMulAction R' N] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A typeclass for `SMul` structures which can be moved across a tensor product.

This typeclass is generated automatically from an `IsScalarTower` instance, but 
exists so that
we can also add an instance for `AddCommGroup.toIntModule`, allowing `z •` to be
 moved even if
`R` does not support negation.

Note that `Module R' (M ⊗[R] N)` is available even without this typeclass on `R'
`; it's only
needed if `TensorProduct.smul_tmul`, `TensorProduct.smul_tmul'`, or `TensorProdu
ct.tmul_smul` is
used.
-/
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : ∀ (r : R') (m : M) (n : N), (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n)

end

/-- Note that this provides the default `CompatibleSMul R R M N` instance through
`IsScalarTower.left`. -/
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Note that this provides the default `CompatibleSMul R R M N` instance through
`IsScalarTower.left`.
-/
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' R M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul R m]
    conv_rhs => rw [← one_smul R n]
    rw [← smul_assoc, ← smul_assoc]
    exact Quotient.sound' <| AddConGen.Rel.of _ _ <| Eqv.of_smul _ _ _⟩

/-- `smul` can be moved from one side of the product to the other . -/
/-
**TensorProduct.smul_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : 
M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
参数：r : R'；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.CompatibleSMul.smul_tmul`：∀ {R : Type u_1} {R' : Type u_4}
 {inst : CommSemiring R} {inst_1 : Monoid R'} {M : Type u_7} {N : Type u_8}   {i
nst_2 : AddCommMonoid M} {in…

--- 原说明 ---
`smul` can be moved from one side of the product to the other .
-/
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) ⊗ₜ n = m ⊗ₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _

set_option backward.privateInPublic true in
@[instance_reducible]
/-
**TensorProduct.addMonoidWithWrongNSMul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def addMonoidWithWrongNSMul : AddMonoid (M ⊗[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

attribute [local instance] addMonoidWithWrongNSMul in
/-- Auxiliary function to defining scalar multiplication on tensor product. -/
/-
**TensorProduct.SMul.aux** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct.SMul`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {M : Type u_7} →       {N
 : Type u_8} →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddCommM
onoid N] →             [inst_3 : _root_.Module R M] →               [inst_4 : _r
oot_.Module R N] →                 {R' : Type u_22} → [SMul R' M] → R' → FreeAdd
Monoid (M × N) →+ TensorProduct R M N
参数：M × N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function to defining scalar multiplication on tensor product.
-/
def SMul.aux {R' : Type*} [SMul R' M] (r : R') : FreeAddMonoid (M × N) →+ M ⊗[R] N :=
  FreeAddMonoid.lift fun p : M × N => (r • p.1) ⊗ₜ p.2
/-
**TensorProduct.SMul.aux_of** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct.SMul`。
形式化陈述：∀ {R : Type u_1} [inst : CommSemiring R] {M : Type u_7} {N : Type u_8} [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] {R' : Type u_22}   [inst_5 : SMul R' M] (r : R') 
(m : M) (n : N), (TensorProduct.SMul.aux r) (FreeAddMonoid.of (m, n)) = (r • m) 
⊗ₜ[R] n
参数：r : R'；m : M；n : N；TensorProduct.SMul.aux r；FreeAddMonoid.of (m, n)；r • m。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SMul.aux_of {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N) :
    SMul.aux r (.of (m, n)) = (r • m) ⊗ₜ[R] n :=
  rfl

variable [SMulCommClass R R' M] [SMulCommClass R R'' M]

/-- Given two modules over a commutative semiring `R`, if one of the factors carries a
(distributive) action of a second type of scalars `R'`, which commutes with the action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module which has the `R'`
action. Two natural ways in which this situation arises are:
* Extension of scalars
* A tensor product of a group representation with a module not carrying an action

Note that in the special case that `R = R'`, since `R` is commutative, we just get the usual scalar
action on a tensor product of two modules. This special case is important enough that, for
performance reasons, we define it explicitly below. -/
/-
**TensorProduct.leftHasSMul** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：leftHasSMul : SMul R' (M otimes[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two modules over a commutative semiring `R`, if one of the factors carries
 a
(distributive) action of a second type of scalars `R'`, which commutes with the 
action of `R`, then
the tensor product (over `R`) carries an action of `R'`.

This instance defines this `R'` action in the case that it is the left module wh
ich has the `R'`
action. Two natural ways in which this situation arises are:
* Extension of scalars
* A tensor product of a group representation with a module not carrying an actio
n

Note that in the special case that `R = R'`, since `R` is commutative, we just g
et the usual scalar
action on a tensor product of two modules. This special case is important enough
 that, for
performance reasons, we define it explicitly below.
-/
instance leftHasSMul : SMul R' (M ⊗[R] N) :=
  id ⟨fun r =>
    (addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ →+ M ⊗[R] N) <|
      AddCon.addConGen_le.2 fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero_right m =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_zero, SMul.aux_of, tmul_zero]
        | _, _, .of_add_left m₁ m₂ n =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, smul_add, add_tmul]
        | _, _, .of_add_right m n₁ n₂ =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, SMul.aux_of, tmul_add]
        | _, _, .of_smul s m n =>
          (AddCon.ker_rel _).2 <| by rw [SMul.aux_of, SMul.aux_of, ← smul_comm, smul_tmul]
        | _, _, .add_comm x y =>
          (AddCon.ker_rel _).2 <| by simp_rw [map_add, add_comm]⟩
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (M ⊗[R] N) :=
  TensorProduct.leftHasSMul
/-
**TensorProduct.smul_zero** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSemiring R] [inst_1 : Monoid 
R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommMonoid M] [inst_3 : AddComm
Monoid N] [inst_4 : DistribMulAction R' M] [inst_5 : _root_.Module R M]   [inst_
6 : _root_.Module R N] [inst_7 : SMulCommClass R R' M] (r : R'), r • 0 = 0
参数：r : R'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
protected theorem smul_zero (r : R') : r • (0 : M ⊗[R] N) = 0 :=
  map_zero _
/-
**TensorProduct.smul_add** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSemiring R] [inst_1 : Monoid 
R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommMonoid M] [inst_3 : AddComm
Monoid N] [inst_4 : DistribMulAction R' M] [inst_5 : _root_.Module R M]   [inst_
6 : _root_.Module R N] [inst_7 : SMulCommClass R R' M] (r : R') (x y : TensorPro
duct R M N),   r • (x + y) = r • x + r • y
参数：r : R'；x y : TensorProduct R M N；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
protected theorem smul_add (r : R') (x y : M ⊗[R] N) : r • (x + y) = r • x + r • y :=
  map_add _ _ _
/-
**TensorProduct.zero_smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} {R'' : Type u_5} [inst : CommSemiring R] [inst_1 : Semiri
ng R''] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R'' M] [inst_5 : _root_.Module R M]   [ins
t_6 : _root_.Module R N] [inst_7 : SMulCommClass R R'' M] (x : TensorProduct R M
 N), 0 • x = 0
参数：x : TensorProduct R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_zero`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSe
miring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddComm
Monoid M] [in…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `TensorProduct.smul_add`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSem
iring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommM
onoid M] [in…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
protected theorem zero_smul (x : M ⊗[R] N) : (0 : R'') • x = 0 :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add, ihx, ihy, add_zero]
/-
**TensorProduct.one_smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSemiring R] [inst_1 : Monoid 
R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommMonoid M] [inst_3 : AddComm
Monoid N] [inst_4 : DistribMulAction R' M] [inst_5 : _root_.Module R M]   [inst_
6 : _root_.Module R N] [inst_7 : SMulCommClass R R' M] (x : TensorProduct R M N)
, 1 • x = x
参数：x : TensorProduct R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_zero`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSe
miring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddComm
Monoid M] [in…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `TensorProduct.smul_add`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSem
iring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommM
onoid M] [in…
-/
protected theorem one_smul (x : M ⊗[R] N) : (1 : R') • x = x :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]
/-
**TensorProduct.add_smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：∀ {R : Type u_1} {R'' : Type u_5} [inst : CommSemiring R] [inst_1 : Semiri
ng R''] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommMonoid M] [inst_3 : Add
CommMonoid N] [inst_4 : _root_.Module R'' M] [inst_5 : _root_.Module R M]   [ins
t_6 : _root_.Module R N] [inst_7 : SMulCommClass R R'' M] (r s : R'') (x : Tenso
rProduct R M N),   (r + s) • x = r • x + s • x
参数：r s : R''；x : TensorProduct R M N；r + s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_zero`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSe
miring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddComm
Monoid M] [in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `TensorProduct.smul_add`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSem
iring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommM
onoid M] [in…
· 使用定理 `add_add_add_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c d 
: G), a + b + (c + d) = a + c + (b + d)
-/
protected theorem add_smul (r s : R'') (x : M ⊗[R] N) : (r + s) • x = r • x + s • x :=
  have : ∀ (r : R'') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx, ihy, add_add_add_comm]
/-
**TensorProduct.addMonoid** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：addMonoid : AddMonoid (M otimes[R] N) where nsmul_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addMonoid : AddMonoid (M ⊗[R] N) where
  nsmul_zero := by simp [TensorProduct.zero_smul]
  nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, forall_const]
/-
**TensorProduct.addCommMonoid** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：{R : Type u_1} →   [inst : CommSemiring R] →     {M : Type u_7} →       {N
 : Type u_8} →         [inst_1 : AddCommMonoid M] →           [inst_2 : AddCommM
onoid N] →             [inst_3 : _root_.Module R M] → [inst_4 : _root_.Module R 
N] → AddCommMonoid (TensorProduct R M N)
参数：TensorProduct R M N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommMonoid : AddCommMonoid (M ⊗[R] N) where

variable (R)
/-
**TensorProduct._root_.IsAddUnit.tmul_left** 是 Mathlib 中的一个定理，位于命名空间 `TensorProd
uct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsAddUnit.tmul_left {n : N} (hn : IsAddUnit n) (m : M) : IsAddUnit (m ⊗ₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hn ⊢
  have ⟨b, eq⟩ := hn
  exact ⟨m ⊗ₜ[R] b, by rw [← tmul_add, eq, tmul_zero]⟩
/-
**TensorProduct._root_.IsAddUnit.tmul_right** 是 Mathlib 中的一个定理，位于命名空间 `TensorPro
duct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsAddUnit.tmul_right {m : M} (hm : IsAddUnit m) (n : N) : IsAddUnit (m ⊗ₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hm ⊢
  have ⟨b, eq⟩ := hm
  exact ⟨b ⊗ₜ[R] n, by rw [← add_tmul, eq, zero_tmul]⟩

variable {R}
/-
**TensorProduct.leftDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：leftDistribMulAction : DistribMulAction R' (M otimes[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.one_smul`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSem
iring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommM
onoid M] [in…
· 使用定理 `TensorProduct.smul_zero`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSe
miring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddComm
Monoid M] [in…
· 使用定理 `TensorProduct.smul_add`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSem
iring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommM
onoid M] [in…
-/
instance leftDistribMulAction : DistribMulAction R' (M ⊗[R] N) :=
  have : ∀ (r : R') (m : M) (n : N), r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
        simp_rw [TensorProduct.smul_add]
        rw [ihx, ihy]
    one_smul := TensorProduct.one_smul
    smul_zero := TensorProduct.smul_zero }
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DistribMulAction R (M ⊗[R] N) :=
  TensorProduct.leftDistribMulAction
/-
**TensorProduct.smul_tmul'** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：smul_tmul' (r : R') (m : M) (n : N) : r • m otimesₜ[R] n = (r • m) otimesₜ
 n
参数：r : R'；m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_tmul' (r : R') (m : M) (n : N) : r • m ⊗ₜ[R] n = (r • m) ⊗ₜ n :=
  rfl

@[simp]
/-
**TensorProduct.tmul_smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : 
M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
参数：r : R'；x : M；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
-/
theorem tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N) :
    x ⊗ₜ (r • y) = r • x ⊗ₜ[R] y :=
  (smul_tmul _ _ _).symm
/-
**TensorProduct.smul_tmul_smul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) otimesₜ[R] (s • n) = (r
 * s) • m otimesₜ[R] n
参数：r s : R；m : M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) ⊗ₜ[R] (s • n) = (r * s) • m ⊗ₜ[R] n := by
  simp_rw [smul_tmul, tmul_smul, mul_smul]
/-
**TensorProduct.tmul_eq_smul_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_eq_smul_one_tmul {S : Type*} [Semiring S] [Module R S] [SMulCommClass
 R S S] (s : S) (m : M) : s otimesₜ[R] m = s • (1 otimesₜ[R] m)
参数：s : S；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
-/
theorem tmul_eq_smul_one_tmul {S : Type*} [Semiring S] [Module R S] [SMulCommClass R S S]
    (s : S) (m : M) : s ⊗ₜ[R] m = s • (1 ⊗ₜ[R] m) := by
  nth_rw 1 [← mul_one s, ← smul_eq_mul, smul_tmul']
/-
**TensorProduct.leftModule** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：leftModule : Module R'' (M otimes[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.add_smul`：∀ {R : Type u_1} {R'' : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring R''] {M : Type u_7} {N : Type u_8}   [inst_2 : AddC
ommMonoid M]…
· 使用定理 `TensorProduct.zero_smul`：∀ {R : Type u_1} {R'' : Type u_5} [inst : CommS
emiring R] [inst_1 : Semiring R''] {M : Type u_7} {N : Type u_8}   [inst_2 : Add
CommMonoid M]…
-/
instance leftModule : Module R'' (M ⊗[R] N) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (M ⊗[R] N) :=
  TensorProduct.leftModule
/-
**TensorProduct.** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M ⊗[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add, smul_add, hx, hy]

section

-- Like `R'`, `R'₂` provides a `DistribMulAction R'₂ (M ⊗[R] N)`
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M]
variable [SMulCommClass R R'₂ M]

/-- `SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)` -/
/-
**TensorProduct.smulCommClass_left** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M otim
es[R] N) where smul_comm r' r'₂ x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.smul_zero`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSe
miring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddComm
Monoid M] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `TensorProduct.smul_add`：∀ {R : Type u_1} {R' : Type u_4} [inst : CommSem
iring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8}   [inst_2 : AddCommM
onoid M] [in…

--- 原说明 ---
`SMulCommClass R' R'₂ M` implies `SMulCommClass R' R'₂ (M ⊗[R] N)`
-/
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M ⊗[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]

variable [SMul R'₂ R']

/-- `IsScalarTower R'₂ R' M` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
/-
**TensorProduct.isScalarTower_left** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M otim
es[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.smul_tmul'`：smul_tmul' (r : R') (m : M) (n : N) : r • m ot
imesₜ[R] n = (r • m) otimesₜ n
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂

--- 原说明 ---
`IsScalarTower R'₂ R' M` implies `IsScalarTower R'₂ R' (M ⊗[R] N)`
-/
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

variable [DistribMulAction R'₂ N] [DistribMulAction R' N]
variable [CompatibleSMul R R'₂ M N] [CompatibleSMul R R' M N]

/-- `IsScalarTower R'₂ R' N` implies `IsScalarTower R'₂ R' (M ⊗[R] N)` -/
/-
**TensorProduct.isScalarTower_right** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M oti
mes[R] N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂

--- 原说明 ---
`IsScalarTower R'₂ R' N` implies `IsScalarTower R'₂ R' (M ⊗[R] N)`
-/
instance isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M ⊗[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add, smul_add, smul_add, ihx, ihy]⟩

end

/-- A short-cut instance for the common case, where the requirements for the `compatible_smul`
instances are sufficient. -/
/-
**TensorProduct.isScalarTower** 是 Mathlib 中的一个实例，位于命名空间 `TensorProduct`。
形式化陈述：isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M o
times[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A short-cut instance for the common case, where the requirements for the `compat
ible_smul`
instances are sufficient.
-/
instance isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M ⊗[R] N) :=
  TensorProduct.isScalarTower_left

-- or right
variable (R M N) in
/-- The canonical bilinear map `M → N → M ⊗[R] N`. -/
/-
**TensorProduct.mk** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：mk : M ->ₗ[R] N ->ₗ[R] M otimes[R] N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂

--- 原说明 ---
The canonical bilinear map `M → N → M ⊗[R] N`.
-/
def mk : M →ₗ[R] N →ₗ[R] M ⊗[R] N :=
  LinearMap.mk₂ R (· ⊗ₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul

@[simp]
/-
**TensorProduct.mk_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：mk_apply (m : M) (n : N) : mk R M N m n = m otimesₜ n
参数：m : M；n : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_apply (m : M) (n : N) : mk R M N m n = m ⊗ₜ n :=
  rfl
/-
**TensorProduct.ite_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] : (if P then x₁ else 0
) otimesₜ[R] x₂ = if P then x₁ otimesₜ x₂ else 0
参数：x₁ : M；x₂ : N；P : Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
-/
theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) ⊗ₜ[R] x₂ = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
/-
**TensorProduct.tmul_ite** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] : (x₁ otimesₜ[R] if P 
then x₂ else 0) = if P then x₁ otimesₜ x₂ else 0
参数：x₁ : M；x₂ : N；P : Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ ⊗ₜ[R] if P then x₂ else 0) = if P then x₁ ⊗ₜ x₂ else 0 := by split_ifs <;> simp
/-
**TensorProduct.tmul_single** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_single {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [forall i, AddCom
mMonoid (M i)] [forall i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) : x 
otimesₜ[R] Pi.single i m j = (Pi.single i (x otimesₜ[R] m) : forall i, N otimes[
R] M i) j
参数：M i；M i；i : ι；x : N；m : M i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
-/
lemma tmul_single {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    x ⊗ₜ[R] Pi.single i m j = (Pi.single i (x ⊗ₜ[R] m) : ∀ i, N ⊗[R] M i) j := by
  by_cases h : i = j <;> aesop
/-
**TensorProduct.single_tmul** 是 Mathlib 中的一个引理，位于命名空间 `TensorProduct`。
形式化陈述：single_tmul {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [forall i, AddCom
mMonoid (M i)] [forall i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) : Pi
.single i m j otimesₜ[R] x = (Pi.single i (m otimesₜ[R] x) : forall i, M i otime
s[R] N) j
参数：M i；M i；i : ι；x : N；m : M i；j : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.single_eq_of_ne'`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι)
 → Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i ≠ i' → ∀ (x : M i), Pi.s
ingle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
-/
lemma single_tmul {ι : Type*} [DecidableEq ι] {M : ι → Type*} [∀ i, AddCommMonoid (M i)]
    [∀ i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    Pi.single i m j ⊗ₜ[R] x = (Pi.single i (m ⊗ₜ[R] x) : ∀ i, M i ⊗[R] N) j := by
  by_cases h : i = j <;> aesop

section

/-
**TensorProduct.sum_tmul** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：sum_tmul {α : Type*} (s : Finset α) (m : α -> M) (n : N) : (∑ a in s, m a)
 otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n
参数：s : Finset α；m : α -> M；n : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
-/
theorem sum_tmul {α : Type*} (s : Finset α) (m : α → M) (n : N) :
    (∑ a ∈ s, m a) ⊗ₜ[R] n = ∑ a ∈ s, m a ⊗ₜ[R] n := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, add_tmul, ih]
/-
**TensorProduct.tmul_sum** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α -> N) : (m otimesₜ[R] ∑
 a in s, n a) = ∑ a in s, m otimesₜ[R] n a
参数：m : M；s : Finset α；n : α -> N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.tmul_zero`：tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
-/
theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α → N) :
    (m ⊗ₜ[R] ∑ a ∈ s, n a) = ∑ a ∈ s, m ⊗ₜ[R] n a := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, tmul_add, ih]

end

variable (R M N)

/-- The simple (aka pure) elements span the tensor product. -/
/-
**TensorProduct.span_tmul_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
形式化陈述：span_tmul_eq_top : Submodule.span R { t : M otimes[R] N | exists m n, m ot
imesₜ n = t } = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…

--- 原说明 ---
The simple (aka pure) elements span the tensor product.
-/
theorem span_tmul_eq_top : Submodule.span R { t : M ⊗[R] N | ∃ m n, m ⊗ₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]
/-
**TensorProduct.map** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：map (f : M ->ₛₗ[σ₁₂] M₂) (g : N ->ₛₗ[σ₁₂] N₂) : M otimes[R] N ->ₛₗ[σ₁₂] M₂
 otimes[R₂] N₂
参数：f : M ->ₛₗ[σ₁₂] M₂；g : N ->ₛₗ[σ₁₂] N₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff, ← span_tmul_eq_top, Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩
/-
**TensorProduct.exists_eq_tmul_of_forall** 是 Mathlib 中的一个定理，位于命名空间 `TensorProduc
t`。
形式化陈述：exists_eq_tmul_of_forall (x : TensorProduct R M N) (h : forall (m₁ m₂ : M)
 (n₁ n₂ : N), exists m n, m₁ otimesₜ n₁ + m₂ otimesₜ n₂ = m otimesₜ[R] n) : exis
ts m n, x = m otimesₜ n
参数：x : TensorProduct R M N；h : forall (m₁ m₂ : M) (n₁ n₂ : N), exists m n, m₁ ot
imesₜ n₁ + m₂ otimesₜ n₂ = m otimesₜ[R] n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `TensorProduct.zero_tmul`：zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : ∀ (m₁ m₂ : M) (n₁ n₂ : N), ∃ m n, m₁ ⊗ₜ n₁ + m₂ ⊗ₜ n₂ = m ⊗ₜ[R] n) :
    ∃ m n, x = m ⊗ₜ n := by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

end Module
end TensorProduct
end Semiring

