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
variable {σ₁₂ : R ->+* R₂} {σ₂₃ : R₂ ->+* R₃} {σ₁₃ : R ->+* R₃}
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

/--
Inductive type `Eqv` / 归纳类型 `Eqv`

English:
inductive Eqv
  parameters: : FreeAddMonoid (M × N) -> FreeAddMonoid (M × N) -> Prop
  constructors (6):
    - of_zero_left: forall n : N, Eqv (.of (0, n)) 0
    - of_zero_right: forall m : M, Eqv (.of (m, 0)) 0
    - of_add_left: forall (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
    - of_add_right: forall (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
    - of_smul: forall (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
    - add_comm: forall x y, Eqv (x + y) (y + x)

中文:
归纳类型 Eqv
  参数: : FreeAddMonoid (M × N) -> FreeAddMonoid (M × N) -> 命题
  构造子 (6 个):
    - of_zero_left: 对任意 n : N, Eqv (.of (0, n)) 0
    - of_zero_right: 对任意 m : M, Eqv (.of (m, 0)) 0
    - of_add_left: 对任意 (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
    - of_add_right: 对任意 (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
    - of_smul: 对任意 (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
    - add_comm: 对任意 x y, Eqv (x + y) (y + x)
-/
inductive Eqv : FreeAddMonoid (M × N) -> FreeAddMonoid (M × N) -> Prop
  | of_zero_left : forall n : N, Eqv (.of (0, n)) 0
  | of_zero_right : forall m : M, Eqv (.of (m, 0)) 0
  | of_add_left : forall (m₁ m₂ : M) (n : N), Eqv (.of (m₁, n) + .of (m₂, n)) (.of (m₁ + m₂, n))
  | of_add_right : forall (m : M) (n₁ n₂ : N), Eqv (.of (m, n₁) + .of (m, n₂)) (.of (m, n₁ + n₂))
  | of_smul : forall (r : R) (m : M) (n : N), Eqv (.of (r • m, n)) (.of (m, r • n))
  | add_comm : forall x y, Eqv (x + y) (y + x)

end

end TensorProduct

variable (R) in
/--
Definition of `TensorProduct` / `TensorProduct` 的定义

English:
definition TensorProduct
  signature: : Type _
  body: (addConGen (TensorProduct.Eqv R M N)).Quotient
deriving Zero, Add, AddZeroClass, AddSemigroup

中文:
定义 张量积
  签名: : 类型 _
  定义体: (addConGen (TensorProduct.Eqv R M N)).Quotient
deriving Zero, Add, AddZeroClass, AddSemigroup

Depends on / 依赖: Quotient, TensorProduct, TensorProduct.Eqv, addConGen
-/
def TensorProduct : Type _ :=
  (addConGen (TensorProduct.Eqv R M N)).Quotient
deriving Zero, Add, AddZeroClass, AddSemigroup

set_option quotPrecheck false in
@[inherit_doc TensorProduct] scoped[TensorProduct] infixl:100 " otimes " => TensorProduct _

@[inherit_doc] scoped[TensorProduct] notation:100 M:100 " otimes[" R "] " N:101 => TensorProduct R M N

namespace TensorProduct

section Module

/--
Instance `addCommSemigroup` / 实例 `addCommSemigroup`

English:
instance addCommSemigroup
  signature: : AddCommSemigroup (M otimes[R] N) where
  body: fun x y =>
    AddCon.induction_on₂ x y fun _ _ =>
Quotient.sound' AddConGen.Rel.of _ _ Eqv.add_comm _ _

中文:
实例 addCommSemigroup
  签名: : 加法交换半群 (M otimes[R] N) where
  定义体: fun x y =>
    AddCon.induction_on₂ x y fun _ _ =>
Quotient.sound' AddConGen.Rel.of _ _ Eqv.add_comm _ _
-/
instance addCommSemigroup : AddCommSemigroup (M otimes[R] N) where
  add_comm := fun x y =>
    AddCon.induction_on₂ x y fun _ _ =>
Quotient.sound' AddConGen.Rel.of _ _ Eqv.add_comm _ _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (M otimes[R] N)
  body: ⟨0⟩

中文:
实例 :
  签名: 可居 (M otimes[R] N)
  定义体: ⟨0⟩
-/
instance : Inhabited (M otimes[R] N) :=
  ⟨0⟩

variable {M N}

variable (R) in
/--
Definition of `tmul` / `tmul` 的定义

English:
definition tmul
  signature: (m : M) (n : N)
  body: AddCon.mk' _ FreeAddMonoid.of (m, n)

中文:
定义 tmul
  签名: (m : M) (n : N)
  定义体: AddCon.mk' _ FreeAddMonoid.of (m, n)

Depends on / 依赖: AddCon, AddCon.mk, FreeAddMonoid, FreeAddMonoid.of
-/
def tmul (m : M) (n : N) : M otimes[R] N :=
AddCon.mk' _ FreeAddMonoid.of (m, n)

/-- The canonical function `M → N → M ⊗ N`. -/
infixl:100 " otimesₜ " => tmul _

/-- The canonical function `M → N → M ⊗ N`. -/
notation:100 x:100 " otimesₜ[" R "] " y:101 => tmul R x y

/-- Produces an arbitrary representation of the form `mₒ ⊗ₜ n₀ + ...`. -/
unsafe instance [Repr M] [Repr N] : Repr (M otimes[R] N) where
  reprPrec mn p :=
    let parts := mn.unquot.toList.map fun (mi, ni) =>
      Std.Format.group f!"{reprPrec mi 100} otimesₜ {reprPrec ni 101}"
    match parts with
    | [] => f!"0"
    | [part] => if p > 100 then Std.Format.bracketFill "(" part ")" else .fill part
    | parts =>
(if p > 65 then (Std.Format.bracketFill "(" · ")") else (.fill ·))
        .joinSep parts f!" +{Std.Format.line}"

@[elab_as_elim, induction_eliminator]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {motive : M otimes[R] N -> Prop} (z : M otimes[R] N)
  proof: AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih

中文:
定理 induction_on
  结论: {motive : M otimes[R] N -> 命题} (z : M otimes[R] N)
  证明: AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih
-/
protected theorem induction_on {motive : M otimes[R] N -> Prop} (z : M otimes[R] N)
    (zero : motive 0)
    (tmul : forall x y, motive <| x otimesₜ[R] y)
    (add : forall x y, motive x -> motive y -> motive (x + y)) : motive z :=
  AddCon.induction_on z fun x =>
    FreeAddMonoid.recOn x zero fun ⟨m, n⟩ y ih => by
      rw [AddCon.coe_add]
      exact add _ _ (tmul ..) ih

variable (M) in
@[simp]
/--
theorem `zero_tmul` / 定理 `zero_tmul`

English:
theorem zero_tmul
  given: (n : N)
  statement: (0 : M) otimesₜ[R] n = 0
  proof: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_left _

中文:
定理 zero_tmul
  条件: (n : N)
  结论: (0 : M) otimesₜ[R] n = 0
  证明: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_left _

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_zero_left, Quotient, Quotient.sound, of_zero_left
-/
theorem zero_tmul (n : N) : (0 : M) otimesₜ[R] n = 0 :=
Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_left _

/--
theorem `add_tmul` / 定理 `add_tmul`

English:
theorem add_tmul
  given: (m₁ m₂ : M) (n : N)
  statement: (m₁ + m₂) otimesₜ n = m₁ otimesₜ n + m₂ otimesₜ[R] n
  proof: Eq.symm Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_add_left _ _ _

中文:
定理 add_tmul
  条件: (m₁ m₂ : M) (n : N)
  结论: (m₁ + m₂) otimesₜ n = m₁ otimesₜ n + m₂ otimesₜ[R] n
  证明: Eq.symm Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_add_left _ _ _

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eq.symm, Eqv.of_add_left, Quotient, Quotient.sound, of_add_left
-/
theorem add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ n = m₁ otimesₜ n + m₂ otimesₜ[R] n :=
Eq.symm Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_add_left _ _ _

variable (N) in
@[simp]
/--
theorem `tmul_zero` / 定理 `tmul_zero`

English:
theorem tmul_zero
  given: (m : M)
  statement: m otimesₜ[R] (0 : N) = 0
  proof: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_right _

中文:
定理 tmul_zero
  条件: (m : M)
  结论: m otimesₜ[R] (0 : N) = 0
  证明: Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_right _

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eqv.of_zero_right, Quotient, Quotient.sound, of_zero_right
-/
theorem tmul_zero (m : M) : m otimesₜ[R] (0 : N) = 0 :=
Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_zero_right _

/--
theorem `tmul_add` / 定理 `tmul_add`

English:
theorem tmul_add
  given: (m : M) (n₁ n₂ : N)
  statement: m otimesₜ (n₁ + n₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
  proof: Eq.symm Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_add_right _ _ _

中文:
定理 tmul_add
  条件: (m : M) (n₁ n₂ : N)
  结论: m otimesₜ (n₁ + n₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
  证明: Eq.symm Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_add_right _ _ _

Depends on / 依赖: AddConGen, AddConGen.Rel.of, Eq.symm, Eqv.of_add_right, Quotient, Quotient.sound, of_add_right
-/
theorem tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n₂) = m otimesₜ n₁ + m otimesₜ[R] n₂ :=
Eq.symm Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_add_right _ _ _

/--
Instance `uniqueLeft` / 实例 `uniqueLeft`

English:
instance uniqueLeft
  signature: [Subsingleton M]
  body: 0
uniq z := z.induction_on rfl (fun x y => by rw [Subsingleton.elim x 0, zero_tmul]) by
    rintro _ _ rfl rfl; apply add_zero

中文:
实例 uniqueLeft
  签名: [子单例 M]
  定义体: 0
uniq z := z.induction_on rfl (fun x y => by rw [Subsingleton.elim x 0, zero_tmul]) by
    rintro _ _ rfl rfl; apply add_zero
-/
instance uniqueLeft [Subsingleton M] : Unique (M otimes[R] N) where
  default := 0
uniq z := z.induction_on rfl (fun x y => by rw [Subsingleton.elim x 0, zero_tmul]) by
    rintro _ _ rfl rfl; apply add_zero

/--
Instance `uniqueRight` / 实例 `uniqueRight`

English:
instance uniqueRight
  signature: [Subsingleton N]
  body: 0
uniq z := z.induction_on rfl (fun x y => by rw [Subsingleton.elim y 0, tmul_zero]) by
    rintro _ _ rfl rfl; apply add_zero

中文:
实例 uniqueRight
  签名: [子单例 N]
  定义体: 0
uniq z := z.induction_on rfl (fun x y => by rw [Subsingleton.elim y 0, tmul_zero]) by
    rintro _ _ rfl rfl; apply add_zero
-/
instance uniqueRight [Subsingleton N] : Unique (M otimes[R] N) where
  default := 0
uniq z := z.induction_on rfl (fun x y => by rw [Subsingleton.elim y 0, tmul_zero]) by
    rintro _ _ rfl rfl; apply add_zero

section

variable (R R' M N)

/--
Definition of `CompatibleSMul` / `CompatibleSMul` 的定义

English:
class CompatibleSMul
  parameters: [DistribMulAction R' N]
  axioms and operations (1):
    - smul_tmul : forall (r : R') (m : M) (n : N), (r • m) otimesₜ n = m otimesₜ[R] (r • n)

中文:
类 余mpatibleSMul
  参数: [分配乘法作用 R' N]
  公理与运算 (1 个):
    - smul_tmul : 对任意 (r : R') (m : M) (n : N), (r • m) otimesₜ n = m otimesₜ[R] (r • n)
-/
class CompatibleSMul [DistribMulAction R' N] : Prop where
  smul_tmul : forall (r : R') (m : M) (n : N), (r • m) otimesₜ n = m otimesₜ[R] (r • n)

end

/-- Note that this provides the default `CompatibleSMul R R M N` instance through
`IsScalarTower.left`. -/
instance (priority := 100) CompatibleSMul.isScalarTower [SMul R' R] [IsScalarTower R' R M]
    [DistribMulAction R' N] [IsScalarTower R' R N] : CompatibleSMul R R' M N :=
  ⟨fun r m n => by
    conv_lhs => rw [← one_smul R m]
    conv_rhs => rw [← one_smul R n]
    rw [← smul_assoc]; rw [← smul_assoc]
exact Quotient.sound' AddConGen.Rel.of _ _ Eqv.of_smul _ _ _⟩

/--
theorem `smul_tmul` / 定理 `smul_tmul`

English:
theorem smul_tmul
  given: [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N)
  proof: CompatibleSMul.smul_tmul _ _ _

中文:
定理 smul_tmul
  条件: [分配乘法作用 R' N] [余mpatibleSMul R R' M N] (r : R') (m : M) (n : N)
  证明: CompatibleSMul.smul_tmul _ _ _

Depends on / 依赖: CompatibleSMul, CompatibleSMul.smul_tmul, smul_tmul
-/
theorem smul_tmul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (m : M) (n : N) :
    (r • m) otimesₜ n = m otimesₜ[R] (r • n) :=
  CompatibleSMul.smul_tmul _ _ _

set_option backward.privateInPublic true in
@[instance_reducible]
/--
Definition of `addMonoidWithWrongNSMul` / `addMonoidWithWrongNSMul` 的定义

English:
definition addMonoidWithWrongNSMul
  signature: : AddMonoid (M otimes[R] N)
  body: { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

中文:
定义 addMonoidWithWrongNSMul
  签名: : 加法幺半群 (M otimes[R] N)
  定义体: { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }
-/
private def addMonoidWithWrongNSMul : AddMonoid (M otimes[R] N) :=
  { (addConGen (TensorProduct.Eqv R M N)).addMonoid with }

attribute [local instance] addMonoidWithWrongNSMul in
/--
Definition of `SMul.aux` / `SMul.aux` 的定义

English:
definition SMul.aux
  signature: {R' : Type*} [SMul R' M] (r : R')
  body: FreeAddMonoid.lift fun p : M × N => (r • p.1) otimesₜ p.2

中文:
定义 标量乘法.aux
  签名: {R' : 类型} [标量乘法 R' M] (r : R')
  定义体: FreeAddMonoid.lift fun p : M × N => (r • p.1) otimesₜ p.2

Depends on / 依赖: FreeAddMonoid, FreeAddMonoid.lift
-/
def SMul.aux {R' : Type*} [SMul R' M] (r : R') : FreeAddMonoid (M × N) ->+ M otimes[R] N :=
  FreeAddMonoid.lift fun p : M × N => (r • p.1) otimesₜ p.2

/--
theorem `SMul.aux_of` / 定理 `SMul.aux_of`

English:
theorem SMul.aux_of
  given: {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N)
  proof: rfl

中文:
定理 标量乘法.aux_of
  条件: {R' : 类型} [标量乘法 R' M] (r : R') (m : M) (n : N)
  证明: rfl
-/
theorem SMul.aux_of {R' : Type*} [SMul R' M] (r : R') (m : M) (n : N) :
    SMul.aux r (.of (m, n)) = (r • m) otimesₜ[R] n :=
  rfl

variable [SMulCommClass R R' M] [SMulCommClass R R'' M]

/--
Instance `leftHasSMul` / 实例 `leftHasSMul`

English:
instance leftHasSMul
  signature: : SMul R' (M otimes[R] N)
  body: id ⟨fun r =>
(addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ ->+ M otimes[R] N)
      AddCon.addConGen_le.2 fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero

中文:
实例 leftHasSMul
  签名: : 标量乘法 R' (M otimes[R] N)
  定义体: id ⟨fun r =>
(addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ ->+ M otimes[R] N)
      AddCon.addConGen_le.2 fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero

Depends on / 依赖: AddCon, AddCon.addConGen_le, AddCon.ker, AddCon.ker_rel, SMul.aux, SMul.aux_of, TensorProduct, TensorProduct.Eqv, addConGen, addConGen_le, add_tmul, aux_of, ker_rel, map_add, map_zero, of_add_left, of_add_right, of_zero_left, of_zero_right, otimes
-/
instance leftHasSMul : SMul R' (M otimes[R] N) :=
  id ⟨fun r =>
(addConGen (TensorProduct.Eqv R M N)).lift (SMul.aux r : _ ->+ M otimes[R] N)
      AddCon.addConGen_le.2 fun x y hxy =>
        match x, y, hxy with
        | _, _, .of_zero_left n =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, SMul.aux_of, smul_zero, zero_tmul]
        | _, _, .of_zero_right m =>
(AddCon.ker_rel _).2 by simp_rw [map_zero, SMul.aux_of, tmul_zero]
        | _, _, .of_add_left m₁ m₂ n =>
(AddCon.ker_rel _).2 by simp_rw [map_add, SMul.aux_of, smul_add, add_tmul]
        | _, _, .of_add_right m n₁ n₂ =>
(AddCon.ker_rel _).2 by simp_rw [map_add, SMul.aux_of, tmul_add]
        | _, _, .of_smul s m n =>
(AddCon.ker_rel _).2 by rw [SMul.aux_of, SMul.aux_of, ← smul_comm, smul_tmul]
        | _, _, .add_comm x y =>
(AddCon.ker_rel _).2 by simp_rw [map_add, add_comm]⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul R (M otimes[R] N)
  body: TensorProduct.leftHasSMul

中文:
实例 :
  签名: 标量乘法 R (M otimes[R] N)
  定义体: TensorProduct.leftHasSMul

Depends on / 依赖: TensorProduct, TensorProduct.leftHasSMul, leftHasSMul
-/
instance : SMul R (M otimes[R] N) :=
  TensorProduct.leftHasSMul

/--
theorem `smul_zero` / 定理 `smul_zero`

English:
theorem smul_zero
  given: (r : R')
  statement: r • (0 : M otimes[R] N) = 0
  proof: map_zero _

中文:
定理 smul_zero
  条件: (r : R')
  结论: r • (0 : M otimes[R] N) = 0
  证明: map_zero _
-/
protected theorem smul_zero (r : R') : r • (0 : M otimes[R] N) = 0 :=
  map_zero _

/--
theorem `smul_add` / 定理 `smul_add`

English:
theorem smul_add
  given: (r : R') (x y : M otimes[R] N)
  statement: r • (x + y) = r • x + r • y
  proof: map_add _ _ _

中文:
定理 smul_add
  条件: (r : R') (x y : M otimes[R] N)
  结论: r • (x + y) = r • x + r • y
  证明: map_add _ _ _
-/
protected theorem smul_add (r : R') (x y : M otimes[R] N) : r • (x + y) = r • x + r • y :=
  map_add _ _ _

/--
theorem `zero_smul` / 定理 `zero_smul`

English:
theorem zero_smul
  given: (x : M otimes[R] N)
  statement: (0 : R'') • x = 0
  proof: have : forall (r : R'') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add]; rw [ihx]; rw [ihy]; rw [add_zero]

中文:
定理 zero_smul
  条件: (x : M otimes[R] N)
  结论: (0 : R'') • x = 0
  证明: have : forall (r : R'') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add]; rw [ihx]; rw [ihy]; rw [add_zero]
-/
protected theorem zero_smul (x : M otimes[R] N) : (0 : R'') • x = 0 :=
  have : forall (r : R'') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, zero_smul, zero_tmul]) fun x y ihx ihy => by
    rw [TensorProduct.smul_add]; rw [ihx]; rw [ihy]; rw [add_zero]

/--
theorem `one_smul` / 定理 `one_smul`

English:
theorem one_smul
  given: (x : M otimes[R] N)
  statement: (1 : R') • x = x
  proof: have : forall (r : R') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]

中文:
定理 one_smul
  条件: (x : M otimes[R] N)
  结论: (1 : R') • x = x
  证明: have : forall (r : R') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]
-/
protected theorem one_smul (x : M otimes[R] N) : (1 : R') • x = x :=
  have : forall (r : R') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by rw [TensorProduct.smul_zero])
    (fun m n => by rw [this, one_smul])
    fun x y ihx ihy => by rw [TensorProduct.smul_add, ihx, ihy]

/--
theorem `add_smul` / 定理 `add_smul`

English:
theorem add_smul
  given: (r s : R'') (x : M otimes[R] N)
  statement: (r + s) • x = r • x + s • x
  proof: have : forall (r : R'') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx]; rw [ih

中文:
定理 add_smul
  条件: (r s : R'') (x : M otimes[R] N)
  结论: (r + s) • x = r • x + s • x
  证明: have : forall (r : R'') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx]; rw [ih
-/
protected theorem add_smul (r s : R'') (x : M otimes[R] N) : (r + s) • x = r • x + s • x :=
  have : forall (r : R'') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  x.induction_on (by simp_rw [TensorProduct.smul_zero, add_zero])
    (fun m n => by simp_rw [this, add_smul, add_tmul]) fun x y ihx ihy => by
    simp_rw [TensorProduct.smul_add]
    rw [ihx]; rw [ihy]; rw [add_add_add_comm]

/--
Instance `addMonoid` / 实例 `addMonoid`

English:
instance addMonoid
  signature: : AddMonoid (M otimes[R] N) where
  body: by simp [TensorProduct.zero_smul]
  nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, forall_const]

中文:
实例 addMonoid
  签名: : 加法幺半群 (M otimes[R] N) where
  定义体: by simp [TensorProduct.zero_smul]
  nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, forall_const]

Depends on / 依赖: TensorProduct, TensorProduct.add_smul, TensorProduct.one_smul, TensorProduct.zero_smul, add_smul, forall_const, nsmul_succ, one_smul, zero_smul
-/
instance addMonoid : AddMonoid (M otimes[R] N) where
  nsmul_zero := by simp [TensorProduct.zero_smul]
  nsmul_succ := by simp only [TensorProduct.one_smul, TensorProduct.add_smul, forall_const]

/--
Instance `addCommMonoid` / 实例 `addCommMonoid`

English:
instance addCommMonoid
  signature: : AddCommMonoid (M otimes[R] N) where

中文:
实例 addCommMonoid
  签名: : 加法交换幺半群 (M otimes[R] N) where
-/
instance addCommMonoid : AddCommMonoid (M otimes[R] N) where

variable (R)

/--
theorem `_root_.IsAddUnit.tmul_left` / 定理 `_root_.IsAddUnit.tmul_left`

English:
theorem _root_.IsAddUnit.tmul_left
  given: {n : N} (hn : IsAddUnit n) (m : M)
  statement: IsAddUnit (m otimesₜ[R] n)
  proof: by
  rw [isAddUnit_iff_exists_neg] at hn ⊢
  have ⟨b, eq⟩ := hn
  exact ⟨m otimesₜ[R] b, by rw [← tmul_add, eq, tmul_zero]⟩

中文:
定理 _root_.IsAddUnit.tmul_left
  条件: {n : N} (hn : IsAddUnit n) (m : M)
  结论: IsAddUnit (m otimesₜ[R] n)
  证明: by
  rw [isAddUnit_iff_exists_neg] at hn ⊢
  have ⟨b, eq⟩ := hn
  exact ⟨m otimesₜ[R] b, by rw [← tmul_add, eq, tmul_zero]⟩

Depends on / 依赖: isAddUnit_iff_exists_neg, tmul_add, tmul_zero
-/
theorem _root_.IsAddUnit.tmul_left {n : N} (hn : IsAddUnit n) (m : M) : IsAddUnit (m otimesₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hn ⊢
  have ⟨b, eq⟩ := hn
  exact ⟨m otimesₜ[R] b, by rw [← tmul_add, eq, tmul_zero]⟩

/--
theorem `_root_.IsAddUnit.tmul_right` / 定理 `_root_.IsAddUnit.tmul_right`

English:
theorem _root_.IsAddUnit.tmul_right
  given: {m : M} (hm : IsAddUnit m) (n : N)
  statement: IsAddUnit (m otimesₜ[R] n)
  proof: by
  rw [isAddUnit_iff_exists_neg] at hm ⊢
  have ⟨b, eq⟩ := hm
  exact ⟨b otimesₜ[R] n, by rw [← add_tmul, eq, zero_tmul]⟩

中文:
定理 _root_.IsAddUnit.tmul_right
  条件: {m : M} (hm : IsAddUnit m) (n : N)
  结论: IsAddUnit (m otimesₜ[R] n)
  证明: by
  rw [isAddUnit_iff_exists_neg] at hm ⊢
  have ⟨b, eq⟩ := hm
  exact ⟨b otimesₜ[R] n, by rw [← add_tmul, eq, zero_tmul]⟩

Depends on / 依赖: add_tmul, isAddUnit_iff_exists_neg, zero_tmul
-/
theorem _root_.IsAddUnit.tmul_right {m : M} (hm : IsAddUnit m) (n : N) : IsAddUnit (m otimesₜ[R] n) := by
  rw [isAddUnit_iff_exists_neg] at hm ⊢
  have ⟨b, eq⟩ := hm
  exact ⟨b otimesₜ[R] n, by rw [← add_tmul, eq, zero_tmul]⟩

variable {R}

/--
Instance `leftDistribMulAction` / 实例 `leftDistribMulAction`

English:
instance leftDistribMulAction
  signature: : DistribMulAction R' (M otimes[R] N)
  body: have : forall (r : R') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x

中文:
实例 leftDistribMulAction
  签名: : 分配乘法作用 R' (M otimes[R] N)
  定义体: have : forall (r : R') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x

Depends on / 依赖: TensorProduct, TensorProduct.one_smul, TensorProduct.smul_add, TensorProduct.smul_zero, induction_on, mul_smul, one_smul, simp_rw, smul_add, smul_zero, x.induction_on
-/
instance leftDistribMulAction : DistribMulAction R' (M otimes[R] N) :=
  have : forall (r : R') (m : M) (n : N), r • m otimesₜ[R] n = (r • m) otimesₜ n := fun _ _ _ => rfl
  { smul_add := fun r x y => TensorProduct.smul_add r x y
    mul_smul := fun r s x =>
      x.induction_on (by simp_rw [TensorProduct.smul_zero])
        (fun m n => by simp_rw [this, mul_smul]) fun x y ihx ihy => by
        simp_rw [TensorProduct.smul_add]
        rw [ihx]; rw [ihy]
    one_smul := TensorProduct.one_smul
    smul_zero := TensorProduct.smul_zero }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: DistribMulAction R (M otimes[R] N)
  body: TensorProduct.leftDistribMulAction

中文:
实例 :
  签名: 分配乘法作用 R (M otimes[R] N)
  定义体: TensorProduct.leftDistribMulAction

Depends on / 依赖: TensorProduct, TensorProduct.leftDistribMulAction, leftDistribMulAction
-/
instance : DistribMulAction R (M otimes[R] N) :=
  TensorProduct.leftDistribMulAction

/--
theorem `smul_tmul'` / 定理 `smul_tmul'`

English:
theorem smul_tmul'
  given: (r : R') (m : M) (n : N)
  statement: r • m otimesₜ[R] n = (r • m) otimesₜ n
  proof: rfl

@[simp]

中文:
定理 smul_tmul'
  条件: (r : R') (m : M) (n : N)
  结论: r • m otimesₜ[R] n = (r • m) otimesₜ n
  证明: rfl

@[simp]
-/
theorem smul_tmul' (r : R') (m : M) (n : N) : r • m otimesₜ[R] n = (r • m) otimesₜ n :=
  rfl

@[simp]
/--
theorem `tmul_smul` / 定理 `tmul_smul`

English:
theorem tmul_smul
  given: [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N)
  proof: (smul_tmul _ _ _).symm

中文:
定理 tmul_smul
  条件: [分配乘法作用 R' N] [余mpatibleSMul R R' M N] (r : R') (x : M) (y : N)
  证明: (smul_tmul _ _ _).symm

Depends on / 依赖: smul_tmul
-/
theorem tmul_smul [DistribMulAction R' N] [CompatibleSMul R R' M N] (r : R') (x : M) (y : N) :
    x otimesₜ (r • y) = r • x otimesₜ[R] y :=
  (smul_tmul _ _ _).symm

/--
theorem `smul_tmul_smul` / 定理 `smul_tmul_smul`

English:
theorem smul_tmul_smul
  given: (r s : R) (m : M) (n : N)
  statement: (r • m) otimesₜ[R] (s • n) = (r * s) • m otimesₜ[R] n
  proof: by
  simp_rw [smul_tmul, tmul_smul, mul_smul]

中文:
定理 smul_tmul_smul
  条件: (r s : R) (m : M) (n : N)
  结论: (r • m) otimesₜ[R] (s • n) = (r * s) • m otimesₜ[R] n
  证明: by
  simp_rw [smul_tmul, tmul_smul, mul_smul]

Depends on / 依赖: mul_smul, simp_rw, smul_tmul, tmul_smul
-/
theorem smul_tmul_smul (r s : R) (m : M) (n : N) : (r • m) otimesₜ[R] (s • n) = (r * s) • m otimesₜ[R] n := by
  simp_rw [smul_tmul, tmul_smul, mul_smul]

/--
theorem `tmul_eq_smul_one_tmul` / 定理 `tmul_eq_smul_one_tmul`

English:
theorem tmul_eq_smul_one_tmul
  statement: {S : Type*} [Semiring S] [Module R S] [SMulCommClass R S S]
  proof: by
  nth_rw 1 [← mul_one s, ← smul_eq_mul, smul_tmul']

中文:
定理 tmul_eq_smul_one_tmul
  结论: {S : 类型} [半环 S] [模 R S] [标量交换类 R S S]
  证明: by
  nth_rw 1 [← mul_one s, ← smul_eq_mul, smul_tmul']

Depends on / 依赖: mul_one, nth_rw, smul_eq_mul, smul_tmul
-/
theorem tmul_eq_smul_one_tmul {S : Type*} [Semiring S] [Module R S] [SMulCommClass R S S]
    (s : S) (m : M) : s otimesₜ[R] m = s • (1 otimesₜ[R] m) := by
  nth_rw 1 [← mul_one s, ← smul_eq_mul, smul_tmul']

/--
Instance `leftModule` / 实例 `leftModule`

English:
instance leftModule
  signature: : Module R'' (M otimes[R] N)
  body: { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }

中文:
实例 leftModule
  签名: : 模 R'' (M otimes[R] N)
  定义体: { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }

Depends on / 依赖: TensorProduct, TensorProduct.add_smul, TensorProduct.zero_smul, add_smul, zero_smul
-/
instance leftModule : Module R'' (M otimes[R] N) :=
  { add_smul := TensorProduct.add_smul
    zero_smul := TensorProduct.zero_smul }

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Module R (M otimes[R] N)
  body: TensorProduct.leftModule

中文:
实例 :
  签名: 模 R (M otimes[R] N)
  定义体: TensorProduct.leftModule

Depends on / 依赖: TensorProduct, TensorProduct.leftModule, leftModule
-/
instance : Module R (M otimes[R] N) :=
  TensorProduct.leftModule

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module
  signature: R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M otimes[R] N) where
  body: x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add]; rw [smul_add]; rw [hx]; rw [hy]

中文:
实例 [模
  签名: R''ᵐᵒᵖ M] [中心标量 R'' M] : 中心标量 R'' (M otimes[R] N) where
  定义体: x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add]; rw [smul_add]; rw [hx]; rw [hy]

Depends on / 依赖: induction_on, op_smul_eq_smul, smul_add, smul_tmul, smul_zero, x.induction_on
-/
instance [Module R''ᵐᵒᵖ M] [IsCentralScalar R'' M] : IsCentralScalar R'' (M otimes[R] N) where
  op_smul_eq_smul r x :=
    x.induction_on (by rw [smul_zero, smul_zero])
      (fun x y => by rw [smul_tmul', smul_tmul', op_smul_eq_smul]) fun x y hx hy => by
      rw [smul_add]; rw [smul_add]; rw [hx]; rw [hy]

section

-- Like `R'`, `R'₂` provides a `DistribMulAction R'₂ (M ⊗[R] N)`
variable {R'₂ : Type*} [Monoid R'₂] [DistribMulAction R'₂ M]
variable [SMulCommClass R R'₂ M]

/--
Instance `smulCommClass_left` / 实例 `smulCommClass_left`

English:
instance smulCommClass_left
  signature: [SMulCommClass R' R'₂ M]
  body: TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]

中文:
实例 smulCommClass_left
  签名: [标量交换类 R' R'₂ M]
  定义体: TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]

Depends on / 依赖: TensorProduct, TensorProduct.induction_on, TensorProduct.smul_add, TensorProduct.smul_zero, induction_on, simp_rw, smul_add, smul_comm, smul_tmul, smul_zero
-/
instance smulCommClass_left [SMulCommClass R' R'₂ M] : SMulCommClass R' R'₂ (M otimes[R] N) where
  smul_comm r' r'₂ x :=
    TensorProduct.induction_on x (by simp_rw [TensorProduct.smul_zero])
      (fun m n => by simp_rw [smul_tmul', smul_comm]) fun x y ihx ihy => by
      simp_rw [TensorProduct.smul_add]; rw [ihx, ihy]

variable [SMul R'₂ R']

/--
Instance `isScalarTower_left` / 实例 `isScalarTower_left`

English:
instance isScalarTower_left
  signature: [IsScalarTower R'₂ R' M]
  body: ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add]; rw [smul_add]; rw [smul_add]; rw [ihx]; rw [ihy]⟩

中文:
实例 isScalarTower_left
  签名: [标量塔 R'₂ R' M]
  定义体: ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add]; rw [smul_add]; rw [smul_add]; rw [ihx]; rw [ihy]⟩

Depends on / 依赖: induction_on, smul_add, smul_assoc, smul_tmul, x.induction_on
-/
instance isScalarTower_left [IsScalarTower R'₂ R' M] : IsScalarTower R'₂ R' (M otimes[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [smul_tmul', smul_tmul', smul_tmul', smul_assoc]) fun x y ihx ihy => by
      rw [smul_add]; rw [smul_add]; rw [smul_add]; rw [ihx]; rw [ihy]⟩

variable [DistribMulAction R'₂ N] [DistribMulAction R' N]
variable [CompatibleSMul R R'₂ M N] [CompatibleSMul R R' M N]

/--
Instance `isScalarTower_right` / 实例 `isScalarTower_right`

English:
instance isScalarTower_right
  signature: [IsScalarTower R'₂ R' N]
  body: ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add]; rw [smul_add]; rw [smul_add]; rw [ihx]; rw [ihy]⟩

中文:
实例 isScalarTower_right
  签名: [标量塔 R'₂ R' N]
  定义体: ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add]; rw [smul_add]; rw [smul_add]; rw [ihx]; rw [ihy]⟩

Depends on / 依赖: induction_on, smul_add, smul_assoc, tmul_smul, x.induction_on
-/
instance isScalarTower_right [IsScalarTower R'₂ R' N] : IsScalarTower R'₂ R' (M otimes[R] N) :=
  ⟨fun s r x =>
    x.induction_on (by simp)
      (fun m n => by rw [← tmul_smul, ← tmul_smul, ← tmul_smul, smul_assoc]) fun x y ihx ihy => by
      rw [smul_add]; rw [smul_add]; rw [smul_add]; rw [ihx]; rw [ihy]⟩

end

/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul R' R] [IsScalarTower R' R M]
  body: TensorProduct.isScalarTower_left

中文:
实例 isScalarTower
  签名: [标量乘法 R' R] [标量塔 R' R M]
  定义体: TensorProduct.isScalarTower_left

Depends on / 依赖: TensorProduct, TensorProduct.isScalarTower_left, isScalarTower_left
-/
instance isScalarTower [SMul R' R] [IsScalarTower R' R M] : IsScalarTower R' R (M otimes[R] N) :=
  TensorProduct.isScalarTower_left

-- or right
variable (R M N) in
/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : M ->ₗ[R] N ->ₗ[R] M otimes[R] N
  body: LinearMap.mk₂ R (· otimesₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul

@[simp]

中文:
定义 mk
  签名: : M ->ₗ[R] N ->ₗ[R] M otimes[R] N
  定义体: LinearMap.mk₂ R (· otimesₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul

@[simp]

Depends on / 依赖: LinearMap, LinearMap.mk, add_tmul, simp_rw, smul_tmul, tmul_add, tmul_smul
-/
def mk : M ->ₗ[R] N ->ₗ[R] M otimes[R] N :=
  LinearMap.mk₂ R (· otimesₜ ·) add_tmul (fun c m n => by simp_rw [smul_tmul, tmul_smul])
    tmul_add tmul_smul

@[simp]
/--
theorem `mk_apply` / 定理 `mk_apply`

English:
theorem mk_apply
  given: (m : M) (n : N)
  statement: mk R M N m n = m otimesₜ n
  proof: rfl

中文:
定理 mk_apply
  条件: (m : M) (n : N)
  结论: mk R M N m n = m otimesₜ n
  证明: rfl
-/
theorem mk_apply (m : M) (n : N) : mk R M N m n = m otimesₜ n :=
  rfl

/--
theorem `ite_tmul` / 定理 `ite_tmul`

English:
theorem ite_tmul
  given: (x₁ : M) (x₂ : N) (P : Prop) [Decidable P]
  proof: by split_ifs <;> simp

中文:
定理 ite_tmul
  条件: (x₁ : M) (x₂ : N) (P : 命题) [可判定 P]
  证明: by split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
theorem ite_tmul (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (if P then x₁ else 0) otimesₜ[R] x₂ = if P then x₁ otimesₜ x₂ else 0 := by split_ifs <;> simp

/--
theorem `tmul_ite` / 定理 `tmul_ite`

English:
theorem tmul_ite
  given: (x₁ : M) (x₂ : N) (P : Prop) [Decidable P]
  proof: by split_ifs <;> simp

中文:
定理 tmul_ite
  条件: (x₁ : M) (x₂ : N) (P : 命题) [可判定 P]
  证明: by split_ifs <;> simp

Depends on / 依赖: split_ifs
-/
theorem tmul_ite (x₁ : M) (x₂ : N) (P : Prop) [Decidable P] :
    (x₁ otimesₜ[R] if P then x₂ else 0) = if P then x₁ otimesₜ x₂ else 0 := by split_ifs <;> simp

/--
lemma `tmul_single` / 引理 `tmul_single`

English:
lemma tmul_single
  statement: {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [forall i, AddCommMonoid (M i)]
  proof: by
  by_cases h : i = j <;> aesop

中文:
引理 tmul_single
  结论: {ι : 类型} [DecidableEq ι] {M : ι -> 类型} [对任意 i, 加法交换幺半群 (M i)]
  证明: by
  by_cases h : i = j <;> aesop
-/
lemma tmul_single {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [forall i, AddCommMonoid (M i)]
    [forall i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    x otimesₜ[R] Pi.single i m j = (Pi.single i (x otimesₜ[R] m) : forall i, N otimes[R] M i) j := by
  by_cases h : i = j <;> aesop

/--
lemma `single_tmul` / 引理 `single_tmul`

English:
lemma single_tmul
  statement: {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [forall i, AddCommMonoid (M i)]
  proof: by
  by_cases h : i = j <;> aesop

中文:
引理 single_tmul
  结论: {ι : 类型} [DecidableEq ι] {M : ι -> 类型} [对任意 i, 加法交换幺半群 (M i)]
  证明: by
  by_cases h : i = j <;> aesop
-/
lemma single_tmul {ι : Type*} [DecidableEq ι] {M : ι -> Type*} [forall i, AddCommMonoid (M i)]
    [forall i, Module R (M i)] (i : ι) (x : N) (m : M i) (j : ι) :
    Pi.single i m j otimesₜ[R] x = (Pi.single i (m otimesₜ[R] x) : forall i, M i otimes[R] N) j := by
  by_cases h : i = j <;> aesop

section

/--
theorem `sum_tmul` / 定理 `sum_tmul`

English:
theorem sum_tmul
  given: {α : Type*} (s : Finset α) (m : α -> M) (n : N)
  proof: by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, add_tmul, ih]

中文:
定理 sum_tmul
  条件: {α : 类型} (s : 有限集 α) (m : α -> M) (n : N)
  证明: by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, add_tmul, ih]

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, add_tmul, classical, insert, sum_insert
-/
theorem sum_tmul {α : Type*} (s : Finset α) (m : α -> M) (n : N) :
    (∑ a in s, m a) otimesₜ[R] n = ∑ a in s, m a otimesₜ[R] n := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, add_tmul, ih]

/--
theorem `tmul_sum` / 定理 `tmul_sum`

English:
theorem tmul_sum
  given: (m : M) {α : Type*} (s : Finset α) (n : α -> N)
  proof: by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, tmul_add, ih]

中文:
定理 tmul_sum
  条件: (m : M) {α : 类型} (s : 有限集 α) (n : α -> N)
  证明: by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, tmul_add, ih]

Depends on / 依赖: Finset, Finset.induction, Finset.sum_insert, classical, insert, sum_insert, tmul_add
-/
theorem tmul_sum (m : M) {α : Type*} (s : Finset α) (n : α -> N) :
    (m otimesₜ[R] ∑ a in s, n a) = ∑ a in s, m otimesₜ[R] n a := by
  classical
    induction s using Finset.induction with
    | empty => simp
    | insert _ _ has ih => simp [Finset.sum_insert has, tmul_add, ih]

end

variable (R M N)

/--
theorem `span_tmul_eq_top` / 定理 `span_tmul_eq_top`

English:
theorem span_tmul_eq_top
  statement: Submodule.span R { t : M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤
  proof: by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]

中文:
定理 span_tmul_eq_top
  结论: 子模.span R { t : M otimes[R] N | 存在 m n, m otimesₜ n = t } = ⊤
  证明: by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]

Depends on / 依赖: Submodule, Submodule.add_mem, Submodule.mem_top, Submodule.subset_span, Submodule.zero_mem, add_mem, iff_true, induction_on, mem_top, subset_span, t.induction_on, zero_mem
-/
theorem span_tmul_eq_top : Submodule.span R { t : M otimes[R] N | exists m n, m otimesₜ n = t } = ⊤ := by
  ext t; simp only [Submodule.mem_top, iff_true]
  refine t.induction_on ?_ ?_ ?_
  · exact Submodule.zero_mem _
  · intro m n
    apply Submodule.subset_span
    use m, n
  · intro t₁ t₂ ht₁ ht₂
    exact Submodule.add_mem _ ht₁ ht₂

@[simp]
/--
theorem `map₂_mk_top_top_eq_top` / 定理 `map₂_mk_top_top_eq_top`

English:
theorem map₂_mk_top_top_eq_top
  statement: Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤
  proof: by
  rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩

中文:
定理 map₂_mk_top_top_eq_top
  结论: 子模.map₂ (mk R M N) ⊤ ⊤ = ⊤
  证明: by
  rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩

Depends on / 依赖: Submodule, Submodule.map, Submodule.span_mono, span_mono, span_tmul_eq_top, top_le_iff
-/
theorem map₂_mk_top_top_eq_top : Submodule.map₂ (mk R M N) ⊤ ⊤ = ⊤ := by
  rw [← top_le_iff]; rw [← span_tmul_eq_top]; rw [Submodule.map₂_eq_span_image2]
  exact Submodule.span_mono fun _ ⟨m, n, h⟩ => ⟨m, trivial, n, trivial, h⟩

/--
theorem `exists_eq_tmul_of_forall` / 定理 `exists_eq_tmul_of_forall`

English:
theorem exists_eq_tmul_of_forall
  statement: (x : TensorProduct R M N)
  proof: by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

中文:
定理 存在_eq_tmul_of_对任意
  结论: (x : 张量积 R M N)
  证明: by
  induction x with
  | zero =>
    use 0, 0
    rw [TensorProduct.zero_tmul]
  | tmul m n => use m, n
  | add x y h₁ h₂ =>
    obtain ⟨m₁, n₁, rfl⟩ := h₁
    obtain ⟨m₂, n₂, rfl⟩ := h₂
    apply h

Depends on / 依赖: TensorProduct, TensorProduct.zero_tmul, zero_tmul
-/
theorem exists_eq_tmul_of_forall (x : TensorProduct R M N)
    (h : forall (m₁ m₂ : M) (n₁ n₂ : N), exists m n, m₁ otimesₜ n₁ + m₂ otimesₜ n₂ = m otimesₜ[R] n) :
    exists m n, x = m otimesₜ n := by
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
