/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
module

public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Data.Set.Piecewise

/-!
# Pi instances for multiplicative actions

This file defines instances for `MulAction` and related structures on `Pi` types.

## See also

* `Mathlib/Algebra/Group/Action/Option.lean`
* `Mathlib/Algebra/Group/Action/Prod.lean`
* `Mathlib/Algebra/Group/Action/Sigma.lean`
* `Mathlib/Algebra/Group/Action/Sum.lean`
-/

public section

assert_not_exists MonoidWithZero

variable {ι M N : Type*} {α β γ : ι -> Type*} (i : ι)

namespace Pi

@[to_additive]
/--
Instance `smul'` / 实例 `smul'`

English:
instance smul'
  signature: [forall i, SMul (α i) (β i)]
  body: s i • x i

@[to_additive (attr := push ←)]

中文:
实例 smul'
  签名: [对任意 i, 标量乘法 (α i) (β i)]
  定义体: s i • x i

@[to_additive (attr := push ←)]
-/
instance smul' [forall i, SMul (α i) (β i)] : SMul (forall i, α i) (forall i, β i) where smul s x i := s i • x i

@[to_additive (attr := push ←)]
/--
lemma `smul_def'` / 引理 `smul_def'`

English:
lemma smul_def'
  given: [forall i, SMul (α i) (β i)] (s : forall i, α i) (x : forall i, β i)
  statement: s • x = fun i => s i • x i
  proof: rfl

@[to_additive (attr := simp)]

中文:
引理 smul_def'
  条件: [对任意 i, 标量乘法 (α i) (β i)] (s : 对任意 i, α i) (x : 对任意 i, β i)
  结论: s • x = fun i => s i • x i
  证明: rfl

@[to_additive (attr := simp)]
-/
lemma smul_def' [forall i, SMul (α i) (β i)] (s : forall i, α i) (x : forall i, β i) : s • x = fun i => s i • x i :=
  rfl

@[to_additive (attr := simp)]
/--
lemma `smul_apply'` / 引理 `smul_apply'`

English:
lemma smul_apply'
  given: [forall i, SMul (α i) (β i)] (s : forall i, α i) (x : forall i, β i)
  statement: (s • x) i = s i • x i
  proof: rfl

@[to_additive]

中文:
引理 smul_apply'
  条件: [对任意 i, 标量乘法 (α i) (β i)] (s : 对任意 i, α i) (x : 对任意 i, β i)
  结论: (s • x) i = s i • x i
  证明: rfl

@[to_additive]
-/
lemma smul_apply' [forall i, SMul (α i) (β i)] (s : forall i, α i) (x : forall i, β i) : (s • x) i = s i • x i :=
  rfl

@[to_additive]
/--
Instance `isScalarTower` / 实例 `isScalarTower`

English:
instance isScalarTower
  signature: [SMul M N] [forall i, SMul N (α i)] [forall i, SMul M (α i)]
  body: funext fun i => smul_assoc x y (z i)

@[to_additive]

中文:
实例 isScalarTower
  签名: [标量乘法 M N] [对任意 i, 标量乘法 N (α i)] [对任意 i, 标量乘法 M (α i)]
  定义体: funext fun i => smul_assoc x y (z i)

@[to_additive]

Depends on / 依赖: smul_assoc
-/
instance isScalarTower [SMul M N] [forall i, SMul N (α i)] [forall i, SMul M (α i)]
    [forall i, IsScalarTower M N (α i)] : IsScalarTower M N (forall i, α i) where
  smul_assoc x y z := funext fun i => smul_assoc x y (z i)

@[to_additive]
/--
Instance `isScalarTower'` / 实例 `isScalarTower'`

English:
instance isScalarTower'
  signature: [forall i, SMul M (α i)] [forall i, SMul (α i) (β i)] [forall i, SMul M (β i)]
  body: funext fun i => smul_assoc x (y i) (z i)

@[to_additive]

中文:
实例 isScalarTower'
  签名: [对任意 i, 标量乘法 M (α i)] [对任意 i, 标量乘法 (α i) (β i)] [对任意 i, 标量乘法 M (β i)]
  定义体: funext fun i => smul_assoc x (y i) (z i)

@[to_additive]

Depends on / 依赖: smul_assoc
-/
instance isScalarTower' [forall i, SMul M (α i)] [forall i, SMul (α i) (β i)] [forall i, SMul M (β i)]
    [forall i, IsScalarTower M (α i) (β i)] : IsScalarTower M (forall i, α i) (forall i, β i) where
  smul_assoc x y z := funext fun i => smul_assoc x (y i) (z i)

@[to_additive]
/--
Instance `isScalarTower''` / 实例 `isScalarTower''`

English:
instance isScalarTower''
  signature: [forall i, SMul (α i) (β i)] [forall i, SMul (β i) (γ i)] [forall i, SMul (α i) (γ i)]
  body: funext fun i => smul_assoc (x i) (y i) (z i)

@[to_additive]

中文:
实例 isScalarTower''
  签名: [对任意 i, 标量乘法 (α i) (β i)] [对任意 i, 标量乘法 (β i) (γ i)] [对任意 i, 标量乘法 (α i) (γ i)]
  定义体: funext fun i => smul_assoc (x i) (y i) (z i)

@[to_additive]

Depends on / 依赖: smul_assoc
-/
instance isScalarTower'' [forall i, SMul (α i) (β i)] [forall i, SMul (β i) (γ i)] [forall i, SMul (α i) (γ i)]
    [forall i, IsScalarTower (α i) (β i) (γ i)] : IsScalarTower (forall i, α i) (forall i, β i) (forall i, γ i) where
  smul_assoc x y z := funext fun i => smul_assoc (x i) (y i) (z i)

@[to_additive]
/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [forall i, SMul M (α i)] [forall i, SMul N (α i)] [forall i, SMulCommClass M N (α i)]
  body: funext fun i => smul_comm x y (z i)

@[to_additive]

中文:
实例 smulCommClass
  签名: [对任意 i, 标量乘法 M (α i)] [对任意 i, 标量乘法 N (α i)] [对任意 i, 标量交换类 M N (α i)]
  定义体: funext fun i => smul_comm x y (z i)

@[to_additive]

Depends on / 依赖: smul_comm
-/
instance smulCommClass [forall i, SMul M (α i)] [forall i, SMul N (α i)] [forall i, SMulCommClass M N (α i)] :
    SMulCommClass M N (forall i, α i) where
  smul_comm x y z := funext fun i => smul_comm x y (z i)

@[to_additive]
/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: [forall i, SMul M (β i)] [forall i, SMul (α i) (β i)]
  body: ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩

@[to_additive]

中文:
实例 smulCommClass'
  签名: [对任意 i, 标量乘法 M (β i)] [对任意 i, 标量乘法 (α i) (β i)]
  定义体: ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩

@[to_additive]

Depends on / 依赖: smul_comm
-/
instance smulCommClass' [forall i, SMul M (β i)] [forall i, SMul (α i) (β i)]
    [forall i, SMulCommClass M (α i) (β i)] : SMulCommClass M (forall i, α i) (forall i, β i) :=
  ⟨fun x y z => funext fun i => smul_comm x (y i) (z i)⟩

@[to_additive]
/--
Instance `smulCommClass''` / 实例 `smulCommClass''`

English:
instance smulCommClass''
  signature: [forall i, SMul (β i) (γ i)] [forall i, SMul (α i) (γ i)]
  body: funext fun i => smul_comm (x i) (y i) (z i)

@[to_additive]

中文:
实例 smulCommClass''
  签名: [对任意 i, 标量乘法 (β i) (γ i)] [对任意 i, 标量乘法 (α i) (γ i)]
  定义体: funext fun i => smul_comm (x i) (y i) (z i)

@[to_additive]

Depends on / 依赖: CancelCommMonoid, CancelCommMonoid.toCancelMonoid, smul_comm, toCancelMonoid
-/
instance smulCommClass'' [forall i, SMul (β i) (γ i)] [forall i, SMul (α i) (γ i)]
    [forall i, SMulCommClass (α i) (β i) (γ i)] : SMulCommClass (forall i, α i) (forall i, β i) (forall i, γ i) where
  smul_comm x y z := funext fun i => smul_comm (x i) (y i) (z i)

@[to_additive]
/--
Instance `isCentralScalar` / 实例 `isCentralScalar`

English:
instance isCentralScalar
  signature: [forall i, SMul M (α i)] [forall i, SMul Mᵐᵒᵖ (α i)] [forall i, IsCentralScalar M (α i)]
  body: funext fun _ => op_smul_eq_smul _ _

中文:
实例 isCentralScalar
  签名: [对任意 i, 标量乘法 M (α i)] [对任意 i, 标量乘法 Mᵐᵒᵖ (α i)] [对任意 i, 中心标量 M (α i)]
  定义体: funext fun _ => op_smul_eq_smul _ _

Depends on / 依赖: CancelMonoid, CancelMonoid.toIsCancelMul, op_smul_eq_smul, toIsCancelMul
-/
instance isCentralScalar [forall i, SMul M (α i)] [forall i, SMul Mᵐᵒᵖ (α i)] [forall i, IsCentralScalar M (α i)] :
    IsCentralScalar M (forall i, α i) where
  op_smul_eq_smul _ _ := funext fun _ => op_smul_eq_smul _ _

/-- If `α i` has a faithful scalar action for a given `i`, then so does `Π i, α i`. This is
not an instance as `i` cannot be inferred. -/
@[to_additive
/-- If `α i` has a faithful additive action for a given `i`, then
so does `Π i, α i`. This is not an instance as `i` cannot be inferred -/]
/--
lemma `faithfulSMul_at` / 引理 `faithfulSMul_at`

English:
lemma faithfulSMul_at
  given: [forall i, SMul M (α i)] [forall i, Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)]
  proof: eq_of_smul_eq_smul fun a : α i => by
    classical
    simpa using
      congr_fun (h <| Function.update (fun j => Classical.choice (‹forall i, Nonempty (α i)› j)) i a) i

@[to_additive]

中文:
引理 faithfulSMul_at
  条件: [对任意 i, 标量乘法 M (α i)] [对任意 i, 非空 (α i)] (i : ι) [忠实标量乘法 M (α i)]
  证明: eq_of_smul_eq_smul fun a : α i => by
    classical
    simpa using
      congr_fun (h <| Function.update (fun j => Classical.choice (‹forall i, Nonempty (α i)› j)) i a) i

@[to_additive]

Depends on / 依赖: Classical, Classical.choice, Function, Function.update, Nonempty, choice, classical, congr_fun, eq_of_smul_eq_smul, update
-/
lemma faithfulSMul_at [forall i, SMul M (α i)] [forall i, Nonempty (α i)] (i : ι) [FaithfulSMul M (α i)] :
    FaithfulSMul M (forall i, α i) where
  eq_of_smul_eq_smul h := eq_of_smul_eq_smul fun a : α i => by
    classical
    simpa using
      congr_fun (h <| Function.update (fun j => Classical.choice (‹forall i, Nonempty (α i)› j)) i a) i

@[to_additive]
/--
Instance `faithfulSMul` / 实例 `faithfulSMul`

English:
instance faithfulSMul
  signature: [Nonempty ι] [forall i, SMul M (α i)] [forall i, Nonempty (α i)]
  body: let ⟨i⟩ := ‹Nonempty ι›
  faithfulSMul_at i

@[to_additive]

中文:
实例 faithfulSMul
  签名: [非空 ι] [对任意 i, 标量乘法 M (α i)] [对任意 i, 非空 (α i)]
  定义体: let ⟨i⟩ := ‹Nonempty ι›
  faithfulSMul_at i

@[to_additive]

Depends on / 依赖: Nonempty, faithfulSMul_at
-/
instance faithfulSMul [Nonempty ι] [forall i, SMul M (α i)] [forall i, Nonempty (α i)]
    [forall i, FaithfulSMul M (α i)] : FaithfulSMul M (forall i, α i) :=
  let ⟨i⟩ := ‹Nonempty ι›
  faithfulSMul_at i

@[to_additive]
/--
Instance `mulAction` / 实例 `mulAction`

English:
instance mulAction
  signature: (M) {m : Monoid M} [forall i, MulAction M (α i)]
  body: funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _

@[to_additive]

中文:
实例 mulAction
  签名: (M) {m : 幺半群 M} [对任意 i, 乘法作用 M (α i)]
  定义体: funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _

@[to_additive]

Depends on / 依赖: mul_smul
-/
instance mulAction (M) {m : Monoid M} [forall i, MulAction M (α i)] : @MulAction M (forall i, α i) m where
  mul_smul _ _ _ := funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _

@[to_additive]
/--
Instance `mulAction'` / 实例 `mulAction'`

English:
instance mulAction'
  signature: {m : forall i, Monoid (α i)} [forall i, MulAction (α i) (β i)]
  body: funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _

中文:
实例 mulAction'
  签名: {m : 对任意 i, 幺半群 (α i)} [对任意 i, 乘法作用 (α i) (β i)]
  定义体: funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _

Depends on / 依赖: mul_smul
-/
instance mulAction' {m : forall i, Monoid (α i)} [forall i, MulAction (α i) (β i)] :
    @MulAction (forall i, α i) (forall i, β i)
      (@Pi.monoid ι α m) where
  mul_smul _ _ _ := funext fun _ => mul_smul _ _ _
  one_smul _ := funext fun _ => one_smul _ _

end Pi

namespace Function

/-- Non-dependent version of `Pi.smul`. Lean gets confused by the dependent instance if this
is not present. -/
@[to_additive
/-- Non-dependent version of `Pi.vadd`. Lean gets confused by the dependent instance
if this is not present. -/]
/--
Instance `hasSMul` / 实例 `hasSMul`

English:
instance hasSMul
  signature: {α : Type*} [SMul M α]
  body: Pi.instSMul

中文:
实例 hasSMul
  签名: {α : 类型} [标量乘法 M α]
  定义体: Pi.instSMul

Depends on / 依赖: Pi.instSMul, instSMul
-/
instance hasSMul {α : Type*} [SMul M α] : SMul M (ι -> α) := Pi.instSMul

/-- Non-dependent version of `Pi.smulCommClass`. Lean gets confused by the dependent instance if
this is not present. -/
@[to_additive
  /-- Non-dependent version of `Pi.vaddCommClass`. Lean gets confused by the dependent
  instance if this is not present. -/]
/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: {α : Type*} [SMul M α] [SMul N α] [SMulCommClass M N α]
  body: Pi.smulCommClass

@[to_additive]

中文:
实例 smulCommClass
  签名: {α : 类型} [标量乘法 M α] [标量乘法 N α] [标量交换类 M N α]
  定义体: Pi.smulCommClass

@[to_additive]

Depends on / 依赖: Pi.smulCommClass, smulCommClass
-/
instance smulCommClass {α : Type*} [SMul M α] [SMul N α] [SMulCommClass M N α] :
    SMulCommClass M N (ι -> α) := Pi.smulCommClass

@[to_additive]
/--
lemma `update_smul` / 引理 `update_smul`

English:
lemma update_smul
  statement: [forall i, SMul M (α i)] [DecidableEq ι] (c : M) (f₁ : forall i, α i)
  proof: funext fun j => (apply_update (β := α) (fun _ => (c • ·)) f₁ i x₁ j).symm

@[to_additive]

中文:
引理 update_smul
  结论: [对任意 i, 标量乘法 M (α i)] [DecidableEq ι] (c : M) (f₁ : 对任意 i, α i)
  证明: funext fun j => (apply_update (β := α) (fun _ => (c • ·)) f₁ i x₁ j).symm

@[to_additive]

Depends on / 依赖: apply_update
-/
lemma update_smul [forall i, SMul M (α i)] [DecidableEq ι] (c : M) (f₁ : forall i, α i)
    (i : ι) (x₁ : α i) : update (c • f₁) i (c • x₁) = c • update f₁ i x₁ :=
  funext fun j => (apply_update (β := α) (fun _ => (c • ·)) f₁ i x₁ j).symm

@[to_additive]
/--
lemma `extend_smul` / 引理 `extend_smul`

English:
lemma extend_smul
  given: {M α β : Type*} [SMul M β] (r : M) (f : ι -> α) (g : ι -> β) (e : α -> β)
  proof: by
  funext x
  classical
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;> rfl

中文:
引理 extend_smul
  条件: {M α β : 类型} [标量乘法 M β] (r : M) (f : ι -> α) (g : ι -> β) (e : α -> β)
  证明: by
  funext x
  classical
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;> rfl

Depends on / 依赖: Pi.smul_apply, classical, extend_def, smul_apply, split_ifs
-/
lemma extend_smul {M α β : Type*} [SMul M β] (r : M) (f : ι -> α) (g : ι -> β) (e : α -> β) :
    extend f (r • g) (r • e) = r • extend f g e := by
  funext x
  classical
  simp only [extend_def, Pi.smul_apply]
  split_ifs <;> rfl

end Function

namespace Set

@[to_additive]
/--
lemma `piecewise_smul` / 引理 `piecewise_smul`

English:
lemma piecewise_smul
  statement: [forall i, SMul M (α i)] (s : Set ι) [forall i, Decidable (i in s)]
  proof: s.piecewise_op (δ' := α) f₁ _ fun _ => (c • ·)

中文:
引理 piecewise_smul
  结论: [对任意 i, 标量乘法 M (α i)] (s : 集合 ι) [对任意 i, 可判定 (i in s)]
  证明: s.piecewise_op (δ' := α) f₁ _ fun _ => (c • ·)

Depends on / 依赖: piecewise_op, s.piecewise_op
-/
lemma piecewise_smul [forall i, SMul M (α i)] (s : Set ι) [forall i, Decidable (i in s)]
    (c : M) (f₁ g₁ : forall i, α i) : s.piecewise (c • f₁) (c • g₁) = c • s.piecewise f₁ g₁ :=
  s.piecewise_op (δ' := α) f₁ _ fun _ => (c • ·)

end Set
