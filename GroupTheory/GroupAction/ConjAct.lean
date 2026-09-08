/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Data.Fintype.Card
public import Mathlib.GroupTheory.GroupAction.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Conjugation action of a group on itself

This file defines the conjugation action of a group on itself. See also `MulAut.conj` for
the definition of conjugation as a homomorphism into the automorphism group.

## Main definitions

A type alias `ConjAct G` is introduced for a group `G`. The group `ConjAct G` acts on `G`
by conjugation. The group `ConjAct G` also acts on any normal subgroup of `G` by conjugation.

As a generalization, this also allows:
* `ConjAct Mˣ` to act on `M`, when `M` is a `Monoid`
* `ConjAct G₀` to act on `G₀`, when `G₀` is a `GroupWithZero`

## Implementation Notes

The scalar action in defined in this file can also be written using `MulAut.conj g • h`. This
has the advantage of not using the type alias `ConjAct`, but the downside of this approach
is that some theorems about the group actions will not apply when since this
`MulAut.conj g • h` describes an action of `MulAut G` on `G`, and not an action of `G`.

-/

@[expose] public section

assert_not_exists MonoidWithZero

variable (α M G : Type*)

/-- A type alias for a group `G`. `ConjAct G` acts on `G` by conjugation -/
/-
**ConjAct** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ConjAct : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type alias for a group `G`. `ConjAct G` acts on `G` by conjugation
-/
def ConjAct : Type _ :=
  G

namespace ConjAct

open MulAction Subgroup

variable {M G}

/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DivInvMonoid G] : DivInvMonoid (ConjAct G) := inferInstanceAs <| DivInvMonoid G
/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Group G] : Group (ConjAct G) := inferInstanceAs <| Group G
/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Fintype G] : Fintype (ConjAct G) := inferInstanceAs <| Fintype G

@[simp]
/-
**ConjAct.card** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl

section DivInvMonoid

variable [DivInvMonoid G]

/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/-- Reinterpret `g : ConjAct G` as an element of `G`. -/
/-
**ConjAct.ofConjAct** 是 Mathlib 中的一个定义，位于命名空间 `ConjAct`。
形式化陈述：ofConjAct : ConjAct G ≃* G where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `g : ConjAct G` as an element of `G`.
-/
def ofConjAct : ConjAct G ≃* G where
  toFun := id
  invFun := id
  map_mul' := fun _ _ => rfl

/-- Reinterpret `g : G` as an element of `ConjAct G`. -/
/-
**ConjAct.toConjAct** 是 Mathlib 中的一个定义，位于命名空间 `ConjAct`。
形式化陈述：toConjAct : G ≃* ConjAct G
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Reinterpret `g : G` as an element of `ConjAct G`.
-/
def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm

/-- A recursor for `ConjAct`, for use as `induction x` when `x : ConjAct G`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/-
**ConjAct.rec** 是 Mathlib 中的一个定义，位于命名空间 `ConjAct`。
形式化陈述：{G : Type u_3} →   [inst : DivInvMonoid G] → {C : ConjAct G → Sort u_4} → 
((g : G) → C (ConjAct.toConjAct g)) → (g : ConjAct G) → C g
参数：(g : G) → C (ConjAct.toConjAct g)；g : ConjAct G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A recursor for `ConjAct`, for use as `induction x` when `x : ConjAct G`.
-/
protected def rec {C : ConjAct G → Sort*} (h : ∀ g, C (toConjAct g)) : ∀ g, C g :=
  h

@[simp]
/-
**ConjAct.** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem «forall» (p : ConjAct G → Prop) : (∀ x : ConjAct G, p x) ↔ ∀ x : G, p (toConjAct x) :=
  id Iff.rfl

@[simp]
/-
**ConjAct.of_mul_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：of_mul_symm_eq : (@ofConjAct G _).symm = toConjAct
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_mul_symm_eq : (@ofConjAct G _).symm = toConjAct :=
  rfl

@[simp]
/-
**ConjAct.to_mul_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：to_mul_symm_eq : (@toConjAct G _).symm = ofConjAct
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem to_mul_symm_eq : (@toConjAct G _).symm = ofConjAct :=
  rfl

@[simp]
/-
**ConjAct.toConjAct_ofConjAct** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_ofConjAct (x : ConjAct G) : toConjAct (ofConjAct x) = x
参数：x : ConjAct G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConjAct_ofConjAct (x : ConjAct G) : toConjAct (ofConjAct x) = x :=
  rfl

@[simp]
/-
**ConjAct.ofConjAct_toConjAct** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：ofConjAct_toConjAct (x : G) : ofConjAct (toConjAct x) = x
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofConjAct_toConjAct (x : G) : ofConjAct (toConjAct x) = x :=
  rfl

@[simp]
/-
**ConjAct.ofConjAct_one** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：ofConjAct_one : ofConjAct (1 : ConjAct G) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofConjAct_one : ofConjAct (1 : ConjAct G) = 1 :=
  rfl

@[simp]
/-
**ConjAct.toConjAct_one** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_one : toConjAct (1 : G) = 1
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConjAct_one : toConjAct (1 : G) = 1 :=
  rfl

@[simp]
/-
**ConjAct.ofConjAct_inv** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹
参数：x : ConjAct G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹ :=
  rfl

@[simp]
/-
**ConjAct.toConjAct_inv** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹
参数：x : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹ :=
  rfl

@[simp]
/-
**ConjAct.ofConjAct_mul** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConj
Act y
参数：x y : ConjAct G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  rfl

@[simp]
/-
**ConjAct.toConjAct_mul** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y
参数：x y : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConjAct_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y :=
  rfl
/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul (ConjAct G) G where smul g h := ofConjAct g * h * (ofConjAct g)⁻¹
/-
**ConjAct.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)
⁻¹
参数：g : ConjAct G；h : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  rfl
/-
**ConjAct.toConjAct_smul** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_smul (g h : G) : toConjAct g • h = g * h * g⁻¹
参数：g h : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConjAct_smul (g h : G) : toConjAct g • h = g * h * g⁻¹ :=
  rfl

end DivInvMonoid

section Units

section Monoid

variable [Monoid M]

/-
**ConjAct.unitsScalar** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：unitsScalar : SMul (ConjAct Mˣ) M where smul g h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unitsScalar : SMul (ConjAct Mˣ) M where smul g h := ofConjAct g * h * ↑(ofConjAct g)⁻¹
/-
**ConjAct.units_smul_def** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofCo
njAct g)⁻¹
参数：g : ConjAct Mˣ；h : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl
/-
**ConjAct.unitsMulDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M where one_sm
ul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M where
  one_smul := by simp [units_smul_def]
  mul_smul := by simp [units_smul_def, mul_assoc]
  smul_mul := by simp [units_smul_def, mul_assoc]
  smul_one := by simp [units_smul_def]
/-
**ConjAct.unitsSMulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：unitsSMulCommClass [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M] 
: SMulCommClass α (ConjAct Mˣ) M where smul_comm a um m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.units_smul_def`：units_smul_def (g : ConjAct Mˣ) (h : M) : g • h 
= ofConjAct g * h * ↑(ofConjAct g)⁻¹
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
instance unitsSMulCommClass [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M] :
    SMulCommClass α (ConjAct Mˣ) M where
  smul_comm a um m := by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]
/-
**ConjAct.unitsSMulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：unitsSMulCommClass' [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M]
 : SMulCommClass (ConjAct Mˣ) α M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance unitsSMulCommClass' [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M] :
    SMulCommClass (ConjAct Mˣ) α M :=
  haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

end Monoid

end Units

variable [Group G]

/-
**ConjAct.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：coe_smul {G : Type*} [Group G] {H : Subgroup G} (g h : H) : (ConjAct.toCon
jAct g • h).1 = ConjAct.toConjAct g.1 • h.1
参数：g h : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul {G : Type*} [Group G] {H : Subgroup G} (g h : H) :
    (ConjAct.toConjAct g • h).1 = ConjAct.toConjAct g.1 • h.1 := by
  rfl
/-
**ConjAct.toConjAct_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_inv_smul (g h : G) : toConjAct g⁻¹ • h = g⁻¹ * h * g
参数：g h : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.toConjAct_smul`：toConjAct_smul (g h : G) : toConjAct g • h = g *
 h * g⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
-/
theorem toConjAct_inv_smul (g h : G) : toConjAct g⁻¹ • h = g⁻¹ * h * g := by
  rw [toConjAct_smul, inv_inv]

-- todo: this file is not in good order; I will refactor this after the PR
/-
**ConjAct.** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulDistribMulAction (ConjAct G) G where
  smul_mul := by simp [smul_def]
  smul_one := by simp [smul_def]
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]
/-
**ConjAct.smulCommClass** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] : SMu
lCommClass α (ConjAct G) G where smul_comm a ug g
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjAct.smul_def`：smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g
 * h * (ofConjAct g)⁻¹
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用引理 `smul_mul_assoc`：smul_mul_assoc [Mul β] [SMul α β] [IsScalarTower α β β] 
(r : α) (x y : β) : r • x * y = r • (x * y)
-/
instance smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] :
    SMulCommClass α (ConjAct G) G where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]
/-
**ConjAct.smulCommClass'** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`。
形式化陈述：smulCommClass' [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G] : SM
ulCommClass (ConjAct G) α G
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
-/
instance smulCommClass' [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G] :
    SMulCommClass (ConjAct G) α G :=
  haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _
/-
**ConjAct.smul_eq_mulAut_conj** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjA
ct g) h
参数：g : ConjAct G；h : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  rfl
/-
**ConjAct.toConjAct_smul_eq_mulAut_conj** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：toConjAct_smul_eq_mulAut_conj (g h : G) : ConjAct.toConjAct g • h = MulAut
.conj g h
参数：g h : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toConjAct_smul_eq_mulAut_conj (g h : G) : ConjAct.toConjAct g • h = MulAut.conj g h :=
  rfl

/-- The set of fixed points of the conjugation action of `G` on itself is the center of `G`. -/
/-
**ConjAct.fixedPoints_eq_center** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：fixedPoints_eq_center : fixedPoints (ConjAct G) G = center G
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The set of fixed points of the conjugation action of `G` on itself is the center
 of `G`.
-/
theorem fixedPoints_eq_center : fixedPoints (ConjAct G) G = center G := by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]

@[simp]
/-
**ConjAct.mem_orbit_conjAct** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：mem_orbit_conjAct {g h : G} : g in orbit (ConjAct G) h ↔ IsConj g h
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isConj_comm`：isConj_comm {g h : α} : IsConj g h ↔ IsConj h g
· 使用定理 `isConj_iff`：isConj_iff {a b : α} : IsConj a b ↔ exists c : α, c * a * c⁻
¹ = b
· 使用定理 `MulAction.mem_orbit_iff`：mem_orbit_iff {a₁ a₂ : α} : a₂ in orbit γ a₁ ↔ 
exists x : γ, x • a₁ = a₂
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_orbit_conjAct {g h : G} : g ∈ orbit (ConjAct G) h ↔ IsConj g h := by
  rw [isConj_comm, isConj_iff, mem_orbit_iff]; rfl
/-
**ConjAct.orbitRel_conjAct** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：orbitRel_conjAct : ⇑(orbitRel (ConjAct G) G) = IsConj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.orbitRel_apply`：orbitRel_apply {a b : α} : orbitRel G α a b ↔ 
a in orbit G b
· 使用定理 `ConjAct.mem_orbit_conjAct`：mem_orbit_conjAct {g h : G} : g in orbit (Con
jAct G) h ↔ IsConj g h
-/
theorem orbitRel_conjAct : ⇑(orbitRel (ConjAct G) G) = IsConj :=
  funext₂ fun g h => by rw [orbitRel_apply, mem_orbit_conjAct]
/-
**ConjAct.orbit_eq_carrier_conjClasses** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：orbit_eq_carrier_conjClasses (g : G) : orbit (ConjAct G) g = (ConjClasses.
mk g).carrier
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ConjClasses.mem_carrier_iff_mk_eq`：mem_carrier_iff_mk_eq {a : α} {b : Co
njClasses α} : a in carrier b ↔ ConjClasses.mk a = b
· 使用定理 `ConjClasses.mk_eq_mk_iff_isConj`：mk_eq_mk_iff_isConj {a b : α} : ConjCla
sses.mk a = ConjClasses.mk b ↔ IsConj a b
· 使用定理 `ConjAct.mem_orbit_conjAct`：mem_orbit_conjAct {g h : G} : g in orbit (Con
jAct G) h ↔ IsConj g h
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem orbit_eq_carrier_conjClasses (g : G) :
    orbit (ConjAct G) g = (ConjClasses.mk g).carrier := by
  ext h
  rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, mem_orbit_conjAct]
/-
**ConjAct.stabilizer_eq_centralizer** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
形式化陈述：stabilizer_eq_centralizer (g : G) : stabilizer (ConjAct G) g = centralizer
 {toConjAct g}
参数：g : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eq_mul_inv_iff_mul_eq`：eq_mul_inv_iff_mul_eq : a = b * c⁻¹ ↔ a * c = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_inv_eq_of_eq_mul`：mul_inv_eq_of_eq_mul (h : a = c * b) : a * b⁻¹ = c
-/
theorem stabilizer_eq_centralizer (g : G) :
    stabilizer (ConjAct G) g = centralizer {toConjAct g} :=
  le_antisymm (fun _ hg _ h ↦ h ▸ eq_mul_inv_iff_mul_eq.mp hg.symm) fun _ h =>
    mul_inv_eq_of_eq_mul (h g rfl).symm
/-
**ConjAct._root_.Subgroup.centralizer_eq_comap_stabilizer** 是 Mathlib 中的一个定理，位于命
名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subgroup.centralizer_eq_comap_stabilizer (g : G) :
    Subgroup.centralizer {g} = Subgroup.comap ConjAct.toConjAct.toMonoidHom
      (MulAction.stabilizer (ConjAct G) g) := by
  ext k
-- NOTE: `Subgroup.mem_centralizer_iff` should probably be stated
-- with the equality in the other direction
  simp only [mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [eq_comm]
  exact Iff.symm mul_inv_eq_iff_eq_mul

/-- As normal subgroups are closed under conjugation, they inherit the conjugation action
  of the underlying group. -/
/-
**ConjAct.Subgroup.conjAction** 是 Mathlib 中的一个定义，位于命名空间 `ConjAct.Subgroup`。
形式化陈述：{G : Type u_3} → [inst : Group G] → {H : Subgroup G} → [hH : H.Normal] → S
Mul (ConjAct G) ↥H
参数：ConjAct G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As normal subgroups are closed under conjugation, they inherit the conjugation a
ction
  of the underlying group.
-/
instance Subgroup.conjAction {H : Subgroup G} [hH : H.Normal] : SMul (ConjAct G) H :=
  ⟨fun g h => ⟨g • (h : G), hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩
/-
**ConjAct.Subgroup.val_conj_smul** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct.Subgroup`。
形式化陈述：∀ {G : Type u_3} [inst : Group G] {H : Subgroup G} [inst_1 : H.Normal] (g 
: ConjAct G) (h : ↥H), ↑(g • h) = g • ↑h
参数：g : ConjAct G；h : ↥H；g • h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Subgroup.val_conj_smul {H : Subgroup G} [H.Normal] (g : ConjAct G) (h : H) :
    ↑(g • h) = g • (h : G) :=
  rfl
/-
**ConjAct.Subgroup.conjMulDistribMulAction** 是 Mathlib 中的一个定义，位于命名空间 `ConjAct.Su
bgroup`。
形式化陈述：{G : Type u_3} → [inst : Group G] → {H : Subgroup G} → [H.Normal] → MulDis
tribMulAction (ConjAct G) ↥H
参数：ConjAct G。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ConjAct.Subgroup.val_conj_smul`：∀ {G : Type u_3} [inst : Group G] {H : S
ubgroup G} [inst_1 : H.Normal] (g : ConjAct G) (h : ↥H), ↑(g • h) = g • ↑h
-/
instance Subgroup.conjMulDistribMulAction {H : Subgroup G} [H.Normal] :
    MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.mulDistribMulAction H.subtype Subgroup.val_conj_smul

/-- Group conjugation on a normal subgroup. Analogous to `MulAut.conj`. -/
/-
**ConjAct._root_.MulAut.conjNormal** 是 Mathlib 中的一个定义，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Group conjugation on a normal subgroup. Analogous to `MulAut.conj`.
-/
def _root_.MulAut.conjNormal {H : Subgroup G} [H.Normal] : G →* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom

@[simp]
/-
**ConjAct._root_.MulAut.conjNormal_apply** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulAut.conjNormal_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ConjAct._root_.MulAut.conjNormal_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulAut.conjNormal_symm_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g := by
  change _ * g⁻¹⁻¹ = _
  rw [inv_inv]
  rfl
/-
**ConjAct._root_.MulAut.conjNormal_inv_apply** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulAut.conjNormal_inv_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conjNormal_symm_apply g h
/-
**ConjAct._root_.MulAut.conjNormal_val** 是 Mathlib 中的一个定理，位于命名空间 `ConjAct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulAut.conjNormal_val {H : Subgroup G} [H.Normal] {h : H} :
    MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun _ => rfl
/-
**ConjAct.normal_of_characteristic_of_normal** 是 Mathlib 中的一个实例，位于命名空间 `ConjAct`
。
形式化陈述：normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal] {K : S
ubgroup H} [h : K.Characteristic] : (K.map H.subtype).Normal
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subgroup.apply_coe_mem_map`：apply_coe_mem_map (f : G ->* N) (K : Subgrou
p G) (x : K) : f x in K.map f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `SetLike.ext_iff`：ext_iff : p = q ↔ forall x, x in p ↔ x in q
· 使用定理 `Subgroup.Characteristic.fixed`：∀ {G : Type u_1} [inst : Group G] {H : Su
bgroup G},   H.Characteristic → ∀ (ϕ : G ≃* G), Subgroup.comap ϕ.toMonoidHom H =
 H
-/
instance normal_of_characteristic_of_normal {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
    [h : K.Characteristic] : (K.map H.subtype).Normal :=
  ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact K.apply_coe_mem_map H.subtype
      ⟨_, (SetLike.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩

end ConjAct

section Units

variable [Monoid M]

/-- The stabilizer of `Mˣ` acting on itself by conjugation at `x : Mˣ` is exactly the
units of the centralizer of `x : M`. -/
@[simps! apply_coe_val symm_apply_val_coe]
/-
**unitsCentralizerEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：unitsCentralizerEquiv (x : Mˣ) : (Submonoid.centralizer ({↑x} : Set M))ˣ ≃
* MulAction.stabilizer (ConjAct Mˣ) x
参数：x : Mˣ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The stabilizer of `Mˣ` acting on itself by conjugation at `x : Mˣ` is exactly th
e
units of the centralizer of `x : M`.
-/
def unitsCentralizerEquiv (x : Mˣ) :
    (Submonoid.centralizer ({↑x} : Set M))ˣ ≃* MulAction.stabilizer (ConjAct Mˣ) x :=
  MulEquiv.symm
  { toFun := MonoidHom.toHomUnits <|
      { toFun := fun u ↦ ⟨↑(ConjAct.ofConjAct u.1 : Mˣ), by
          rintro x ⟨rfl⟩
          have : (u : ConjAct Mˣ) • x = x := u.2
          rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩,
        map_one' := rfl,
        map_mul' := fun _ _ ↦ rfl }
    invFun := fun u ↦
      ⟨ConjAct.toConjAct (Units.map (Submonoid.centralizer ({↑x} : Set M)).subtype u), by
      change _ • _ = _
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
      exact Units.ext <| (u.1.2 x <| Set.mem_singleton _).symm⟩
    map_mul' := map_mul _ }

end Units

