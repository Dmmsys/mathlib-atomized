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

/--
Definition of `ConjAct` / `ConjAct` 的定义

English:
definition ConjAct
  signature: : Type _
  body: G

中文:
定义 ConjAct
  签名: : Type _
  定义体: G
-/
def ConjAct : Type _ :=
  G

namespace ConjAct

open MulAction Subgroup

variable {M G}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [DivInvMonoid
  signature: G] : DivInvMonoid (ConjAct G)
  body: inferInstanceAs DivInvMonoid G

中文:
实例 [DivInvMonoid
  签名: G] : DivInvMonoid (ConjAct G)
  定义体: inferInstanceAs DivInvMonoid G

Depends on / 依赖: DivInvMonoid
-/
instance [DivInvMonoid G] : DivInvMonoid (ConjAct G) := inferInstanceAs DivInvMonoid G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Group
  signature: G] : Group (ConjAct G)
  body: inferInstanceAs Group G

中文:
实例 [Group
  签名: G] : Group (ConjAct G)
  定义体: inferInstanceAs Group G
-/
instance [Group G] : Group (ConjAct G) := inferInstanceAs Group G

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Fintype
  signature: G] : Fintype (ConjAct G)
  body: inferInstanceAs Fintype G

@[simp]

中文:
实例 [Fintype
  签名: G] : Fintype (ConjAct G)
  定义体: inferInstanceAs Fintype G

@[simp]

Depends on / 依赖: Fintype
-/
instance [Fintype G] : Fintype (ConjAct G) := inferInstanceAs Fintype G

@[simp]
/--
theorem `card` / 定理 `card`

English:
theorem card
  given: [Fintype G]
  statement: Fintype.card (ConjAct G) = Fintype.card G
  proof: rfl

中文:
定理 card
  条件: [Fintype G]
  结论: Fintype.card (ConjAct G) = Fintype.card G
  证明: rfl
-/
theorem card [Fintype G] : Fintype.card (ConjAct G) = Fintype.card G :=
  rfl

section DivInvMonoid

variable [DivInvMonoid G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ConjAct G)
  body: ⟨1⟩

中文:
实例 :
  签名: Inhabited (ConjAct G)
  定义体: ⟨1⟩
-/
instance : Inhabited (ConjAct G) :=
  ⟨1⟩

/--
Definition of `ofConjAct` / `ofConjAct` 的定义

English:
definition ofConjAct
  signature: : ConjAct G ≃* G where
  body: id
  invFun := id
  map_mul' := fun _ _ => rfl

中文:
定义 ofConjAct
  签名: : ConjAct G ≃* G where
  定义体: id
  invFun := id
  map_mul' := fun _ _ => rfl
-/
def ofConjAct : ConjAct G ≃* G where
  toFun := id
  invFun := id
  map_mul' := fun _ _ => rfl

/--
Definition of `toConjAct` / `toConjAct` 的定义

English:
definition toConjAct
  signature: : G ≃* ConjAct G
  body: ofConjAct.symm

中文:
定义 toConjAct
  签名: : G ≃* ConjAct G
  定义体: ofConjAct.symm

Depends on / 依赖: ofConjAct, ofConjAct.symm
-/
def toConjAct : G ≃* ConjAct G :=
  ofConjAct.symm

/-- A recursor for `ConjAct`, for use as `induction x` when `x : ConjAct G`. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: {C : ConjAct G -> Sort*} (h : forall g, C (toConjAct g))
  body: h

@[simp]

中文:
定义 rec
  签名: {C : ConjAct G -> Sort*} (h : 对任意 g, C (toConjAct g))
  定义体: h

@[simp]
-/
protected def rec {C : ConjAct G -> Sort*} (h : forall g, C (toConjAct g)) : forall g, C g :=
  h

@[simp]
/--
theorem `«forall»` / 定理 `«forall»`

English:
theorem «forall»
  given: (p : ConjAct G -> Prop)
  statement: (forall x : ConjAct G, p x) ↔ forall x : G, p (toConjAct x)
  proof: id Iff.rfl

@[simp]

中文:
定理 «forall»
  条件: (p : ConjAct G -> 命题)
  结论: (对任意 x : ConjAct G, p x) ↔ 对任意 x : G, p (toConjAct x)
  证明: id Iff.rfl

@[simp]
-/
theorem «forall» (p : ConjAct G -> Prop) : (forall x : ConjAct G, p x) ↔ forall x : G, p (toConjAct x) :=
  id Iff.rfl

@[simp]
/--
theorem `of_mul_symm_eq` / 定理 `of_mul_symm_eq`

English:
theorem of_mul_symm_eq
  statement: (@ofConjAct G _).symm = toConjAct
  proof: rfl

@[simp]

中文:
定理 of_mul_symm_eq
  结论: (@ofConjAct G _).symm = toConjAct
  证明: rfl

@[simp]
-/
theorem of_mul_symm_eq : (@ofConjAct G _).symm = toConjAct :=
  rfl

@[simp]
/--
theorem `to_mul_symm_eq` / 定理 `to_mul_symm_eq`

English:
theorem to_mul_symm_eq
  statement: (@toConjAct G _).symm = ofConjAct
  proof: rfl

@[simp]

中文:
定理 to_mul_symm_eq
  结论: (@toConjAct G _).symm = ofConjAct
  证明: rfl

@[simp]
-/
theorem to_mul_symm_eq : (@toConjAct G _).symm = ofConjAct :=
  rfl

@[simp]
/--
theorem `toConjAct_ofConjAct` / 定理 `toConjAct_ofConjAct`

English:
theorem toConjAct_ofConjAct
  given: (x : ConjAct G)
  statement: toConjAct (ofConjAct x) = x
  proof: rfl

@[simp]

中文:
定理 toConjAct_ofConjAct
  条件: (x : ConjAct G)
  结论: toConjAct (ofConjAct x) = x
  证明: rfl

@[simp]
-/
theorem toConjAct_ofConjAct (x : ConjAct G) : toConjAct (ofConjAct x) = x :=
  rfl

@[simp]
/--
theorem `ofConjAct_toConjAct` / 定理 `ofConjAct_toConjAct`

English:
theorem ofConjAct_toConjAct
  given: (x : G)
  statement: ofConjAct (toConjAct x) = x
  proof: rfl

@[simp]

中文:
定理 ofConjAct_toConjAct
  条件: (x : G)
  结论: ofConjAct (toConjAct x) = x
  证明: rfl

@[simp]
-/
theorem ofConjAct_toConjAct (x : G) : ofConjAct (toConjAct x) = x :=
  rfl

@[simp]
/--
theorem `ofConjAct_one` / 定理 `ofConjAct_one`

English:
theorem ofConjAct_one
  statement: ofConjAct (1 : ConjAct G) = 1
  proof: rfl

@[simp]

中文:
定理 ofConjAct_one
  结论: ofConjAct (1 : ConjAct G) = 1
  证明: rfl

@[simp]
-/
theorem ofConjAct_one : ofConjAct (1 : ConjAct G) = 1 :=
  rfl

@[simp]
/--
theorem `toConjAct_one` / 定理 `toConjAct_one`

English:
theorem toConjAct_one
  statement: toConjAct (1 : G) = 1
  proof: rfl

@[simp]

中文:
定理 toConjAct_one
  结论: toConjAct (1 : G) = 1
  证明: rfl

@[simp]
-/
theorem toConjAct_one : toConjAct (1 : G) = 1 :=
  rfl

@[simp]
/--
theorem `ofConjAct_inv` / 定理 `ofConjAct_inv`

English:
theorem ofConjAct_inv
  given: (x : ConjAct G)
  statement: ofConjAct x⁻¹ = (ofConjAct x)⁻¹
  proof: rfl

@[simp]

中文:
定理 ofConjAct_inv
  条件: (x : ConjAct G)
  结论: ofConjAct x⁻¹ = (ofConjAct x)⁻¹
  证明: rfl

@[simp]
-/
theorem ofConjAct_inv (x : ConjAct G) : ofConjAct x⁻¹ = (ofConjAct x)⁻¹ :=
  rfl

@[simp]
/--
theorem `toConjAct_inv` / 定理 `toConjAct_inv`

English:
theorem toConjAct_inv
  given: (x : G)
  statement: toConjAct x⁻¹ = (toConjAct x)⁻¹
  proof: rfl

@[simp]

中文:
定理 toConjAct_inv
  条件: (x : G)
  结论: toConjAct x⁻¹ = (toConjAct x)⁻¹
  证明: rfl

@[simp]
-/
theorem toConjAct_inv (x : G) : toConjAct x⁻¹ = (toConjAct x)⁻¹ :=
  rfl

@[simp]
/--
theorem `ofConjAct_mul` / 定理 `ofConjAct_mul`

English:
theorem ofConjAct_mul
  given: (x y : ConjAct G)
  statement: ofConjAct (x * y) = ofConjAct x * ofConjAct y
  proof: rfl

@[simp]

中文:
定理 ofConjAct_mul
  条件: (x y : ConjAct G)
  结论: ofConjAct (x * y) = ofConjAct x * ofConjAct y
  证明: rfl

@[simp]
-/
theorem ofConjAct_mul (x y : ConjAct G) : ofConjAct (x * y) = ofConjAct x * ofConjAct y :=
  rfl

@[simp]
/--
theorem `toConjAct_mul` / 定理 `toConjAct_mul`

English:
theorem toConjAct_mul
  given: (x y : G)
  statement: toConjAct (x * y) = toConjAct x * toConjAct y
  proof: rfl

中文:
定理 toConjAct_mul
  条件: (x y : G)
  结论: toConjAct (x * y) = toConjAct x * toConjAct y
  证明: rfl
-/
theorem toConjAct_mul (x y : G) : toConjAct (x * y) = toConjAct x * toConjAct y :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (ConjAct G) G
  body: ofConjAct g * h * (ofConjAct g)⁻¹

中文:
实例 :
  签名: SMul (ConjAct G) G
  定义体: ofConjAct g * h * (ofConjAct g)⁻¹

Depends on / 依赖: ofConjAct
-/
instance : SMul (ConjAct G) G where smul g h := ofConjAct g * h * (ofConjAct g)⁻¹

/--
theorem `smul_def` / 定理 `smul_def`

English:
theorem smul_def
  given: (g : ConjAct G) (h : G)
  statement: g • h = ofConjAct g * h * (ofConjAct g)⁻¹
  proof: rfl

中文:
定理 smul_def
  条件: (g : ConjAct G) (h : G)
  结论: g • h = ofConjAct g * h * (ofConjAct g)⁻¹
  证明: rfl
-/
theorem smul_def (g : ConjAct G) (h : G) : g • h = ofConjAct g * h * (ofConjAct g)⁻¹ :=
  rfl

/--
theorem `toConjAct_smul` / 定理 `toConjAct_smul`

English:
theorem toConjAct_smul
  given: (g h : G)
  statement: toConjAct g • h = g * h * g⁻¹
  proof: rfl

中文:
定理 toConjAct_smul
  条件: (g h : G)
  结论: toConjAct g • h = g * h * g⁻¹
  证明: rfl
-/
theorem toConjAct_smul (g h : G) : toConjAct g • h = g * h * g⁻¹ :=
  rfl

end DivInvMonoid

section Units

section Monoid

variable [Monoid M]

/--
Instance `unitsScalar` / 实例 `unitsScalar`

English:
instance unitsScalar
  signature: : SMul (ConjAct Mˣ) M where smul g h
  body: ofConjAct g * h * ↑(ofConjAct g)⁻¹

中文:
实例 unitsScalar
  签名: : SMul (ConjAct Mˣ) M where smul g h
  定义体: ofConjAct g * h * ↑(ofConjAct g)⁻¹

Depends on / 依赖: ofConjAct
-/
instance unitsScalar : SMul (ConjAct Mˣ) M where smul g h := ofConjAct g * h * ↑(ofConjAct g)⁻¹

/--
theorem `units_smul_def` / 定理 `units_smul_def`

English:
theorem units_smul_def
  given: (g : ConjAct Mˣ) (h : M)
  statement: g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹
  proof: rfl

中文:
定理 units_smul_def
  条件: (g : ConjAct Mˣ) (h : M)
  结论: g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹
  证明: rfl
-/
theorem units_smul_def (g : ConjAct Mˣ) (h : M) : g • h = ofConjAct g * h * ↑(ofConjAct g)⁻¹ :=
  rfl

/--
Instance `unitsMulDistribMulAction` / 实例 `unitsMulDistribMulAction`

English:
instance unitsMulDistribMulAction
  signature: : MulDistribMulAction (ConjAct Mˣ) M where
  body: by simp [units_smul_def]
  mul_smul := by simp [units_smul_def, mul_assoc]
  smul_mul := by simp [units_smul_def, mul_assoc]
  smul_one := by simp [units_smul_def]

中文:
实例 unitsMulDistribMulAction
  签名: : MulDistribMulAction (ConjAct Mˣ) M where
  定义体: by simp [units_smul_def]
  mul_smul := by simp [units_smul_def, mul_assoc]
  smul_mul := by simp [units_smul_def, mul_assoc]
  smul_one := by simp [units_smul_def]

Depends on / 依赖: mul_assoc, mul_smul, smul_mul, smul_one, units_smul_def
-/
instance unitsMulDistribMulAction : MulDistribMulAction (ConjAct Mˣ) M where
  one_smul := by simp [units_smul_def]
  mul_smul := by simp [units_smul_def, mul_assoc]
  smul_mul := by simp [units_smul_def, mul_assoc]
  smul_one := by simp [units_smul_def]


/--
Instance `unitsSMulCommClass` / 实例 `unitsSMulCommClass`

English:
instance unitsSMulCommClass
  signature: [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M]
  body: by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]

中文:
实例 unitsSMulCommClass
  签名: [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M]
  定义体: by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]

Depends on / 依赖: mul_smul_comm, smul_mul_assoc, units_smul_def
-/
instance unitsSMulCommClass [SMul α M] [SMulCommClass α M M] [IsScalarTower α M M] :
    SMulCommClass α (ConjAct Mˣ) M where
  smul_comm a um m := by rw [units_smul_def, units_smul_def, mul_smul_comm, smul_mul_assoc]

/--
Instance `unitsSMulCommClass'` / 实例 `unitsSMulCommClass'`

English:
instance unitsSMulCommClass'
  signature: [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M]
  body: haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

中文:
实例 unitsSMulCommClass'
  签名: [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M]
  定义体: haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance unitsSMulCommClass' [SMul α M] [SMulCommClass M α M] [IsScalarTower α M M] :
    SMulCommClass (ConjAct Mˣ) α M :=
  haveI : SMulCommClass α M M := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

end Monoid

end Units

variable [Group G]

/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: {G : Type*} [Group G] {H : Subgroup G} (g h : H)
  proof: by
  rfl

中文:
定理 coe_smul
  条件: {G : 类型} [Group G] {H : Subgroup G} (g h : H)
  证明: by
  rfl
-/
theorem coe_smul {G : Type*} [Group G] {H : Subgroup G} (g h : H) :
    (ConjAct.toConjAct g • h).1 = ConjAct.toConjAct g.1 • h.1 := by
  rfl

/--
theorem `toConjAct_inv_smul` / 定理 `toConjAct_inv_smul`

English:
theorem toConjAct_inv_smul
  given: (g h : G)
  statement: toConjAct g⁻¹ • h = g⁻¹ * h * g
  proof: by
  rw [toConjAct_smul]; rw [inv_inv]

中文:
定理 toConjAct_inv_smul
  条件: (g h : G)
  结论: toConjAct g⁻¹ • h = g⁻¹ * h * g
  证明: by
  rw [toConjAct_smul]; rw [inv_inv]

Depends on / 依赖: inv_inv, toConjAct_smul
-/
theorem toConjAct_inv_smul (g h : G) : toConjAct g⁻¹ • h = g⁻¹ * h * g := by
  rw [toConjAct_smul]; rw [inv_inv]

-- todo: this file is not in good order; I will refactor this after the PR

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MulDistribMulAction (ConjAct G) G
  body: by simp [smul_def]
  smul_one := by simp [smul_def]
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

中文:
实例 :
  签名: MulDistribMulAction (ConjAct G) G
  定义体: by simp [smul_def]
  smul_one := by simp [smul_def]
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

Depends on / 依赖: mul_assoc, mul_smul, one_smul, smul_def, smul_one
-/
instance : MulDistribMulAction (ConjAct G) G where
  smul_mul := by simp [smul_def]
  smul_one := by simp [smul_def]
  one_smul := by simp [smul_def]
  mul_smul := by simp [smul_def, mul_assoc]

/--
Instance `smulCommClass` / 实例 `smulCommClass`

English:
instance smulCommClass
  signature: [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G]
  body: by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

中文:
实例 smulCommClass
  签名: [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G]
  定义体: by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

Depends on / 依赖: mul_smul_comm, smul_def, smul_mul_assoc
-/
instance smulCommClass [SMul α G] [SMulCommClass α G G] [IsScalarTower α G G] :
    SMulCommClass α (ConjAct G) G where
  smul_comm a ug g := by rw [smul_def, smul_def, mul_smul_comm, smul_mul_assoc]

/--
Instance `smulCommClass'` / 实例 `smulCommClass'`

English:
instance smulCommClass'
  signature: [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G]
  body: haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _

中文:
实例 smulCommClass'
  签名: [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G]
  定义体: haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _

Depends on / 依赖: SMulCommClass, SMulCommClass.symm
-/
instance smulCommClass' [SMul α G] [SMulCommClass G α G] [IsScalarTower α G G] :
    SMulCommClass (ConjAct G) α G :=
  haveI := SMulCommClass.symm G α G
  SMulCommClass.symm _ _ _

/--
theorem `smul_eq_mulAut_conj` / 定理 `smul_eq_mulAut_conj`

English:
theorem smul_eq_mulAut_conj
  given: (g : ConjAct G) (h : G)
  statement: g • h = MulAut.conj (ofConjAct g) h
  proof: rfl

中文:
定理 smul_eq_mulAut_conj
  条件: (g : ConjAct G) (h : G)
  结论: g • h = MulAut.conj (ofConjAct g) h
  证明: rfl
-/
theorem smul_eq_mulAut_conj (g : ConjAct G) (h : G) : g • h = MulAut.conj (ofConjAct g) h :=
  rfl

/--
theorem `toConjAct_smul_eq_mulAut_conj` / 定理 `toConjAct_smul_eq_mulAut_conj`

English:
theorem toConjAct_smul_eq_mulAut_conj
  given: (g h : G)
  statement: ConjAct.toConjAct g • h = MulAut.conj g h
  proof: rfl

中文:
定理 toConjAct_smul_eq_mulAut_conj
  条件: (g h : G)
  结论: ConjAct.toConjAct g • h = MulAut.conj g h
  证明: rfl
-/
theorem toConjAct_smul_eq_mulAut_conj (g h : G) : ConjAct.toConjAct g • h = MulAut.conj g h :=
  rfl

/--
theorem `fixedPoints_eq_center` / 定理 `fixedPoints_eq_center`

English:
theorem fixedPoints_eq_center
  statement: fixedPoints (ConjAct G) G = center G
  proof: by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]

@[simp]

中文:
定理 fixedPoints_eq_center
  结论: fixedPoints (ConjAct G) G = center G
  证明: by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]

@[simp]

Depends on / 依赖: mem_center_iff, mul_inv_eq_iff_eq_mul, smul_def
-/
theorem fixedPoints_eq_center : fixedPoints (ConjAct G) G = center G := by
  ext x
  simp [mem_center_iff, smul_def, mul_inv_eq_iff_eq_mul]

@[simp]
/--
theorem `mem_orbit_conjAct` / 定理 `mem_orbit_conjAct`

English:
theorem mem_orbit_conjAct
  given: {g h : G}
  statement: g in orbit (ConjAct G) h ↔ IsConj g h
  proof: by
  rw [isConj_comm]; rw [isConj_iff]; rw [mem_orbit_iff]; rfl

中文:
定理 mem_orbit_conjAct
  条件: {g h : G}
  结论: g in orbit (ConjAct G) h ↔ IsConj g h
  证明: by
  rw [isConj_comm]; rw [isConj_iff]; rw [mem_orbit_iff]; rfl

Depends on / 依赖: isConj_comm, isConj_iff, mem_orbit_iff
-/
theorem mem_orbit_conjAct {g h : G} : g in orbit (ConjAct G) h ↔ IsConj g h := by
  rw [isConj_comm]; rw [isConj_iff]; rw [mem_orbit_iff]; rfl

/--
theorem `orbitRel_conjAct` / 定理 `orbitRel_conjAct`

English:
theorem orbitRel_conjAct
  statement: ⇑(orbitRel (ConjAct G) G) = IsConj
  proof: funext₂ fun g h => by rw [orbitRel_apply, mem_orbit_conjAct]

中文:
定理 orbitRel_conjAct
  结论: ⇑(orbitRel (ConjAct G) G) = IsConj
  证明: funext₂ fun g h => by rw [orbitRel_apply, mem_orbit_conjAct]

Depends on / 依赖: mem_orbit_conjAct, orbitRel_apply
-/
theorem orbitRel_conjAct : ⇑(orbitRel (ConjAct G) G) = IsConj :=
  funext₂ fun g h => by rw [orbitRel_apply, mem_orbit_conjAct]

/--
theorem `orbit_eq_carrier_conjClasses` / 定理 `orbit_eq_carrier_conjClasses`

English:
theorem orbit_eq_carrier_conjClasses
  given: (g : G)
  proof: by
  ext h
  rw [ConjClasses.mem_carrier_iff_mk_eq]; rw [ConjClasses.mk_eq_mk_iff_isConj]; rw [mem_orbit_conjAct]

中文:
定理 orbit_eq_carrier_conjClasses
  条件: (g : G)
  证明: by
  ext h
  rw [ConjClasses.mem_carrier_iff_mk_eq]; rw [ConjClasses.mk_eq_mk_iff_isConj]; rw [mem_orbit_conjAct]

Depends on / 依赖: ConjClasses, ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj, mem_carrier_iff_mk_eq, mem_orbit_conjAct, mk_eq_mk_iff_isConj
-/
theorem orbit_eq_carrier_conjClasses (g : G) :
    orbit (ConjAct G) g = (ConjClasses.mk g).carrier := by
  ext h
  rw [ConjClasses.mem_carrier_iff_mk_eq]; rw [ConjClasses.mk_eq_mk_iff_isConj]; rw [mem_orbit_conjAct]

/--
theorem `stabilizer_eq_centralizer` / 定理 `stabilizer_eq_centralizer`

English:
theorem stabilizer_eq_centralizer
  given: (g : G)
  proof: le_antisymm (fun _ hg _ h => h ▸ eq_mul_inv_iff_mul_eq.mp hg.symm) fun _ h =>
    mul_inv_eq_of_eq_mul (h g rfl).symm

中文:
定理 stabilizer_eq_centralizer
  条件: (g : G)
  证明: le_antisymm (fun _ hg _ h => h ▸ eq_mul_inv_iff_mul_eq.mp hg.symm) fun _ h =>
    mul_inv_eq_of_eq_mul (h g rfl).symm

Depends on / 依赖: eq_mul_inv_iff_mul_eq, eq_mul_inv_iff_mul_eq.mp, hg.symm, le_antisymm, mul_inv_eq_of_eq_mul
-/
theorem stabilizer_eq_centralizer (g : G) :
    stabilizer (ConjAct G) g = centralizer {toConjAct g} :=
  le_antisymm (fun _ hg _ h => h ▸ eq_mul_inv_iff_mul_eq.mp hg.symm) fun _ h =>
    mul_inv_eq_of_eq_mul (h g rfl).symm

/--
theorem `_root_.Subgroup.centralizer_eq_comap_stabilizer` / 定理 `_root_.Subgroup.centralizer_eq_comap_stabilizer`

English:
theorem _root_.Subgroup.centralizer_eq_comap_stabilizer
  given: (g : G)
  proof: by
  ext k

中文:
定理 _root_.Subgroup.centralizer_eq_comap_stabilizer
  条件: (g : G)
  证明: by
  ext k
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

/--
Instance `Subgroup.conjAction` / 实例 `Subgroup.conjAction`

English:
instance Subgroup.conjAction
  signature: {H : Subgroup G} [hH : H.Normal]
  body: ⟨fun g h => ⟨g • (h : G), hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩

中文:
实例 Subgroup.conjAction
  签名: {H : Subgroup G} [hH : H.Normal]
  定义体: ⟨fun g h => ⟨g • (h : G), hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩

Depends on / 依赖: conj_mem, hH.conj_mem, ofConjAct
-/
instance Subgroup.conjAction {H : Subgroup G} [hH : H.Normal] : SMul (ConjAct G) H :=
  ⟨fun g h => ⟨g • (h : G), hH.conj_mem h.1 h.2 (ofConjAct g)⟩⟩

/--
theorem `Subgroup.val_conj_smul` / 定理 `Subgroup.val_conj_smul`

English:
theorem Subgroup.val_conj_smul
  given: {H : Subgroup G} [H.Normal] (g : ConjAct G) (h : H)
  proof: rfl

中文:
定理 Subgroup.val_conj_smul
  条件: {H : Subgroup G} [H.Normal] (g : ConjAct G) (h : H)
  证明: rfl
-/
theorem Subgroup.val_conj_smul {H : Subgroup G} [H.Normal] (g : ConjAct G) (h : H) :
    ↑(g • h) = g • (h : G) :=
  rfl

/--
Instance `Subgroup.conjMulDistribMulAction` / 实例 `Subgroup.conjMulDistribMulAction`

English:
instance Subgroup.conjMulDistribMulAction
  signature: {H : Subgroup G} [H.Normal]
  body: Subtype.coe_injective.mulDistribMulAction H.subtype Subgroup.val_conj_smul

中文:
实例 Subgroup.conjMulDistribMulAction
  签名: {H : Subgroup G} [H.Normal]
  定义体: Subtype.coe_injective.mulDistribMulAction H.subtype Subgroup.val_conj_smul

Depends on / 依赖: H.subtype, Subgroup, Subgroup.val_conj_smul, Subtype, Subtype.coe_injective.mulDistribMulAction, coe_injective, mulDistribMulAction, subtype, val_conj_smul
-/
instance Subgroup.conjMulDistribMulAction {H : Subgroup G} [H.Normal] :
    MulDistribMulAction (ConjAct G) H :=
  Subtype.coe_injective.mulDistribMulAction H.subtype Subgroup.val_conj_smul

/--
Definition of `_root_.MulAut.conjNormal` / `_root_.MulAut.conjNormal` 的定义

English:
definition _root_.MulAut.conjNormal
  signature: {H : Subgroup G} [H.Normal]
  body: (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom

@[simp]

中文:
定义 _root_.MulAut.conjNormal
  签名: {H : Subgroup G} [H.Normal]
  定义体: (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom

@[simp]

Depends on / 依赖: ConjAct, MulDistribMulAction, MulDistribMulAction.toMulAut, toConjAct, toConjAct.toMonoidHom, toMonoidHom, toMulAut
-/
def _root_.MulAut.conjNormal {H : Subgroup G} [H.Normal] : G ->* MulAut H :=
  (MulDistribMulAction.toMulAut (ConjAct G) H).comp toConjAct.toMonoidHom

@[simp]
/--
theorem `_root_.MulAut.conjNormal_apply` / 定理 `_root_.MulAut.conjNormal_apply`

English:
theorem _root_.MulAut.conjNormal_apply
  given: {H : Subgroup G} [H.Normal] (g : G) (h : H)
  proof: rfl

中文:
定理 _root_.MulAut.conjNormal_apply
  条件: {H : Subgroup G} [H.Normal] (g : G) (h : H)
  证明: rfl
-/
theorem _root_.MulAut.conjNormal_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑(MulAut.conjNormal g h) = g * h * g⁻¹ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
theorem `_root_.MulAut.conjNormal_symm_apply` / 定理 `_root_.MulAut.conjNormal_symm_apply`

English:
theorem _root_.MulAut.conjNormal_symm_apply
  given: {H : Subgroup G} [H.Normal] (g : G) (h : H)
  proof: by
  change _ * g⁻¹⁻¹ = _
  rw [inv_inv]
  rfl

中文:
定理 _root_.MulAut.conjNormal_symm_apply
  条件: {H : Subgroup G} [H.Normal] (g : G) (h : H)
  证明: by
  change _ * g⁻¹⁻¹ = _
  rw [inv_inv]
  rfl

Depends on / 依赖: inv_inv
-/
theorem _root_.MulAut.conjNormal_symm_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g).symm h) = g⁻¹ * h * g := by
  change _ * g⁻¹⁻¹ = _
  rw [inv_inv]
  rfl

/--
theorem `_root_.MulAut.conjNormal_inv_apply` / 定理 `_root_.MulAut.conjNormal_inv_apply`

English:
theorem _root_.MulAut.conjNormal_inv_apply
  given: {H : Subgroup G} [H.Normal] (g : G) (h : H)
  proof: MulAut.conjNormal_symm_apply g h

中文:
定理 _root_.MulAut.conjNormal_inv_apply
  条件: {H : Subgroup G} [H.Normal] (g : G) (h : H)
  证明: MulAut.conjNormal_symm_apply g h

Depends on / 依赖: MulAut, MulAut.conjNormal_symm_apply, conjNormal_symm_apply
-/
theorem _root_.MulAut.conjNormal_inv_apply {H : Subgroup G} [H.Normal] (g : G) (h : H) :
    ↑((MulAut.conjNormal g)⁻¹ h) = g⁻¹ * h * g :=
  MulAut.conjNormal_symm_apply g h

/--
theorem `_root_.MulAut.conjNormal_val` / 定理 `_root_.MulAut.conjNormal_val`

English:
theorem _root_.MulAut.conjNormal_val
  given: {H : Subgroup G} [H.Normal] {h : H}
  proof: MulEquiv.ext fun _ => rfl

中文:
定理 _root_.MulAut.conjNormal_val
  条件: {H : Subgroup G} [H.Normal] {h : H}
  证明: MulEquiv.ext fun _ => rfl

Depends on / 依赖: MulEquiv, MulEquiv.ext
-/
theorem _root_.MulAut.conjNormal_val {H : Subgroup G} [H.Normal] {h : H} :
    MulAut.conjNormal ↑h = MulAut.conj h :=
  MulEquiv.ext fun _ => rfl

/--
Instance `normal_of_characteristic_of_normal` / 实例 `normal_of_characteristic_of_normal`

English:
instance normal_of_characteristic_of_normal
  signature: {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
  body: ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact K.apply_coe_mem_map H.subtype
      ⟨_, (SetLike.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩

中文:
实例 normal_of_characteristic_of_normal
  签名: {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
  定义体: ⟨fun a ha b => by
    obtain ⟨a, ha, rfl⟩ := ha
    exact K.apply_coe_mem_map H.subtype
      ⟨_, (SetLike.ext_iff.mp (h.fixed (MulAut.conjNormal b)) a).mpr ha⟩⟩

Depends on / 依赖: H.subtype, K.apply_coe_mem_map, MulAut, MulAut.conjNormal, SetLike, SetLike.ext_iff.mp, apply_coe_mem_map, conjNormal, ext_iff, h.fixed, subtype
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
/--
Definition of `unitsCentralizerEquiv` / `unitsCentralizerEquiv` 的定义

English:
definition unitsCentralizerEquiv
  signature: (x : Mˣ)
  body: MulEquiv.symm
  { toFun := MonoidHom.toHomUnits <|
      { toFun := fun u => ⟨↑(ConjAct.ofConjAct u.1 : Mˣ), by
          rintro x ⟨rfl⟩
          have : (u : ConjAct Mˣ) • x = x := u.2
          rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩,
        map_one' := rfl,

中文:
定义 unitsCentralizerEquiv
  签名: (x : Mˣ)
  定义体: MulEquiv.symm
  { toFun := MonoidHom.toHomUnits <|
      { toFun := fun u => ⟨↑(ConjAct.ofConjAct u.1 : Mˣ), by
          rintro x ⟨rfl⟩
          have : (u : ConjAct Mˣ) • x = x := u.2
          rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩,
        map_one' := rfl,

Depends on / 依赖: ConjAct, ConjAct.ofConjAct, ConjAct.ofConjAct_toConjAct, ConjAct.smul_def, ConjAct.toConjAct, MonoidHom, MonoidHom.toHomUnits, MulEquiv, MulEquiv.symm, Submonoid, Submonoid.centralizer, Units.ext, Units.ext_iff, Units.map, centralizer, eq_comm, ext_iff, invFun, map_mul, map_one
-/
def unitsCentralizerEquiv (x : Mˣ) :
    (Submonoid.centralizer ({↑x} : Set M))ˣ ≃* MulAction.stabilizer (ConjAct Mˣ) x :=
  MulEquiv.symm
  { toFun := MonoidHom.toHomUnits <|
      { toFun := fun u => ⟨↑(ConjAct.ofConjAct u.1 : Mˣ), by
          rintro x ⟨rfl⟩
          have : (u : ConjAct Mˣ) • x = x := u.2
          rwa [ConjAct.smul_def, mul_inv_eq_iff_eq_mul, Units.ext_iff, eq_comm] at this⟩,
        map_one' := rfl,
        map_mul' := fun _ _ => rfl }
    invFun := fun u =>
      ⟨ConjAct.toConjAct (Units.map (Submonoid.centralizer ({↑x} : Set M)).subtype u), by
      change _ • _ = _
      simp only [ConjAct.smul_def, ConjAct.ofConjAct_toConjAct, mul_inv_eq_iff_eq_mul]
exact Units.ext (u.1.2 x <| Set.mem_singleton _).symm⟩
    map_mul' := map_mul _ }

end Units
