/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Module.Opposite
public import Mathlib.Algebra.Ring.Opposite

/-!
# Algebra structures on the multiplicative opposite

## Main definitions

* `MulOpposite.instAlgebra`: the algebra on `Aᵐᵒᵖ`
* `AlgHom.op`/`AlgHom.unop`: simultaneously convert the domain and codomain of a morphism to the
  opposite algebra.
* `AlgHom.opComm`: swap which side of a morphism lies in the opposite algebra.
* `AlgEquiv.op`/`AlgEquiv.unop`: simultaneously convert the source and target of an isomorphism to
  the opposite algebra.
* `AlgEquiv.opOp`: any algebra is isomorphic to the opposite of its opposite.
* `AlgEquiv.toOpposite`: in a commutative algebra, the opposite algebra is isomorphic to the
  original algebra.
* `AlgEquiv.opComm`: swap which side of an isomorphism lies in the opposite algebra.
-/

@[expose] public section


variable {R S A B : Type*}

open MulOpposite

section Semiring

variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Algebra S A] [SMulCommClass R S A]
variable [IsScalarTower R S A]

namespace MulOpposite

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instAlgebra` / 实例 `instAlgebra`

English:
instance instAlgebra
  signature: : Algebra R Aᵐᵒᵖ where
  body: (algebraMap R A).toOpposite fun _ _ => Algebra.commutes _ _
smul_def' c x := unop_injective by
    simp only [unop_smul, RingHom.toOpposite_apply, Function.comp_apply, unop_mul,
      Algebra.smul_def, Algebra.commutes, unop_op]
  commutes' r := MulOpposite.rec' fun x => by
    simp only [RingHom.to

中文:
实例 instAlgebra
  签名: : 代数 R Aᵐᵒᵖ where
  定义体: (algebraMap R A).toOpposite fun _ _ => Algebra.commutes _ _
smul_def' c x := unop_injective by
    simp only [unop_smul, RingHom.toOpposite_apply, Function.comp_apply, unop_mul,
      Algebra.smul_def, Algebra.commutes, unop_op]
  commutes' r := MulOpposite.rec' fun x => by
    simp only [RingHom.to

Depends on / 依赖: Algebra, Algebra.commutes, algebraMap, commutes, toOpposite
-/
instance instAlgebra : Algebra R Aᵐᵒᵖ where
  algebraMap := (algebraMap R A).toOpposite fun _ _ => Algebra.commutes _ _
smul_def' c x := unop_injective by
    simp only [unop_smul, RingHom.toOpposite_apply, Function.comp_apply, unop_mul,
      Algebra.smul_def, Algebra.commutes, unop_op]
  commutes' r := MulOpposite.rec' fun x => by
    simp only [RingHom.toOpposite_apply, Function.comp_apply, ← op_mul, Algebra.commutes]

@[simp]
/--
theorem `algebraMap_apply` / 定理 `algebraMap_apply`

English:
theorem algebraMap_apply
  given: (c : R)
  statement: algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c)
  proof: rfl

中文:
定理 algebraMap_apply
  条件: (c : R)
  结论: algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c)
  证明: rfl
-/
theorem algebraMap_apply (c : R) : algebraMap R Aᵐᵒᵖ c = op (algebraMap R A c) :=
  rfl

end MulOpposite

namespace AlgEquiv
variable (R A)

/-- An algebra is isomorphic to the opposite of its opposite. -/
@[simps!]
/--
Definition of `opOp` / `opOp` 的定义

English:
definition opOp
  signature: : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where
  body: RingEquiv.opOp A
  commutes' _ := rfl

中文:
定义 opOp
  签名: : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where
  定义体: RingEquiv.opOp A
  commutes' _ := rfl

Depends on / 依赖: RingEquiv, RingEquiv.opOp
-/
def opOp : A ≃ₐ[R] Aᵐᵒᵖᵐᵒᵖ where
  __ := RingEquiv.opOp A
  commutes' _ := rfl

/--
theorem `toRingEquiv_opOp` / 定理 `toRingEquiv_opOp`

English:
theorem toRingEquiv_opOp
  statement: (opOp R A : A ≃+* Aᵐᵒᵖᵐᵒᵖ) = RingEquiv.opOp A
  proof: rfl

中文:
定理 toRingEquiv_opOp
  结论: (opOp R A : A ≃+* Aᵐᵒᵖᵐᵒᵖ) = 环等价.opOp A
  证明: rfl
-/
@[simp] theorem toRingEquiv_opOp : (opOp R A : A ≃+* Aᵐᵒᵖᵐᵒᵖ) = RingEquiv.opOp A := rfl

end AlgEquiv

namespace AlgHom

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism from `Aᵐᵒᵖ`. -/
@[simps -fullyApplied]
/--
Definition of `fromOpposite` / `fromOpposite` 的定义

English:
definition fromOpposite
  signature: (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y))
  body: { f.toRingHom.fromOpposite hf with
    toFun := f ∘ unop
    commutes' := fun r => f.commutes r }

@[simp]

中文:
定义 fromOpposite
  签名: (f : A ->ₐ[R] B) (hf : 对任意 x y, Commute (f x) (f y))
  定义体: { f.toRingHom.fromOpposite hf with
    toFun := f ∘ unop
    commutes' := fun r => f.commutes r }

@[simp]

Depends on / 依赖: commutes, f.commutes, f.toRingHom.fromOpposite, fromOpposite, toRingHom
-/
def fromOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) : Aᵐᵒᵖ ->ₐ[R] B :=
  { f.toRingHom.fromOpposite hf with
    toFun := f ∘ unop
    commutes' := fun r => f.commutes r }

@[simp]
/--
theorem `toLinearMap_fromOpposite` / 定理 `toLinearMap_fromOpposite`

English:
theorem toLinearMap_fromOpposite
  given: (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y))
  proof: rfl

@[simp]

中文:
定理 toLinearMap_fromOpposite
  条件: (f : A ->ₐ[R] B) (hf : 对任意 x y, Commute (f x) (f y))
  证明: rfl

@[simp]
-/
theorem toLinearMap_fromOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) :
    (f.fromOpposite hf).toLinearMap = f.toLinearMap ∘ₗ (opLinearEquiv R (M := A)).symm :=
  rfl

@[simp]
/--
theorem `toRingHom_fromOpposite` / 定理 `toRingHom_fromOpposite`

English:
theorem toRingHom_fromOpposite
  given: (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y))
  proof: rfl

中文:
定理 toRingHom_fromOpposite
  条件: (f : A ->ₐ[R] B) (hf : 对任意 x y, Commute (f x) (f y))
  证明: rfl
-/
theorem toRingHom_fromOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) :
    (f.fromOpposite hf : Aᵐᵒᵖ ->+* B) = (f : A ->+* B).fromOpposite hf :=
  rfl

/--
An algebra homomorphism `f : A →ₐ[R] B` such that `f x` commutes with `f y` for all `x, y` defines
an algebra homomorphism to `Bᵐᵒᵖ`. -/
@[simps -fullyApplied]
/--
Definition of `toOpposite` / `toOpposite` 的定义

English:
definition toOpposite
  signature: (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y))
  body: { f.toRingHom.toOpposite hf with
    toFun := op ∘ f
commutes' := fun r => unop_injective f.commutes r }

@[simp]

中文:
定义 toOpposite
  签名: (f : A ->ₐ[R] B) (hf : 对任意 x y, Commute (f x) (f y))
  定义体: { f.toRingHom.toOpposite hf with
    toFun := op ∘ f
commutes' := fun r => unop_injective f.commutes r }

@[simp]

Depends on / 依赖: commutes, f.commutes, f.toRingHom.toOpposite, toOpposite, toRingHom, unop_injective
-/
def toOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) : A ->ₐ[R] Bᵐᵒᵖ :=
  { f.toRingHom.toOpposite hf with
    toFun := op ∘ f
commutes' := fun r => unop_injective f.commutes r }

@[simp]
/--
theorem `toLinearMap_toOpposite` / 定理 `toLinearMap_toOpposite`

English:
theorem toLinearMap_toOpposite
  given: (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y))
  proof: rfl

@[simp]

中文:
定理 toLinearMap_toOpposite
  条件: (f : A ->ₐ[R] B) (hf : 对任意 x y, Commute (f x) (f y))
  证明: rfl

@[simp]
-/
theorem toLinearMap_toOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) :
    (f.toOpposite hf).toLinearMap = (opLinearEquiv R : B ≃ₗ[R] Bᵐᵒᵖ) ∘ₗ f.toLinearMap :=
  rfl

@[simp]
/--
theorem `toRingHom_toOpposite` / 定理 `toRingHom_toOpposite`

English:
theorem toRingHom_toOpposite
  given: (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y))
  proof: rfl

中文:
定理 toRingHom_toOpposite
  条件: (f : A ->ₐ[R] B) (hf : 对任意 x y, Commute (f x) (f y))
  证明: rfl
-/
theorem toRingHom_toOpposite (f : A ->ₐ[R] B) (hf : forall x y, Commute (f x) (f y)) :
    (f.toOpposite hf : A ->+* Bᵐᵒᵖ) = (f : A ->+* B).toOpposite hf :=
  rfl

/-- An algebra hom `A →ₐ[R] B` can equivalently be viewed as an algebra hom `Aᵐᵒᵖ →ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : (A ->ₐ[R] B) ≃ (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) where
  body: { RingHom.op f.toRingHom with commutes' := fun r => unop_injective <| f.commutes r }
  invFun f := { RingHom.unop f.toRingHom with commutes' := fun r => op_injective <| f.commutes r }

中文:
定义 op
  签名: : (A ->ₐ[R] B) ≃ (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) where
  定义体: { RingHom.op f.toRingHom with commutes' := fun r => unop_injective <| f.commutes r }
  invFun f := { RingHom.unop f.toRingHom with commutes' := fun r => op_injective <| f.commutes r }
-/
protected def op : (A ->ₐ[R] B) ≃ (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) where
  toFun f := { RingHom.op f.toRingHom with commutes' := fun r => unop_injective <| f.commutes r }
  invFun f := { RingHom.unop f.toRingHom with commutes' := fun r => op_injective <| f.commutes r }

/--
theorem `toRingHom_op` / 定理 `toRingHom_op`

English:
theorem toRingHom_op
  given: (f : A ->ₐ[R] B)
  statement: f.op.toRingHom = RingHom.op f.toRingHom
  proof: rfl

中文:
定理 toRingHom_op
  条件: (f : A ->ₐ[R] B)
  结论: f.op.toRingHom = 环态射.op f.toRingHom
  证明: rfl
-/
theorem toRingHom_op (f : A ->ₐ[R] B) : f.op.toRingHom = RingHom.op f.toRingHom :=
  rfl

/--
Definition of `unop` / `unop` 的定义

English:
abbreviation unop
  signature: : (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) ≃ (A ->ₐ[R] B)
  body: AlgHom.op.symm

中文:
缩写 unop
  签名: : (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) ≃ (A ->ₐ[R] B)
  定义体: AlgHom.op.symm

Depends on / 依赖: AlgHom, AlgHom.op.symm
-/
abbrev unop : (Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) ≃ (A ->ₐ[R] B) := AlgHom.op.symm

/--
theorem `toRingHom_unop` / 定理 `toRingHom_unop`

English:
theorem toRingHom_unop
  given: (f : Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ)
  statement: f.unop.toRingHom = RingHom.unop f.toRingHom
  proof: rfl

中文:
定理 toRingHom_unop
  条件: (f : Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ)
  结论: f.unop.toRingHom = 环态射.unop f.toRingHom
  证明: rfl
-/
theorem toRingHom_unop (f : Aᵐᵒᵖ ->ₐ[R] Bᵐᵒᵖ) : f.unop.toRingHom = RingHom.unop f.toRingHom :=
  rfl

/-- Swap the `ᵐᵒᵖ` on an algebra hom to the opposite side. -/
@[simps!]
/--
Definition of `opComm` / `opComm` 的定义

English:
definition opComm
  signature: : (A ->ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ->ₐ[R] B)
  body: AlgHom.op.trans AlgEquiv.refl.arrowCongr (AlgEquiv.opOp R B).symm

中文:
定义 opComm
  签名: : (A ->ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ->ₐ[R] B)
  定义体: AlgHom.op.trans AlgEquiv.refl.arrowCongr (AlgEquiv.opOp R B).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.opOp, AlgEquiv.refl.arrowCongr, AlgHom, AlgHom.op.trans, arrowCongr
-/
def opComm : (A ->ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ->ₐ[R] B) :=
AlgHom.op.trans AlgEquiv.refl.arrowCongr (AlgEquiv.opOp R B).symm

end AlgHom

namespace AlgEquiv

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- An algebra iso `A ≃ₐ[R] B` can equivalently be viewed as an algebra iso `Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ`.
This is the action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps!]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: : (A ≃ₐ[R] B) ≃ Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ where
  body: { RingEquiv.op f.toRingEquiv with
commutes' := fun r => MulOpposite.unop_injective f.commutes r }
  invFun f :=
    { RingEquiv.unop f.toRingEquiv with
commutes' := fun r => MulOpposite.op_injective f.commutes r }

中文:
定义 op
  签名: : (A ≃ₐ[R] B) ≃ Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ where
  定义体: { RingEquiv.op f.toRingEquiv with
commutes' := fun r => MulOpposite.unop_injective f.commutes r }
  invFun f :=
    { RingEquiv.unop f.toRingEquiv with
commutes' := fun r => MulOpposite.op_injective f.commutes r }

Depends on / 依赖: MulOpposite, MulOpposite.op_injective, MulOpposite.unop_injective, RingEquiv, RingEquiv.op, RingEquiv.unop, commutes, f.commutes, f.toRingEquiv, invFun, op_injective, toRingEquiv, unop_injective
-/
def op : (A ≃ₐ[R] B) ≃ Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ where
  toFun f :=
    { RingEquiv.op f.toRingEquiv with
commutes' := fun r => MulOpposite.unop_injective f.commutes r }
  invFun f :=
    { RingEquiv.unop f.toRingEquiv with
commutes' := fun r => MulOpposite.op_injective f.commutes r }

/--
theorem `toAlgHom_op` / 定理 `toAlgHom_op`

English:
theorem toAlgHom_op
  given: (f : A ≃ₐ[R] B)
  proof: rfl

中文:
定理 toAlgHom_op
  条件: (f : A ≃ₐ[R] B)
  证明: rfl
-/
theorem toAlgHom_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toAlgHom = AlgHom.op f.toAlgHom :=
  rfl

/--
theorem `toRingEquiv_op` / 定理 `toRingEquiv_op`

English:
theorem toRingEquiv_op
  given: (f : A ≃ₐ[R] B)
  proof: rfl

中文:
定理 toRingEquiv_op
  条件: (f : A ≃ₐ[R] B)
  证明: rfl
-/
theorem toRingEquiv_op (f : A ≃ₐ[R] B) :
    (AlgEquiv.op f).toRingEquiv = RingEquiv.op f.toRingEquiv :=
  rfl

/--
Definition of `unop` / `unop` 的定义

English:
abbreviation unop
  signature: : (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) ≃ A ≃ₐ[R] B
  body: AlgEquiv.op.symm

中文:
缩写 unop
  签名: : (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) ≃ A ≃ₐ[R] B
  定义体: AlgEquiv.op.symm

Depends on / 依赖: AlgEquiv, AlgEquiv.op.symm
-/
abbrev unop : (Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) ≃ A ≃ₐ[R] B := AlgEquiv.op.symm

/--
theorem `toAlgHom_unop` / 定理 `toAlgHom_unop`

English:
theorem toAlgHom_unop
  given: (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ)
  statement: f.unop.toAlgHom = AlgHom.unop f.toAlgHom
  proof: rfl

中文:
定理 toAlgHom_unop
  条件: (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ)
  结论: f.unop.toAlgHom = 代数态射.unop f.toAlgHom
  证明: rfl
-/
theorem toAlgHom_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) : f.unop.toAlgHom = AlgHom.unop f.toAlgHom :=
  rfl

/--
theorem `toRingEquiv_unop` / 定理 `toRingEquiv_unop`

English:
theorem toRingEquiv_unop
  given: (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ)
  proof: rfl

#adaptation_note

中文:
定理 toRingEquiv_unop
  条件: (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ)
  证明: rfl

#adaptation_note
-/
theorem toRingEquiv_unop (f : Aᵐᵒᵖ ≃ₐ[R] Bᵐᵒᵖ) :
    (AlgEquiv.unop f).toRingEquiv = RingEquiv.unop f.toRingEquiv :=
  rfl

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Swap the `ᵐᵒᵖ` on an algebra isomorphism to the opposite side. -/
@[simps!]
/--
Definition of `opComm` / `opComm` 的定义

English:
definition opComm
  signature: : (A ≃ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ≃ₐ[R] B)
  body: AlgEquiv.op.trans AlgEquiv.refl.equivCongr (opOp R B).symm

中文:
定义 opComm
  签名: : (A ≃ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ≃ₐ[R] B)
  定义体: AlgEquiv.op.trans AlgEquiv.refl.equivCongr (opOp R B).symm

Depends on / 依赖: AlgEquiv, AlgEquiv.op.trans, AlgEquiv.refl.equivCongr, equivCongr
-/
def opComm : (A ≃ₐ[R] Bᵐᵒᵖ) ≃ (Aᵐᵒᵖ ≃ₐ[R] B) :=
AlgEquiv.op.trans AlgEquiv.refl.equivCongr (opOp R B).symm

variable (R S)

/--
Definition of `moduleEndSelf` / `moduleEndSelf` 的定义

English:
definition moduleEndSelf
  signature: : Aᵐᵒᵖ ≃ₐ[R] Module.End A A where
  body: RingEquiv.moduleEndSelf A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

中文:
定义 moduleEndSelf
  签名: : Aᵐᵒᵖ ≃ₐ[R] 模.End A A where
  定义体: RingEquiv.moduleEndSelf A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]
-/
@[simps!] def moduleEndSelf : Aᵐᵒᵖ ≃ₐ[R] Module.End A A where
  __ := RingEquiv.moduleEndSelf A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

/--
Definition of `moduleEndSelfOp` / `moduleEndSelfOp` 的定义

English:
definition moduleEndSelfOp
  signature: : A ≃ₐ[R] Module.End Aᵐᵒᵖ A where
  body: RingEquiv.moduleEndSelfOp A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

中文:
定义 moduleEndSelfOp
  签名: : A ≃ₐ[R] 模.End Aᵐᵒᵖ A where
  定义体: RingEquiv.moduleEndSelfOp A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]
-/
@[simps!] def moduleEndSelfOp : A ≃ₐ[R] Module.End Aᵐᵒᵖ A where
  __ := RingEquiv.moduleEndSelfOp A
  commutes' _ := by ext; simp [Algebra.algebraMap_eq_smul_one]

end AlgEquiv

end Semiring

section CommSemiring
variable (R A) [CommSemiring R] [CommSemiring A] [Algebra R A]

namespace AlgEquiv

/-- A commutative algebra is isomorphic to its opposite. -/
@[simps!]
/--
Definition of `toOpposite` / `toOpposite` 的定义

English:
definition toOpposite
  signature: : A ≃ₐ[R] Aᵐᵒᵖ where
  body: RingEquiv.toOpposite A
  commutes' _r := rfl

中文:
定义 toOpposite
  签名: : A ≃ₐ[R] Aᵐᵒᵖ where
  定义体: RingEquiv.toOpposite A
  commutes' _r := rfl

Depends on / 依赖: RingEquiv, RingEquiv.toOpposite, toOpposite
-/
def toOpposite : A ≃ₐ[R] Aᵐᵒᵖ where
  __ := RingEquiv.toOpposite A
  commutes' _r := rfl

/--
lemma `toRingEquiv_toOpposite` / 引理 `toRingEquiv_toOpposite`

English:
lemma toRingEquiv_toOpposite
  statement: (toOpposite R A : A ≃+* Aᵐᵒᵖ) = RingEquiv.toOpposite A
  proof: rfl

中文:
引理 toRingEquiv_toOpposite
  结论: (toOpposite R A : A ≃+* Aᵐᵒᵖ) = 环等价.toOpposite A
  证明: rfl
-/
@[simp] lemma toRingEquiv_toOpposite : (toOpposite R A : A ≃+* Aᵐᵒᵖ) = RingEquiv.toOpposite A := rfl
/--
lemma `toLinearEquiv_toOpposite` / 引理 `toLinearEquiv_toOpposite`

English:
lemma toLinearEquiv_toOpposite
  statement: toLinearEquiv (toOpposite R A) = opLinearEquiv R
  proof: rfl

中文:
引理 toLinearEquiv_toOpposite
  结论: toLinearEquiv (toOpposite R A) = opLinearEquiv R
  证明: rfl
-/
@[simp] lemma toLinearEquiv_toOpposite : toLinearEquiv (toOpposite R A) = opLinearEquiv R := rfl

end AlgEquiv

end CommSemiring
