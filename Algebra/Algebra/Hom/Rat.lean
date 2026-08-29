/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.Algebra.Algebra.Rat

/-!
# Homomorphisms of `ℚ`-algebras

-/

@[expose] public section

variable {R S : Type*} [Ring R] [Ring S] [Algebra Rat R] [Algebra Rat S]

namespace RingHom

/--
Definition of `toRatAlgHom` / `toRatAlgHom` 的定义

English:
definition toRatAlgHom
  signature: (f : R ->+* S)
  body: { f with commutes' := f.map_rat_algebraMap }

@[simp]

中文:
定义 toRatAlgHom
  签名: (f : R ->+* S)
  定义体: { f with commutes' := f.map_rat_algebraMap }

@[simp]

Depends on / 依赖: commutes, f.map_rat_algebraMap, map_rat_algebraMap
-/
def toRatAlgHom (f : R ->+* S) : R ->ₐ[Rat] S :=
  { f with commutes' := f.map_rat_algebraMap }

@[simp]
/--
theorem `toRatAlgHom_toRingHom` / 定理 `toRatAlgHom_toRingHom`

English:
theorem toRatAlgHom_toRingHom
  given: (f : R ->+* S)
  proof: RingHom.ext fun _x => rfl

@[simp]

中文:
定理 toRatAlgHom_toRingHom
  条件: (f : R ->+* S)
  证明: RingHom.ext fun _x => rfl

@[simp]

Depends on / 依赖: RingHom, RingHom.ext
-/
theorem toRatAlgHom_toRingHom (f : R ->+* S) :
    ↑f.toRatAlgHom = f :=
  RingHom.ext fun _x => rfl

@[simp]
/--
theorem `toRatAlgHom_apply` / 定理 `toRatAlgHom_apply`

English:
theorem toRatAlgHom_apply
  given: (f : R ->+* S) (x : R)
  proof: rfl

中文:
定理 toRatAlgHom_apply
  条件: (f : R ->+* S) (x : R)
  证明: rfl
-/
theorem toRatAlgHom_apply (f : R ->+* S) (x : R) :
    f.toRatAlgHom x = f x :=
  rfl

end RingHom

@[simp]
/--
theorem `AlgHom.toRingHom_toRatAlgHom` / 定理 `AlgHom.toRingHom_toRatAlgHom`

English:
theorem AlgHom.toRingHom_toRatAlgHom
  given: (f : R ->ₐ[Rat] S)
  statement: (f : R ->+* S).toRatAlgHom = f
  proof: AlgHom.ext fun _x => rfl

中文:
定理 AlgHom.toRingHom_toRatAlgHom
  条件: (f : R ->ₐ[Rat] S)
  结论: (f : R ->+* S).toRatAlgHom = f
  证明: AlgHom.ext fun _x => rfl

Depends on / 依赖: AlgHom, AlgHom.ext
-/
theorem AlgHom.toRingHom_toRatAlgHom (f : R ->ₐ[Rat] S) : (f : R ->+* S).toRatAlgHom = f :=
  AlgHom.ext fun _x => rfl

variable (R) (S) in
/-- The equivalence between `RingHom` and `ℚ`-algebra homomorphisms. -/
@[simps]
/--
Definition of `RingHom.equivRatAlgHom` / `RingHom.equivRatAlgHom` 的定义

English:
definition RingHom.equivRatAlgHom
  signature: : (R ->+* S) ≃ (R ->ₐ[Rat] S) where
  body: RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom

中文:
定义 RingHom.equivRatAlgHom
  签名: : (R ->+* S) ≃ (R ->ₐ[Rat] S) where
  定义体: RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom

Depends on / 依赖: RingHom, RingHom.toRatAlgHom, toRatAlgHom
-/
def RingHom.equivRatAlgHom : (R ->+* S) ≃ (R ->ₐ[Rat] S) where
  toFun := RingHom.toRatAlgHom
  invFun := AlgHom.toRingHom

namespace RingEquiv

/-- Reinterpret a `RingEquiv` as a `ℚ`-algebra isomorphism. This actually yields an
equivalence, see `RingEquiv.equivRatAlgEquiv`. -/
@[simps! -isSimp apply]
/--
Definition of `toRatAlgEquiv` / `toRatAlgEquiv` 的定义

English:
definition toRatAlgEquiv
  signature: (f : R ≃+* S)
  body: f
  __ := f.toRingHom.toRatAlgHom

@[simp]

中文:
定义 toRatAlgEquiv
  签名: (f : R ≃+* S)
  定义体: f
  __ := f.toRingHom.toRatAlgHom

@[simp]
-/
def toRatAlgEquiv (f : R ≃+* S) : R ≃ₐ[Rat] S where
  toEquiv := f
  __ := f.toRingHom.toRatAlgHom

@[simp]
/--
theorem `coe_toRatAlgEquiv` / 定理 `coe_toRatAlgEquiv`

English:
theorem coe_toRatAlgEquiv
  given: (f : R ≃+* S)
  statement: ⇑f.toRatAlgEquiv = ⇑f
  proof: rfl

@[simp]

中文:
定理 coe_toRatAlgEquiv
  条件: (f : R ≃+* S)
  结论: ⇑f.toRatAlgEquiv = ⇑f
  证明: rfl

@[simp]
-/
theorem coe_toRatAlgEquiv (f : R ≃+* S) : ⇑f.toRatAlgEquiv = ⇑f := rfl

@[simp]
/--
theorem `toRingEquiv_toRatAlgEquiv` / 定理 `toRingEquiv_toRatAlgEquiv`

English:
theorem toRingEquiv_toRatAlgEquiv
  given: (f : R ≃+* S)
  proof: rfl

中文:
定理 toRingEquiv_toRatAlgEquiv
  条件: (f : R ≃+* S)
  证明: rfl
-/
theorem toRingEquiv_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv = f :=
  rfl

/--
theorem `toAlgHom_toRatAlgEquiv` / 定理 `toAlgHom_toRatAlgEquiv`

English:
theorem toAlgHom_toRatAlgEquiv
  given: (f : R ≃+* S)
  proof: rfl

@[simp]

中文:
定理 toAlgHom_toRatAlgEquiv
  条件: (f : R ≃+* S)
  证明: rfl

@[simp]
-/
theorem toAlgHom_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.toAlgHom = (f : R ->+* S).toRatAlgHom :=
  rfl

@[simp]
/--
theorem `symm_toRatAlgEquiv` / 定理 `symm_toRatAlgEquiv`

English:
theorem symm_toRatAlgEquiv
  given: (f : R ≃+* S)
  proof: rfl

中文:
定理 symm_toRatAlgEquiv
  条件: (f : R ≃+* S)
  证明: rfl
-/
theorem symm_toRatAlgEquiv (f : R ≃+* S) :
    f.toRatAlgEquiv.symm = f.symm.toRatAlgEquiv :=
  rfl

end RingEquiv

@[simp]
/--
theorem `AlgEquiv.toRatAlgEquiv_toRingEquiv` / 定理 `AlgEquiv.toRatAlgEquiv_toRingEquiv`

English:
theorem AlgEquiv.toRatAlgEquiv_toRingEquiv
  given: (f : R ≃ₐ[Rat] S)
  statement: (f : R ≃+* S).toRatAlgEquiv = f
  proof: rfl

中文:
定理 AlgEquiv.toRatAlgEquiv_toRingEquiv
  条件: (f : R ≃ₐ[Rat] S)
  结论: (f : R ≃+* S).toRatAlgEquiv = f
  证明: rfl
-/
theorem AlgEquiv.toRatAlgEquiv_toRingEquiv (f : R ≃ₐ[Rat] S) : (f : R ≃+* S).toRatAlgEquiv = f :=
  rfl

variable (R) (S) in
/-- The equivalence between `RingEquiv` and `ℚ`-algebra isomorphisms. -/
@[simps apply symm_apply]
/--
Definition of `RingEquiv.equivRatAlgEquiv` / `RingEquiv.equivRatAlgEquiv` 的定义

English:
definition RingEquiv.equivRatAlgEquiv
  signature: : (R ≃+* S) ≃ (R ≃ₐ[Rat] S) where
  body: RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv

中文:
定义 RingEquiv.equivRatAlgEquiv
  签名: : (R ≃+* S) ≃ (R ≃ₐ[Rat] S) where
  定义体: RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv

Depends on / 依赖: RingEquiv, RingEquiv.toRatAlgEquiv, toRatAlgEquiv
-/
def RingEquiv.equivRatAlgEquiv : (R ≃+* S) ≃ (R ≃ₐ[Rat] S) where
  toFun := RingEquiv.toRatAlgEquiv
  invFun := AlgEquiv.toRingEquiv

/--
lemma `RingEquiv.toRatAlgEquiv_injective` / 引理 `RingEquiv.toRatAlgEquiv_injective`

English:
lemma RingEquiv.toRatAlgEquiv_injective
  proof: (RingEquiv.equivRatAlgEquiv R S).injective

中文:
引理 RingEquiv.toRatAlgEquiv_injective
  证明: (RingEquiv.equivRatAlgEquiv R S).injective

Depends on / 依赖: RingEquiv, RingEquiv.equivRatAlgEquiv, equivRatAlgEquiv, injective
-/
lemma RingEquiv.toRatAlgEquiv_injective :
    Function.Injective (RingEquiv.toRatAlgEquiv : (R ≃+* S) -> _) :=
  (RingEquiv.equivRatAlgEquiv R S).injective
