/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.TensorProduct
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
public import Mathlib.Tactic.LinearCombination

/-!
# The quadratic form on a tensor product

## Main definitions

* `QuadraticForm.tensorDistrib (Q₁ ⊗ₜ Q₂)`: the quadratic form on `M₁ ⊗ M₂` constructed by applying
  `Q₁` on `M₁` and `Q₂` on `M₂`. This construction is not available in characteristic two.

-/

@[expose] public section

universe uR uA uM₁ uM₂ uN₁ uN₂

variable {R : Type uR} {A : Type uA} {M₁ : Type uM₁} {M₂ : Type uM₂} {N₁ : Type uN₁} {N₂ : Type uN₂}

open LinearMap (BilinMap BilinForm)
open TensorProduct QuadraticMap

section CommRing
variable [CommRing R] [CommRing A]
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup N₁] [AddCommGroup N₂]
variable [Algebra R A] [Module R M₁] [Module A M₁] [Module R N₁] [Module A N₁]
variable [SMulCommClass R A M₁] [IsScalarTower R A M₁] [IsScalarTower R A N₁]
variable [Module R M₂] [Module R N₂]

section InvertibleTwo
variable [Invertible (2 : R)]

namespace QuadraticMap

variable (R A) in
/--
Definition of `tensorDistrib` / `tensorDistrib` 的定义

English:
definition tensorDistrib
  signature: :
  body: letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ otimes[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.associated : QuadraticMap A M₁ N₁ ->ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.associated : QuadraticMap R M₂ N₂ ->ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB

@[simp]

中文:
定义 tensorDistrib
  签名: :
  定义体: letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ otimes[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.associated : QuadraticMap A M₁ N₁ ->ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.associated : QuadraticMap R M₂ N₂ ->ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB

@[simp]

Depends on / 依赖: Invertible, Invertible.map, algebraMap, map_ofNat
-/
def tensorDistrib :
    QuadraticMap A M₁ N₁ otimes[R] QuadraticMap R M₂ N₂ ->ₗ[A] QuadraticMap A (M₁ otimes[R] M₂) (N₁ otimes[R] N₂) :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  -- while `letI`s would produce a better term than `let`, they would make this already-slow
  -- definition even slower.
  let toQ := BilinMap.toQuadraticMapLinearMap A A (M₁ otimes[R] M₂)
  let tmulB := BilinMap.tensorDistrib R A (M₁ := M₁) (M₂ := M₂)
  let toB := AlgebraTensorModule.map
      (QuadraticMap.associated : QuadraticMap A M₁ N₁ ->ₗ[A] BilinMap A M₁ N₁)
      (QuadraticMap.associated : QuadraticMap R M₂ N₂ ->ₗ[R] BilinMap R M₂ N₂)
  toQ ∘ₗ tmulB ∘ₗ toB

@[simp]
/--
theorem `tensorDistrib_tmul` / 定理 `tensorDistrib_tmul`

English:
theorem tensorDistrib_tmul
  statement: (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) (m₁ : M₁)
  proof: letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
(BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

中文:
定理 tensorDistrib_tmul
  结论: (Q₁ : 二次映射 A M₁ N₁) (Q₂ : 二次映射 R M₂ N₂) (m₁ : M₁)
  证明: letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
(BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

Depends on / 依赖: BilinMap, BilinMap.tensorDistrib_tmul, Invertible, Invertible.map, algebraMap, associated_eq_self_apply, map_ofNat, tensorDistrib_tmul
-/
theorem tensorDistrib_tmul (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) (m₁ : M₁)
    (m₂ : M₂) : tensorDistrib R A (Q₁ otimesₜ Q₂) (m₁ otimesₜ m₂) = Q₁ m₁ otimesₜ Q₂ m₂ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
(BilinMap.tensorDistrib_tmul _ _ _ _ _ _).trans congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/--
Definition of `tmul` / `tmul` 的定义

English:
abbreviation tmul
  signature: (Q₁ : QuadraticMap A M₁ N₁)
  body: tensorDistrib R A (Q₁ otimesₜ[R] Q₂)

中文:
缩写 tmul
  签名: (Q₁ : 二次映射 A M₁ N₁)
  定义体: tensorDistrib R A (Q₁ otimesₜ[R] Q₂)
-/
protected abbrev tmul (Q₁ : QuadraticMap A M₁ N₁)
    (Q₂ : QuadraticMap R M₂ N₂) : QuadraticMap A (M₁ otimes[R] M₂) (N₁ otimes[R] N₂) :=
  tensorDistrib R A (Q₁ otimesₜ[R] Q₂)

/--
theorem `associated_tmul` / 定理 `associated_tmul`

English:
theorem associated_tmul
  statement: [Invertible (2 : A)]
  proof: by
  let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  rw [QuadraticMap.tmul]; rw [BilinMap.tmul]
  have : Subsingleton (Invertible (2 : A)) := inferInstance
  convert!
    associated_left_inverse A
      (LinearMap.BilinMap.tmul_isSymm (QuadraticMap.associated_isSymm A Q₁)
        (QuadraticMap.associated_isSymm R Q₂))

中文:
定理 associated_tmul
  结论: [可逆 (2 : A)]
  证明: by
  let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  rw [QuadraticMap.tmul]; rw [BilinMap.tmul]
  have : Subsingleton (Invertible (2 : A)) := inferInstance
  convert!
    associated_left_inverse A
      (LinearMap.BilinMap.tmul_isSymm (QuadraticMap.associated_isSymm A Q₁)
        (QuadraticMap.associated_isSymm R Q₂))

Depends on / 依赖: BilinMap, BilinMap.tmul, Invertible, Invertible.map, LinearMap, LinearMap.BilinMap.tmul_isSymm, QuadraticMap, QuadraticMap.associated_isSymm, QuadraticMap.tmul, Subsingleton, algebraMap, associated_isSymm, associated_left_inverse, convert, map_ofNat, tmul_isSymm
-/
theorem associated_tmul [Invertible (2 : A)]
    (Q₁ : QuadraticMap A M₁ N₁) (Q₂ : QuadraticMap R M₂ N₂) :
    (Q₁.tmul Q₂).associated = Q₁.associated.tmul Q₂.associated := by
  let : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
  rw [QuadraticMap.tmul]; rw [BilinMap.tmul]
  have : Subsingleton (Invertible (2 : A)) := inferInstance
  convert!
    associated_left_inverse A
      (LinearMap.BilinMap.tmul_isSymm (QuadraticMap.associated_isSymm A Q₁)
        (QuadraticMap.associated_isSymm R Q₂))

end QuadraticMap

namespace QuadraticForm

variable (R A) in
/--
Definition of `tensorDistrib` / `tensorDistrib` 的定义

English:
definition tensorDistrib
  signature: :
  body: (AlgebraTensorModule.rid R A A).congrQuadraticMap.toLinearMap ∘ₗ QuadraticMap.tensorDistrib R A

中文:
定义 tensorDistrib
  签名: :
  定义体: (AlgebraTensorModule.rid R A A).congrQuadraticMap.toLinearMap ∘ₗ QuadraticMap.tensorDistrib R A

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.rid, QuadraticMap, QuadraticMap.tensorDistrib, congrQuadraticMap, congrQuadraticMap.toLinearMap, tensorDistrib, toLinearMap
-/
def tensorDistrib :
    QuadraticForm A M₁ otimes[R] QuadraticForm R M₂ ->ₗ[A] QuadraticForm A (M₁ otimes[R] M₂) :=
  (AlgebraTensorModule.rid R A A).congrQuadraticMap.toLinearMap ∘ₗ QuadraticMap.tensorDistrib R A

-- TODO: make the RHS `MulOpposite.op (Q₂ m₂) • Q₁ m₁` so that this has a nicer defeq for
-- `R = A` of `Q₁ m₁ * Q₂ m₂`.
@[simp]
/--
theorem `tensorDistrib_tmul` / 定理 `tensorDistrib_tmul`

English:
theorem tensorDistrib_tmul
  given: (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂)
  proof: letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
(LinearMap.BilinForm.tensorDistrib_tmul _ _ _ _ _ _ _ _).trans congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

中文:
定理 tensorDistrib_tmul
  条件: (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂)
  证明: letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
(LinearMap.BilinForm.tensorDistrib_tmul _ _ _ _ _ _ _ _).trans congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

Depends on / 依赖: BilinForm, Invertible, Invertible.map, LinearMap, LinearMap.BilinForm.tensorDistrib_tmul, algebraMap, associated_eq_self_apply, map_ofNat, tensorDistrib_tmul
-/
theorem tensorDistrib_tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) (m₁ : M₁) (m₂ : M₂) :
    tensorDistrib R A (Q₁ otimesₜ Q₂) (m₁ otimesₜ m₂) = Q₂ m₂ • Q₁ m₁ :=
  letI : Invertible (2 : A) := (Invertible.map (algebraMap R A) 2).copy 2 (map_ofNat _ _).symm
(LinearMap.BilinForm.tensorDistrib_tmul _ _ _ _ _ _ _ _).trans congr_arg₂ _
    (associated_eq_self_apply _ _ _) (associated_eq_self_apply _ _ _)

/--
Definition of `tmul` / `tmul` 的定义

English:
abbreviation tmul
  signature: (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂)
  body: tensorDistrib R A (Q₁ otimesₜ[R] Q₂)

中文:
缩写 tmul
  签名: (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂)
  定义体: tensorDistrib R A (Q₁ otimesₜ[R] Q₂)
-/
protected abbrev tmul (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    QuadraticForm A (M₁ otimes[R] M₂) :=
  tensorDistrib R A (Q₁ otimesₜ[R] Q₂)

/--
theorem `associated_tmul` / 定理 `associated_tmul`

English:
theorem associated_tmul
  given: [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂)
  proof: by
  rw [BilinForm.tmul]; rw [BilinForm.tensorDistrib]; rw [LinearMap.comp_apply]; rw [← BilinMap.tmul]; rw [← QuadraticMap.associated_tmul Q₁ Q₂]; rw [LinearEquiv.coe_coe]; rw [LinearEquiv.congrRight₂_apply]
  ext : 6
  simp [associated_apply]
  rfl

中文:
定理 associated_tmul
  条件: [可逆 (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂)
  证明: by
  rw [BilinForm.tmul]; rw [BilinForm.tensorDistrib]; rw [LinearMap.comp_apply]; rw [← BilinMap.tmul]; rw [← QuadraticMap.associated_tmul Q₁ Q₂]; rw [LinearEquiv.coe_coe]; rw [LinearEquiv.congrRight₂_apply]
  ext : 6
  simp [associated_apply]
  rfl

Depends on / 依赖: BilinForm, BilinForm.tensorDistrib, BilinForm.tmul, BilinMap, BilinMap.tmul, LinearEquiv, LinearEquiv.coe_coe, LinearEquiv.congrRight, LinearMap, LinearMap.comp_apply, QuadraticMap, QuadraticMap.associated_tmul, associated_apply, associated_tmul, coe_coe, comp_apply, tensorDistrib
-/
theorem associated_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    (Q₁.tmul Q₂).associated = BilinForm.tmul Q₁.associated Q₂.associated := by
  rw [BilinForm.tmul]; rw [BilinForm.tensorDistrib]; rw [LinearMap.comp_apply]; rw [← BilinMap.tmul]; rw [← QuadraticMap.associated_tmul Q₁ Q₂]; rw [LinearEquiv.coe_coe]; rw [LinearEquiv.congrRight₂_apply]
  ext : 6
  simp [associated_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
theorem `polarBilin_tmul` / 定理 `polarBilin_tmul`

English:
theorem polarBilin_tmul
  given: [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂)
  proof: by
  simp_rw [← two_nsmul_associated A, ← two_nsmul_associated R, BilinForm.tmul, tmul_smul,
    ← smul_tmul', map_nsmul, associated_tmul]
  rw [smul_comm (_ : A) (_ : Nat)]; rw [← smul_assoc]; rw [two_smul _ (_ : A)]; rw [invOf_two_add_invOf_two]; rw [one_smul]

中文:
定理 polarBilin_tmul
  条件: [可逆 (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂)
  证明: by
  simp_rw [← two_nsmul_associated A, ← two_nsmul_associated R, BilinForm.tmul, tmul_smul,
    ← smul_tmul', map_nsmul, associated_tmul]
  rw [smul_comm (_ : A) (_ : Nat)]; rw [← smul_assoc]; rw [two_smul _ (_ : A)]; rw [invOf_two_add_invOf_two]; rw [one_smul]

Depends on / 依赖: BilinForm, BilinForm.tmul, associated_tmul, invOf_two_add_invOf_two, map_nsmul, one_smul, simp_rw, smul_assoc, smul_comm, smul_tmul, tmul_smul, two_nsmul_associated, two_smul
-/
theorem polarBilin_tmul [Invertible (2 : A)] (Q₁ : QuadraticForm A M₁) (Q₂ : QuadraticForm R M₂) :
    polarBilin (Q₁.tmul Q₂) = ⅟(2 : A) • BilinForm.tmul (polarBilin Q₁) (polarBilin Q₂) := by
  simp_rw [← two_nsmul_associated A, ← two_nsmul_associated R, BilinForm.tmul, tmul_smul,
    ← smul_tmul', map_nsmul, associated_tmul]
  rw [smul_comm (_ : A) (_ : Nat)]; rw [← smul_assoc]; rw [two_smul _ (_ : A)]; rw [invOf_two_add_invOf_two]; rw [one_smul]

variable (A) in
/--
Definition of `baseChange` / `baseChange` 的定义

English:
definition baseChange
  signature: (Q : QuadraticForm R M₂)
  body: QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticMap.sq (R := A)) Q

@[simp]

中文:
定义 baseChange
  签名: (Q : QuadraticForm R M₂)
  定义体: QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticMap.sq (R := A)) Q

@[simp]
-/
protected def baseChange (Q : QuadraticForm R M₂) : QuadraticForm A (A otimes[R] M₂) :=
  QuadraticForm.tmul (R := R) (A := A) (M₁ := A) (M₂ := M₂) (QuadraticMap.sq (R := A)) Q

@[simp]
/--
theorem `baseChange_tmul` / 定理 `baseChange_tmul`

English:
theorem baseChange_tmul
  given: (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂)
  proof: tensorDistrib_tmul _ _ _ _

中文:
定理 baseChange_tmul
  条件: (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂)
  证明: tensorDistrib_tmul _ _ _ _

Depends on / 依赖: tensorDistrib_tmul
-/
theorem baseChange_tmul (Q : QuadraticForm R M₂) (a : A) (m₂ : M₂) :
    Q.baseChange A (a otimesₜ m₂) = Q m₂ • (a * a) :=
  tensorDistrib_tmul _ _ _ _

/--
theorem `associated_baseChange` / 定理 `associated_baseChange`

English:
theorem associated_baseChange
  given: [Invertible (2 : A)] (Q : QuadraticForm R M₂)
  proof: by
  dsimp only [QuadraticForm.baseChange, LinearMap.baseChange]
  rw [associated_tmul (QuadraticMap.sq (R := A)) Q]; rw [associated_sq]
  exact rfl

中文:
定理 associated_baseChange
  条件: [可逆 (2 : A)] (Q : QuadraticForm R M₂)
  证明: by
  dsimp only [QuadraticForm.baseChange, LinearMap.baseChange]
  rw [associated_tmul (QuadraticMap.sq (R := A)) Q]; rw [associated_sq]
  exact rfl

Depends on / 依赖: BilinForm, BilinForm.baseChange, LinearMap, LinearMap.baseChange, Q.baseChange, QuadraticForm, QuadraticForm.baseChange, QuadraticMap, QuadraticMap.sq, associated, associated_sq, associated_tmul, baseChange
-/
theorem associated_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    associated (R := A) (Q.baseChange A) = BilinForm.baseChange A (associated (R := R) Q) := by
  dsimp only [QuadraticForm.baseChange, LinearMap.baseChange]
  rw [associated_tmul (QuadraticMap.sq (R := A)) Q]; rw [associated_sq]
  exact rfl

/--
theorem `polarBilin_baseChange` / 定理 `polarBilin_baseChange`

English:
theorem polarBilin_baseChange
  given: [Invertible (2 : A)] (Q : QuadraticForm R M₂)
  proof: by
  rw [QuadraticForm.baseChange]; rw [BilinForm.baseChange]; rw [polarBilin_tmul]; rw [BilinForm.tmul]; rw [← map_smul]; rw [smul_tmul']; rw [← two_nsmul_associated R]; rw [coe_associatedHom]; rw [associated_sq]; rw [smul_comm]; rw [← smul_assoc]; rw [two_smul]; rw [invOf_two_add_invOf_two]; rw [one_smul]

中文:
定理 polarBilin_baseChange
  条件: [可逆 (2 : A)] (Q : QuadraticForm R M₂)
  证明: by
  rw [QuadraticForm.baseChange]; rw [BilinForm.baseChange]; rw [polarBilin_tmul]; rw [BilinForm.tmul]; rw [← map_smul]; rw [smul_tmul']; rw [← two_nsmul_associated R]; rw [coe_associatedHom]; rw [associated_sq]; rw [smul_comm]; rw [← smul_assoc]; rw [two_smul]; rw [invOf_two_add_invOf_two]; rw [one_smul]

Depends on / 依赖: BilinForm, BilinForm.baseChange, BilinForm.tmul, QuadraticForm, QuadraticForm.baseChange, associated_sq, baseChange, coe_associatedHom, invOf_two_add_invOf_two, map_smul, one_smul, polarBilin_tmul, smul_assoc, smul_comm, smul_tmul, two_nsmul_associated, two_smul
-/
theorem polarBilin_baseChange [Invertible (2 : A)] (Q : QuadraticForm R M₂) :
    polarBilin (Q.baseChange A) = BilinForm.baseChange A (polarBilin Q) := by
  rw [QuadraticForm.baseChange]; rw [BilinForm.baseChange]; rw [polarBilin_tmul]; rw [BilinForm.tmul]; rw [← map_smul]; rw [smul_tmul']; rw [← two_nsmul_associated R]; rw [coe_associatedHom]; rw [associated_sq]; rw [smul_comm]; rw [← smul_assoc]; rw [two_smul]; rw [invOf_two_add_invOf_two]; rw [one_smul]

end QuadraticForm

end InvertibleTwo

set_option backward.defeqAttrib.useBackward true in
/-- If two quadratic maps from `A ⊗[R] M₂` agree on elements of the form `1 ⊗ m`, they are equal.

In other words, if a base change exists for a quadratic map, it is unique.

Note that unlike `QuadraticForm.baseChange`, this does not need `Invertible (2 : R)`. -/
@[ext]
/--
theorem `baseChange_ext` / 定理 `baseChange_ext`

English:
theorem baseChange_ext
  given: ⦃Q₁ Q₂
  statement: QuadraticMap A (A otimes[R] M₂) N₁⦄
  proof: by
  replace h (a m) : Q₁ (a otimesₜ m) = Q₂ (a otimesₜ m) := by
    rw [← mul_one a]; rw [← smul_eq_mul]; rw [← smul_tmul']; rw [QuadraticMap.map_smul]; rw [QuadraticMap.map_smul]; rw [h]
  ext x
  induction x with
  | tmul => simp [h]
  | zero => simp
  | add x y hx hy =>
    have : Q₁.polarBilin = Q₂.polarBilin := by
      ext
      dsimp [polar]
      rw [← TensorProduct.tmul_add]; rw [h]; rw [h]; rw [h]
    replace := congr($this x y)
    dsimp [polar] at this
    linear_combination (norm := module) this + hx + hy

中文:
定理 baseChange_ext
  条件: ⦃Q₁ Q₂
  结论: 二次映射 A (A otimes[R] M₂) N₁⦄
  证明: by
  replace h (a m) : Q₁ (a otimesₜ m) = Q₂ (a otimesₜ m) := by
    rw [← mul_one a]; rw [← smul_eq_mul]; rw [← smul_tmul']; rw [QuadraticMap.map_smul]; rw [QuadraticMap.map_smul]; rw [h]
  ext x
  induction x with
  | tmul => simp [h]
  | zero => simp
  | add x y hx hy =>
    have : Q₁.polarBilin = Q₂.polarBilin := by
      ext
      dsimp [polar]
      rw [← TensorProduct.tmul_add]; rw [h]; rw [h]; rw [h]
    replace := congr($this x y)
    dsimp [polar] at this
    linear_combination (norm := module) this + hx + hy

Depends on / 依赖: QuadraticMap, QuadraticMap.map_smul, TensorProduct, TensorProduct.tmul_add, linear_combination, map_smul, module, mul_one, polarBilin, replace, smul_eq_mul, smul_tmul, tmul_add
-/
theorem baseChange_ext ⦃Q₁ Q₂ : QuadraticMap A (A otimes[R] M₂) N₁⦄
    (h : forall m, Q₁ (1 otimesₜ m) = Q₂ (1 otimesₜ m)) :
    Q₁ = Q₂ := by
  replace h (a m) : Q₁ (a otimesₜ m) = Q₂ (a otimesₜ m) := by
    rw [← mul_one a]; rw [← smul_eq_mul]; rw [← smul_tmul']; rw [QuadraticMap.map_smul]; rw [QuadraticMap.map_smul]; rw [h]
  ext x
  induction x with
  | tmul => simp [h]
  | zero => simp
  | add x y hx hy =>
    have : Q₁.polarBilin = Q₂.polarBilin := by
      ext
      dsimp [polar]
      rw [← TensorProduct.tmul_add]; rw [h]; rw [h]; rw [h]
    replace := congr($this x y)
    dsimp [polar] at this
    linear_combination (norm := module) this + hx + hy

end CommRing
