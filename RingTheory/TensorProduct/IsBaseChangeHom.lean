/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.TensorProduct.IsBaseChangeFree
public import Mathlib.LinearAlgebra.Determinant

/-! # Base change properties for modules of linear maps

* `IsBaseChange.linearMapRight`:
  If `M` is finite free and `P` is a base change of `N` to `S`,
  then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.linearMapLeftRight`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  if `Q` is a base change of `N` to `S`,
  then `P →ₗ[S] Q` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.end`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  then `P →ₗ[S] P` is a base change of `M →ₗ[R] M` to `S`.

-/

@[expose] public section

namespace IsBaseChange

open LinearMap TensorProduct Module

variable {R : Type*} [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {P : Type*} [AddCommMonoid P] [Module R P]

section LinearMapRight

variable [Module S P] [IsScalarTower R S P]

/--
Definition of `linearMapRightBaseChangeHom` / `linearMapRightBaseChangeHom` 的定义

English:
definition linearMapRightBaseChangeHom
  signature: (ε : N ->ₗ[R] P)
  body: (TensorProduct.lift {
    toFun s := s • (LinearMap.compRight R ε (M := M))
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by simp }).toAddHom
  map_smul' s x := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

中文:
定义 linearMapRightBaseChangeHom
  签名: (ε : N ->ₗ[R] P)
  定义体: (TensorProduct.lift {
    toFun s := s • (LinearMap.compRight R ε (M := M))
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by simp }).toAddHom
  map_smul' s x := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

Depends on / 依赖: TensorProduct, TensorProduct.lift
-/
def linearMapRightBaseChangeHom (ε : N ->ₗ[R] P) :
    (S otimes[R] (M ->ₗ[R] N)) ->ₗ[S] (M ->ₗ[R] P) where
  toAddHom := (TensorProduct.lift {
    toFun s := s • (LinearMap.compRight R ε (M := M))
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by simp }).toAddHom
  map_smul' s x := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

variable [Free R M] [Module.Finite R M]

variable {S}

/--
Definition of `linearMapRightBaseChangeEquiv` / `linearMapRightBaseChangeEquiv` 的定义

English:
definition linearMapRightBaseChangeEquiv
  body: by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Free.chooseBasis R M
  set ι := Free.ChooseBasisIndex R M
  have := Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S otimes[R] (M ->ₗ[R] N) ≃ₗ[S] S otimes[R] (ι -> N) :=
    LinearEquiv.baseChange R S (M ->ₗ[R] N) (ι -> N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this, ← LinearEquiv.trans_assoc e'.symm e']
  ext φ i
  simp
  simp [f, e', linearMapRightBaseChangeHom, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

中文:
定义 linearMapRightBaseChangeEquiv
  定义体: by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Free.chooseBasis R M
  set ι := Free.ChooseBasisIndex R M
  have := Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S otimes[R] (M ->ₗ[R] N) ≃ₗ[S] S otimes[R] (ι -> N) :=
    LinearEquiv.baseChange R S (M ->ₗ[R] N) (ι -> N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this, ← LinearEquiv.trans_assoc e'.symm e']
  ext φ i
  simp
  simp [f, e', linearMapRightBaseChangeHom, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

Depends on / 依赖: ChooseBasisIndex, Finsupp, Finsupp.llift, Free.ChooseBasisIndex, Free.ChooseBasisIndex.fintype, Free.chooseBasis, LinearEquiv, LinearEquiv.baseChange, LinearEquiv.ofBijective, b.repr.congrLeft, baseChange, chooseBasis, congrLeft, f.toLinearMap.comp, fintype, linearMapRightBaseChangeHom, ofBijective, otimes, toLinearMap
-/
noncomputable def linearMapRightBaseChangeEquiv
    {ε : N ->ₗ[R] P} (ibc : IsBaseChange S ε) :
    S otimes[R] (M ->ₗ[R] N) ≃ₗ[S] (M ->ₗ[R] P) := by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Free.chooseBasis R M
  set ι := Free.ChooseBasisIndex R M
  have := Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S otimes[R] (M ->ₗ[R] N) ≃ₗ[S] S otimes[R] (ι -> N) :=
    LinearEquiv.baseChange R S (M ->ₗ[R] N) (ι -> N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this, ← LinearEquiv.trans_assoc e'.symm e']
  ext φ i
  simp
  simp [f, e', linearMapRightBaseChangeHom, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

/--
theorem `linearMapRight` / 定理 `linearMapRight`

English:
theorem linearMapRight
  given: {ε : N ->ₗ[R] P} (ibc : IsBaseChange S ε)
  proof: by
  apply of_equiv (linearMapRightBaseChangeEquiv M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom]

中文:
定理 linearMapRight
  条件: {ε : N ->ₗ[R] P} (ibc : IsBaseChange S ε)
  证明: by
  apply of_equiv (linearMapRightBaseChangeEquiv M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom]

Depends on / 依赖: linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom, of_equiv
-/
theorem linearMapRight {ε : N ->ₗ[R] P} (ibc : IsBaseChange S ε) :
    IsBaseChange S (LinearMap.compRight (M := M) R ε) := by
  apply of_equiv (linearMapRightBaseChangeEquiv M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom]

end LinearMapRight

section LinearMapLeftRight

variable {S M}
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]

/--
Definition of `linearMapLeftRightHom` / `linearMapLeftRightHom` 的定义

English:
definition linearMapLeftRightHom
  signature: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  body: ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S otimes[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))

中文:
定义 linearMapLeftRightHom
  签名: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  定义体: ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S otimes[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))

Depends on / 依赖: LinearMap, LinearMap.llcomp, RingHom, RingHom.id, compRight, j.equiv.symm.toLinearMap, liftBaseChangeEquiv, llcomp, otimes, restrictScalars, toLinearMap, toLinearMap.restrictScalars
-/
noncomputable def linearMapLeftRightHom {α : M ->ₗ[R] P} (j : IsBaseChange S α)
    (β : N ->ₗ[R] Q) :
    (M ->ₗ[R] N) ->ₗ[R] (P ->ₗ[S] Q) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S otimes[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))

/--
theorem `linearMapLeftRightHom_apply` / 定理 `linearMapLeftRightHom_apply`

English:
theorem linearMapLeftRightHom_apply
  proof: by
  rfl

中文:
定理 linearMapLeftRightHom_apply
  证明: by
  rfl
-/
theorem linearMapLeftRightHom_apply
    {α : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N ->ₗ[R] Q) (f : M ->ₗ[R] N) (p : P) :
    linearMapLeftRightHom j β f p = ((liftBaseChangeEquiv S) (β ∘ₗ f)) (j.equiv.symm p) := by
  rfl

/--
theorem `linearMapLeftRightHom_comp_apply` / 定理 `linearMapLeftRightHom_comp_apply`

English:
theorem linearMapLeftRightHom_comp_apply
  proof: by
  simp [linearMapLeftRightHom_apply, IsBaseChange.equiv_symm_apply]

中文:
定理 linearMapLeftRightHom_comp_apply
  证明: by
  simp [linearMapLeftRightHom_apply, IsBaseChange.equiv_symm_apply]
-/
@[simp] theorem linearMapLeftRightHom_comp_apply
    {α : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N ->ₗ[R] Q) (f : M ->ₗ[R] N) (m : M) :
    linearMapLeftRightHom j β f (α m) = β (f m) := by
  simp [linearMapLeftRightHom_apply, IsBaseChange.equiv_symm_apply]

/--
theorem `linearMapLeftRightHom_comp` / 定理 `linearMapLeftRightHom_comp`

English:
theorem linearMapLeftRightHom_comp
  proof: by
  ext; simp [linearMapLeftRightHom_comp_apply]

中文:
定理 linearMapLeftRightHom_comp
  证明: by
  ext; simp [linearMapLeftRightHom_comp_apply]
-/
@[simp] theorem linearMapLeftRightHom_comp
    {α : M ->ₗ[R] P} (j : IsBaseChange S α) (β : N ->ₗ[R] Q) (f : M ->ₗ[R] N) :
    (linearMapLeftRightHom j β f).restrictScalars R ∘ₗ α = β ∘ₗ f := by
  ext; simp [linearMapLeftRightHom_comp_apply]

variable [Free R M] [Module.Finite R M]

/--
theorem `linearMapLeftRight` / 定理 `linearMapLeftRight`

English:
theorem linearMapLeftRight
  statement: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  proof: by
apply of_equiv
      (k.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft Q S j.equiv
  intro f
  ext p
  simp [IsBaseChange.equiv_tmul, LinearEquiv.congrLeft, linearMapLeftRightHom_apply]

中文:
定理 linearMapLeftRight
  结论: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  证明: by
apply of_equiv
      (k.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft Q S j.equiv
  intro f
  ext p
  simp [IsBaseChange.equiv_tmul, LinearEquiv.congrLeft, linearMapLeftRightHom_apply]

Depends on / 依赖: IsBaseChange, IsBaseChange.equiv_tmul, LinearEquiv, LinearEquiv.congrLeft, congrLeft, equiv_tmul, j.equiv, k.linearMapRight, liftBaseChangeEquiv, linearMapLeftRightHom_apply, linearMapRight, of_equiv
-/
theorem linearMapLeftRight {α : M ->ₗ[R] P} (j : IsBaseChange S α)
    {β : N ->ₗ[R] Q} (k : IsBaseChange S β) :
    IsBaseChange S (linearMapLeftRightHom j β) := by
apply of_equiv
      (k.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft Q S j.equiv
  intro f
  ext p
  simp [IsBaseChange.equiv_tmul, LinearEquiv.congrLeft, linearMapLeftRightHom_apply]

end LinearMapLeftRight

section End

variable {S M}
  [Module S P] [IsScalarTower R S P]

/--
Definition of `endHom` / `endHom` 的定义

English:
definition endHom
  signature: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  body: ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S otimes[R] M) P).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R α (M := M))

中文:
定义 endHom
  签名: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  定义体: ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S otimes[R] M) P).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R α (M := M))

Depends on / 依赖: LinearMap, LinearMap.llcomp, RingHom, RingHom.id, compRight, j.equiv.symm.toLinearMap, liftBaseChangeEquiv, llcomp, otimes, restrictScalars, toLinearMap, toLinearMap.restrictScalars
-/
noncomputable def endHom {α : M ->ₗ[R] P} (j : IsBaseChange S α) :
    (M ->ₗ[R] M) ->ₗ[R] (P ->ₗ[S] P) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S otimes[R] M) P).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R α (M := M))

/--
theorem `endHom_apply` / 定理 `endHom_apply`

English:
theorem endHom_apply
  proof: by
  rfl

中文:
定理 endHom_apply
  证明: by
  rfl
-/
theorem endHom_apply
    {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) (p : P) :
    endHom j f p = ((liftBaseChangeEquiv S) (α ∘ₗ f)) (j.equiv.symm p) := by
  rfl

/--
theorem `endHom_comp_apply` / 定理 `endHom_comp_apply`

English:
theorem endHom_comp_apply
  proof: by
  simp [endHom_apply, IsBaseChange.equiv_symm_apply]

中文:
定理 endHom_comp_apply
  证明: by
  simp [endHom_apply, IsBaseChange.equiv_symm_apply]

Depends on / 依赖: IsBaseChange, IsBaseChange.equiv_symm_apply, endHom_apply, equiv_symm_apply
-/
theorem endHom_comp_apply
    {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) (m : M) :
    endHom j f (α m) = α (f m) := by
  simp [endHom_apply, IsBaseChange.equiv_symm_apply]

/--
theorem `endHom_comp` / 定理 `endHom_comp`

English:
theorem endHom_comp
  proof: by
  ext; simp [endHom_comp_apply]

中文:
定理 endHom_comp
  证明: by
  ext; simp [endHom_comp_apply]

Depends on / 依赖: endHom_comp_apply
-/
theorem endHom_comp
    {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) :
    (endHom j f).restrictScalars R ∘ₗ α = α ∘ₗ f := by
  ext; simp [endHom_comp_apply]

/--
theorem `endHom_one` / 定理 `endHom_one`

English:
theorem endHom_one
  given: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  proof: by
  ext p
  induction p using j.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul _ _ h => simp [h]
  | tmul m => simp [endHom_comp_apply]

中文:
定理 endHom_one
  条件: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  证明: by
  ext p
  induction p using j.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul _ _ h => simp [h]
  | tmul m => simp [endHom_comp_apply]

Depends on / 依赖: endHom_comp_apply, inductionOn, j.inductionOn
-/
theorem endHom_one {α : M ->ₗ[R] P} (j : IsBaseChange S α) :
    j.endHom 1 = 1 := by
  ext p
  induction p using j.inductionOn with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | smul _ _ h => simp [h]
  | tmul m => simp [endHom_comp_apply]

variable [Free R M] [Module.Finite R M]

/--
theorem `_root_.IsBaseChange.end` / 定理 `_root_.IsBaseChange.end`

English:
theorem _root_.IsBaseChange.end
  given: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  proof: by
apply of_equiv
      (j.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft P S j.equiv
  intro f
  ext p
  simp [equiv_tmul, LinearEquiv.congrLeft, endHom_apply]

中文:
定理 _root_.IsBaseChange.end
  条件: {α : M ->ₗ[R] P} (j : IsBaseChange S α)
  证明: by
apply of_equiv
      (j.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft P S j.equiv
  intro f
  ext p
  simp [equiv_tmul, LinearEquiv.congrLeft, endHom_apply]

Depends on / 依赖: LinearEquiv, LinearEquiv.congrLeft, congrLeft, endHom_apply, equiv_tmul, j.equiv, j.linearMapRight, liftBaseChangeEquiv, linearMapRight, of_equiv
-/
theorem _root_.IsBaseChange.end {α : M ->ₗ[R] P} (j : IsBaseChange S α) :
    IsBaseChange S (endHom j) := by
apply of_equiv
      (j.linearMapRight M).equiv ≪≫ₗ liftBaseChangeEquiv S ≪≫ₗ LinearEquiv.congrLeft P S j.equiv
  intro f
  ext p
  simp [equiv_tmul, LinearEquiv.congrLeft, endHom_apply]

end End

section Matrix

variable {Q : Type*} [AddCommMonoid Q] [Module R Q] [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]
  {α : M ->ₗ[R] P} {β : N ->ₗ[R] Q}
  (ibcM : IsBaseChange S α) (ibcN : IsBaseChange S β)
  {ι θ : Type*} [DecidableEq ι] [Fintype ι] [Finite θ]
  (b : Module.Basis ι R M) (c : Module.Basis θ R N)

/--
theorem `linearMapLeftRightHom_toMatrix` / 定理 `linearMapLeftRightHom_toMatrix`

English:
theorem linearMapLeftRightHom_toMatrix
  given: (f : M ->ₗ[R] N)
  proof: by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply, basis_apply,
    linearMapLeftRightHom_comp_apply, basis_repr_comp_apply]

中文:
定理 linearMapLeftRightHom_toMatrix
  条件: (f : M ->ₗ[R] N)
  证明: by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply, basis_apply,
    linearMapLeftRightHom_comp_apply, basis_repr_comp_apply]

Depends on / 依赖: Matrix, Matrix.map_apply, basis_apply, basis_repr_comp_apply, linearMapLeftRightHom_comp_apply, map_apply, toMatrix_apply
-/
theorem linearMapLeftRightHom_toMatrix (f : M ->ₗ[R] N) :
    (linearMapLeftRightHom ibcM β f).toMatrix (ibcM.basis b) (ibcN.basis c) =
      (f.toMatrix b c).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply, basis_apply,
    linearMapLeftRightHom_comp_apply, basis_repr_comp_apply]

/--
theorem `endHom_toMatrix` / 定理 `endHom_toMatrix`

English:
theorem endHom_toMatrix
  given: (f : M ->ₗ[R] M)
  proof: by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply]
  simp only [basis_apply, endHom_comp_apply, basis_repr_comp_apply]

中文:
定理 endHom_toMatrix
  条件: (f : M ->ₗ[R] M)
  证明: by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply]
  simp only [basis_apply, endHom_comp_apply, basis_repr_comp_apply]

Depends on / 依赖: Matrix, Matrix.map_apply, basis_apply, basis_repr_comp_apply, endHom_comp_apply, map_apply, toMatrix_apply
-/
theorem endHom_toMatrix (f : M ->ₗ[R] M) :
    (endHom ibcM f).toMatrix (ibcM.basis b) (ibcM.basis b) =
      (f.toMatrix b b).map (algebraMap R S) := by
  ext i j
  simp only [toMatrix_apply, Matrix.map_apply]
  simp only [basis_apply, endHom_comp_apply, basis_repr_comp_apply]


end Matrix

section determinant

variable {R : Type*} [CommRing R]
    (S : Type*) [CommRing S] [Algebra R S]
    (M : Type*) [AddCommGroup M] [Module R M]
    {P : Type*} [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]

variable [Free R M] [Module.Finite R M]

/--
theorem `det_endHom` / 定理 `det_endHom`

English:
theorem det_endHom
  given: {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M)
  proof: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : f = 1 := by
      have : Subsingleton M := Module.subsingleton R M
      exact Subsingleton.eq_one f
    simp [this, endHom_one]
  let b := Module.finBasis R M
  rw [← f.det_toMatrix b]; rw [← (j.endHom f).det_toMatrix (j.basis b)]; rw [endHom_toMatrix]; rw [← RingHom.mapMatrix_apply]; rw [← RingHom.map_det]

中文:
定理 det_endHom
  条件: {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M)
  证明: by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : f = 1 := by
      have : Subsingleton M := Module.subsingleton R M
      exact Subsingleton.eq_one f
    simp [this, endHom_one]
  let b := Module.finBasis R M
  rw [← f.det_toMatrix b]; rw [← (j.endHom f).det_toMatrix (j.basis b)]; rw [endHom_toMatrix]; rw [← RingHom.mapMatrix_apply]; rw [← RingHom.map_det]

Depends on / 依赖: Module, Module.finBasis, Module.subsingleton, RingHom, RingHom.mapMatrix_apply, RingHom.map_det, Subsingleton, Subsingleton.eq_one, det_toMatrix, endHom, endHom_one, endHom_toMatrix, eq_one, f.det_toMatrix, finBasis, j.basis, j.endHom, mapMatrix_apply, map_det, subsingleton
-/
theorem det_endHom {α : M ->ₗ[R] P} (j : IsBaseChange S α) (f : M ->ₗ[R] M) :
    LinearMap.det (endHom j f) = algebraMap R S (LinearMap.det f) := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · have : f = 1 := by
      have : Subsingleton M := Module.subsingleton R M
      exact Subsingleton.eq_one f
    simp [this, endHom_one]
  let b := Module.finBasis R M
  rw [← f.det_toMatrix b]; rw [← (j.endHom f).det_toMatrix (j.basis b)]; rw [endHom_toMatrix]; rw [← RingHom.mapMatrix_apply]; rw [← RingHom.map_det]

end determinant

end IsBaseChange
