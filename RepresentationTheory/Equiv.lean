/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.RepresentationTheory.Intertwining

/-!
## Main purpose

This file is a preliminary file for the `Iso`s in `Rep`, we build all the isomorphisms from
representation level to avoid abusing defeq.

TODO (Edison) : refactor `Rep` into a two-field structure (bundled `Representation`) and rebuild
all the `Iso`s in `Rep` using the equivs in this file.

-/

@[expose] public section

open scoped MonoidAlgebra

universe u u' v v' w w'

variable {k : Type u} [Semiring k] {G : Type v} [Monoid G] {V : Type v'} [AddCommMonoid V]
  [Module k V] {W : Type w'} [AddCommMonoid W] [Module k W] (H : Type w) [Subsingleton H]
  [MulOneClass H] [MulAction G H]

namespace Representation

noncomputable section

variable (k G) in
/--
Definition of `ofMulActionSubsingletonEquivTrivial` / `ofMulActionSubsingletonEquivTrivial` 的定义

English:
definition ofMulActionSubsingletonEquivTrivial
  signature: : (ofMulAction k G H).Equiv (trivial k G k)
  body: .mk (MonoidAlgebra.uniqueLinearEquiv k H) fun g => by ext a; simp [Subsingleton.elim (g • a) a]

@[simp]

中文:
定义 ofMulActionSubsingletonEquivTrivial
  签名: : (ofMulAction k G H).Equiv (trivial k G k)
  定义体: .mk (MonoidAlgebra.uniqueLinearEquiv k H) fun g => by ext a; simp [Subsingleton.elim (g • a) a]

@[simp]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.uniqueLinearEquiv, Subsingleton, Subsingleton.elim, uniqueLinearEquiv
-/
def ofMulActionSubsingletonEquivTrivial : (ofMulAction k G H).Equiv (trivial k G k) :=
  .mk (MonoidAlgebra.uniqueLinearEquiv k H) fun g => by ext a; simp [Subsingleton.elim (g • a) a]

@[simp]
/--
lemma `ofMulActionSubsingletonEquivTrivial_apply` / 引理 `ofMulActionSubsingletonEquivTrivial_apply`

English:
lemma ofMulActionSubsingletonEquivTrivial_apply
  given: (f : k[H])
  proof: rfl

@[simp]

中文:
引理 ofMulActionSubsingletonEquivTrivial_apply
  条件: (f : k[H])
  证明: rfl

@[simp]
-/
lemma ofMulActionSubsingletonEquivTrivial_apply (f : k[H]) :
    (ofMulActionSubsingletonEquivTrivial k G H).toIntertwiningMap.toLinearMap f = f.coeff 1 := rfl

@[simp]
/--
lemma `ofMulActionSubsingletonEquivTrivial_symm_apply` / 引理 `ofMulActionSubsingletonEquivTrivial_symm_apply`

English:
lemma ofMulActionSubsingletonEquivTrivial_symm_apply
  given: (r : k)
  proof: rfl

中文:
引理 ofMulActionSubsingletonEquivTrivial_symm_apply
  条件: (r : k)
  证明: rfl
-/
lemma ofMulActionSubsingletonEquivTrivial_symm_apply (r : k) :
    (ofMulActionSubsingletonEquivTrivial k G H).symm.toIntertwiningMap.toLinearMap r =
      .single 1 r := rfl

variable (k G) in
/--
Definition of `diagonalOneEquivLeftRegular` / `diagonalOneEquivLeftRegular` 的定义

English:
definition diagonalOneEquivLeftRegular
  signature: : (diagonal k G 1).Equiv (leftRegular k G)
  body: .mk (MonoidAlgebra.mapDomainLinearEquiv _ _ <| .funUnique _ _) fun g => by ext; simp

@[simp]

中文:
定义 diagonalOneEquivLeftRegular
  签名: : (diagonal k G 1).Equiv (leftRegular k G)
  定义体: .mk (MonoidAlgebra.mapDomainLinearEquiv _ _ <| .funUnique _ _) fun g => by ext; simp

@[simp]

Depends on / 依赖: MonoidAlgebra, MonoidAlgebra.mapDomainLinearEquiv, funUnique, mapDomainLinearEquiv
-/
def diagonalOneEquivLeftRegular : (diagonal k G 1).Equiv (leftRegular k G) :=
  .mk (MonoidAlgebra.mapDomainLinearEquiv _ _ <| .funUnique _ _) fun g => by ext; simp

@[simp]
/--
lemma `diagonalOneEquivLeftRegular_apply_single` / 引理 `diagonalOneEquivLeftRegular_apply_single`

English:
lemma diagonalOneEquivLeftRegular_apply_single
  given: (f : Fin 1 -> G) (r : k)
  proof: by
  simp [diagonalOneEquivLeftRegular]

@[simp]

中文:
引理 diagonalOneEquivLeftRegular_apply_single
  条件: (f : Fin 1 -> G) (r : k)
  证明: by
  simp [diagonalOneEquivLeftRegular]

@[simp]

Depends on / 依赖: diagonalOneEquivLeftRegular
-/
lemma diagonalOneEquivLeftRegular_apply_single (f : Fin 1 -> G) (r : k) :
    (diagonalOneEquivLeftRegular k G) (.single f r) = .single (f 0) r := by
  simp [diagonalOneEquivLeftRegular]

@[simp]
/--
lemma `diagonalOneEquivLeftRegular_symm_apply_single` / 引理 `diagonalOneEquivLeftRegular_symm_apply_single`

English:
lemma diagonalOneEquivLeftRegular_symm_apply_single
  given: (g : G) (r : k)
  proof: by
  simp [diagonalOneEquivLeftRegular]

中文:
引理 diagonalOneEquivLeftRegular_symm_apply_single
  条件: (g : G) (r : k)
  证明: by
  simp [diagonalOneEquivLeftRegular]

Depends on / 依赖: diagonalOneEquivLeftRegular
-/
lemma diagonalOneEquivLeftRegular_symm_apply_single (g : G) (r : k) :
    (diagonalOneEquivLeftRegular k G).symm (.single g r) = .single (uniqueElim g) r := by
  simp [diagonalOneEquivLeftRegular]

section comm

variable {k : Type u} [CommSemiring k] [Module k V] [Module k W] (σ : Representation k G V)
  (ρ : Representation k G W)

section finsupp

open Finsupp

/-- Every `f : α → V` can induce an intertwining map between `(α →₀ k[G])` and `V`. -/
@[simps! toLinearMap]
/--
Definition of `freeLift` / `freeLift` 的定义

English:
definition freeLift
  signature: {α : Type w'} (f : α -> V)
  body: linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MonoidAlgebra.coeffLinearEquiv _).toLinearMap
  isIntertwining' g := by ext; simp

@[simp]

中文:
定义 freeLift
  签名: {α : Type w'} (f : α -> V)
  定义体: linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MonoidAlgebra.coeffLinearEquiv _).toLinearMap
  isIntertwining' g := by ext; simp

@[simp]

Depends on / 依赖: linearCombination
-/
def freeLift {α : Type w'} (f : α -> V) : (free k G α).IntertwiningMap σ where
  toLinearMap := linearCombination k (fun x => σ x.2 (f x.1)) ∘ₗ
    (curryLinearEquiv k).symm.toLinearMap ∘ₗ
    Finsupp.mapRange.linearMap (MonoidAlgebra.coeffLinearEquiv _).toLinearMap
  isIntertwining' g := by ext; simp

@[simp]
/--
lemma `freeLift_single_single` / 引理 `freeLift_single_single`

English:
lemma freeLift_single_single
  given: {α : Type w'} (i : α) (g : G) (r : k) (f : α -> V)
  proof: by
  simp [freeLift]

中文:
引理 freeLift_single_single
  条件: {α : Type w'} (i : α) (g : G) (r : k) (f : α -> V)
  证明: by
  simp [freeLift]

Depends on / 依赖: freeLift
-/
lemma freeLift_single_single {α : Type w'} (i : α) (g : G) (r : k) (f : α -> V) :
    freeLift σ f (Finsupp.single i (.single g r)) = r • σ g (f i) := by
  simp [freeLift]

open IntertwiningMap

/-- Equiv between the intertwining map module `(α →₀ G →₀ k) → V` and the function space `α → V`. -/
@[simps]
/--
Definition of `freeLiftLEquiv` / `freeLiftLEquiv` 的定义

English:
definition freeLiftLEquiv
  signature: (α : Type w')
  body: f (single i (.single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by ext; simp [← f.isIntertwining]
  right_inv f := by simp [← toLinearMap_apply]

中文:
定义 freeLiftLEquiv
  签名: (α : Type w')
  定义体: f (single i (.single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by ext; simp [← f.isIntertwining]
  right_inv f := by simp [← toLinearMap_apply]

Depends on / 依赖: single
-/
def freeLiftLEquiv (α : Type w') : ((free k G α).IntertwiningMap σ) ≃ₗ[k] (α -> V) where
  toFun f i := f (single i (.single 1 1))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun := freeLift σ
  left_inv f := by ext; simp [← f.isIntertwining]
  right_inv f := by simp [← toLinearMap_apply]

/--
Definition of `finsuppTensorLeft` / `finsuppTensorLeft` 的定义

English:
definition finsuppTensorLeft
  signature: (α : Type w') [DecidableEq α]
  body: .mk (TensorProduct.finsuppLeft _ _ _ _ _) fun g => by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]

中文:
定义 finsuppTensorLeft
  签名: (α : Type w') [DecidableEq α]
  定义体: .mk (TensorProduct.finsuppLeft _ _ _ _ _) fun g => by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]

Depends on / 依赖: TensorProduct, TensorProduct.finsuppLeft, TensorProduct.finsuppLeft_apply_tmul, finsuppLeft, finsuppLeft_apply_tmul
-/
def finsuppTensorLeft (α : Type w') [DecidableEq α] :
    ((σ.finsupp α).tprod ρ).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppLeft _ _ _ _ _) fun g => by
    ext; simp [TensorProduct.finsuppLeft_apply_tmul]

/--
lemma `finsuppTensorLeft_apply_tmul` / 引理 `finsuppTensorLeft_apply_tmul`

English:
lemma finsuppTensorLeft_apply_tmul
  given: {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W)
  proof: by
  simp [finsuppTensorLeft, TensorProduct.finsuppLeft_apply_tmul]

@[simp]

中文:
引理 finsuppTensorLeft_apply_tmul
  条件: {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W)
  证明: by
  simp [finsuppTensorLeft, TensorProduct.finsuppLeft_apply_tmul]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.finsuppLeft_apply_tmul, finsuppLeft_apply_tmul, finsuppTensorLeft
-/
lemma finsuppTensorLeft_apply_tmul {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W) :
    finsuppTensorLeft σ ρ α (f otimesₜ w) = f.sum fun i v => Finsupp.single i (v otimesₜ w) := by
  simp [finsuppTensorLeft, TensorProduct.finsuppLeft_apply_tmul]

@[simp]
/--
lemma `finsuppTensorLeft_apply_tmul_apply` / 引理 `finsuppTensorLeft_apply_tmul_apply`

English:
lemma finsuppTensorLeft_apply_tmul_apply
  statement: {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W)
  proof: by
  simp +contextual [finsuppTensorLeft_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]

中文:
引理 finsuppTensorLeft_apply_tmul_apply
  结论: {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W)
  证明: by
  simp +contextual [finsuppTensorLeft_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, Finsupp.sum_apply, contextual, finsuppTensorLeft_apply_tmul, single_apply, sum_apply
-/
lemma finsuppTensorLeft_apply_tmul_apply {α : Type w'} [DecidableEq α] (f : α ->₀ V) (w : W)
    (i : α) : finsuppTensorLeft σ ρ α (f otimesₜ w) i = f i otimesₜ w := by
  simp +contextual [finsuppTensorLeft_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]
/--
lemma `finsuppTensorLeft_symm_apply_single` / 引理 `finsuppTensorLeft_symm_apply_single`

English:
lemma finsuppTensorLeft_symm_apply_single
  given: {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W)
  proof: by
  simp [finsuppTensorLeft]

中文:
引理 finsuppTensorLeft_symm_apply_single
  条件: {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W)
  证明: by
  simp [finsuppTensorLeft]

Depends on / 依赖: finsuppTensorLeft
-/
lemma finsuppTensorLeft_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W) :
    (finsuppTensorLeft σ ρ α).symm (Finsupp.single i (v otimesₜ w)) = Finsupp.single i v otimesₜ w := by
  simp [finsuppTensorLeft]

/--
Definition of `finsuppTensorRight` / `finsuppTensorRight` 的定义

English:
definition finsuppTensorRight
  signature: (α : Type w') [DecidableEq α]
  body: .mk (TensorProduct.finsuppRight _ _ _ _ _) fun g => by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]

中文:
定义 finsuppTensorRight
  签名: (α : Type w') [DecidableEq α]
  定义体: .mk (TensorProduct.finsuppRight _ _ _ _ _) fun g => by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]

Depends on / 依赖: TensorProduct, TensorProduct.finsuppRight, TensorProduct.finsuppRight_apply_tmul, finsuppRight, finsuppRight_apply_tmul
-/
def finsuppTensorRight (α : Type w') [DecidableEq α] :
    (σ.tprod (ρ.finsupp α)).Equiv ((σ.tprod ρ).finsupp α) :=
  .mk (TensorProduct.finsuppRight _ _ _ _ _) fun g => by
    ext; simp [TensorProduct.finsuppRight_apply_tmul]

/--
lemma `finsuppTensorRight_apply_tmul` / 引理 `finsuppTensorRight_apply_tmul`

English:
lemma finsuppTensorRight_apply_tmul
  given: {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W)
  proof: by
  simp [finsuppTensorRight, TensorProduct.finsuppRight_apply_tmul]

@[simp]

中文:
引理 finsuppTensorRight_apply_tmul
  条件: {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W)
  证明: by
  simp [finsuppTensorRight, TensorProduct.finsuppRight_apply_tmul]

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.finsuppRight_apply_tmul, finsuppRight_apply_tmul, finsuppTensorRight
-/
lemma finsuppTensorRight_apply_tmul {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W) :
    finsuppTensorRight σ ρ α (v otimesₜ f) = f.sum fun i w => Finsupp.single i (v otimesₜ w) := by
  simp [finsuppTensorRight, TensorProduct.finsuppRight_apply_tmul]

@[simp]
/--
lemma `finsuppTensorRight_apply_tmul_apply` / 引理 `finsuppTensorRight_apply_tmul_apply`

English:
lemma finsuppTensorRight_apply_tmul_apply
  statement: {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W)
  proof: by
  simp +contextual [finsuppTensorRight_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]

中文:
引理 finsuppTensorRight_apply_tmul_apply
  结论: {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W)
  证明: by
  simp +contextual [finsuppTensorRight_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]

Depends on / 依赖: Finsupp, Finsupp.single_apply, Finsupp.sum_apply, contextual, finsuppTensorRight_apply_tmul, single_apply, sum_apply
-/
lemma finsuppTensorRight_apply_tmul_apply {α : Type w'} [DecidableEq α] (v : V) (f : α ->₀ W)
    (i : α) : finsuppTensorRight σ ρ α (v otimesₜ f) i = v otimesₜ f i := by
  simp +contextual [finsuppTensorRight_apply_tmul, Finsupp.sum_apply, Finsupp.single_apply]

@[simp]
/--
lemma `finsuppTensorRight_symm_apply_single` / 引理 `finsuppTensorRight_symm_apply_single`

English:
lemma finsuppTensorRight_symm_apply_single
  given: {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W)
  proof: by
  simp [finsuppTensorRight]

中文:
引理 finsuppTensorRight_symm_apply_single
  条件: {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W)
  证明: by
  simp [finsuppTensorRight]

Depends on / 依赖: finsuppTensorRight
-/
lemma finsuppTensorRight_symm_apply_single {α : Type w'} [DecidableEq α] (i : α) (v : V) (w : W) :
    (finsuppTensorRight σ ρ α).symm (Finsupp.single i (v otimesₜ w)) = v otimesₜ Finsupp.single i w := by
  simp [finsuppTensorRight]

/--
Definition of `leftRegularTensorTrivialIsoFree` / `leftRegularTensorTrivialIsoFree` 的定义

English:
definition leftRegularTensorTrivialIsoFree
  signature: (α : Type w')
  body: .mk (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv _) (MonoidAlgebra.coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ curryLinearEquiv k
      ≪≫ₗ Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv _).symm) fun g => by ext; simp



中文:
定义 leftRegularTensorTrivialIsoFree
  签名: (α : Type w')
  定义体: .mk (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv _) (MonoidAlgebra.coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ curryLinearEquiv k
      ≪≫ₗ Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv _).symm) fun g => by ext; simp



Depends on / 依赖: Equiv.prodComm, Finsupp, Finsupp.domLCongr, Finsupp.mapRange.linearEquiv, MonoidAlgebra, MonoidAlgebra.coeffLinearEquiv, TensorProduct, TensorProduct.congr, coeffLinearEquiv, curryLinearEquiv, domLCongr, finsuppTensorFinsupp, linearEquiv, mapRange, prodComm
-/
def leftRegularTensorTrivialIsoFree (α : Type w') :
    ((leftRegular k G).tprod (trivial k G k[α])).Equiv (free k G α) :=
  .mk (TensorProduct.congr (MonoidAlgebra.coeffLinearEquiv _) (MonoidAlgebra.coeffLinearEquiv _) ≪≫ₗ
    finsuppTensorFinsupp' k G α ≪≫ₗ Finsupp.domLCongr (Equiv.prodComm G α) ≪≫ₗ curryLinearEquiv k
      ≪≫ₗ Finsupp.mapRange.linearEquiv (MonoidAlgebra.coeffLinearEquiv _).symm) fun g => by ext; simp

@[simp]
/--
lemma `leftRegularTensorTrivialIsoFree_apply_single_tmul_single` / 引理 `leftRegularTensorTrivialIsoFree_apply_single_tmul_single`

English:
lemma leftRegularTensorTrivialIsoFree_apply_single_tmul_single
  statement: {α : Type w'} (g : G) (i : α)
  proof: by
  simp [leftRegularTensorTrivialIsoFree]

@[simp]

中文:
引理 leftRegularTensorTrivialIsoFree_apply_single_tmul_single
  结论: {α : Type w'} (g : G) (i : α)
  证明: by
  simp [leftRegularTensorTrivialIsoFree]

@[simp]

Depends on / 依赖: leftRegularTensorTrivialIsoFree
-/
lemma leftRegularTensorTrivialIsoFree_apply_single_tmul_single {α : Type w'} (g : G) (i : α)
    (r s : k) : leftRegularTensorTrivialIsoFree α (.single g r otimesₜ .single i s) =
      .single i (.single g (r * s)) := by
  simp [leftRegularTensorTrivialIsoFree]

@[simp]
/--
lemma `leftRegularTensorTrivialIsoFree_symm_apply_single_single` / 引理 `leftRegularTensorTrivialIsoFree_symm_apply_single_single`

English:
lemma leftRegularTensorTrivialIsoFree_symm_apply_single_single
  statement: {α : Type w'} (i : α) (g : G)
  proof: by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

中文:
引理 leftRegularTensorTrivialIsoFree_symm_apply_single_single
  结论: {α : Type w'} (i : α) (g : G)
  证明: by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

Depends on / 依赖: _symm_single_eq_single_one_tmul, finsuppTensorFinsupp, leftRegularTensorTrivialIsoFree
-/
lemma leftRegularTensorTrivialIsoFree_symm_apply_single_single {α : Type w'} (i : α) (g : G)
    (r : k) :
    (leftRegularTensorTrivialIsoFree α).symm (.single i (.single g r)) =
      .single g 1 otimesₜ .single i r := by
  simp [leftRegularTensorTrivialIsoFree, finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

end finsupp

/-- The linear equiv between the hom module `k[G] ⟶ᵍ V` and `V` itself. -/
@[simps!]
/--
Definition of `leftRegularMapEquiv` / `leftRegularMapEquiv` 的定义

English:
definition leftRegularMapEquiv
  signature: : (leftRegular k G).IntertwiningMap σ ≃ₗ[k] V where
  body: (Finsupp.llift V k k G).symm
    (f.toLinearMap ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap) (1 : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.llift _ _ k _ (fun g => σ g v) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv _).toLinearMap, fun g => by ext g'; simp⟩
  left_i

中文:
定义 leftRegularMapEquiv
  签名: : (leftRegular k G).整数ertwiningMap σ ≃ₗ[k] V where
  定义体: (Finsupp.llift V k k G).symm
    (f.toLinearMap ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap) (1 : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.llift _ _ k _ (fun g => σ g v) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv _).toLinearMap, fun g => by ext g'; simp⟩
  left_i

Depends on / 依赖: Finsupp, Finsupp.llift
-/
def leftRegularMapEquiv : (leftRegular k G).IntertwiningMap σ ≃ₗ[k] V where
  toFun f := (Finsupp.llift V k k G).symm
    (f.toLinearMap ∘ₗ (MonoidAlgebra.coeffLinearEquiv _).symm.toLinearMap) (1 : G)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨Finsupp.llift _ _ k _ (fun g => σ g v) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv _).toLinearMap, fun g => by ext g'; simp⟩
  left_inv x := by ext; simp [← x.isIntertwining]
  right_inv v := by simp

set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftRegularMapEquiv_symm_single` / 引理 `leftRegularMapEquiv_symm_single`

English:
lemma leftRegularMapEquiv_symm_single
  given: (g : G) (v : V)
  proof: by
  simp

中文:
引理 leftRegularMapEquiv_symm_single
  条件: (g : G) (v : V)
  证明: by
  simp
-/
lemma leftRegularMapEquiv_symm_single (g : G) (v : V) :
    ((leftRegularMapEquiv σ).symm v) (.single g 1) = σ g v := by
  simp

end comm

end

end Representation
