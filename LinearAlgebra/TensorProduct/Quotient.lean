/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Jujian Zhang
-/
module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!

# Interaction between Quotients and Tensor Products

This file contains constructions that relate quotients and tensor products. This file is also a home
for results whose proof depends on both tensor products and linear algebraic quotients.
Let `M, N` be `R`-modules, `m ≤ M` and `n ≤ N` be an `R`-submodules and `I ≤ R` an ideal. We prove
the following isomorphisms:

## Main results
- `TensorProduct.quotientTensorQuotientEquiv`:
  `(M ⧸ m) ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N ⊔ M ⊗ n)`
- `TensorProduct.quotientTensorEquiv`:
  `(M ⧸ m) ⊗[R] N ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N)`
- `TensorProduct.tensorQuotientEquiv`:
  `M ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (M ⊗ n)`
- `TensorProduct.quotTensorEquivQuotSMul`:
  `(R ⧸ I) ⊗[R] M ≃ₗ[R] M ⧸ (I • M)`
- `TensorProduct.tensorQuotEquivQuotSMul`:
  `M ⊗[R] (R ⧸ I) ≃ₗ[R] M ⧸ (I • M)`

## Tags

Quotient, Tensor Product

-/

@[expose] public section

assert_not_exists Cardinal

namespace TensorProduct

variable {R M N : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

attribute [local ext high] ext LinearMap.prod_ext

/--
Definition of `quotientTensorQuotientEquiv` / `quotientTensorQuotientEquiv` 的定义

English:
definition quotientTensorQuotientEquiv
  signature: (m : Submodule R M) (n : Submodule R N)
  body: LinearEquiv.ofLinearMap
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_a

中文:
定义 quotientTensorQuotientEquiv
  签名: (m : 子模 R M) (n : 子模 R N)
  定义体: LinearEquiv.ofLinearMap
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_a

Depends on / 依赖: Function, Function.comp_apply, LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.coe_comp, LinearMap.compr, LinearMap.flip, LinearMap.flip_apply, LinearMap.zero_apply, Quotient, Submodule, Submodule.Quotient.mk_eq_zero, Submodule.liftQ, Submodule.liftQ_apply, Submodule.mem_sup_right, Submodule.mkQ, Submodule.mkQ_apply, coe_comp, comp_apply
-/
noncomputable def quotientTensorQuotientEquiv (m : Submodule R M) (n : Submodule R N) :
    (M ⧸ (m : Submodule R M)) otimes[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M otimes[R] N) ⧸
      (LinearMap.range (map m.subtype LinearMap.id) ⊔
        LinearMap.range (map LinearMap.id n.subtype)) :=
  LinearEquiv.ofLinearMap
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right ⟨y otimesₜ ⟨x, hx⟩, rfl⟩) fun x hx => by
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
        Submodule.liftQ_apply, LinearMap.compr₂_apply, mk_apply, LinearMap.zero_comp,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left ⟨⟨x, hx⟩ otimesₜ y, rfl⟩)
    (Submodule.liftQ _ (map (Submodule.mkQ _) (Submodule.mkQ _)) fun x hx => by
      rw [Submodule.mem_sup] at hx
      rcases hx with ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      simp only [LinearMap.mem_ker, map_add]
      set f := (map m.mkQ n.mkQ) ∘ₗ (map m.subtype LinearMap.id)
      set g := (map m.mkQ n.mkQ) ∘ₗ (map LinearMap.id n.subtype)
      have eq : LinearMap.coprod f g = 0 := by
        ext x y
        · simp [f, Submodule.Quotient.mk_eq_zero _ |>.2 x.2]
        · simp [g, Submodule.Quotient.mk_eq_zero _ |>.2 y.2]
      exact congr($eq (a, b)))
    (by ext; simp) (by ext; simp)

@[simp]
/--
lemma `quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk` / 引理 `quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk`

English:
lemma quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
  proof: rfl

@[simp]

中文:
引理 quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
  证明: rfl

@[simp]
-/
lemma quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    quotientTensorQuotientEquiv m n
      (Submodule.Quotient.mk x otimesₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x otimesₜ y) := rfl

@[simp]
/--
lemma `quotientTensorQuotientEquiv_symm_apply_mk_tmul` / 引理 `quotientTensorQuotientEquiv_symm_apply_mk_tmul`

English:
lemma quotientTensorQuotientEquiv_symm_apply_mk_tmul
  proof: rfl

中文:
引理 quotientTensorQuotientEquiv_symm_apply_mk_tmul
  证明: rfl
-/
lemma quotientTensorQuotientEquiv_symm_apply_mk_tmul
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    (quotientTensorQuotientEquiv m n).symm (Submodule.Quotient.mk (x otimesₜ y)) =
      Submodule.Quotient.mk x otimesₜ[R] Submodule.Quotient.mk y := rfl

variable (N) in
/--
Definition of `quotientTensorEquiv` / `quotientTensorEquiv` 的定义

English:
definition quotientTensorEquiv
  signature: (m : Submodule R M)
  body: congr (LinearEquiv.refl _ _) ((Submodule.quotEquivOfEqBot _ rfl).symm) ≪≫ₗ
  quotientTensorQuotientEquiv (N := N) m ⊥ ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp [Submodule.map_span, range_map_eq_span_tmul])

@[simp]

中文:
定义 quotientTensorEquiv
  签名: (m : 子模 R M)
  定义体: congr (LinearEquiv.refl _ _) ((Submodule.quotEquivOfEqBot _ rfl).symm) ≪≫ₗ
  quotientTensorQuotientEquiv (N := N) m ⊥ ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp [Submodule.map_span, range_map_eq_span_tmul])

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, Quotient, Submodule, Submodule.Quotient.equiv, Submodule.map_span, Submodule.quotEquivOfEqBot, map_span, quotEquivOfEqBot, quotientTensorQuotientEquiv, range_map_eq_span_tmul
-/
noncomputable def quotientTensorEquiv (m : Submodule R M) :
    (M ⧸ (m : Submodule R M)) otimes[R] N ≃ₗ[R]
    (M otimes[R] N) ⧸ (LinearMap.range (map m.subtype (LinearMap.id : N ->ₗ[R] N))) :=
  congr (LinearEquiv.refl _ _) ((Submodule.quotEquivOfEqBot _ rfl).symm) ≪≫ₗ
  quotientTensorQuotientEquiv (N := N) m ⊥ ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp [Submodule.map_span, range_map_eq_span_tmul])

@[simp]
/--
lemma `quotientTensorEquiv_apply_tmul_mk` / 引理 `quotientTensorEquiv_apply_tmul_mk`

English:
lemma quotientTensorEquiv_apply_tmul_mk
  given: (m : Submodule R M) (x : M) (y : N)
  proof: rfl

@[simp]

中文:
引理 quotientTensorEquiv_apply_tmul_mk
  条件: (m : 子模 R M) (x : M) (y : N)
  证明: rfl

@[simp]
-/
lemma quotientTensorEquiv_apply_tmul_mk (m : Submodule R M) (x : M) (y : N) :
    quotientTensorEquiv N m (Submodule.Quotient.mk x otimesₜ[R] y) =
    Submodule.Quotient.mk (x otimesₜ y) :=
  rfl

@[simp]
/--
lemma `quotientTensorEquiv_symm_apply_mk_tmul` / 引理 `quotientTensorEquiv_symm_apply_mk_tmul`

English:
lemma quotientTensorEquiv_symm_apply_mk_tmul
  given: (m : Submodule R M) (x : M) (y : N)
  proof: rfl

中文:
引理 quotientTensorEquiv_symm_apply_mk_tmul
  条件: (m : 子模 R M) (x : M) (y : N)
  证明: rfl
-/
lemma quotientTensorEquiv_symm_apply_mk_tmul (m : Submodule R M) (x : M) (y : N) :
    (quotientTensorEquiv N m).symm (Submodule.Quotient.mk (x otimesₜ y)) =
    Submodule.Quotient.mk x otimesₜ[R] y :=
  rfl

variable (M) in
/--
Definition of `tensorQuotientEquiv` / `tensorQuotientEquiv` 的定义

English:
definition tensorQuotientEquiv
  signature: (n : Submodule R N)
  body: congr ((Submodule.quotEquivOfEqBot _ rfl).symm) (LinearEquiv.refl _ _) ≪≫ₗ
  quotientTensorQuotientEquiv (⊥ : Submodule R M) n ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by simp [range_map_eq_span_tmul])

@[simp]

中文:
定义 tensorQuotientEquiv
  签名: (n : 子模 R N)
  定义体: congr ((Submodule.quotEquivOfEqBot _ rfl).symm) (LinearEquiv.refl _ _) ≪≫ₗ
  quotientTensorQuotientEquiv (⊥ : Submodule R M) n ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by simp [range_map_eq_span_tmul])

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.refl, Quotient, Submodule, Submodule.Quotient.equiv, Submodule.quotEquivOfEqBot, quotEquivOfEqBot, quotientTensorQuotientEquiv, range_map_eq_span_tmul
-/
noncomputable def tensorQuotientEquiv (n : Submodule R N) :
    M otimes[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M otimes[R] N) ⧸ (LinearMap.range (map (LinearMap.id : M ->ₗ[R] M) n.subtype)) :=
  congr ((Submodule.quotEquivOfEqBot _ rfl).symm) (LinearEquiv.refl _ _) ≪≫ₗ
  quotientTensorQuotientEquiv (⊥ : Submodule R M) n ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by simp [range_map_eq_span_tmul])

@[simp]
/--
lemma `tensorQuotientEquiv_apply_mk_tmul` / 引理 `tensorQuotientEquiv_apply_mk_tmul`

English:
lemma tensorQuotientEquiv_apply_mk_tmul
  given: (n : Submodule R N) (x : M) (y : N)
  proof: rfl

@[simp]

中文:
引理 tensorQuotientEquiv_apply_mk_tmul
  条件: (n : 子模 R N) (x : M) (y : N)
  证明: rfl

@[simp]
-/
lemma tensorQuotientEquiv_apply_mk_tmul (n : Submodule R N) (x : M) (y : N) :
    tensorQuotientEquiv M n (x otimesₜ[R] Submodule.Quotient.mk y) =
    Submodule.Quotient.mk (x otimesₜ y) :=
  rfl

@[simp]
/--
lemma `tensorQuotientEquiv_symm_apply_tmul_mk` / 引理 `tensorQuotientEquiv_symm_apply_tmul_mk`

English:
lemma tensorQuotientEquiv_symm_apply_tmul_mk
  given: (n : Submodule R N) (x : M) (y : N)
  proof: rfl

中文:
引理 tensorQuotientEquiv_symm_apply_tmul_mk
  条件: (n : 子模 R N) (x : M) (y : N)
  证明: rfl
-/
lemma tensorQuotientEquiv_symm_apply_tmul_mk (n : Submodule R N) (x : M) (y : N) :
    (tensorQuotientEquiv M n).symm (Submodule.Quotient.mk (x otimesₜ y)) =
    x otimesₜ[R] Submodule.Quotient.mk y :=
  rfl

variable (M) in
/--
Definition of `quotTensorEquivQuotSMul` / `quotTensorEquivQuotSMul` 的定义

English:
definition quotTensorEquivQuotSMul
  signature: (I : Ideal R)
  body: quotientTensorEquiv M I ≪≫ₗ
  (Submodule.Quotient.equiv _ _ (TensorProduct.lid R M) <| by
    rw [← LinearMap.range_comp]; rw [← (Submodule.topEquiv.lTensor I).range_comp]; rw [Submodule.smul_eq_map₂]; rw [map₂_eq_range_lift_comp_mapIncl]
    exact congr_arg _ (TensorProduct.ext' fun _ _ => by simp)

中文:
定义 quotTensorEquivQuotSMul
  签名: (I : 理想 R)
  定义体: quotientTensorEquiv M I ≪≫ₗ
  (Submodule.Quotient.equiv _ _ (TensorProduct.lid R M) <| by
    rw [← LinearMap.range_comp]; rw [← (Submodule.topEquiv.lTensor I).range_comp]; rw [Submodule.smul_eq_map₂]; rw [map₂_eq_range_lift_comp_mapIncl]
    exact congr_arg _ (TensorProduct.ext' fun _ _ => by simp)

Depends on / 依赖: LinearMap, LinearMap.range_comp, Quotient, Submodule, Submodule.Quotient.equiv, Submodule.smul_eq_map, Submodule.topEquiv.lTensor, TensorProduct, TensorProduct.ext, TensorProduct.lid, congr_arg, lTensor, quotientTensorEquiv, range_comp, topEquiv
-/
noncomputable def quotTensorEquivQuotSMul (I : Ideal R) :
    ((R ⧸ I) otimes[R] M) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  quotientTensorEquiv M I ≪≫ₗ
  (Submodule.Quotient.equiv _ _ (TensorProduct.lid R M) <| by
    rw [← LinearMap.range_comp]; rw [← (Submodule.topEquiv.lTensor I).range_comp]; rw [Submodule.smul_eq_map₂]; rw [map₂_eq_range_lift_comp_mapIncl]
    exact congr_arg _ (TensorProduct.ext' fun _ _ => by simp))

variable (M) in
/--
Definition of `tensorQuotEquivQuotSMul` / `tensorQuotEquivQuotSMul` 的定义

English:
definition tensorQuotEquivQuotSMul
  signature: (I : Ideal R)
  body: TensorProduct.comm _ _ _ ≪≫ₗ quotTensorEquivQuotSMul M I

@[simp]

中文:
定义 tensorQuotEquivQuotSMul
  签名: (I : 理想 R)
  定义体: TensorProduct.comm _ _ _ ≪≫ₗ quotTensorEquivQuotSMul M I

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.comm, quotTensorEquivQuotSMul
-/
noncomputable def tensorQuotEquivQuotSMul (I : Ideal R) :
    (M otimes[R] (R ⧸ I)) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  TensorProduct.comm _ _ _ ≪≫ₗ quotTensorEquivQuotSMul M I

@[simp]
/--
lemma `quotTensorEquivQuotSMul_mk_tmul` / 引理 `quotTensorEquivQuotSMul_mk_tmul`

English:
lemma quotTensorEquivQuotSMul_mk_tmul
  given: (I : Ideal R) (r : R) (x : M)
  proof: (quotTensorEquivQuotSMul M I).eq_symm_apply.mp
    Eq.trans (congrArg (· otimesₜ[R] x) <|
        Eq.trans (congrArg (Ideal.Quotient.mk I)
                    (Eq.trans (smul_eq_mul ..) (mul_one r))).symm <|
          Submodule.Quotient.mk_smul I r 1) <|
      smul_tmul r _ x

@[simp]

中文:
引理 quotTensorEquivQuotSMul_mk_tmul
  条件: (I : 理想 R) (r : R) (x : M)
  证明: (quotTensorEquivQuotSMul M I).eq_symm_apply.mp
    Eq.trans (congrArg (· otimesₜ[R] x) <|
        Eq.trans (congrArg (Ideal.Quotient.mk I)
                    (Eq.trans (smul_eq_mul ..) (mul_one r))).symm <|
          Submodule.Quotient.mk_smul I r 1) <|
      smul_tmul r _ x

@[simp]

Depends on / 依赖: Eq.trans, Ideal.Quotient.mk, Quotient, Submodule, Submodule.Quotient.mk_smul, eq_symm_apply, eq_symm_apply.mp, mk_smul, mul_one, quotTensorEquivQuotSMul, smul_eq_mul, smul_tmul
-/
lemma quotTensorEquivQuotSMul_mk_tmul (I : Ideal R) (r : R) (x : M) :
    quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I r otimesₜ[R] x) =
      Submodule.Quotient.mk (r • x) :=
(quotTensorEquivQuotSMul M I).eq_symm_apply.mp
    Eq.trans (congrArg (· otimesₜ[R] x) <|
        Eq.trans (congrArg (Ideal.Quotient.mk I)
                    (Eq.trans (smul_eq_mul ..) (mul_one r))).symm <|
          Submodule.Quotient.mk_smul I r 1) <|
      smul_tmul r _ x

@[simp]
/--
lemma `quotTensorEquivQuotSMul_mk_one_tmul` / 引理 `quotTensorEquivQuotSMul_mk_one_tmul`

English:
lemma quotTensorEquivQuotSMul_mk_one_tmul
  given: (I : Ideal R) (x : M)
  proof: by
  rw [← RingHom.map_one (Ideal.Quotient.mk I)]; rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp

中文:
引理 quotTensorEquivQuotSMul_mk_one_tmul
  条件: (I : 理想 R) (x : M)
  证明: by
  rw [← RingHom.map_one (Ideal.Quotient.mk I)]; rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp

Depends on / 依赖: Ideal.Quotient.mk, Quotient, RingHom, RingHom.map_one, TensorProduct, TensorProduct.quotTensorEquivQuotSMul_mk_tmul, map_one, quotTensorEquivQuotSMul_mk_tmul
-/
lemma quotTensorEquivQuotSMul_mk_one_tmul (I : Ideal R) (x : M) :
    quotTensorEquivQuotSMul M I (1 otimesₜ x) = Submodule.Quotient.mk x := by
  rw [← RingHom.map_one (Ideal.Quotient.mk I)]; rw [TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp

/--
lemma `quotTensorEquivQuotSMul_comp_mkQ_rTensor` / 引理 `quotTensorEquivQuotSMul_comp_mkQ_rTensor`

English:
lemma quotTensorEquivQuotSMul_comp_mkQ_rTensor
  given: (I : Ideal R)
  proof: TensorProduct.ext' (quotTensorEquivQuotSMul_mk_tmul I)

@[simp]

中文:
引理 quotTensorEquivQuotSMul_comp_mkQ_rTensor
  条件: (I : 理想 R)
  证明: TensorProduct.ext' (quotTensorEquivQuotSMul_mk_tmul I)

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.ext, quotTensorEquivQuotSMul_mk_tmul
-/
lemma quotTensorEquivQuotSMul_comp_mkQ_rTensor (I : Ideal R) :
    quotTensorEquivQuotSMul M I ∘ₗ I.mkQ.rTensor M =
      (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.lid R M :=
  TensorProduct.ext' (quotTensorEquivQuotSMul_mk_tmul I)

@[simp]
/--
lemma `quotTensorEquivQuotSMul_symm_mk` / 引理 `quotTensorEquivQuotSMul_symm_mk`

English:
lemma quotTensorEquivQuotSMul_symm_mk
  given: (I : Ideal R) (x : M)
  proof: rfl

中文:
引理 quotTensorEquivQuotSMul_symm_mk
  条件: (I : 理想 R) (x : M)
  证明: rfl
-/
lemma quotTensorEquivQuotSMul_symm_mk (I : Ideal R) (x : M) :
    (quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk x) = 1 otimesₜ[R] x :=
  rfl

/--
lemma `quotTensorEquivQuotSMul_symm_comp_mkQ` / 引理 `quotTensorEquivQuotSMul_symm_comp_mkQ`

English:
lemma quotTensorEquivQuotSMul_symm_comp_mkQ
  given: (I : Ideal R)
  proof: LinearMap.ext (quotTensorEquivQuotSMul_symm_mk I)

中文:
引理 quotTensorEquivQuotSMul_symm_comp_mkQ
  条件: (I : 理想 R)
  证明: LinearMap.ext (quotTensorEquivQuotSMul_symm_mk I)

Depends on / 依赖: LinearMap, LinearMap.ext, quotTensorEquivQuotSMul_symm_mk
-/
lemma quotTensorEquivQuotSMul_symm_comp_mkQ (I : Ideal R) :
    (quotTensorEquivQuotSMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ =
      TensorProduct.mk R (R ⧸ I) M 1 :=
  LinearMap.ext (quotTensorEquivQuotSMul_symm_mk I)

/--
lemma `quotTensorEquivQuotSMul_comp_mk` / 引理 `quotTensorEquivQuotSMul_comp_mk`

English:
lemma quotTensorEquivQuotSMul_comp_mk
  given: (I : Ideal R)
  proof: Eq.symm (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp
    quotTensorEquivQuotSMul_symm_comp_mkQ I

@[simp]

中文:
引理 quotTensorEquivQuotSMul_comp_mk
  条件: (I : 理想 R)
  证明: Eq.symm (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp
    quotTensorEquivQuotSMul_symm_comp_mkQ I

@[simp]

Depends on / 依赖: Eq.symm, LinearEquiv, LinearEquiv.toLinearMap_symm_comp_eq, quotTensorEquivQuotSMul_symm_comp_mkQ, toLinearMap_symm_comp_eq
-/
lemma quotTensorEquivQuotSMul_comp_mk (I : Ideal R) :
    quotTensorEquivQuotSMul M I ∘ₗ TensorProduct.mk R (R ⧸ I) M 1 =
      Submodule.mkQ (I • ⊤) :=
Eq.symm (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp
    quotTensorEquivQuotSMul_symm_comp_mkQ I

@[simp]
/--
lemma `tensorQuotEquivQuotSMul_tmul_mk` / 引理 `tensorQuotEquivQuotSMul_tmul_mk`

English:
lemma tensorQuotEquivQuotSMul_tmul_mk
  given: (I : Ideal R) (x : M) (r : R)
  proof: quotTensorEquivQuotSMul_mk_tmul I r x

中文:
引理 tensorQuotEquivQuotSMul_tmul_mk
  条件: (I : 理想 R) (x : M) (r : R)
  证明: quotTensorEquivQuotSMul_mk_tmul I r x

Depends on / 依赖: quotTensorEquivQuotSMul_mk_tmul
-/
lemma tensorQuotEquivQuotSMul_tmul_mk (I : Ideal R) (x : M) (r : R) :
    tensorQuotEquivQuotSMul M I (x otimesₜ[R] Ideal.Quotient.mk I r) =
      Submodule.Quotient.mk (r • x) :=
  quotTensorEquivQuotSMul_mk_tmul I r x

/--
lemma `tensorQuotEquivQuotSMul_comp_mkQ_lTensor` / 引理 `tensorQuotEquivQuotSMul_comp_mkQ_lTensor`

English:
lemma tensorQuotEquivQuotSMul_comp_mkQ_lTensor
  given: (I : Ideal R)
  proof: TensorProduct.ext' (tensorQuotEquivQuotSMul_tmul_mk I)

@[simp]

中文:
引理 tensorQuotEquivQuotSMul_comp_mkQ_lTensor
  条件: (I : 理想 R)
  证明: TensorProduct.ext' (tensorQuotEquivQuotSMul_tmul_mk I)

@[simp]

Depends on / 依赖: TensorProduct, TensorProduct.ext, tensorQuotEquivQuotSMul_tmul_mk
-/
lemma tensorQuotEquivQuotSMul_comp_mkQ_lTensor (I : Ideal R) :
    tensorQuotEquivQuotSMul M I ∘ₗ I.mkQ.lTensor M =
      (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.rid R M :=
  TensorProduct.ext' (tensorQuotEquivQuotSMul_tmul_mk I)

@[simp]
/--
lemma `tensorQuotEquivQuotSMul_symm_mk` / 引理 `tensorQuotEquivQuotSMul_symm_mk`

English:
lemma tensorQuotEquivQuotSMul_symm_mk
  given: (I : Ideal R) (x : M)
  proof: rfl

中文:
引理 tensorQuotEquivQuotSMul_symm_mk
  条件: (I : 理想 R) (x : M)
  证明: rfl
-/
lemma tensorQuotEquivQuotSMul_symm_mk (I : Ideal R) (x : M) :
    (tensorQuotEquivQuotSMul M I).symm (Submodule.Quotient.mk x) = x otimesₜ[R] 1 :=
  rfl

/--
lemma `tensorQuotEquivQuotSMul_symm_comp_mkQ` / 引理 `tensorQuotEquivQuotSMul_symm_comp_mkQ`

English:
lemma tensorQuotEquivQuotSMul_symm_comp_mkQ
  given: (I : Ideal R)
  proof: LinearMap.ext (tensorQuotEquivQuotSMul_symm_mk I)

中文:
引理 tensorQuotEquivQuotSMul_symm_comp_mkQ
  条件: (I : 理想 R)
  证明: LinearMap.ext (tensorQuotEquivQuotSMul_symm_mk I)

Depends on / 依赖: LinearMap, LinearMap.ext, tensorQuotEquivQuotSMul_symm_mk
-/
lemma tensorQuotEquivQuotSMul_symm_comp_mkQ (I : Ideal R) :
    (tensorQuotEquivQuotSMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ =
      (TensorProduct.mk R M (R ⧸ I)).flip 1 :=
  LinearMap.ext (tensorQuotEquivQuotSMul_symm_mk I)

/--
lemma `tensorQuotEquivQuotSMul_comp_mk` / 引理 `tensorQuotEquivQuotSMul_comp_mk`

English:
lemma tensorQuotEquivQuotSMul_comp_mk
  given: (I : Ideal R)
  proof: Eq.symm (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp
    tensorQuotEquivQuotSMul_symm_comp_mkQ I

中文:
引理 tensorQuotEquivQuotSMul_comp_mk
  条件: (I : 理想 R)
  证明: Eq.symm (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp
    tensorQuotEquivQuotSMul_symm_comp_mkQ I

Depends on / 依赖: Eq.symm, LinearEquiv, LinearEquiv.toLinearMap_symm_comp_eq, tensorQuotEquivQuotSMul_symm_comp_mkQ, toLinearMap_symm_comp_eq
-/
lemma tensorQuotEquivQuotSMul_comp_mk (I : Ideal R) :
    tensorQuotEquivQuotSMul M I ∘ₗ (TensorProduct.mk R M (R ⧸ I)).flip 1 =
      Submodule.mkQ (I • ⊤) :=
Eq.symm (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp
    tensorQuotEquivQuotSMul_symm_comp_mkQ I

variable (S : Type*) [CommRing S] [Algebra R S]

/--
Definition of `_root_.Ideal.qoutMapEquivTensorQout` / `_root_.Ideal.qoutMapEquivTensorQout` 的定义

English:
definition _root_.Ideal.qoutMapEquivTensorQout
  signature: {I : Ideal R}
  body: LinearEquiv.symm tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp)
    ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _
  map_smul' := by
    rintro _ ⟨_⟩
    congr

中文:
定义 _root_.理想.qoutMapEquivTensorQout
  签名: {I : 理想 R}
  定义体: LinearEquiv.symm tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp)
    ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _
  map_smul' := by
    rintro _ ⟨_⟩
    congr

Depends on / 依赖: LinearEquiv, LinearEquiv.symm, Submodule, Submodule.quotEquivOfEq, quotEquivOfEq, tensorQuotEquivQuotSMul
-/
noncomputable def _root_.Ideal.qoutMapEquivTensorQout {I : Ideal R} :
    (S ⧸ I.map (algebraMap R S)) ≃ₗ[S] S otimes[R] (R ⧸ I) where
__ := LinearEquiv.symm tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp)
    ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _
  map_smul' := by
    rintro _ ⟨_⟩
    congr

variable (M) in
/--
Definition of `tensorQuotMapSMulEquivTensorQuot` / `tensorQuotMapSMulEquivTensorQuot` 的定义

English:
definition tensorQuotMapSMulEquivTensorQuot
  signature: (I : Ideal R)
  body: (tensorQuotEquivQuotSMul (S otimes[R] M) (I.map (algebraMap R S))).symm ≪≫ₗ
    TensorProduct.comm S (S otimes[R] M) _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S _ M ≪≫ₗ
      AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (LinearEquiv.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc R R 

中文:
定义 tensorQuotMapSMulEquivTensorQuot
  签名: (I : 理想 R)
  定义体: (tensorQuotEquivQuotSMul (S otimes[R] M) (I.map (algebraMap R S))).symm ≪≫ₗ
    TensorProduct.comm S (S otimes[R] M) _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S _ M ≪≫ₗ
      AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (LinearEquiv.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc R R 

Depends on / 依赖: AlgebraTensorModule, AlgebraTensorModule.assoc, AlgebraTensorModule.cancelBaseChange, AlgebraTensorModule.congr, I.map, I.qoutMapEquivTensorQout, LinearEquiv, LinearEquiv.refl, TensorProduct, TensorProduct.comm, algebraMap, baseChange, cancelBaseChange, otimes, qoutMapEquivTensorQout, tensorQuotEquivQuotSMul
-/
noncomputable def tensorQuotMapSMulEquivTensorQuot (I : Ideal R) :
    ((S otimes[R] M) ⧸ I.map (algebraMap R S) • (⊤ : Submodule S (S otimes[R] M))) ≃ₗ[S]
    S otimes[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  (tensorQuotEquivQuotSMul (S otimes[R] M) (I.map (algebraMap R S))).symm ≪≫ₗ
    TensorProduct.comm S (S otimes[R] M) _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S _ M ≪≫ₗ
      AlgebraTensorModule.congr (I.qoutMapEquivTensorQout S) (LinearEquiv.refl R M) ≪≫ₗ
        AlgebraTensorModule.assoc R R S S _ M ≪≫ₗ (TensorProduct.comm R _ M).baseChange R S _ _ ≪≫ₗ
          (tensorQuotEquivQuotSMul M I).baseChange R S _ _

end TensorProduct

open TensorProduct

namespace TensorProduct.AlgebraTensorModule

variable {R : Type*} (A B : Type*) [CommRing R] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B]
variable (M : Type*) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
variable {N : Type*} [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N]

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `tensorQuotientEquiv` / `tensorQuotientEquiv` 的定义

English:
definition tensorQuotientEquiv
  signature: (n : Submodule B N)
  body: TensorProduct.tensorQuotientEquiv M (n.restrictScalars R)
  map_smul' m x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
      obtain ⟨y, rfl⟩ := Submodule.Quotient.

中文:
定义 tensorQuotientEquiv
  签名: (n : 子模 B N)
  定义体: TensorProduct.tensorQuotientEquiv M (n.restrictScalars R)
  map_smul' m x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
      obtain ⟨y, rfl⟩ := Submodule.Quotient.

Depends on / 依赖: TensorProduct, TensorProduct.tensorQuotientEquiv, n.restrictScalars, restrictScalars, tensorQuotientEquiv
-/
noncomputable def tensorQuotientEquiv (n : Submodule B N) :
    M otimes[R] (N ⧸ n) ≃ₗ[A]
      (M otimes[R] N) ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) where
  __ := TensorProduct.tensorQuotientEquiv M (n.restrictScalars R)
  map_smul' m x := by
    simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearEquiv.coe_coe]
    induction x with
    | zero => simp
    | add x y hx hy => simp [hx, hy]
    | tmul x y =>
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [smul_tmul']
      rfl

@[simp]
/--
lemma `tensorQuotientEquiv_apply_tmul` / 引理 `tensorQuotientEquiv_apply_tmul`

English:
lemma tensorQuotientEquiv_apply_tmul
  given: (n : Submodule B N) (x : M) (y : N)
  proof: rfl

@[simp]

中文:
引理 tensorQuotientEquiv_apply_tmul
  条件: (n : 子模 B N) (x : M) (y : N)
  证明: rfl

@[simp]
-/
lemma tensorQuotientEquiv_apply_tmul (n : Submodule B N) (x : M) (y : N) :
    tensorQuotientEquiv A B M n (x otimesₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x otimesₜ[R] y) :=
  rfl

@[simp]
/--
lemma `tensorQuotientEquiv_symm_apply_mk_tmul` / 引理 `tensorQuotientEquiv_symm_apply_mk_tmul`

English:
lemma tensorQuotientEquiv_symm_apply_mk_tmul
  given: (n : Submodule B N) (x : M) (y : N)
  proof: rfl

中文:
引理 tensorQuotientEquiv_symm_apply_mk_tmul
  条件: (n : 子模 B N) (x : M) (y : N)
  证明: rfl
-/
lemma tensorQuotientEquiv_symm_apply_mk_tmul (n : Submodule B N) (x : M) (y : N) :
    (tensorQuotientEquiv A B M n).symm (Submodule.Quotient.mk (x otimesₜ[R] y)) =
      x otimesₜ[R] Submodule.Quotient.mk y :=
  rfl


variable [Module A N] [IsScalarTower R A N]

/--
lemma `ker_mapOfCompatibleSMul` / 引理 `ker_mapOfCompatibleSMul`

English:
lemma ker_mapOfCompatibleSMul
  proof: by
  refine (Submodule.span_eq_of_le (mapOfCompatibleSMul A R A M N).ker ?_ ?_).symm
  · rintro - ⟨a, m, n, rfl⟩
    simp [smul_tmul]
  · let S := Submodule.span A {(a • m) otimesₜ[R] n - m otimesₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M otimes[A] N ->ₗ[A] (M otimes[R] N) ⧸ S := TensorPr

中文:
引理 ker_mapOfCompatibleSMul
  证明: by
  refine (Submodule.span_eq_of_le (mapOfCompatibleSMul A R A M N).ker ?_ ?_).symm
  · rintro - ⟨a, m, n, rfl⟩
    simp [smul_tmul]
  · let S := Submodule.span A {(a • m) otimesₜ[R] n - m otimesₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M otimes[A] N ->ₗ[A] (M otimes[R] N) ⧸ S := TensorPr

Depends on / 依赖: Quotient, S.mkQ, Submodule, Submodule.Quotient.mk_smul, Submodule.mkQ_apply, Submodule.span, Submodule.span_eq_of_le, TensorProduct, TensorProduct.lift, eq_comm, mapOfCompatibleSMul, map_add, map_smul, mkQ_apply, mk_smul, otimes, smul_tmul, span_eq_of_le, tmul_add
-/
lemma ker_mapOfCompatibleSMul :
    (mapOfCompatibleSMul A R A M N).ker =
      Submodule.span A {(a • m) otimesₜ[R] n - m otimesₜ[R] (a • n) | (a : A) (m : M) (n : N)} := by
  refine (Submodule.span_eq_of_le (mapOfCompatibleSMul A R A M N).ker ?_ ?_).symm
  · rintro - ⟨a, m, n, rfl⟩
    simp [smul_tmul]
  · let S := Submodule.span A {(a • m) otimesₜ[R] n - m otimesₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M otimes[A] N ->ₗ[A] (M otimes[R] N) ⧸ S := TensorProduct.lift ({
      toFun m := {
        toFun n := S.mkQ (m otimesₜ[R] n)
        map_add' _ _ := by simp [tmul_add]
        map_smul' a n := by
          rw [Submodule.mkQ_apply]; rw [Submodule.mkQ_apply]; rw [← Submodule.Quotient.mk_smul]; rw [eq_comm]; rw [Submodule.Quotient.eq]; rw [RingHom.id_apply]
          exact Submodule.subset_span ⟨a, m, n, rfl⟩ }
      map_add' _ _ := by ext _; simp [add_tmul]
      map_smul' _ _ := by simp; rfl })
    have h : F ∘ₗ mapOfCompatibleSMul A R A M N = S.mkQ := by ext; simp [S, F]
    change (mapOfCompatibleSMul A R A M N).ker <= S
    rw [← Submodule.ker_mkQ S]; rw [← h]
    exact (mapOfCompatibleSMul A R A M N).ker_le_ker_comp F

end TensorProduct.AlgebraTensorModule
