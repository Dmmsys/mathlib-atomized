/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro
-/
module

public import Mathlib.Algebra.Algebra.Hom
public import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# Associators and unitors for tensor products of modules over a commutative ring.

-/

@[expose] public section

variable {R : Type*} [CommSemiring R]
variable {R' : Type*} [Monoid R']
variable {R'' : Type*} [Semiring R'']
variable {A M N P Q S T : Type*}
variable [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [AddCommMonoid Q] [AddCommMonoid S] [AddCommMonoid T]
variable [Module R M] [Module R N] [Module R Q] [Module R S] [Module R T]
variable [DistribMulAction R' M]
variable [Module R'' M]
variable (M N)

namespace TensorProduct

variable [Module R P]

variable {M N}

section

variable (R M)

/--
Definition of `lid` / `lid` 的定义

English:
definition lid
  signature: : R otimes[R] M ≃ₗ[R] M
  body: LinearEquiv.ofLinearMap
    (lift <| LinearMap.lsmul R M)
    (mk R R M 1)
    (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

中文:
定义 lid
  签名: : R otimes[R] M ≃ₗ[R] M
  定义体: LinearEquiv.ofLinearMap
    (lift <| LinearMap.lsmul R M)
    (mk R R M 1)
    (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])
-/
protected def lid : R otimes[R] M ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (lift <| LinearMap.lsmul R M)
    (mk R R M 1)
    (LinearMap.ext fun _ => by simp)
    (ext' fun r m => by simp [← tmul_smul, ← smul_tmul, smul_eq_mul, mul_one])

end

@[simp]
/--
theorem `lid_tmul` / 定理 `lid_tmul`

English:
theorem lid_tmul
  given: (m : M) (r : R)
  statement: (TensorProduct.lid R M : R otimes M -> M) (r otimesₜ m) = r • m
  proof: rfl

@[simp]

中文:
定理 lid_tmul
  条件: (m : M) (r : R)
  结论: (TensorProduct.lid R M : R otimes M -> M) (r otimesₜ m) = r • m
  证明: rfl

@[simp]
-/
theorem lid_tmul (m : M) (r : R) : (TensorProduct.lid R M : R otimes M -> M) (r otimesₜ m) = r • m :=
  rfl

@[simp]
/--
theorem `lid_symm_apply` / 定理 `lid_symm_apply`

English:
theorem lid_symm_apply
  given: (m : M)
  statement: (TensorProduct.lid R M).symm m = 1 otimesₜ m
  proof: rfl

中文:
定理 lid_symm_apply
  条件: (m : M)
  结论: (TensorProduct.lid R M).symm m = 1 otimesₜ m
  证明: rfl
-/
theorem lid_symm_apply (m : M) : (TensorProduct.lid R M).symm m = 1 otimesₜ m :=
  rfl

/--
theorem `toLinearMap_symm_lid` / 定理 `toLinearMap_symm_lid`

English:
theorem toLinearMap_symm_lid
  statement: (TensorProduct.lid R M).symm.toLinearMap = mk R R M 1
  proof: rfl

中文:
定理 toLinearMap_symm_lid
  结论: (TensorProduct.lid R M).symm.toLinearMap = mk R R M 1
  证明: rfl
-/
theorem toLinearMap_symm_lid : (TensorProduct.lid R M).symm.toLinearMap = mk R R M 1 := rfl

/--
lemma `includeRight_lid` / 引理 `includeRight_lid`

English:
lemma includeRight_lid
  given: {S : Type*} [Semiring S] [Algebra R S] (m : R otimes[R] M)
  proof: by
  suffices forall m, (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 otimesₜ[R] m by
    simp [← this]
  intros; simp

中文:
引理 includeRight_lid
  条件: {S : 类型} [Semiring S] [Algebra R S] (m : R otimes[R] M)
  证明: by
  suffices forall m, (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 otimesₜ[R] m by
    simp [← this]
  intros; simp

Depends on / 依赖: Algebra, Algebra.algHom, LinearMap, LinearMap.rTensor, TensorProduct, TensorProduct.lid, algHom, intros, rTensor, symm.toLinearMap, toLinearMap
-/
lemma includeRight_lid {S : Type*} [Semiring S] [Algebra R S] (m : R otimes[R] M) :
    (1 : S) otimesₜ[R] (TensorProduct.lid R M) m =
      (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap) m := by
  suffices forall m, (LinearMap.rTensor M (Algebra.algHom R R S).toLinearMap).comp
    (TensorProduct.lid R M).symm.toLinearMap m = 1 otimesₜ[R] m by
    simp [← this]
  intros; simp

section

variable (R M)

/--
Definition of `rid` / `rid` 的定义

English:
definition rid
  signature: : M otimes[R] R ≃ₗ[R] M
  body: LinearEquiv.ofLinearMap
    (lift <| .flip (LinearMap.lsmul R M))
    (mk R M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext <| by ext; simp)

中文:
定义 rid
  签名: : M otimes[R] R ≃ₗ[R] M
  定义体: LinearEquiv.ofLinearMap
    (lift <| .flip (LinearMap.lsmul R M))
    (mk R M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext <| by ext; simp)
-/
protected def rid : M otimes[R] R ≃ₗ[R] M :=
  LinearEquiv.ofLinearMap
    (lift <| .flip (LinearMap.lsmul R M))
    (mk R M R |>.flip 1)
    (LinearMap.ext <| one_smul _)
    (ext <| by ext; simp)

end

@[simp]
/--
theorem `rid_tmul` / 定理 `rid_tmul`

English:
theorem rid_tmul
  given: (m : M) (r : R)
  statement: (TensorProduct.rid R M) (m otimesₜ r) = r • m
  proof: rfl

@[simp]

中文:
定理 rid_tmul
  条件: (m : M) (r : R)
  结论: (TensorProduct.rid R M) (m otimesₜ r) = r • m
  证明: rfl

@[simp]
-/
theorem rid_tmul (m : M) (r : R) : (TensorProduct.rid R M) (m otimesₜ r) = r • m :=
  rfl

@[simp]
/--
theorem `rid_symm_apply` / 定理 `rid_symm_apply`

English:
theorem rid_symm_apply
  given: (m : M)
  statement: (TensorProduct.rid R M).symm m = m otimesₜ 1
  proof: rfl

中文:
定理 rid_symm_apply
  条件: (m : M)
  结论: (TensorProduct.rid R M).symm m = m otimesₜ 1
  证明: rfl
-/
theorem rid_symm_apply (m : M) : (TensorProduct.rid R M).symm m = m otimesₜ 1 :=
  rfl

/--
theorem `toLinearMap_symm_rid` / 定理 `toLinearMap_symm_rid`

English:
theorem toLinearMap_symm_rid
  statement: (TensorProduct.rid R M).symm.toLinearMap = (mk R M R).flip 1
  proof: rfl

@[simp]

中文:
定理 toLinearMap_symm_rid
  结论: (TensorProduct.rid R M).symm.toLinearMap = (mk R M R).flip 1
  证明: rfl

@[simp]
-/
theorem toLinearMap_symm_rid : (TensorProduct.rid R M).symm.toLinearMap = (mk R M R).flip 1 := rfl

@[simp]
/--
theorem `comm_trans_lid` / 定理 `comm_trans_lid`

English:
theorem comm_trans_lid
  proof: LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

中文:
定理 comm_trans_lid
  证明: LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, toLinearMap_injective
-/
theorem comm_trans_lid :
    TensorProduct.comm R M R ≪≫ₗ TensorProduct.lid R M = TensorProduct.rid R M :=
  LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

/--
lemma `lid_comm` / 引理 `lid_comm`

English:
lemma lid_comm
  given: (x)
  proof: congr($comm_trans_lid _)

@[simp]

中文:
引理 lid_comm
  条件: (x)
  证明: congr($comm_trans_lid _)

@[simp]
-/
@[simp] lemma lid_comm (x) :
    TensorProduct.lid R M (TensorProduct.comm R M R x) = TensorProduct.rid R M x :=
  congr($comm_trans_lid _)

@[simp]
/--
theorem `comm_trans_rid` / 定理 `comm_trans_rid`

English:
theorem comm_trans_rid
  proof: LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

中文:
定理 comm_trans_rid
  证明: LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, toLinearMap_injective
-/
theorem comm_trans_rid :
    TensorProduct.comm R R M ≪≫ₗ TensorProduct.rid R M = TensorProduct.lid R M :=
  LinearEquiv.toLinearMap_injective (ext (by ext; rfl))

/--
lemma `rid_comm` / 引理 `rid_comm`

English:
lemma rid_comm
  given: (x)
  proof: congr($comm_trans_rid _)

中文:
引理 rid_comm
  条件: (x)
  证明: congr($comm_trans_rid _)
-/
@[simp] lemma rid_comm (x) :
    TensorProduct.rid R M (TensorProduct.comm R R M x) = TensorProduct.lid R M x :=
  congr($comm_trans_rid _)

variable (R) in
/--
theorem `lid_eq_rid` / 定理 `lid_eq_rid`

English:
theorem lid_eq_rid
  statement: TensorProduct.lid R R = TensorProduct.rid R R
  proof: LinearEquiv.toLinearMap_injective ext' mul_comm

中文:
定理 lid_eq_rid
  结论: TensorProduct.lid R R = TensorProduct.rid R R
  证明: LinearEquiv.toLinearMap_injective ext' mul_comm

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, mul_comm, toLinearMap_injective
-/
theorem lid_eq_rid : TensorProduct.lid R R = TensorProduct.rid R R :=
LinearEquiv.toLinearMap_injective ext' mul_comm

section CompatibleSMul

variable (R A M N) [CommSemiring A] [Module A M] [Module A N]
  [CompatibleSMul R A M N] [Module R A] [SMulCommClass R A A] [CompatibleSMul R A A M]
  [CompatibleSMul A R A M]

/--
Definition of `lidOfCompatibleSMul` / `lidOfCompatibleSMul` 的定义

English:
definition lidOfCompatibleSMul
  signature: : A otimes[R] M ≃ₗ[A] M
  body: (equivOfCompatibleSMul R A A A M).symm ≪≫ₗ TensorProduct.lid _ _

中文:
定义 lidOfCompatibleSMul
  签名: : A otimes[R] M ≃ₗ[A] M
  定义体: (equivOfCompatibleSMul R A A A M).symm ≪≫ₗ TensorProduct.lid _ _

Depends on / 依赖: TensorProduct, TensorProduct.lid, equivOfCompatibleSMul
-/
def lidOfCompatibleSMul : A otimes[R] M ≃ₗ[A] M :=
  (equivOfCompatibleSMul R A A A M).symm ≪≫ₗ TensorProduct.lid _ _

/--
theorem `lidOfCompatibleSMul_tmul` / 定理 `lidOfCompatibleSMul_tmul`

English:
theorem lidOfCompatibleSMul_tmul
  given: (a m)
  statement: lidOfCompatibleSMul R A M (a otimesₜ[R] m) = a • m
  proof: rfl

中文:
定理 lidOfCompatibleSMul_tmul
  条件: (a m)
  结论: lidOfCompatibleSMul R A M (a otimesₜ[R] m) = a • m
  证明: rfl
-/
theorem lidOfCompatibleSMul_tmul (a m) : lidOfCompatibleSMul R A M (a otimesₜ[R] m) = a • m := rfl

variable {R} in
/--
lemma `CompatibleSMul.of_algebraMap_surjective` / 引理 `CompatibleSMul.of_algebraMap_surjective`

English:
lemma CompatibleSMul.of_algebraMap_surjective
  statement: {A : Type*} [CommSemiring A] [Algebra R A]
  proof: by
    obtain ⟨r, rfl⟩ := h a
    simp [smul_tmul]

中文:
引理 CompatibleSMul.of_algebraMap_surjective
  结论: {A : 类型} [CommSemiring A] [Algebra R A]
  证明: by
    obtain ⟨r, rfl⟩ := h a
    simp [smul_tmul]

Depends on / 依赖: smul_tmul
-/
lemma CompatibleSMul.of_algebraMap_surjective {A : Type*} [CommSemiring A] [Algebra R A]
    [Module A M] [IsScalarTower R A M] [Module A N] [IsScalarTower R A N]
    (h : Function.Surjective (algebraMap R A)) :
    CompatibleSMul R A M N where
  smul_tmul a m n := by
    obtain ⟨r, rfl⟩ := h a
    simp [smul_tmul]

end CompatibleSMul

open LinearMap

section

variable (R M N P)

attribute [local ext high] ext in
/--
Definition of `assoc` / `assoc` 的定义

English:
definition assoc
  signature: : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] (N otimes[R] P)
  body: LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry _ _ _ _ ∘ₗ mk _ _ _)
    (lift <| uncurry _ _ _ _ ∘ₗ curry (mk R _ _))
    (by ext; rfl)
    (by ext; rfl)

中文:
定义 assoc
  签名: : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] (N otimes[R] P)
  定义体: LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry _ _ _ _ ∘ₗ mk _ _ _)
    (lift <| uncurry _ _ _ _ ∘ₗ curry (mk R _ _))
    (by ext; rfl)
    (by ext; rfl)
-/
protected def assoc : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] (N otimes[R] P) :=
  LinearEquiv.ofLinearMap
    (lift <| lift <| lcurry _ _ _ _ ∘ₗ mk _ _ _)
    (lift <| uncurry _ _ _ _ ∘ₗ curry (mk R _ _))
    (by ext; rfl)
    (by ext; rfl)

end

@[simp]
/--
theorem `assoc_tmul` / 定理 `assoc_tmul`

English:
theorem assoc_tmul
  given: (m : M) (n : N) (p : P)
  proof: rfl

@[simp]

中文:
定理 assoc_tmul
  条件: (m : M) (n : N) (p : P)
  证明: rfl

@[simp]
-/
theorem assoc_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P) (m otimesₜ n otimesₜ p) = m otimesₜ (n otimesₜ p) :=
  rfl

@[simp]
/--
theorem `assoc_symm_tmul` / 定理 `assoc_symm_tmul`

English:
theorem assoc_symm_tmul
  given: (m : M) (n : N) (p : P)
  proof: rfl

中文:
定理 assoc_symm_tmul
  条件: (m : M) (n : N) (p : P)
  证明: rfl
-/
theorem assoc_symm_tmul (m : M) (n : N) (p : P) :
    (TensorProduct.assoc R M N P).symm (m otimesₜ (n otimesₜ p)) = m otimesₜ n otimesₜ p :=
  rfl

/--
lemma `map_map_comp_assoc_eq` / 引理 `map_map_comp_assoc_eq`

English:
lemma map_map_comp_assoc_eq
  given: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T)
  proof: ext ext LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

中文:
引理 map_map_comp_assoc_eq
  条件: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T)
  证明: ext ext LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

Depends on / 依赖: LinearMap, LinearMap.ext
-/
lemma map_map_comp_assoc_eq (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) :
    map f (map g h) ∘ₗ TensorProduct.assoc R M N P =
      TensorProduct.assoc R Q S T ∘ₗ map (map f g) h :=
ext ext LinearMap.ext fun _ => LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/--
lemma `map_map_assoc` / 引理 `map_map_assoc`

English:
lemma map_map_assoc
  given: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M otimes[R] N otimes[R] P)
  proof: DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _

中文:
引理 map_map_assoc
  条件: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M otimes[R] N otimes[R] P)
  证明: DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_map_comp_assoc_eq
-/
lemma map_map_assoc (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M otimes[R] N otimes[R] P) :
    map f (map g h) (TensorProduct.assoc R M N P x) =
      TensorProduct.assoc R Q S T (map (map f g) h x) :=
  DFunLike.congr_fun (map_map_comp_assoc_eq _ _ _) _

/--
lemma `map_map_comp_assoc_symm_eq` / 引理 `map_map_comp_assoc_symm_eq`

English:
lemma map_map_comp_assoc_symm_eq
  given: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T)
  proof: ext LinearMap.ext fun _ => ext LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

中文:
引理 map_map_comp_assoc_symm_eq
  条件: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T)
  证明: ext LinearMap.ext fun _ => ext LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

Depends on / 依赖: LinearMap, LinearMap.ext
-/
lemma map_map_comp_assoc_symm_eq (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) :
    map (map f g) h ∘ₗ (TensorProduct.assoc R M N P).symm =
      (TensorProduct.assoc R Q S T).symm ∘ₗ map f (map g h) :=
ext LinearMap.ext fun _ => ext LinearMap.ext fun _ => LinearMap.ext fun _ => rfl

/--
lemma `map_map_assoc_symm` / 引理 `map_map_assoc_symm`

English:
lemma map_map_assoc_symm
  given: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M otimes[R] (N otimes[R] P))
  proof: DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _

中文:
引理 map_map_assoc_symm
  条件: (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M otimes[R] (N otimes[R] P))
  证明: DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _

Depends on / 依赖: DFunLike, DFunLike.congr_fun, congr_fun, map_map_comp_assoc_symm_eq
-/
lemma map_map_assoc_symm (f : M ->ₗ[R] Q) (g : N ->ₗ[R] S) (h : P ->ₗ[R] T) (x : M otimes[R] (N otimes[R] P)) :
    map (map f g) h ((TensorProduct.assoc R M N P).symm x) =
      (TensorProduct.assoc R Q S T).symm (map f (map g h) x) :=
  DFunLike.congr_fun (map_map_comp_assoc_symm_eq _ _ _) _

/--
lemma `assoc_tensor` / 引理 `assoc_tensor`

English:
lemma assoc_tensor
  proof: LinearEquiv.toLinearMap_inj.mp ext_fourfold fun _ _ _ => congrFun rfl

中文:
引理 assoc_tensor
  证明: LinearEquiv.toLinearMap_inj.mp ext_fourfold fun _ _ _ => congrFun rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, ext_fourfold, toLinearMap_inj
-/
lemma assoc_tensor :
    TensorProduct.assoc R (M otimes[R] N) Q S = .rTensor S (TensorProduct.assoc R M N Q) ≪≫ₗ
      TensorProduct.assoc R M (N otimes[R] Q) S ≪≫ₗ .lTensor M (TensorProduct.assoc R N Q S) ≪≫ₗ
      (TensorProduct.assoc R M N (Q otimes[R] S)).symm :=
LinearEquiv.toLinearMap_inj.mp ext_fourfold fun _ _ _ => congrFun rfl

/--
lemma `assoc_tensor'` / 引理 `assoc_tensor'`

English:
lemma assoc_tensor'
  proof: LinearEquiv.toLinearMap_inj.mp ext_fourfold'' fun _ _ _ => congrFun rfl

中文:
引理 assoc_tensor'
  证明: LinearEquiv.toLinearMap_inj.mp ext_fourfold'' fun _ _ _ => congrFun rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, ext_fourfold, toLinearMap_inj
-/
lemma assoc_tensor' :
    TensorProduct.assoc R M (N otimes[R] Q) S = .rTensor S (TensorProduct.assoc R M N Q).symm ≪≫ₗ
      (TensorProduct.assoc R (M otimes[R] N) Q S) ≪≫ₗ TensorProduct.assoc R M N (Q otimes[R] S) ≪≫ₗ
      .lTensor M (TensorProduct.assoc R N Q S).symm :=
LinearEquiv.toLinearMap_inj.mp ext_fourfold'' fun _ _ _ => congrFun rfl

/--
lemma `assoc_tensor''` / 引理 `assoc_tensor''`

English:
lemma assoc_tensor''
  proof: LinearEquiv.toLinearMap_inj.mp ext_fourfold' fun _ _ _ => congrFun rfl

中文:
引理 assoc_tensor''
  证明: LinearEquiv.toLinearMap_inj.mp ext_fourfold' fun _ _ _ => congrFun rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, ext_fourfold, toLinearMap_inj
-/
lemma assoc_tensor'' :
    TensorProduct.assoc R M N (Q otimes[R] S) = (TensorProduct.assoc R (M otimes[R] N) Q S).symm ≪≫ₗ
      .rTensor S (TensorProduct.assoc R M N Q) ≪≫ₗ TensorProduct.assoc R M (N otimes[R] Q) S ≪≫ₗ
      .lTensor M (TensorProduct.assoc R N Q S) :=
LinearEquiv.toLinearMap_inj.mp ext_fourfold' fun _ _ _ => congrFun rfl

/--
lemma `lid_tensor` / 引理 `lid_tensor`

English:
lemma lid_tensor
  proof: LinearEquiv.toLinearMap_inj.mp ext_threefold' fun _ _ => congrFun rfl

中文:
引理 lid_tensor
  证明: LinearEquiv.toLinearMap_inj.mp ext_threefold' fun _ _ => congrFun rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_inj.mp, ext_threefold, toLinearMap_inj
-/
lemma lid_tensor :
    TensorProduct.lid R (M otimes[R] N) = (TensorProduct.assoc R R M N).symm ≪≫ₗ
      .rTensor N (TensorProduct.lid R M) :=
LinearEquiv.toLinearMap_inj.mp ext_threefold' fun _ _ => congrFun rfl

section

variable {P' Q' : Type*}
variable [AddCommMonoid P'] [Module R P']
variable [AddCommMonoid Q'] [Module R Q']

variable (R M N P Q)

/--
Definition of `leftComm` / `leftComm` 的定义

English:
definition leftComm
  signature: : M otimes[R] (N otimes[R] P) ≃ₗ[R] N otimes[R] (M otimes[R] P)
  body: let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

中文:
定义 leftComm
  签名: : M otimes[R] (N otimes[R] P) ≃ₗ[R] N otimes[R] (M otimes[R] P)
  定义体: let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

Depends on / 依赖: TensorProduct, TensorProduct.assoc, TensorProduct.comm
-/
def leftComm : M otimes[R] (N otimes[R] P) ≃ₗ[R] N otimes[R] (M otimes[R] P) :=
  let e₁ := (TensorProduct.assoc R M N P).symm
  let e₂ := congr (TensorProduct.comm R M N) (1 : P ≃ₗ[R] P)
  let e₃ := TensorProduct.assoc R N M P
  e₁ ≪≫ₗ (e₂ ≪≫ₗ e₃)

variable {M N P Q}

@[simp]
/--
theorem `leftComm_tmul` / 定理 `leftComm_tmul`

English:
theorem leftComm_tmul
  given: (m : M) (n : N) (p : P)
  statement: leftComm R M N P (m otimesₜ (n otimesₜ p)) = n otimesₜ (m otimesₜ p)
  proof: rfl

@[simp]

中文:
定理 leftComm_tmul
  条件: (m : M) (n : N) (p : P)
  结论: leftComm R M N P (m otimesₜ (n otimesₜ p)) = n otimesₜ (m otimesₜ p)
  证明: rfl

@[simp]
-/
theorem leftComm_tmul (m : M) (n : N) (p : P) : leftComm R M N P (m otimesₜ (n otimesₜ p)) = n otimesₜ (m otimesₜ p) :=
  rfl

@[simp]
/--
theorem `leftComm_symm_tmul` / 定理 `leftComm_symm_tmul`

English:
theorem leftComm_symm_tmul
  given: (m : M) (n : N) (p : P)
  proof: rfl

中文:
定理 leftComm_symm_tmul
  条件: (m : M) (n : N) (p : P)
  证明: rfl
-/
theorem leftComm_symm_tmul (m : M) (n : N) (p : P) :
    (leftComm R M N P).symm (n otimesₜ (m otimesₜ p)) = m otimesₜ (n otimesₜ p) :=
  rfl

attribute [local ext high] TensorProduct.ext in
/--
lemma `leftComm_def` / 引理 `leftComm_def`

English:
lemma leftComm_def
  statement: leftComm R M N P =
  proof: by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

中文:
引理 leftComm_def
  结论: leftComm R M N P =
  证明: by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, toLinearMap_injective
-/
lemma leftComm_def : leftComm R M N P =
    (TensorProduct.assoc R _ _ _).symm ≪≫ₗ congr (TensorProduct.comm _ _ _) (.refl _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _) := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

variable (M N P) in
attribute [local ext high] ext in
/--
Definition of `rightComm` / `rightComm` 的定义

English:
definition rightComm
  signature: : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] P otimes[R] N
  body: LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
  (by ext; rfl) (by ext; rfl)

@[simp]

中文:
定义 rightComm
  签名: : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] P otimes[R] N
  定义体: LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
  (by ext; rfl) (by ext; rfl)

@[simp]

Depends on / 依赖: LinearEquiv, LinearEquiv.ofLinearMap, LinearMap, LinearMap.lflip.toLinearMap, ofLinearMap, toLinearMap
-/
def rightComm : M otimes[R] N otimes[R] P ≃ₗ[R] M otimes[R] P otimes[R] N :=
  LinearEquiv.ofLinearMap
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
    (lift (lift (LinearMap.lflip.toLinearMap ∘ₗ (mk _ _ _).compr₂ (mk _ _ _))))
  (by ext; rfl) (by ext; rfl)

@[simp]
/--
theorem `rightComm_tmul` / 定理 `rightComm_tmul`

English:
theorem rightComm_tmul
  given: (m : M) (n : N) (p : P)
  proof: rfl

@[simp]

中文:
定理 rightComm_tmul
  条件: (m : M) (n : N) (p : P)
  证明: rfl

@[simp]
-/
theorem rightComm_tmul (m : M) (n : N) (p : P) :
    rightComm R M N P ((m otimesₜ n) otimesₜ p) = (m otimesₜ p) otimesₜ n :=
  rfl

@[simp]
/--
theorem `rightComm_symm` / 定理 `rightComm_symm`

English:
theorem rightComm_symm
  statement: (rightComm R M N P).symm = rightComm R M P N
  proof: rfl

中文:
定理 rightComm_symm
  结论: (rightComm R M N P).symm = rightComm R M P N
  证明: rfl
-/
theorem rightComm_symm : (rightComm R M N P).symm = rightComm R M P N := rfl

attribute [local ext high] TensorProduct.ext in
/--
lemma `rightComm_def` / 引理 `rightComm_def`

English:
lemma rightComm_def
  statement: rightComm R M N P =
  proof: by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

中文:
引理 rightComm_def
  结论: rightComm R M N P =
  证明: by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

Depends on / 依赖: LinearEquiv, LinearEquiv.toLinearMap_injective, toLinearMap_injective
-/
lemma rightComm_def : rightComm R M N P =
    TensorProduct.assoc R _ _ _ ≪≫ₗ congr (.refl _ _) (TensorProduct.comm _ _ _) ≪≫ₗ
      (TensorProduct.assoc R _ _ _).symm := by
  apply LinearEquiv.toLinearMap_injective; ext; rfl

variable (M N P Q)

/--
Definition of `tensorTensorTensorComm` / `tensorTensorTensorComm` 的定义

English:
definition tensorTensorTensorComm
  signature: : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M otimes[R] P otimes[R] (N otimes[R] Q)
  body: (TensorProduct.assoc R (M otimes[R] N) P Q).symm
    ≪≫ₗ congr (TensorProduct.rightComm R M N P) (.refl R Q)
    ≪≫ₗ TensorProduct.assoc R (M otimes[R] P) N Q

中文:
定义 tensorTensorTensorComm
  签名: : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M otimes[R] P otimes[R] (N otimes[R] Q)
  定义体: (TensorProduct.assoc R (M otimes[R] N) P Q).symm
    ≪≫ₗ congr (TensorProduct.rightComm R M N P) (.refl R Q)
    ≪≫ₗ TensorProduct.assoc R (M otimes[R] P) N Q

Depends on / 依赖: TensorProduct, TensorProduct.assoc, TensorProduct.rightComm, otimes, rightComm
-/
def tensorTensorTensorComm : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M otimes[R] P otimes[R] (N otimes[R] Q) :=
  (TensorProduct.assoc R (M otimes[R] N) P Q).symm
    ≪≫ₗ congr (TensorProduct.rightComm R M N P) (.refl R Q)
    ≪≫ₗ TensorProduct.assoc R (M otimes[R] P) N Q

variable {M N P Q}

@[simp]
/--
theorem `tensorTensorTensorComm_tmul` / 定理 `tensorTensorTensorComm_tmul`

English:
theorem tensorTensorTensorComm_tmul
  given: (m : M) (n : N) (p : P) (q : Q)
  proof: rfl

@[simp]

中文:
定理 tensorTensorTensorComm_tmul
  条件: (m : M) (n : N) (p : P) (q : Q)
  证明: rfl

@[simp]
-/
theorem tensorTensorTensorComm_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorComm R M N P Q (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ p otimesₜ (n otimesₜ q) :=
  rfl

@[simp]
/--
theorem `tensorTensorTensorComm_symm` / 定理 `tensorTensorTensorComm_symm`

English:
theorem tensorTensorTensorComm_symm
  proof: rfl

中文:
定理 tensorTensorTensorComm_symm
  证明: rfl
-/
theorem tensorTensorTensorComm_symm :
    (tensorTensorTensorComm R M N P Q).symm = tensorTensorTensorComm R M P N Q :=
  rfl

/--
theorem `tensorTensorTensorComm_trans_tensorTensorTensorComm` / 定理 `tensorTensorTensorComm_trans_tensorTensorTensorComm`

English:
theorem tensorTensorTensorComm_trans_tensorTensorTensorComm
  proof: by
  rw [← tensorTensorTensorComm_symm]
  exact LinearEquiv.symm_trans_self _

中文:
定理 tensorTensorTensorComm_trans_tensorTensorTensorComm
  证明: by
  rw [← tensorTensorTensorComm_symm]
  exact LinearEquiv.symm_trans_self _
-/
@[simp] theorem tensorTensorTensorComm_trans_tensorTensorTensorComm :
    tensorTensorTensorComm R M N P Q ≪≫ₗ tensorTensorTensorComm R M P N Q = .refl R _ := by
  rw [← tensorTensorTensorComm_symm]
  exact LinearEquiv.symm_trans_self _

/--
theorem `tensorTensorTensorComm_comp_map` / 定理 `tensorTensorTensorComm_comp_map`

English:
theorem tensorTensorTensorComm_comp_map
  statement: {V W : Type*}
  proof: ext_fourfold' fun _ _ _ _ => rfl

中文:
定理 tensorTensorTensorComm_comp_map
  结论: {V W : 类型}
  证明: ext_fourfold' fun _ _ _ _ => rfl

Depends on / 依赖: ext_fourfold
-/
theorem tensorTensorTensorComm_comp_map {V W : Type*}
    [AddCommMonoid V] [AddCommMonoid W] [Module R V] [Module R W]
    (f : M ->ₗ[R] S) (g : N ->ₗ[R] T) (h : P ->ₗ[R] V) (j : Q ->ₗ[R] W) :
    tensorTensorTensorComm R S T V W ∘ₗ map (map f g) (map h j) =
      map (map f h) (map g j) ∘ₗ tensorTensorTensorComm R M N P Q :=
  ext_fourfold' fun _ _ _ _ => rfl

variable (M N P Q)

/--
Definition of `tensorTensorTensorAssoc` / `tensorTensorTensorAssoc` 的定义

English:
definition tensorTensorTensorAssoc
  signature: : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M otimes[R] (N otimes[R] P) otimes[R] Q
  body: (TensorProduct.assoc R (M otimes[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)

中文:
定义 tensorTensorTensorAssoc
  签名: : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M otimes[R] (N otimes[R] P) otimes[R] Q
  定义体: (TensorProduct.assoc R (M otimes[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)

Depends on / 依赖: TensorProduct, TensorProduct.assoc, otimes
-/
def tensorTensorTensorAssoc : M otimes[R] N otimes[R] (P otimes[R] Q) ≃ₗ[R] M otimes[R] (N otimes[R] P) otimes[R] Q :=
  (TensorProduct.assoc R (M otimes[R] N) P Q).symm ≪≫ₗ
    congr (TensorProduct.assoc R M N P) (1 : Q ≃ₗ[R] Q)

variable {M N P Q}

@[simp]
/--
theorem `tensorTensorTensorAssoc_tmul` / 定理 `tensorTensorTensorAssoc_tmul`

English:
theorem tensorTensorTensorAssoc_tmul
  given: (m : M) (n : N) (p : P) (q : Q)
  proof: rfl

@[simp]

中文:
定理 tensorTensorTensorAssoc_tmul
  条件: (m : M) (n : N) (p : P) (q : Q)
  证明: rfl

@[simp]
-/
theorem tensorTensorTensorAssoc_tmul (m : M) (n : N) (p : P) (q : Q) :
    tensorTensorTensorAssoc R M N P Q (m otimesₜ n otimesₜ (p otimesₜ q)) = m otimesₜ (n otimesₜ p) otimesₜ q :=
  rfl

@[simp]
/--
theorem `tensorTensorTensorAssoc_symm_tmul` / 定理 `tensorTensorTensorAssoc_symm_tmul`

English:
theorem tensorTensorTensorAssoc_symm_tmul
  given: (m : M) (n : N) (p : P) (q : Q)
  proof: rfl

中文:
定理 tensorTensorTensorAssoc_symm_tmul
  条件: (m : M) (n : N) (p : P) (q : Q)
  证明: rfl
-/
theorem tensorTensorTensorAssoc_symm_tmul (m : M) (n : N) (p : P) (q : Q) :
    (tensorTensorTensorAssoc R M N P Q).symm (m otimesₜ (n otimesₜ p) otimesₜ q) = m otimesₜ n otimesₜ (p otimesₜ q) :=
  rfl

end

end TensorProduct

open scoped TensorProduct

variable [Module R P]

namespace LinearMap

variable {N}

variable (g : P ->ₗ[R] Q) (f : N ->ₗ[R] P)

open TensorProduct (assoc lid rid)

/--
lemma `lTensor_tensor` / 引理 `lTensor_tensor`

English:
lemma lTensor_tensor
  given: (f : P ->ₗ[R] Q)
  proof: TensorProduct.ext TensorProduct.ext rfl

中文:
引理 lTensor_tensor
  条件: (f : P ->ₗ[R] Q)
  证明: TensorProduct.ext TensorProduct.ext rfl

Depends on / 依赖: TensorProduct, TensorProduct.ext
-/
lemma lTensor_tensor (f : P ->ₗ[R] Q) :
    lTensor (M otimes[R] N) f = (assoc R M N Q).symm ∘ₗ (f.lTensor N).lTensor M ∘ₗ assoc R M N P :=
TensorProduct.ext TensorProduct.ext rfl

/--
theorem `rTensor_tensor` / 定理 `rTensor_tensor`

English:
theorem rTensor_tensor
  statement: rTensor (M otimes[R] N) g =
  proof: TensorProduct.ext LinearMap.ext fun _ => TensorProduct.ext rfl

中文:
定理 rTensor_tensor
  结论: rTensor (M otimes[R] N) g =
  证明: TensorProduct.ext LinearMap.ext fun _ => TensorProduct.ext rfl

Depends on / 依赖: LinearMap, LinearMap.ext, TensorProduct, TensorProduct.ext
-/
theorem rTensor_tensor : rTensor (M otimes[R] N) g =
    assoc R Q M N ∘ₗ rTensor N (rTensor M g) ∘ₗ (assoc R P M N).symm :=
TensorProduct.ext LinearMap.ext fun _ => TensorProduct.ext rfl

open TensorProduct

/--
theorem `lid_comp_rTensor` / 定理 `lid_comp_rTensor`

English:
theorem lid_comp_rTensor
  given: (f : N ->ₗ[R] R)
  proof: ext' fun _ _ => rfl

中文:
定理 lid_comp_rTensor
  条件: (f : N ->ₗ[R] R)
  证明: ext' fun _ _ => rfl
-/
theorem lid_comp_rTensor (f : N ->ₗ[R] R) :
    (lid R M).comp (rTensor M f) = lift ((lsmul R M).comp f) := ext' fun _ _ => rfl

/--
lemma `rid_comp_lTensor` / 引理 `rid_comp_lTensor`

English:
lemma rid_comp_lTensor
  given: (f : M ->ₗ[R] R)
  proof: ext' fun _ _ => rfl

中文:
引理 rid_comp_lTensor
  条件: (f : M ->ₗ[R] R)
  证明: ext' fun _ _ => rfl
-/
lemma rid_comp_lTensor (f : M ->ₗ[R] R) :
    (rid R N).comp (lTensor N f) = lift ((lsmul R N).flip.compl₂ f) := ext' fun _ _ => rfl

/--
lemma `lTensor_rTensor_comp_assoc` / 引理 `lTensor_rTensor_comp_assoc`

English:
lemma lTensor_rTensor_comp_assoc
  given: (x : M ->ₗ[R] N)
  proof: by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_eq]

中文:
引理 lTensor_rTensor_comp_assoc
  条件: (x : M ->ₗ[R] N)
  证明: by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_eq]

Depends on / 依赖: lTensor, map_map_comp_assoc_eq, rTensor, simp_rw
-/
lemma lTensor_rTensor_comp_assoc (x : M ->ₗ[R] N) :
    lTensor P (rTensor Q x) ∘ₗ TensorProduct.assoc R P M Q
    = TensorProduct.assoc R P N Q ∘ₗ rTensor Q (lTensor P x) := by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_eq]

/--
lemma `rTensor_lTensor_comp_assoc_symm` / 引理 `rTensor_lTensor_comp_assoc_symm`

English:
lemma rTensor_lTensor_comp_assoc_symm
  given: (x : M ->ₗ[R] N)
  proof: by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]

中文:
引理 rTensor_lTensor_comp_assoc_symm
  条件: (x : M ->ₗ[R] N)
  证明: by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]

Depends on / 依赖: lTensor, map_map_comp_assoc_symm_eq, rTensor, simp_rw
-/
lemma rTensor_lTensor_comp_assoc_symm (x : M ->ₗ[R] N) :
    rTensor Q (lTensor P x) ∘ₗ (TensorProduct.assoc R P M Q).symm
    = (TensorProduct.assoc R P N Q).symm ∘ₗ lTensor P (rTensor Q x) := by
  simp_rw [rTensor, lTensor, map_map_comp_assoc_symm_eq]

end LinearMap

namespace Equiv
variable {R A A' B B' C C' : Type*}
variable [CommSemiring R] [AddCommMonoid A'] [AddCommMonoid B'] [AddCommMonoid C']
variable [Module R A'] [Module R B'] [Module R C']

variable (R) in
open TensorProduct in
/--
lemma `tensorProductAssoc_def` / 引理 `tensorProductAssoc_def`

English:
lemma tensorProductAssoc_def
  given: (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C')
  proof: eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eC.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    letI := eC.module R
    TensorProduct.assoc R A B C = .trans
      (congr (congr (eA.linearEquiv R) (eB.linearEquiv R)) (eC.linearEquiv R)) (.trans
(TensorProduct.assoc R A'

中文:
引理 tensorProductAssoc_def
  条件: (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C')
  证明: eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eC.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    letI := eC.module R
    TensorProduct.assoc R A B C = .trans
      (congr (congr (eA.linearEquiv R) (eB.linearEquiv R)) (eC.linearEquiv R)) (.trans
(TensorProduct.assoc R A'

Depends on / 依赖: addCommMonoid, eA.addCommMonoid
-/
lemma tensorProductAssoc_def (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C') :
    letI := eA.addCommMonoid
    letI := eB.addCommMonoid
    letI := eC.addCommMonoid
    letI := eA.module R
    letI := eB.module R
    letI := eC.module R
    TensorProduct.assoc R A B C = .trans
      (congr (congr (eA.linearEquiv R) (eB.linearEquiv R)) (eC.linearEquiv R)) (.trans
(TensorProduct.assoc R A' B' C') congr (eA.linearEquiv R).symm
        congr (eB.linearEquiv R).symm (eC.linearEquiv R).symm) := by
  ext x
  induction x with
  | zero => simp
  | add => simp [*]
  | tmul x a => induction x <;> simp [*, add_tmul]

end Equiv
