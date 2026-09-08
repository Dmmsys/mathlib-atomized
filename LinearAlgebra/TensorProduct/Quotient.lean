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
Let `M, N` be `R`-modules, `m ≤ M` and `n ≤ N` be an `R`-submodules. Then we have a linear
isomorphism between tensor products of the quotients and the quotient of the tensor product:
`(M ⧸ m) ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N ⊔ M ⊗ n)`.
-/
/-
**TensorProduct.quotientTensorQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TensorPro
duct`。
形式化陈述：quotientTensorQuotientEquiv (m : Submodule R M) (n : Submodule R N) : (M ⧸
 (m : Submodule R M)) otimes[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R] (M otimes[R] N) 
⧸ (LinearMap.range (map m.subtype LinearMap.id) ⊔ LinearMap.range (map LinearMap
.id n.subtype))
参数：m : Submodule R M；n : Submodule R N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M, N` be `R`-modules, `m ≤ M` and `n ≤ N` be an `R`-submodules. Then we hav
e a linear
isomorphism between tensor products of the quotients and the quotient of the ten
sor product:
`(M ⧸ m) ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N ⊔ M ⊗ n)`.
-/
noncomputable def quotientTensorQuotientEquiv (m : Submodule R M) (n : Submodule R N) :
    (M ⧸ (m : Submodule R M)) ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸
      (LinearMap.range (map m.subtype LinearMap.id) ⊔
        LinearMap.range (map LinearMap.id n.subtype)) :=
  LinearEquiv.ofLinearMap
    (lift <| Submodule.liftQ _ (LinearMap.flip <| Submodule.liftQ _
      ((mk R (M := M) (N := N)).flip.compr₂ (Submodule.mkQ _)) fun x hx => by
      ext y
      simp only [LinearMap.compr₂_apply, LinearMap.flip_apply, mk_apply, Submodule.mkQ_apply,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_right ⟨y ⊗ₜ ⟨x, hx⟩, rfl⟩) fun x hx => by
      ext y
      simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, LinearMap.flip_apply,
        Submodule.liftQ_apply, LinearMap.compr₂_apply, mk_apply, LinearMap.zero_comp,
        LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.mem_sup_left ⟨⟨x, hx⟩ ⊗ₜ y, rfl⟩)
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
/-
**TensorProduct.quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk** 是 Mathlib 中的
一个引理，位于命名空间 `TensorProduct`。
形式化陈述：quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk (m : Submodule R M) (n :
 Submodule R N) (x : M) (y : N) : quotientTensorQuotientEquiv m n (Submodule.Quo
tient.mk x otimesₜ[R] Submodule.Quotient.mk y) = Submodule.Quotient.mk (x otimes
ₜ y)
参数：m : Submodule R M；n : Submodule R N；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientTensorQuotientEquiv_apply_tmul_mk_tmul_mk
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    quotientTensorQuotientEquiv m n
      (Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ y) := rfl

@[simp]
/-
**TensorProduct.quotientTensorQuotientEquiv_symm_apply_mk_tmul** 是 Mathlib 中的一个引
理，位于命名空间 `TensorProduct`。
形式化陈述：quotientTensorQuotientEquiv_symm_apply_mk_tmul (m : Submodule R M) (n : Su
bmodule R N) (x : M) (y : N) : (quotientTensorQuotientEquiv m n).symm (Submodule
.Quotient.mk (x otimesₜ y)) = Submodule.Quotient.mk x otimesₜ[R] Submodule.Quoti
ent.mk y
参数：m : Submodule R M；n : Submodule R N；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientTensorQuotientEquiv_symm_apply_mk_tmul
    (m : Submodule R M) (n : Submodule R N) (x : M) (y : N) :
    (quotientTensorQuotientEquiv m n).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
      Submodule.Quotient.mk x ⊗ₜ[R] Submodule.Quotient.mk y := rfl

variable (N) in
/--
Let `M, N` be `R`-modules, `m ≤ M` be an `R`-submodule. Then we have a linear isomorphism between
tensor products of the quotient and the quotient of the tensor product:
`(M ⧸ m) ⊗[R] N ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N)`.
-/
/-
**TensorProduct.quotientTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：quotientTensorEquiv (m : Submodule R M) : (M ⧸ (m : Submodule R M)) otimes
[R] N ≃ₗ[R] (M otimes[R] N) ⧸ (LinearMap.range (map m.subtype (LinearMap.id : N 
->ₗ[R] N)))
参数：m : Submodule R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M, N` be `R`-modules, `m ≤ M` be an `R`-submodule. Then we have a linear is
omorphism between
tensor products of the quotient and the quotient of the tensor product:
`(M ⧸ m) ⊗[R] N ≃ₗ[R] (M ⊗[R] N) ⧸ (m ⊗ N)`.
-/
noncomputable def quotientTensorEquiv (m : Submodule R M) :
    (M ⧸ (m : Submodule R M)) ⊗[R] N ≃ₗ[R]
    (M ⊗[R] N) ⧸ (LinearMap.range (map m.subtype (LinearMap.id : N →ₗ[R] N))) :=
  congr (LinearEquiv.refl _ _) ((Submodule.quotEquivOfEqBot _ rfl).symm) ≪≫ₗ
  quotientTensorQuotientEquiv (N := N) m ⊥ ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by
    simp [Submodule.map_span, range_map_eq_span_tmul])

@[simp]
/-
**TensorProduct.quotientTensorEquiv_apply_tmul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Ten
sorProduct`。
形式化陈述：quotientTensorEquiv_apply_tmul_mk (m : Submodule R M) (x : M) (y : N) : qu
otientTensorEquiv N m (Submodule.Quotient.mk x otimesₜ[R] y) = Submodule.Quotien
t.mk (x otimesₜ y)
参数：m : Submodule R M；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientTensorEquiv_apply_tmul_mk (m : Submodule R M) (x : M) (y : N) :
    quotientTensorEquiv N m (Submodule.Quotient.mk x ⊗ₜ[R] y) =
    Submodule.Quotient.mk (x ⊗ₜ y) :=
  rfl

@[simp]
/-
**TensorProduct.quotientTensorEquiv_symm_apply_mk_tmul** 是 Mathlib 中的一个引理，位于命名空间
 `TensorProduct`。
形式化陈述：quotientTensorEquiv_symm_apply_mk_tmul (m : Submodule R M) (x : M) (y : N)
 : (quotientTensorEquiv N m).symm (Submodule.Quotient.mk (x otimesₜ y)) = Submod
ule.Quotient.mk x otimesₜ[R] y
参数：m : Submodule R M；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotientTensorEquiv_symm_apply_mk_tmul (m : Submodule R M) (x : M) (y : N) :
    (quotientTensorEquiv N m).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
    Submodule.Quotient.mk x ⊗ₜ[R] y :=
  rfl

variable (M) in
/--
Let `M, N` be `R`-modules, `n ≤ N` be an `R`-submodule. Then we have a linear isomorphism between
tensor products of the quotient and the quotient of the tensor product:
`M ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (M ⊗ n)`.
-/
/-
**TensorProduct.tensorQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct`。
形式化陈述：tensorQuotientEquiv (n : Submodule R N) : M otimes[R] (N ⧸ (n : Submodule 
R N)) ≃ₗ[R] (M otimes[R] N) ⧸ (LinearMap.range (map (LinearMap.id : M ->ₗ[R] M) 
n.subtype))
参数：n : Submodule R N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M, N` be `R`-modules, `n ≤ N` be an `R`-submodule. Then we have a linear is
omorphism between
tensor products of the quotient and the quotient of the tensor product:
`M ⊗[R] (N ⧸ n) ≃ₗ[R] (M ⊗[R] N) ⧸ (M ⊗ n)`.
-/
noncomputable def tensorQuotientEquiv (n : Submodule R N) :
    M ⊗[R] (N ⧸ (n : Submodule R N)) ≃ₗ[R]
    (M ⊗[R] N) ⧸ (LinearMap.range (map (LinearMap.id : M →ₗ[R] M) n.subtype)) :=
  congr ((Submodule.quotEquivOfEqBot _ rfl).symm) (LinearEquiv.refl _ _) ≪≫ₗ
  quotientTensorQuotientEquiv (⊥ : Submodule R M) n ≪≫ₗ
  Submodule.Quotient.equiv _ _ (LinearEquiv.refl _ _) (by simp [range_map_eq_span_tmul])

@[simp]
/-
**TensorProduct.tensorQuotientEquiv_apply_mk_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Ten
sorProduct`。
形式化陈述：tensorQuotientEquiv_apply_mk_tmul (n : Submodule R N) (x : M) (y : N) : te
nsorQuotientEquiv M n (x otimesₜ[R] Submodule.Quotient.mk y) = Submodule.Quotien
t.mk (x otimesₜ y)
参数：n : Submodule R N；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorQuotientEquiv_apply_mk_tmul (n : Submodule R N) (x : M) (y : N) :
    tensorQuotientEquiv M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
    Submodule.Quotient.mk (x ⊗ₜ y) :=
  rfl

@[simp]
/-
**TensorProduct.tensorQuotientEquiv_symm_apply_tmul_mk** 是 Mathlib 中的一个引理，位于命名空间
 `TensorProduct`。
形式化陈述：tensorQuotientEquiv_symm_apply_tmul_mk (n : Submodule R N) (x : M) (y : N)
 : (tensorQuotientEquiv M n).symm (Submodule.Quotient.mk (x otimesₜ y)) = x otim
esₜ[R] Submodule.Quotient.mk y
参数：n : Submodule R N；x : M；y : N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorQuotientEquiv_symm_apply_tmul_mk (n : Submodule R N) (x : M) (y : N) :
    (tensorQuotientEquiv M n).symm (Submodule.Quotient.mk (x ⊗ₜ y)) =
    x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl

variable (M) in
/-- Left tensoring a module with a quotient of the ring is the same as
quotienting that module by the corresponding submodule. -/
/-
**TensorProduct.quotTensorEquivQuotSMul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
`。
形式化陈述：quotTensorEquivQuotSMul (I : Ideal R) : ((R ⧸ I) otimes[R] M) ≃ₗ[R] M ⧸ (I
 • (⊤ : Submodule R M))
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Left tensoring a module with a quotient of the ring is the same as
quotienting that module by the corresponding submodule.
-/
noncomputable def quotTensorEquivQuotSMul (I : Ideal R) :
    ((R ⧸ I) ⊗[R] M) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  quotientTensorEquiv M I ≪≫ₗ
  (Submodule.Quotient.equiv _ _ (TensorProduct.lid R M) <| by
    rw [← LinearMap.range_comp, ← (Submodule.topEquiv.lTensor I).range_comp, Submodule.smul_eq_map₂,
      map₂_eq_range_lift_comp_mapIncl]
    exact congr_arg _ (TensorProduct.ext' fun _ _ ↦ by simp))

variable (M) in
/-- Right tensoring a module with a quotient of the ring is the same as
quotienting that module by the corresponding submodule. -/
/-
**TensorProduct.tensorQuotEquivQuotSMul** 是 Mathlib 中的一个定义，位于命名空间 `TensorProduct
`。
形式化陈述：tensorQuotEquivQuotSMul (I : Ideal R) : (M otimes[R] (R ⧸ I)) ≃ₗ[R] M ⧸ (I
 • (⊤ : Submodule R M))
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Right tensoring a module with a quotient of the ring is the same as
quotienting that module by the corresponding submodule.
-/
noncomputable def tensorQuotEquivQuotSMul (I : Ideal R) :
    (M ⊗[R] (R ⧸ I)) ≃ₗ[R] M ⧸ (I • (⊤ : Submodule R M)) :=
  TensorProduct.comm _ _ _ ≪≫ₗ quotTensorEquivQuotSMul M I

@[simp]
/-
**TensorProduct.quotTensorEquivQuotSMul_mk_tmul** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct`。
形式化陈述：quotTensorEquivQuotSMul_mk_tmul (I : Ideal R) (r : R) (x : M) : quotTensor
EquivQuotSMul M I (Ideal.Quotient.mk I r otimesₜ[R] x) = Submodule.Quotient.mk (
r • x)
参数：I : Ideal R；r : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
-/
lemma quotTensorEquivQuotSMul_mk_tmul (I : Ideal R) (r : R) (x : M) :
    quotTensorEquivQuotSMul M I (Ideal.Quotient.mk I r ⊗ₜ[R] x) =
      Submodule.Quotient.mk (r • x) :=
  (quotTensorEquivQuotSMul M I).eq_symm_apply.mp <|
    Eq.trans (congrArg (· ⊗ₜ[R] x) <|
        Eq.trans (congrArg (Ideal.Quotient.mk I)
                    (Eq.trans (smul_eq_mul ..) (mul_one r))).symm <|
          Submodule.Quotient.mk_smul I r 1) <|
      smul_tmul r _ x

@[simp]
/-
**TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul** 是 Mathlib 中的一个引理，位于命名空间 `T
ensorProduct`。
形式化陈述：quotTensorEquivQuotSMul_mk_one_tmul (I : Ideal R) (x : M) : quotTensorEqui
vQuotSMul M I (1 otimesₜ x) = Submodule.Quotient.mk x
参数：I : Ideal R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_mk_tmul`：quotTensorEquivQuotSMul_m
k_tmul (I : Ideal R) (r : R) (x : M) : quotTensorEquivQuotSMul M I (Ideal.Quotie
nt.mk I r otimesₜ[R] x) = Submodule…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quotTensorEquivQuotSMul_mk_one_tmul (I : Ideal R) (x : M) :
    quotTensorEquivQuotSMul M I (1 ⊗ₜ x) = Submodule.Quotient.mk x := by
  rw [← RingHom.map_one (Ideal.Quotient.mk I), TensorProduct.quotTensorEquivQuotSMul_mk_tmul]
  simp
/-
**TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor** 是 Mathlib 中的一个引理，位于命名
空间 `TensorProduct`。
形式化陈述：quotTensorEquivQuotSMul_comp_mkQ_rTensor (I : Ideal R) : quotTensorEquivQu
otSMul M I ∘ₗ I.mkQ.rTensor M = (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.lid
 R M
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_mk_tmul`：quotTensorEquivQuotSMul_m
k_tmul (I : Ideal R) (r : R) (x : M) : quotTensorEquivQuotSMul M I (Ideal.Quotie
nt.mk I r otimesₜ[R] x) = Submodule…
-/
lemma quotTensorEquivQuotSMul_comp_mkQ_rTensor (I : Ideal R) :
    quotTensorEquivQuotSMul M I ∘ₗ I.mkQ.rTensor M =
      (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.lid R M :=
  TensorProduct.ext' (quotTensorEquivQuotSMul_mk_tmul I)

@[simp]
/-
**TensorProduct.quotTensorEquivQuotSMul_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct`。
形式化陈述：quotTensorEquivQuotSMul_symm_mk (I : Ideal R) (x : M) : (quotTensorEquivQu
otSMul M I).symm (Submodule.Quotient.mk x) = 1 otimesₜ[R] x
参数：I : Ideal R；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma quotTensorEquivQuotSMul_symm_mk (I : Ideal R) (x : M) :
    (quotTensorEquivQuotSMul M I).symm (Submodule.Quotient.mk x) = 1 ⊗ₜ[R] x :=
  rfl
/-
**TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ** 是 Mathlib 中的一个引理，位于命名空间 
`TensorProduct`。
形式化陈述：quotTensorEquivQuotSMul_symm_comp_mkQ (I : Ideal R) : (quotTensorEquivQuot
SMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ = TensorProduct.mk R (R ⧸ I) M 1
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_symm_mk`：quotTensorEquivQuotSMul_s
ymm_mk (I : Ideal R) (x : M) : (quotTensorEquivQuotSMul M I).symm (Submodule.Quo
tient.mk x) = 1 otimesₜ[R] x
-/
lemma quotTensorEquivQuotSMul_symm_comp_mkQ (I : Ideal R) :
    (quotTensorEquivQuotSMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ =
      TensorProduct.mk R (R ⧸ I) M 1 :=
  LinearMap.ext (quotTensorEquivQuotSMul_symm_mk I)
/-
**TensorProduct.quotTensorEquivQuotSMul_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct`。
形式化陈述：quotTensorEquivQuotSMul_comp_mk (I : Ideal R) : quotTensorEquivQuotSMul M 
I ∘ₗ TensorProduct.mk R (R ⧸ I) M 1 = Submodule.mkQ (I • ⊤)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_symm_comp_eq`：toLinearMap_symm_comp_eq (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.t
oLinearMap.comp f
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_symm_comp_mkQ`：quotTensorEquivQuot
SMul_symm_comp_mkQ (I : Ideal R) : (quotTensorEquivQuotSMul M I).symm ∘ₗ (I • ⊤ 
: Submodule R M).mkQ = TensorProduct.mk R…
-/
lemma quotTensorEquivQuotSMul_comp_mk (I : Ideal R) :
    quotTensorEquivQuotSMul M I ∘ₗ TensorProduct.mk R (R ⧸ I) M 1 =
      Submodule.mkQ (I • ⊤) :=
  Eq.symm <| (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp <|
    quotTensorEquivQuotSMul_symm_comp_mkQ I

@[simp]
/-
**TensorProduct.tensorQuotEquivQuotSMul_tmul_mk** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct`。
形式化陈述：tensorQuotEquivQuotSMul_tmul_mk (I : Ideal R) (x : M) (r : R) : tensorQuot
EquivQuotSMul M I (x otimesₜ[R] Ideal.Quotient.mk I r) = Submodule.Quotient.mk (
r • x)
参数：I : Ideal R；x : M；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_mk_tmul`：quotTensorEquivQuotSMul_m
k_tmul (I : Ideal R) (r : R) (x : M) : quotTensorEquivQuotSMul M I (Ideal.Quotie
nt.mk I r otimesₜ[R] x) = Submodule…
-/
lemma tensorQuotEquivQuotSMul_tmul_mk (I : Ideal R) (x : M) (r : R) :
    tensorQuotEquivQuotSMul M I (x ⊗ₜ[R] Ideal.Quotient.mk I r) =
      Submodule.Quotient.mk (r • x) :=
  quotTensorEquivQuotSMul_mk_tmul I r x
/-
**TensorProduct.tensorQuotEquivQuotSMul_comp_mkQ_lTensor** 是 Mathlib 中的一个引理，位于命名
空间 `TensorProduct`。
形式化陈述：tensorQuotEquivQuotSMul_comp_mkQ_lTensor (I : Ideal R) : tensorQuotEquivQu
otSMul M I ∘ₗ I.mkQ.lTensor M = (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.rid
 R M
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.ext'`：ext' {g h : M otimes[R] N ->ₛₗ[σ₁₂] P₂} (H : forall 
x y, g (x otimesₜ y) = h (x otimesₜ y)) : g = h
· 使用引理 `TensorProduct.tensorQuotEquivQuotSMul_tmul_mk`：tensorQuotEquivQuotSMul_t
mul_mk (I : Ideal R) (x : M) (r : R) : tensorQuotEquivQuotSMul M I (x otimesₜ[R]
 Ideal.Quotient.mk I r) = Submodule…
-/
lemma tensorQuotEquivQuotSMul_comp_mkQ_lTensor (I : Ideal R) :
    tensorQuotEquivQuotSMul M I ∘ₗ I.mkQ.lTensor M =
      (I • ⊤ : Submodule R M).mkQ ∘ₗ TensorProduct.rid R M :=
  TensorProduct.ext' (tensorQuotEquivQuotSMul_tmul_mk I)

@[simp]
/-
**TensorProduct.tensorQuotEquivQuotSMul_symm_mk** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct`。
形式化陈述：tensorQuotEquivQuotSMul_symm_mk (I : Ideal R) (x : M) : (tensorQuotEquivQu
otSMul M I).symm (Submodule.Quotient.mk x) = x otimesₜ[R] 1
参数：I : Ideal R；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tensorQuotEquivQuotSMul_symm_mk (I : Ideal R) (x : M) :
    (tensorQuotEquivQuotSMul M I).symm (Submodule.Quotient.mk x) = x ⊗ₜ[R] 1 :=
  rfl
/-
**TensorProduct.tensorQuotEquivQuotSMul_symm_comp_mkQ** 是 Mathlib 中的一个引理，位于命名空间 
`TensorProduct`。
形式化陈述：tensorQuotEquivQuotSMul_symm_comp_mkQ (I : Ideal R) : (tensorQuotEquivQuot
SMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ = (TensorProduct.mk R M (R ⧸ I)).f
lip 1
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用引理 `TensorProduct.tensorQuotEquivQuotSMul_symm_mk`：tensorQuotEquivQuotSMul_s
ymm_mk (I : Ideal R) (x : M) : (tensorQuotEquivQuotSMul M I).symm (Submodule.Quo
tient.mk x) = x otimesₜ[R] 1
-/
lemma tensorQuotEquivQuotSMul_symm_comp_mkQ (I : Ideal R) :
    (tensorQuotEquivQuotSMul M I).symm ∘ₗ (I • ⊤ : Submodule R M).mkQ =
      (TensorProduct.mk R M (R ⧸ I)).flip 1 :=
  LinearMap.ext (tensorQuotEquivQuotSMul_symm_mk I)
/-
**TensorProduct.tensorQuotEquivQuotSMul_comp_mk** 是 Mathlib 中的一个引理，位于命名空间 `Tenso
rProduct`。
形式化陈述：tensorQuotEquivQuotSMul_comp_mk (I : Ideal R) : tensorQuotEquivQuotSMul M 
I ∘ₗ (TensorProduct.mk R M (R ⧸ I)).flip 1 = Submodule.mkQ (I • ⊤)
参数：I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearEquiv.toLinearMap_symm_comp_eq`：toLinearMap_symm_comp_eq (f : M₃ -
>ₛₗ[σ₃₁] M₁) (g : M₃ ->ₛₗ[σ₃₂] M₂) : e₁₂.symm.toLinearMap.comp g = f ↔ g = e₁₂.t
oLinearMap.comp f
· 使用引理 `TensorProduct.tensorQuotEquivQuotSMul_symm_comp_mkQ`：tensorQuotEquivQuot
SMul_symm_comp_mkQ (I : Ideal R) : (tensorQuotEquivQuotSMul M I).symm ∘ₗ (I • ⊤ 
: Submodule R M).mkQ = (TensorProduct.mk …
-/
lemma tensorQuotEquivQuotSMul_comp_mk (I : Ideal R) :
    tensorQuotEquivQuotSMul M I ∘ₗ (TensorProduct.mk R M (R ⧸ I)).flip 1 =
      Submodule.mkQ (I • ⊤) :=
  Eq.symm <| (LinearEquiv.toLinearMap_symm_comp_eq _ _).mp <|
    tensorQuotEquivQuotSMul_symm_comp_mkQ I

variable (S : Type*) [CommRing S] [Algebra R S]

/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`, then `S ⧸ IS` is
  isomorphic to `S ⊗[R] (R ⧸ I)` as `S` modules. -/
/-
**TensorProduct._root_.Ideal.qoutMapEquivTensorQout** 是 Mathlib 中的一个定义，位于命名空间 `T
ensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`, th
en `S ⧸ IS` is
  isomorphic to `S ⊗[R] (R ⧸ I)` as `S` modules.
-/
noncomputable def _root_.Ideal.qoutMapEquivTensorQout {I : Ideal R} :
    (S ⧸ I.map (algebraMap R S)) ≃ₗ[S] S ⊗[R] (R ⧸ I) where
  __ := LinearEquiv.symm <| tensorQuotEquivQuotSMul S I ≪≫ₗ Submodule.quotEquivOfEq _ _ (by simp)
    ≪≫ₗ Submodule.Quotient.restrictScalarsEquiv R _
  map_smul' := by
    rintro _ ⟨_⟩
    congr

variable (M) in
/-- Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`,
  then `S ⊗[R] M ⧸ I(S ⊗[R] M)` is isomorphic to `S ⊗[R] (M ⧸ IM)` as `S` modules. -/
/-
**TensorProduct.tensorQuotMapSMulEquivTensorQuot** 是 Mathlib 中的一个定义，位于命名空间 `Tens
orProduct`。
形式化陈述：tensorQuotMapSMulEquivTensorQuot (I : Ideal R) : ((S otimes[R] M) ⧸ I.map 
(algebraMap R S) • (⊤ : Submodule S (S otimes[R] M))) ≃ₗ[S] S otimes[R] (M ⧸ (I 
• (⊤ : Submodule R M)))
参数：I : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `R` be a commutative ring, `S` be an `R`-algebra, `I` is be ideal of `R`,
  then `S ⊗[R] M ⧸ I(S ⊗[R] M)` is isomorphic to `S ⊗[R] (M ⧸ IM)` as `S` module
s.
-/
noncomputable def tensorQuotMapSMulEquivTensorQuot (I : Ideal R) :
    ((S ⊗[R] M) ⧸ I.map (algebraMap R S) • (⊤ : Submodule S (S ⊗[R] M))) ≃ₗ[S]
    S ⊗[R] (M ⧸ (I • (⊤ : Submodule R M))) :=
  (tensorQuotEquivQuotSMul (S ⊗[R] M) (I.map (algebraMap R S))).symm ≪≫ₗ
    TensorProduct.comm S (S ⊗[R] M) _ ≪≫ₗ AlgebraTensorModule.cancelBaseChange R S S _ M ≪≫ₗ
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
/-- More linear version of `TensorProduct.tensorQuotientEquiv`. -/
/-
**TensorProduct.AlgebraTensorModule.tensorQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空
间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorQuotientEquiv (n : Submodule B N) : M otimes[R] (N ⧸ n) ≃ₗ[A] (M oti
mes[R] N) ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) where __
参数：n : Submodule B N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
More linear version of `TensorProduct.tensorQuotientEquiv`.
-/
noncomputable def tensorQuotientEquiv (n : Submodule B N) :
    M ⊗[R] (N ⧸ n) ≃ₗ[A]
      (M ⊗[R] N) ⧸ LinearMap.range (lTensor A M (n.subtype.restrictScalars R)) where
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
/-
**TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_apply_tmul** 是 Mathlib 中
的一个引理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorQuotientEquiv_apply_tmul (n : Submodule B N) (x : M) (y : N) : tenso
rQuotientEquiv A B M n (x otimesₜ[R] Submodule.Quotient.mk y) = Submodule.Quotie
nt.mk (x otimesₜ[R] y)
参数：n : Submodule B N；x : M；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
lemma tensorQuotientEquiv_apply_tmul (n : Submodule B N) (x : M) (y : N) :
    tensorQuotientEquiv A B M n (x ⊗ₜ[R] Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x ⊗ₜ[R] y) :=
  rfl

@[simp]
/-
**TensorProduct.AlgebraTensorModule.tensorQuotientEquiv_symm_apply_mk_tmul** 是 M
athlib 中的一个引理，位于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：tensorQuotientEquiv_symm_apply_mk_tmul (n : Submodule B N) (x : M) (y : N)
 : (tensorQuotientEquiv A B M n).symm (Submodule.Quotient.mk (x otimesₜ[R] y)) =
 x otimesₜ[R] Submodule.Quotient.mk y
参数：n : Submodule B N；x : M；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
-/
lemma tensorQuotientEquiv_symm_apply_mk_tmul (n : Submodule B N) (x : M) (y : N) :
    (tensorQuotientEquiv A B M n).symm (Submodule.Quotient.mk (x ⊗ₜ[R] y)) =
      x ⊗ₜ[R] Submodule.Quotient.mk y :=
  rfl


variable [Module A N] [IsScalarTower R A N]

/- This lemma characterizes the kernel of `TensorProduct.mapOfCompatibleSMul`. Together with
`TensorProduct.mapOfCompatibleSMul_surjective` it gives an alternative characterization of
`M ⊗[A] N` as the quotient of `M ⊗[R] N` by the submodule `S` described below. -/
/-
**TensorProduct.AlgebraTensorModule.ker_mapOfCompatibleSMul** 是 Mathlib 中的一个引理，位
于命名空间 `TensorProduct.AlgebraTensorModule`。
形式化陈述：ker_mapOfCompatibleSMul : (mapOfCompatibleSMul A R A M N).ker = Submodule.
span A {(a • m) otimesₜ[R] n - m otimesₜ[R] (a • n) | (a : A) (m : M) (n : N)}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `TensorProduct.CompatibleSMul.isScalarTower`：∀ {R : Type u_1} {R' : Type 
u_4} [inst : CommSemiring R] [inst_1 : Monoid R'] {M : Type u_7} {N : Type u_8} 
  [inst_2 : AddCommMonoid M] [in…
· 使用定理 `Submodule.span_eq_of_le`：span_eq_of_le (h₁ : s subseteq p) (h₂ : p <= sp
an R s) : span R s = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TensorProduct.smul_tmul`：smul_tmul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (m : M) (n : N) : (r • m) otimesₜ n = m otimesₜ[R] (r • n)
· 使用定理 `TensorProduct.tmul_smul`：tmul_smul [DistribMulAction R' N] [CompatibleSM
ul R R' M N] (r : R') (x : M) (y : N) : x otimesₜ (r • y) = r • x otimesₜ[R] y
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorProduct.tmul_add`：tmul_add (m : M) (n₁ n₂ : N) : m otimesₜ (n₁ + n
₂) = m otimesₜ n₁ + m otimesₜ[R] n₂
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Submodule.Quotient.eq`：∀ {R : Type u_1} {M : Type u_2} [inst : Ring R] [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (p : Submodule R M) {x y
 : M}, Subm…
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TensorProduct.add_tmul`：add_tmul (m₁ m₂ : M) (n : N) : (m₁ + m₂) otimesₜ
 n = m₁ otimesₜ n + m₂ otimesₜ[R] n
· 使用定理 `AddHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [
inst_1 : Add N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_add' 
: ∀ (x y :…
· 使用定理 `LinearMap.mk.congr_simp`：∀ {R : Type u_14} {S : Type u_15} [inst : Semir
ing R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [i
nst_2 : AddCo…
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma characterizes the kernel of `TensorProduct.mapOfCompatibleSMul`. Toge
ther with
`TensorProduct.mapOfCompatibleSMul_surjective` it gives an alternative character
ization of
`M ⊗[A] N` as the quotient of `M ⊗[R] N` by the submodule `S` described below.
-/
lemma ker_mapOfCompatibleSMul :
    (mapOfCompatibleSMul A R A M N).ker =
      Submodule.span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)} := by
  refine (Submodule.span_eq_of_le (mapOfCompatibleSMul A R A M N).ker ?_ ?_).symm
  · rintro - ⟨a, m, n, rfl⟩
    simp [smul_tmul]
  · let S := Submodule.span A {(a • m) ⊗ₜ[R] n - m ⊗ₜ[R] (a • n) | (a : A) (m : M) (n : N)}
    let F : M ⊗[A] N →ₗ[A] (M ⊗[R] N) ⧸ S := TensorProduct.lift ({
      toFun m := {
        toFun n := S.mkQ (m ⊗ₜ[R] n)
        map_add' _ _ := by simp [tmul_add]
        map_smul' a n := by
          rw [Submodule.mkQ_apply, Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, eq_comm,
            Submodule.Quotient.eq, RingHom.id_apply]
          exact Submodule.subset_span ⟨a, m, n, rfl⟩ }
      map_add' _ _ := by ext _; simp [add_tmul]
      map_smul' _ _ := by simp; rfl })
    have h : F ∘ₗ mapOfCompatibleSMul A R A M N = S.mkQ := by ext; simp [S, F]
    change (mapOfCompatibleSMul A R A M N).ker ≤ S
    rw [← Submodule.ker_mkQ S, ← h]
    exact (mapOfCompatibleSMul A R A M N).ker_le_ker_comp F

end TensorProduct.AlgebraTensorModule

