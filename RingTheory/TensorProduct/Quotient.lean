/-
Copyright (c) 2025 Christian Merten, Yi Song, Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Yi Song, Sihan Su
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Interaction between quotients and tensor products for algebras

This file proves algebra analogs of the isomorphisms in
`Mathlib/LinearAlgebra/TensorProduct/Quotient.lean`.

## Main results

- `Algebra.TensorProduct.quotIdealMapEquivTensorQuot`:
  `B ⧸ (I.map <| algebraMap A B) ≃ₐ[B] B ⊗[A] (A ⧸ I)`
-/

@[expose] public section

open TensorProduct

namespace Algebra.TensorProduct

section

variable {A : Type*} (B : Type*) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal A)

/-- (Implementation): Use `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` instead. -/
/-
**Algebra.TensorProduct.quotIdealMapEquivTensorQuotAux** 是 Mathlib 中的一个定义，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：quotIdealMapEquivTensorQuotAux : (B ⧸ (I.map <| algebraMap A B)) ≃ₗ[B] B o
times[A] (A ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
(Implementation): Use `Algebra.TensorProduct.quotIdealMapEquivTensorQuot` instea
d.
-/
noncomputable def quotIdealMapEquivTensorQuotAux :
      (B ⧸ (I.map <| algebraMap A B)) ≃ₗ[B] B ⊗[A] (A ⧸ I) :=
  AddEquiv.toLinearEquiv (TensorProduct.tensorQuotEquivQuotSMul B I ≪≫ₗ
      Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map I) ≪≫ₗ
      Submodule.Quotient.restrictScalarsEquiv A (I.map <| algebraMap A B)).symm <| by
    intro c x
    obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
/-
**Algebra.TensorProduct.quotIdealMapEquivTensorQuotAux_mk** 是 Mathlib 中的一个引理，位于命
名空间 `Algebra.TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma quotIdealMapEquivTensorQuotAux_mk (b : B) :
    (quotIdealMapEquivTensorQuotAux B I) b = b ⊗ₜ[A] 1 :=
  rfl

/-- `B ⊗[A] (A ⧸ I)` is isomorphic as a `B`-algebra to `B ⧸ I B`. -/
/-
**Algebra.TensorProduct.quotIdealMapEquivTensorQuot** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebra.TensorProduct`。
形式化陈述：quotIdealMapEquivTensorQuot : (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[B] B otim
es[A] (A ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`B ⊗[A] (A ⧸ I)` is isomorphic as a `B`-algebra to `B ⧸ I B`.
-/
noncomputable def quotIdealMapEquivTensorQuot :
    (B ⧸ (I.map <| algebraMap A B)) ≃ₐ[B] B ⊗[A] (A ⧸ I) :=
  AlgEquiv.ofLinearEquiv (quotIdealMapEquivTensorQuotAux B I) rfl
    (fun x y ↦ by
      obtain ⟨u, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective y
      simp_rw [← map_mul, quotIdealMapEquivTensorQuotAux_mk]
      simp)

@[simp]
/-
**Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：quotIdealMapEquivTensorQuot_mk (b : B) : quotIdealMapEquivTensorQuot B I b
 = b otimesₜ[A] 1
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotIdealMapEquivTensorQuot_mk (b : B) :
    quotIdealMapEquivTensorQuot B I b = b ⊗ₜ[A] 1 :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：quotIdealMapEquivTensorQuot_symm_tmul (b : B) (a : A) : (quotIdealMapEquiv
TensorQuot B I).symm (b otimesₜ[A] a) = Submodule.Quotient.mk (a • b)
参数：b : B；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotIdealMapEquivTensorQuot_symm_tmul (b : B) (a : A) :
    (quotIdealMapEquivTensorQuot B I).symm (b ⊗ₜ[A] a) = Submodule.Quotient.mk (a • b) :=
  rfl

/-- `(A ⧸ I) ⊗[A] B` is isomorphic as an `A ⧸ I`-algebra to `B ⧸ I B`. -/
/-
**Algebra.TensorProduct.quotIdealMapEquivQuotTensor** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebra.TensorProduct`。
形式化陈述：quotIdealMapEquivQuotTensor : (B ⧸ (I.map (algebraMap A B))) ≃ₐ[A ⧸ I] (A 
⧸ I) otimes[A] B
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.Quotient.tower_quotient_map_quotient`：∀ {R : Type u_1} [inst : Com
mRing R] {S : Type u_2} [inst_1 : CommRing S] {p : Ideal R} [inst_2 : Algebra R 
S],   IsScalarTower R (R ⧸ p) (S…

--- 原说明 ---
`(A ⧸ I) ⊗[A] B` is isomorphic as an `A ⧸ I`-algebra to `B ⧸ I B`.
-/
noncomputable def quotIdealMapEquivQuotTensor :
    (B ⧸ (I.map (algebraMap A B))) ≃ₐ[A ⧸ I] (A ⧸ I) ⊗[A] B :=
  AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective
  { __ := (quotIdealMapEquivTensorQuot B I).toRingEquiv.trans
      (Algebra.TensorProduct.comm A B (A ⧸ I)).toRingEquiv
    commutes' x := by
      suffices Algebra.TensorProduct.comm A B (A ⧸ I) (quotIdealMapEquivTensorQuot B I
        (Ideal.Quotient.mk (I.map (algebraMap A B)) (algebraMap A B x))) =
          (algebraMap A (TensorProduct A (A ⧸ I) B)) x by simpa
      rw [quotIdealMapEquivTensorQuot_mk, tmul_one_eq_one_tmul]
      simp }

@[simp]
/-
**Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：quotIdealMapEquivQuotTensor_mk (b : B) : quotIdealMapEquivQuotTensor B I b
 = 1 otimesₜ[A] b
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotIdealMapEquivQuotTensor_mk (b : B) :
    quotIdealMapEquivQuotTensor B I b = 1 ⊗ₜ[A] b :=
  rfl

end

section

variable {R : Type*} (S T A : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [CommRing T] [Algebra R T] [CommRing A] [Algebra R A] [Algebra S A] [IsScalarTower R S A]

set_option backward.isDefEq.respectTransparency false in
/-- The tensor product of an `S`-algebra `A` over `R` with the quotient of `T` by an ideal `I`
is isomorphic (as an `S`-algebra) to the quotient of `A ⊗[R] T` by the extended ideal. -/
/-
**Algebra.TensorProduct.tensorQuotientEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：tensorQuotientEquiv (I : Ideal T) : A otimes[R] (T ⧸ I) ≃ₐ[S] (A otimes[R]
 T) ⧸ I.map (includeRight (A
参数：I : Ideal T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product of an `S`-algebra `A` over `R` with the quotient of `T` by an
 ideal `I`
is isomorphic (as an `S`-algebra) to the quotient of `A ⊗[R] T` by the extended 
ideal.
-/
noncomputable def tensorQuotientEquiv (I : Ideal T) :
    A ⊗[R] (T ⧸ I) ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (includeRight (A := A) (R := R)) :=
  letI g : (A ⊗[R] T ⧸ LinearMap.range (AlgebraTensorModule.lTensor S A
      (I.subtype.restrictScalars R))) ≃ₗ[S]
      A ⊗[R] T ⧸ (I.map (includeRight (A := A) (R := R))).restrictScalars S :=
    Submodule.quotEquivOfEq _ _ (AlgebraTensorModule.range_lTensor_idealMap _ _ _)
  .ofLinearEquiv (AlgebraTensorModule.tensorQuotientEquiv (R := R) S T A I ≪≫ₗ g) rfl <| by
    refine LinearMap.map_mul_of_map_mul_tmul fun a₁ a₂ b₁ b₂ ↦ ?_
    obtain ⟨b₁, rfl⟩ := Ideal.Quotient.mk_surjective b₁
    obtain ⟨b₂, rfl⟩ := Ideal.Quotient.mk_surjective b₂
    rw [← map_mul]
    simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, g,
      AlgebraTensorModule.tensorQuotientEquiv_apply_tmul, ← Ideal.Quotient.mk_eq_mk,
      ← Algebra.TensorProduct.tmul_mul_tmul]
    rfl

@[simp]
/-
**Algebra.TensorProduct.tensorQuotientEquiv_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：tensorQuotientEquiv_apply_tmul (I : Ideal T) (a : A) (t : T) : tensorQuoti
entEquiv (R
参数：I : Ideal T；a : A；t : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma tensorQuotientEquiv_apply_tmul (I : Ideal T) (a : A) (t : T) :
    tensorQuotientEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.tensorQuotientEquiv_symm_apply_tmul** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.TensorProduct`。
形式化陈述：tensorQuotientEquiv_symm_apply_tmul (I : Ideal T) (a : A) (t : T) : (tenso
rQuotientEquiv (R
参数：I : Ideal T；a : A；t : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma tensorQuotientEquiv_symm_apply_tmul (I : Ideal T) (a : A) (t : T) :
    (tensorQuotientEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = a ⊗ₜ[R] (Ideal.Quotient.mk I t) :=
  rfl

/-- The tensor product over `R` of the quotient of an `S`-algebra `A` by an ideal `I` with `T`
is isomorphic (as an `S`-algebra) to the quotient of `A ⊗[R] T` by the extended ideal. -/
/-
**Algebra.TensorProduct.quotientTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.T
ensorProduct`。
形式化陈述：quotientTensorEquiv (I : Ideal A) : (A ⧸ I) otimes[R] T ≃ₐ[S] (A otimes[R]
 T) ⧸ I.map (algebraMap A (A otimes[R] T)) where __
参数：I : Ideal A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The tensor product over `R` of the quotient of an `S`-algebra `A` by an ideal `I
` with `T`
is isomorphic (as an `S`-algebra) to the quotient of `A ⊗[R] T` by the extended 
ideal.
-/
noncomputable def quotientTensorEquiv (I : Ideal A) :
    (A ⧸ I) ⊗[R] T ≃ₐ[S] (A ⊗[R] T) ⧸ I.map (algebraMap A (A ⊗[R] T)) where
  __ := (TensorProduct.comm R (A ⧸ I) T).toRingEquiv.trans <|
    (tensorQuotientEquiv (R := R) R A T I).toRingEquiv.trans <|
    Ideal.quotientEquiv _ _ (TensorProduct.comm R T A).toRingEquiv <| (I.map_map _ _).symm
  commutes' _ := rfl

@[simp]
/-
**Algebra.TensorProduct.quotientTensorEquiv_apply_tmul** 是 Mathlib 中的一个引理，位于命名空间
 `Algebra.TensorProduct`。
形式化陈述：quotientTensorEquiv_apply_tmul (I : Ideal A) (a : A) (t : T) : quotientTen
sorEquiv (R
参数：I : Ideal A；a : A；t : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotientTensorEquiv_apply_tmul (I : Ideal A) (a : A) (t : T) :
    quotientTensorEquiv (R := R) S T A I (a ⊗ₜ t) = a ⊗ₜ[R] t :=
  rfl

@[simp]
/-
**Algebra.TensorProduct.quotientTensorEquiv_symm_apply_tmul** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.TensorProduct`。
形式化陈述：quotientTensorEquiv_symm_apply_tmul (I : Ideal A) (a : A) (t : T) : (quoti
entTensorEquiv (R
参数：I : Ideal A；a : A；t : T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
lemma quotientTensorEquiv_symm_apply_tmul (I : Ideal A) (a : A) (t : T) :
    (quotientTensorEquiv (R := R) S T A I).symm (a ⊗ₜ[R] t) = Ideal.Quotient.mk _ a ⊗ₜ[R] t :=
  rfl

end

end Algebra.TensorProduct

/-
**Ideal.subtype_rTensor_range** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.subtype_rTensor_range {R : Type*} [CommRing R] (M : Type*) [AddCommG
roup M] [Module R M] (I : Ideal R) : ((TensorProduct.lid R M).comp (I.subtype.rT
ensor M)).range = I • (⊤ : Submodule R M)
参数：M : Type*；I : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `Submodule.map_symm_eq_iff`：map_symm_eq_iff (e : M ≃ₛₗ[τ₁₂] M₂) {K : Subm
odule R₂ M₂} : K.map (e.symm : M₂ ->ₛₗ[τ₂₁] M) = p ↔ p.map (e : M ->ₛₗ[τ₁₂] M₂) 
= K
· 使用定理 `Submodule.comap_equiv_eq_map_symm`：comap_equiv_eq_map_symm (e : M ≃ₛₗ[τ₁
₂] M₂) (K : Submodule R₂ M₂) : K.comap (e : M ->ₛₗ[τ₁₂] M₂) = K.map (e.symm : M₂
 ->ₛₗ[τ₂₁] M)
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用引理 `TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor`：quotTensorEquivQ
uotSMul_comp_mkQ_rTensor (I : Ideal R) : quotTensorEquivQuotSMul M I ∘ₗ I.mkQ.rT
ensor M = (I • ⊤ : Submodule R M).mkQ ∘ₗ Ten…
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
-/
lemma Ideal.subtype_rTensor_range {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]
    (I : Ideal R) :
    ((TensorProduct.lid R M).comp (I.subtype.rTensor M)).range = I • (⊤ : Submodule R M) := by
  rw [← Submodule.ker_mkQ (I • (⊤ : Submodule R M)), LinearMap.range_comp,
    ← Submodule.map_symm_eq_iff, ← Submodule.comap_equiv_eq_map_symm, ← LinearMap.ker_comp,
    ← TensorProduct.quotTensorEquivQuotSMul_comp_mkQ_rTensor, LinearEquiv.ker_comp]
  exact LinearMap.exact_iff.mp (rTensor_exact M (LinearMap.exact_subtype_mkQ I) I.mkQ_surjective)

section

variable {R R' R'' S : Type*} [CommRing R] [CommRing R'] [CommRing R''] [CommRing S]
  [Algebra R R'] [Algebra R R''] [Algebra R' R''] [IsScalarTower R R' R''] [Algebra R S]

variable (R'') in
set_option backward.isDefEq.respectTransparency false in
attribute [local ext high] Ideal.Quotient.algHom_ext in
/-- Let `e` be an element of `R' ⊗[R] S`. Then `R'' ⊗[R'] ((R' ⊗[R] S) / e)` is isomorphic to
`(R'' ⊗[R] S) / e` as `R''`-algebras. -/
noncomputable
/-
**Algebra.tensorQuotientTensorEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Algebra.tensorQuotientTensorEquiv (e : R' otimes[R] S) : R'' otimes[R'] (R
' otimes[R] S ⧸ Ideal.span {e}) ≃ₐ[R''] (R'' otimes[R] S ⧸ Ideal.span {Algebra.T
ensorProduct.rTensor S (Algebra.ofId R' R'') e})
参数：e : R' otimes[R] S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Algebra.tensorQuotientTensorEquiv (e : R' ⊗[R] S) :
    R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) ≃ₐ[R'']
    (R'' ⊗[R] S ⧸ Ideal.span {Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'') e}) :=
  letI φ := Algebra.TensorProduct.rTensor S (Algebra.ofId R' R'')
  letI ψ : R'' ⊗[R] S →ₐ[R''] R'' ⊗[R'] (R' ⊗[R] S ⧸ Ideal.span {e}) :=
    Algebra.TensorProduct.lift (Algebra.ofId _ _)
      ((Algebra.TensorProduct.includeRight.restrictScalars R).comp
      ((Ideal.Quotient.mkₐ _ _).comp Algebra.TensorProduct.includeRight)) fun _ _ ↦ .all _ _
  haveI hψφ : (ψ.restrictScalars R').comp φ =
      (Algebra.TensorProduct.includeRight.restrictScalars R').comp (Ideal.Quotient.mkₐ _ _) := by
    ext; simp [ψ, φ]
  haveI heψ : Ideal.span {φ e} ≤ RingHom.ker ψ := by simpa [Ideal.span_le] using congr($hψφ e)
  AlgEquiv.ofAlgHom (Algebra.TensorProduct.lift (Algebra.ofId _ _) (Ideal.quotientMapₐ _ φ
    (Ideal.map_le_iff_le_comap.mp (by simp [Ideal.map_span, φ]))) fun _ _ ↦ .all _ _)
    (Ideal.Quotient.liftₐ _ ψ heψ) (by ext; simp [ψ, φ]) (by ext; simp [φ, ψ])

@[simp]
/-
**Algebra.tensorQuotientTensorEquiv_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.tensorQuotientTensorEquiv_tmul (e : R' otimes[R] S) (a : R'') (b :
 R') (c : S) : Algebra.tensorQuotientTensorEquiv R'' e (a otimesₜ Ideal.Quotient
.mk _ (b otimesₜ c)) = Ideal.Quotient.mk _ ((a * algebraMap R' R'' b) otimesₜ c)
参数：e : R' otimes[R] S；a : R''；b : R'；c : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂}
 [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3
 : Algebra R …
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Algebra.tensorQuotientTensorEquiv_tmul (e : R' ⊗[R] S) (a : R'') (b : R') (c : S) :
    Algebra.tensorQuotientTensorEquiv R'' e (a ⊗ₜ Ideal.Quotient.mk _ (b ⊗ₜ c)) =
      Ideal.Quotient.mk _ ((a * algebraMap R' R'' b) ⊗ₜ c) := by
  simp [Algebra.tensorQuotientTensorEquiv, ← Ideal.Quotient.mk_algebraMap, ← map_mul]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**Algebra.tensorQuotientTensorEquiv_symm_tmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Algebra.tensorQuotientTensorEquiv_symm_tmul (e : R' otimes[R] S) (a : R'')
 (b : S) : (Algebra.tensorQuotientTensorEquiv R'' e).symm (Ideal.Quotient.mk _ (
a otimesₜ b)) = a otimesₜ Ideal.Quotient.mk _ (1 otimesₜ b)
参数：e : R' otimes[R] S；a : R''；b : S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.ofAlgHom_symm_apply`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type
 uA₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [i
nst_3 : Algebra R …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Algebra.tensorQuotientTensorEquiv_symm_tmul (e : R' ⊗[R] S) (a : R'') (b : S) :
    (Algebra.tensorQuotientTensorEquiv R'' e).symm (Ideal.Quotient.mk _ (a ⊗ₜ b)) =
      a ⊗ₜ Ideal.Quotient.mk _ (1 ⊗ₜ b) := by
  simp [Algebra.tensorQuotientTensorEquiv]

end

