/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Module version of Chinese remainder theorem
-/

public section

open Function

variable {R : Type*} [CommRing R] {ι : Type*}
variable (M : Type*) [AddCommGroup M] [Module R M]
variable (I : ι → Ideal R) (hI : Pairwise (IsCoprime on I))

namespace Ideal

open TensorProduct LinearMap

set_option backward.isDefEq.respectTransparency.types false in
/-
**Ideal.pi_mkQ_rTensor** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：pi_mkQ_rTensor [Fintype ι] [DecidableEq ι] : (LinearMap.pi fun i => (I i).
mkQ).rTensor M = (piLeft ..).symm.toLinearMap ∘ₗ .pi (fun i => TensorProduct.mk 
R (R ⧸ I i) M 1) ∘ₗ TensorProduct.lid R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_injective`：∀ {R : Type uR} {A : 
Type uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst
_1 : Semiring A]   [inst_2 : Algebra R …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `LinearMap.ext_ring`：ext_ring {f g : R ->ₛₗ[σ] M₃} (h : f 1 = g 1) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `TensorProduct.AlgebraTensorModule.curry_apply`：∀ {R : Type uR} {A : Type
 uA} {M : Type uM} {N : Type uN} {P : Type uP} [inst : CommSemiring R] [inst_1 :
 Semiring A]   [inst_2 : Algebra R …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AddHom.map_add'`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (self : M →ₙ+ N) (x y : M),   self.toFun (x + y) = self.toFun x + sel
f.toF…
· 使用定理 `LinearMap.map_smul'`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring 
R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_
2 : AddCo…
· 使用定理 `LinearEquiv.left_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `LinearEquiv.right_inv`：∀ {R : Type u_14} {S : Type u_15} [inst : Semirin
g R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPa
ir σ σ'] [i…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `TensorProduct.piRight_symm_apply`：piRight_symm_apply (x : N) (m : forall
 i, M i) : (piRight R S N M).symm (fun i => x otimesₜ m i) = x otimesₜ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma pi_mkQ_rTensor [Fintype ι] [DecidableEq ι] :
    (LinearMap.pi fun i ↦ (I i).mkQ).rTensor M = (piLeft ..).symm.toLinearMap ∘ₗ
      .pi (fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) ∘ₗ TensorProduct.lid R M := by
  ext; simp [LinearMap.pi, LinearEquiv.piCongrRight]

variable [Finite ι]
include hI

attribute [local instance] Fintype.ofFinite

/-- A form of Chinese remainder theorem for modules, part I: if ideals `Iᵢ` of `R` are pairwise
coprime, then for any `R`-module `M`, the natural map `M → Πᵢ (R ⧸ Iᵢ) ⊗[R] M` is surjective. -/
/-
**Ideal.pi_tensorProductMk_quotient_surjective** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`
。
形式化陈述：pi_tensorProductMk_quotient_surjective : Surjective (LinearMap.pi fun i =>
 TensorProduct.mk R (R ⧸ I i) M 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
· 使用引理 `Ideal.pi_mkQ_surjective`：pi_mkQ_surjective {I : ι -> Ideal R} (hI : Pair
wise (IsCoprime on I)) : Surjective (LinearMap.pi fun i => (I i).mkQ)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Ideal.pi_mkQ_rTensor`：pi_mkQ_rTensor [Fintype ι] [DecidableEq ι] : (Line
arMap.pi fun i => (I i).mkQ).rTensor M = (piLeft ..).symm.toLinearMap ∘ₗ .pi (fu
n i => Ten…

--- 原说明 ---
A form of Chinese remainder theorem for modules, part I: if ideals `Iᵢ` of `R` a
re pairwise
coprime, then for any `R`-module `M`, the natural map `M → Πᵢ (R ⧸ Iᵢ) ⊗[R] M` i
s surjective.
-/
theorem pi_tensorProductMk_quotient_surjective :
    Surjective (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) := by
  have := rTensor_surjective M (pi_mkQ_surjective hI)
  classical rw [pi_mkQ_rTensor] at this
  simpa using this

/-- A form of Chinese remainder theorem for modules, part II: if ideals `Iᵢ` of `R` are pairwise
coprime, then for any `R`-module `M`, the kernel of `M → Πᵢ (R ⧸ Iᵢ) ⊗[R] M` equals `(⋂ᵢ Iᵢ) • M`.
-/
/-
**Ideal.ker_tensorProductMk_quotient** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ker_tensorProductMk_quotient : ker (LinearMap.pi fun i => TensorProduct.mk
 R (R ⧸ I i) M 1) = (⨅ i, I i) • (⊤ : Submodule R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用引理 `LinearMap.exact_subtype_ker_map`：exact_subtype_ker_map (g : N ->ₗ[R] P) 
: Exact (Submodule.subtype (ker g)) g
· 使用引理 `Ideal.pi_mkQ_surjective`：pi_mkQ_surjective {I : ι -> Ideal R} (hI : Pair
wise (IsCoprime on I)) : Surjective (LinearMap.pi fun i => (I i).mkQ)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用引理 `Ideal.pi_mkQ_rTensor`：pi_mkQ_rTensor [Fintype ι] [DecidableEq ι] : (Line
arMap.pi fun i => (I i).mkQ).rTensor M = (piLeft ..).symm.toLinearMap ∘ₗ .pi (fu
n i => Ten…
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.ker_pi`：ker_pi (f : (i : ι) -> M₂ ->ₗ[R] φ i) : ker (pi f) = ⨅
 i : ι, ker (f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `TensorProduct.induction_on`：∀ {R : Type u_1} [inst : CommSemiring R] {M 
: Type u_7} {N : Type u_8} [inst_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid 
N] [inst_3 : _ro…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Subtype.mem`：Subtype.mem {α : Type*} {s : Set α} (p : s) : (p : α) in s
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
A form of Chinese remainder theorem for modules, part II: if ideals `Iᵢ` of `R` 
are pairwise
coprime, then for any `R`-module `M`, the kernel of `M → Πᵢ (R ⧸ Iᵢ) ⊗[R] M` equ
als `(⋂ᵢ Iᵢ) • M`.
-/
theorem ker_tensorProductMk_quotient :
    ker (LinearMap.pi fun i ↦ TensorProduct.mk R (R ⧸ I i) M 1) =
      (⨅ i, I i) • (⊤ : Submodule R M) := by
  have := rTensor_exact M (exact_subtype_ker_map _) (pi_mkQ_surjective hI)
  rw [← (TensorProduct.lid R M).conj_exact_iff_exact, exact_iff] at this
  convert! this
  · classical simp [pi_mkQ_rTensor, LinearMap.comp_assoc]
  refine le_antisymm (Submodule.smul_le.mpr fun r hr m _ ↦ ⟨⟨r, ?_⟩ ⊗ₜ m, rfl⟩) ?_
  · simpa only [ker_pi, Submodule.ker_mkQ]
  rintro _ ⟨x, rfl⟩
  refine x.induction_on (by simp) (fun r m ↦ Submodule.smul_mem_smul ?_ ⟨⟩) fun _ _ ↦ ?_
  · simpa only [← (I _).ker_mkQ, ← ker_pi] using! Subtype.mem _
  · simpa using! add_mem

end Ideal

