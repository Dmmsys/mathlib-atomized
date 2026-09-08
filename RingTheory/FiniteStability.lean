/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-!

# Stability of finiteness conditions in commutative algebra

In this file we show that `Algebra.FiniteType` and `Algebra.FinitePresentation` are
stable under base change.

-/

public section

open scoped TensorProduct

universe w₁ w₂ w₃

variable {R : Type w₁} [CommRing R]
variable {A : Type w₂} [CommRing A] [Algebra R A]
variable (B : Type w₃) [CommRing B] [Algebra R B]

namespace Algebra

namespace FiniteType

/-
**Algebra.FiniteType.baseChangeAux_surj** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.Finit
eType`。
形式化陈述：baseChangeAux_surj {σ : Type*} {f : MvPolynomial σ R ->ₐ[R] A} (hf : Funct
ion.Surjective f) : Function.Surjective (Algebra.TensorProduct.map (AlgHom.id B 
B) f)
参数：hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.TensorProduct.map_surjective`：Algebra.TensorProduct.map_surjecti
ve (hf : Function.Surjective f) (hg : Function.Surjective g) : Function.Surjecti
ve (map f g)
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
theorem baseChangeAux_surj {σ : Type*} {f : MvPolynomial σ R →ₐ[R] A} (hf : Function.Surjective f) :
    Function.Surjective (Algebra.TensorProduct.map (AlgHom.id B B) f) := by
  change Function.Surjective (TensorProduct.map (AlgHom.id R B) f)
  apply TensorProduct.map_surjective
  · exact Function.RightInverse.surjective (congrFun rfl)
  · exact hf
/-
**Algebra.FiniteType.baseChange** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FiniteType`。
形式化陈述：baseChange [hfa : FiniteType R A] : Algebra.FiniteType B (B otimes[R] A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FiniteType.iff_quotient_mvPolynomial''`：iff_quotient_mvPolynomia
l'' : FiniteType R S ↔ exists (n : Nat) (f : MvPolynomial (Fin n) R ->ₐ[R] S), S
urjective f
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FiniteType.baseChangeAux_surj`：baseChangeAux_surj {σ : Type*} {f
 : MvPolynomial σ R ->ₐ[R] A} (hf : Function.Surjective f) : Function.Surjective
 (Algebra.TensorProduct.map…
-/
instance baseChange [hfa : FiniteType R A] : Algebra.FiniteType B (B ⊗[R] A) := by
  rw [iff_quotient_mvPolynomial''] at *
  obtain ⟨n, f, hf⟩ := hfa
  let g : B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have : Function.Surjective g := baseChangeAux_surj B hf
  use n, AlgHom.comp g (MvPolynomial.algebraTensorAlgEquiv R B).symm.toAlgHom
  simpa

end FiniteType

namespace FinitePresentation

/-
**Algebra.FinitePresentation.baseChange** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.Finit
ePresentation`。
形式化陈述：baseChange [FinitePresentation R A] : FinitePresentation B (B otimes[R] A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.FiniteType.baseChangeAux_surj`：baseChangeAux_surj {σ : Type*} {f
 : MvPolynomial σ R ->ₐ[R] A} (hf : Function.Surjective f) : Function.Surjective
 (Algebra.TensorProduct.map…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用引理 `Algebra.TensorProduct.lTensor_ker`：Algebra.TensorProduct.lTensor_ker (hg
 : Function.Surjective g) : RingHom.ker (map (AlgHom.id R A) g) = (RingHom.ker g
).map (Algebra.TensorPr…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.FG.map`：∀ {R : Type u_3} {S : Type u_4} [inst : Semiring R] [inst_
1 : Semiring S] {I : Ideal R},   I.FG → ∀ (f : R →+* S), (Ideal.map f I).FG
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ideal.fg_ker_comp`：fg_ker_comp {R S A : Type*} [CommRing R] [CommRing S]
 [CommRing A] (f : R ->+* S) (g : S ->+* A) (hf : (RingHom.ker f).FG) (hg : (Rin
gHom.ke…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `RingHom.ker_equiv`：ker_equiv {F' : Type*} [EquivLike F' R S] [RingEquivC
lass F' R S] (f : F') : ker f = ⊥
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `Submodule.fg_bot`：fg_bot : (⊥ : Submodule R M).FG
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
instance baseChange [FinitePresentation R A] : FinitePresentation B (B ⊗[R] A) := by
  obtain ⟨n, f, hsurj, hfg⟩ := ‹FinitePresentation R A›
  let g : B ⊗[R] MvPolynomial (Fin n) R →ₐ[B] B ⊗[R] A :=
    Algebra.TensorProduct.map (AlgHom.id B B) f
  have hgsurj : Function.Surjective g := Algebra.FiniteType.baseChangeAux_surj B hsurj
  have hker_eq : RingHom.ker g = Ideal.map Algebra.TensorProduct.includeRight (RingHom.ker f) :=
    Algebra.TensorProduct.lTensor_ker f hsurj
  have hfgg : Ideal.FG (RingHom.ker g) := by
    rw [hker_eq]
    exact Ideal.FG.map hfg _
  let g' : MvPolynomial (Fin n) B →ₐ[B] B ⊗[R] A :=
    AlgHom.comp g (MvPolynomial.algebraTensorAlgEquiv R B).symm.toAlgHom
  refine ⟨n, g', ?_, Ideal.fg_ker_comp _ _ ?_ hfgg ?_⟩
  · simp_all [g, g']
  · change Ideal.FG (RingHom.ker (AlgEquiv.symm (MvPolynomial.algebraTensorAlgEquiv R B)))
    simp only [RingHom.ker_equiv]
    exact Submodule.fg_bot
  · simpa using EquivLike.surjective _

end FinitePresentation

end Algebra

