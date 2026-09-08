/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Finiteness.Subalgebra
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Descend finiteness along quotients by nilpotent ideals -/

public section

open TensorProduct

/-- If `I` is a finitely generated nilpotent ideal of an `R`-algebra `S`, and `T = S / I` is
`R`-finite, then `S` is also `R`-finite. -/
/-
**Module.finite_of_surjective_of_ker_le_nilradical** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finite_of_surjective_of_ker_le_nilradical {R S T : Type*} [CommRing
 R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T] [Module.Finite R T] (f
 : S ->ₐ[R] T) (hf₁ : Function.Surjective f) (hf₂ : RingHom.ker f <= nilradical 
S) (hf₃ : (RingHom.ker f).FG) : Module.Finite R S
参数：f : S ->ₐ[R] T；hf₁ : Function.Surjective f；hf₂ : RingHom.ker f <= nilradical 
S；hf₃ : (RingHom.ker f).FG。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RingHom.instIsTwoSidedKer`：∀ {R : Type u} {S : Type v} {F : Type u_1} [i
nst : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHo
mClass F R S] (…
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Module.Finite.of_finite`：∀ {R : Type u_1} {M : Type u_4} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   Modul
e.Finite R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `Ideal.Quotient.factor_surjective`：factor_surjective (H : S <= T) : Funct
ion.Surjective (factor H)
· 使用定理 `Submodule.fg_of_fg_map_of_fg_inf_ker`：fg_of_fg_map_of_fg_inf_ker (f : M 
->ₗ[R] P) {s : Submodule R M} (hs1 : (s.map f).FG) (hs2 : (s ⊓ LinearMap.ker f).
FG) : s.FG
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `Ideal.Quotient.isScalarTower`：∀ (R₁ : Type u_1) (R₂ : Type u_2) {A : Typ
e u_3} [inst : CommSemiring R₁] [inst_1 : CommSemiring R₂] [inst_2 : Ring A]   [
inst_3 : Algebra R…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用定理 `Submodule.FG.pow`：∀ {R : Type u_1} {A : Type u_2} [inst : CommSemiring R
] [inst_1 : Semiring A] [inst_2 : Algebra R A]   {M : Submodule R A}, M.FG → ∀ (
n : ℕ)…
· 使用定理 `Module.Finite.trans`：∀ {R : Type u_6} (A : Type u_7) (M : Type u_8) [ins
t : Semiring R] [inst_1 : Semiring A] [inst_2 : _root_.Module R A]   [inst_3 : A
ddCommMon…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.map_le_map_iff_of_injective`：map_le_map_iff_of_injective (p q 
: Submodule R M) : p.map f <= q.map f ↔ p <= q
· 使用引理 `Submodule.subtype_injective`：subtype_injective : Function.Injective p.su
btype
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
If `I` is a finitely generated nilpotent ideal of an `R`-algebra `S`, and `T = S
 / I` is
`R`-finite, then `S` is also `R`-finite.
-/
lemma Module.finite_of_surjective_of_ker_le_nilradical
    {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T]
    [Module.Finite R T] (f : S →ₐ[R] T)
    (hf₁ : Function.Surjective f) (hf₂ : RingHom.ker f ≤ nilradical S)
    (hf₃ : (RingHom.ker f).FG) :
    Module.Finite R S := by
  have : Module.Finite R (S ⧸ RingHom.ker f) :=
    let e := Ideal.quotientKerAlgEquivOfSurjective hf₁
    .of_surjective e.symm.toLinearMap e.symm.surjective
  generalize hI : RingHom.ker f = I at *
  suffices ∀ i, Module.Finite R (S ⧸ I ^ i) by
    obtain ⟨n, hn : _ = ⊥⟩ := hf₃.isNilpotent_iff_le_nilradical.mpr hf₂
    let e : (S ⧸ I ^ n) ≃ₐ[R] S := hn ▸ (AlgEquiv.quotientBot R S)
    exact .of_surjective e.toLinearMap e.surjective
  intro n
  induction n with
  | zero => rw [pow_zero, Ideal.one_eq_top]; infer_instance
  | succ n IH =>
    let φ : (S ⧸ I ^ (n + 1)) →ₐ[S] S ⧸ I ^ n :=
      Ideal.Quotient.factorₐ _ (Ideal.pow_le_pow_right n.le_succ)
    have hφ : Function.Surjective φ :=
      Ideal.Quotient.factor_surjective (Ideal.pow_le_pow_right n.le_succ)
    have hφ' : φ.toLinearMap ∘ₗ (I ^ (n + 1)).mkQ = (I ^ n).mkQ := rfl
    refine ⟨Submodule.fg_of_fg_map_of_fg_inf_ker (φ.toLinearMap.restrictScalars R) ?_ ?_⟩
    · simpa [LinearMap.range_eq_top_of_surjective (φ.toLinearMap.restrictScalars R) hφ] using
        Module.Finite.fg_top
    · have : Module.Finite R ((S ⧸ I) ⊗[S] ↑(I ^ n)) := by
        have : Module.Finite S ↑(I ^ n) := .of_fg (.pow hf₃ _)
        exact .trans (S ⧸ I) _
      let ψ : (S ⧸ I) ⊗[S] ↑(I ^ n) →ₗ[S] (S ⧸ I ^ (n + 1)) := by
        refine ?_ ∘ₗ (TensorProduct.quotTensorEquivQuotSMul _ I).toLinearMap
        refine Submodule.liftQ _ ((Submodule.mkQ _).comp (I ^ n).subtype) ?_
        rw [LinearMap.ker_comp, ← Submodule.map_le_map_iff_of_injective (I ^ n).subtype_injective,
          Submodule.map_smul'', Submodule.map_comap_eq]
        simpa [pow_succ'] using Ideal.mul_le_right (I := I) (J := I ^ n)
      convert! Module.Finite.fg_top.map (ψ.restrictScalars R) using 1
      suffices LinearMap.ker φ.toLinearMap = Submodule.map (I ^ (n + 1)).mkQ (I ^ n) by
        simpa [LinearMap.range_restrictScalars, ψ, LinearMap.range_comp, Submodule.range_liftQ]
      apply Submodule.comap_injective_of_surjective (I ^ (n + 1)).mkQ_surjective
      simpa [← LinearMap.ker_comp, hφ'] using Ideal.pow_le_pow_right n.le_succ
