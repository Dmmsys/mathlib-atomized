/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.Finsupp
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop

/-!

# Freeness of `QuotSMulTop` by a regular element

Let `M` be a finitely presented module over a commutative ring `R`. If `x` is in the
Jacobson radical of `R` and `x` is `M`-regular, then `M/xM` is free over `R/(x)` if and only if
`M` is free over `R`.

-/

public section

variable (R : Type*) [CommRing R] (M : Type*) [AddCommGroup M] [Module R M]

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Module.Free R M] (x : R) : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) :=
  Module.Free.of_equiv ((QuotSMulTop.equivQuotTensor x M).extendScalarsOfSurjective
    Ideal.Quotient.mk_surjective).symm

open Pointwise in
/-
**Module.free_quotSMulTop_iff_free** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.free_quotSMulTop_iff_free [Module.FinitePresentation R M] {x : R} (
mem : x in (⊥ : Ideal R).jacobson) (reg : IsSMulRegular M x) : Module.Free (R ⧸ 
Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M
参数：mem : x in (⊥ : Ideal R).jacobson；reg : IsSMulRegular M x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_restrictScalars_finite`：of_restrictScalars_finite (R A 
M : Type*) [Semiring R] [Semiring A] [AddCommMonoid M] [Module R M] [Module A M]
 [SMul R A] [IsScalarTower R …
· 使用定理 `Module.IsTorsionBySet.isScalarTower`：∀ {R : Type u_1} {M : Type u_2} [in
st : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {I : Ideal R
}   (hM : Module.IsTorsio…
· 使用引理 `Module.isTorsionBy_quotient_element_smul`：isTorsionBy_quotient_element_s
mul : IsTorsionBy R (M ⧸ r • (⊤ : Submodule R M)) r
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_cod`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.finsupp`：∀ (R : Type u_1) (M : Type u_2) (ι : Type u_3) [ins
t : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Modul
e.Free R …
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用引理 `Finsupp.mapRange_surjective`：mapRange_surjective (e : M -> N) (he₀ : e 0
 = 0) (he : Surjective e) : Surjective (Finsupp.mapRange (α
· 使用引理 `LinearMap.surjective_of_surjective_comp_mkQ`：LinearMap.surjective_of_sur
jective_comp_mkQ {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] (
f : M ->ₗ[R] N) (I : Ideal R) (Il…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ideal_span_singleton_smul`：ideal_span_singleton_smul (r : R) (
N : Submodule R M) : (Ideal.span {r} : Ideal R) • N = r • N
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `Finsupp.ker_mapRange`：ker_mapRange (f : M ->ₗ[R] N) (I : Type*) : Linear
Map.ker (mapRange.linearMap (α
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.mul_top`：mul_top [I.IsTwoSided] : I * ⊤ = I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用引理 `Finsupp.submodule_smul`：Finsupp.submodule_smul {M : Type*} [AddCommGroup
 M] [Module R M] (ι : Type*) (p : ι -> Submodule R M) (I : Ideal R) : Finsupp.su
bmodule (fun…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Finsupp.submodule_top`：submodule_top : Finsupp.submodule (fun _ : α => (
⊤ : Submodule R M)) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
（共 43 条，此处仅展示前 30 条）
-/
lemma Module.free_quotSMulTop_iff_free [Module.FinitePresentation R M] {x : R}
    (mem : x ∈ (⊥ : Ideal R).jacobson) (reg : IsSMulRegular M x) :
    Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M) ↔ Module.Free R M := by
  refine ⟨fun free ↦ ?_, fun free ↦ inferInstance⟩
  have := Module.Finite.of_restrictScalars_finite R (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b' : QuotSMulTop x M ≃ₗ[R] I →₀ R ⧸ Ideal.span {x} := b.1.restrictScalars R
  let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
  rcases Module.projective_lifting_property (Submodule.mkQ (x • (⊤ : Submodule R M))) f
    (Submodule.mkQ_surjective _) with ⟨g, hg⟩
  have surjf : Function.Surjective f := by
    simpa [f] using! Finsupp.mapRange_surjective _ rfl (Submodule.mkQ_surjective (Ideal.span {x}))
  have lejac : Ideal.span {x} ≤ (⊥ :Ideal R).jacobson := by simpa
  have surjg : Function.Surjective g := by
    apply g.surjective_of_surjective_comp_mkQ (Ideal.span {x}) lejac
    rwa [Submodule.ideal_span_singleton_smul x ⊤, hg]
  have kerf : LinearMap.ker f = x • (⊤ : Submodule R (I →₀ R)) := by
    simp only [LinearEquiv.ker_comp, f]
    rw [Finsupp.ker_mapRange, Submodule.ker_mkQ, ← (Ideal.span {x}).mul_top, ← smul_eq_mul,
      Finsupp.submodule_smul]
    simp [Submodule.ideal_span_singleton_smul]
  have injg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    have fg : (LinearMap.ker g).FG := Module.FinitePresentation.fg_ker g surjg
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ fg _ lejac
    rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    have : y ∈ x • (⊤ : Submodule R (I →₀ R)) := by simp [← kerf, ← hg, LinearMap.mem_ker.mp hy]
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp this with ⟨z, _, hz⟩
    simp only [← hz, LinearMap.mem_ker, map_smul] at hy
    have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
    simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg, surjg⟩)
