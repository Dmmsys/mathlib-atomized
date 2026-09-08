/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Flat.EquationalCriterion
public import Mathlib.RingTheory.Ideal.Quotient.ChineseRemainder
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.Support
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# Finite modules over local rings

This file gathers various results about finite modules over a local ring `(R, 𝔪, k)`.

## Main results
- `IsLocalRing.subsingleton_tensorProduct`: If `M` is finitely generated, `k ⊗ M = 0 ↔ M = 0`.
- `Module.free_of_maximalIdeal_rTensor_injective`:
  If `M` is a finitely presented module such that `m ⊗ M → M` is injective
  (for example when `M` is flat), then `M` is free.
- `Module.free_of_lTensor_residueField_injective`: If `N → M → P → 0` is a presentation of `P` with
  `N` finite and `M` finite free, then injectivity of `k ⊗ N → k ⊗ M` implies that `P` is free.
- `IsLocalRing.split_injective_iff_lTensor_residueField_injective`:
  Given an `R`-linear map `l : M → N` with `M` finite and `N` finite free,
  `l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/

public section

open Module

universe u
variable {R M N P : Type*} [CommRing R]

section

variable [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

open Function (Injective Surjective Exact)
open IsLocalRing TensorProduct

local notation "k" => ResidueField R
local notation "𝔪" => maximalIdeal R

variable [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)

namespace IsLocalRing

variable [IsLocalRing R]

/-
**IsLocalRing.map_mkQ_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ <= N₂) (h' : N₂.FG) : N₁.map (S
ubmodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂
参数：h : N₁ <= N₂；h' : N₂.FG。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_mkQ`：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p 
⊔ p'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …
· 使用定理 `IsLocalRing.jacobson_eq_maximalIdeal`：jacobson_eq_maximalIdeal (I : Idea
l R) (h : I != ⊤) : I.jacobson = IsLocalRing.maximalIdeal R
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Ideal.instNontrivial`：∀ {α : Type u} [inst : Semiring α] [Nontrivial α],
 Nontrivial (Ideal α)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ ≤ N₂) (h' : N₂.FG) :
    N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂)) ↔ N₁ = N₂ := by
  constructor
  · intro hN
    have : N₂ ≤ 𝔪 • N₂ ⊔ N₁ := by
      simpa using Submodule.comap_mono (f := Submodule.mkQ (𝔪 • N₂)) hN.ge
    rw [sup_comm] at this
    exact h.antisymm (Submodule.le_of_le_smul_of_le_jacobson_bot h'
      (by rw [jacobson_eq_maximalIdeal]; exact bot_ne_top) this)
  · rintro rfl; simp
/-
**IsLocalRing.map_mkQ_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`。
形式化陈述：map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] : N.map (Submodule.
mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.map_mkQ_eq`：map_mkQ_eq {N₁ N₂ : Submodule R M} (h : N₁ <= N₂
) (h' : N₂.FG) : N₁.map (Submodule.mkQ (𝔪 • N₂)) = N₂.map (Submodule.mkQ (𝔪 • N₂
)) ↔ N₁ = N₂
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_mkQ_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤ := by
  rw [← map_mkQ_eq (N₁ := N) le_top Module.Finite.fg_top, Submodule.map_top, Submodule.range_mkQ]
/-
**IsLocalRing.map_tensorProduct_mk_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing
`。
形式化陈述：map_tensorProduct_mk_eq_top {N : Submodule R M} [Module.Finite R M] : N.ma
p (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `LinearMap.instIsScalarTower`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `LinearMap.restrictScalars.congr_simp`：∀ (R : Type u_1) {S : Type u_5} {M
 : Type u_8} {M₂ : Type u_10} [inst : Semiring R] [inst_1 : Semiring S]   [inst_
2 : AddCommMonoid M] [inst…
· 使用定理 `LinearMap.ringLmapEquivSelf_symm_apply`：∀ (R : Type u_1) (S : Type u_4) 
(M : Type u_5) [inst : Semiring R] [inst_1 : Semiring S] [inst_2 : AddCommMonoid
 M]   [inst_3 : _root_.Modul…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `IsLocalRing.map_mkQ_eq_top`：map_mkQ_eq_top {N : Submodule R M} [Module.F
inite R M] : N.map (Submodule.mkQ (𝔪 • ⊤)) = ⊤ ↔ N = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `TensorProduct.mk_surjective`：TensorProduct.mk_surjective (h : Function.S
urjective (algebraMap R S)) : Function.Surjective (TensorProduct.mk R S M 1)
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
-/
theorem map_tensorProduct_mk_eq_top {N : Submodule R M} [Module.Finite R M] :
    N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N = ⊤ := by
  constructor
  · intro hN
    let : Module k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (Module (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let : IsScalarTower R k (M ⧸ (𝔪 • ⊤ : Submodule R M)) :=
      inferInstanceAs (IsScalarTower R (R ⧸ 𝔪) (M ⧸ 𝔪 • (⊤ : Submodule R M)))
    let f := AlgebraTensorModule.lift (((LinearMap.ringLmapEquivSelf k k _).symm
      (Submodule.mkQ (𝔪 • ⊤ : Submodule R M))).restrictScalars R)
    have : f.comp (TensorProduct.mk R k M 1) = Submodule.mkQ (𝔪 • ⊤) := by ext; simp [f]
    have hf : Function.Surjective f := by
      intro x; obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
      rw [← this, LinearMap.comp_apply]; exact ⟨_, rfl⟩
    apply_fun Submodule.map f at hN
    rwa [← Submodule.map_comp, this, Submodule.map_top, LinearMap.range_eq_top.2 hf,
      map_mkQ_eq_top] at hN
  · rintro rfl; rw [Submodule.map_top, LinearMap.range_eq_top]
    exact TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective
/-
**IsLocalRing.subsingleton_tensorProduct** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRing`
。
形式化陈述：subsingleton_tensorProduct [Module.Finite R M] : Subsingleton (k otimes[R]
 M) ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.subsingleton_iff`：subsingleton_iff : Subsingleton (Submodule R
 M) ↔ Subsingleton M
· 使用定理 `subsingleton_iff_bot_eq_top`：subsingleton_iff_bot_eq_top : (⊥ : α) = (⊤ 
: α) ↔ Subsingleton α
· 使用定理 `IsLocalRing.map_tensorProduct_mk_eq_top`：map_tensorProduct_mk_eq_top {N 
: Submodule R M} [Module.Finite R M] : N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N 
= ⊤
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem subsingleton_tensorProduct [Module.Finite R M] :
    Subsingleton (k ⊗[R] M) ↔ Subsingleton M := by
  rw [← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← Submodule.subsingleton_iff R, ← subsingleton_iff_bot_eq_top,
    ← map_tensorProduct_mk_eq_top (M := M), Submodule.map_bot]
/-
**IsLocalRing.span_eq_top_of_tmul_eq_basis** 是 Mathlib 中的一个定理，位于命名空间 `IsLocalRin
g`。
形式化陈述：span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι} (f : ι -> M) (b : Bas
is ι k (k otimes[R] M)) (hb : forall i, 1 otimesₜ f i = b i) : Submodule.span R 
(Set.range f) = ⊤
参数：f : ι -> M；b : Basis ι k (k otimes[R] M)；hb : forall i, 1 otimesₜ f i = b i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsLocalRing.map_tensorProduct_mk_eq_top`：map_tensorProduct_mk_eq_top {N 
: Submodule R M} [Module.Finite R M] : N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N 
= ⊤
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Submodule.restrictScalars_span`：restrictScalars_span (hsur : Function.Su
rjective (algebraMap R A)) (X : Set M) : restrictScalars R (span A X) = span R X
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.restrictScalars_eq_top_iff`：restrictScalars_eq_top_iff {p : Su
bmodule R M} : restrictScalars S p = ⊤ ↔ p = ⊤
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem span_eq_top_of_tmul_eq_basis [Module.Finite R M] {ι}
    (f : ι → M) (b : Basis ι k (k ⊗[R] M))
    (hb : ∀ i, 1 ⊗ₜ f i = b i) : Submodule.span R (Set.range f) = ⊤ := by
  rw [← map_tensorProduct_mk_eq_top, Submodule.map_span, ← Submodule.restrictScalars_span R k
    Ideal.Quotient.mk_surjective, Submodule.restrictScalars_eq_top_iff,
    ← b.span_eq, ← Set.range_comp]
  simp only [Function.comp_def, mk_apply, hb, Basis.span_eq]

end IsLocalRing

/-
**Module.mem_support_iff_nontrivial_residueField_tensorProduct** 是 Mathlib 中的一个引
理，位于命名空间 ``。
形式化陈述：Module.mem_support_iff_nontrivial_residueField_tensorProduct [Module.Finit
e R M] (p : PrimeSpectrum R) : p in Module.support R M ↔ Nontrivial (p.asIdeal.R
esidueField otimes[R] M)
参数：p : PrimeSpectrum R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PrimeSpectrum.isPrime`：∀ {R : Type u_1} [inst : CommSemiring R] (self : 
PrimeSpectrum R), self.asIdeal.IsPrime
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nontrivial_congr`：nontrivial_congr {α β} (e : α ≃ β) : Nontrivial 
α ↔ Nontrivial β
· 使用引理 `Module.mem_support_iff`：Module.mem_support_iff : p in Module.support R M
 ↔ Nontrivial (LocalizedModule p.asIdeal.primeCompl M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `not_nontrivial_iff_subsingleton`：not_nontrivial_iff_subsingleton : ¬Nont
rivial α ↔ Subsingleton α
· 使用定理 `IsLocalRing.subsingleton_tensorProduct`：subsingleton_tensorProduct [Modu
le.Finite R M] : Subsingleton (k otimes[R] M) ↔ Subsingleton M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Module.mem_support_iff_nontrivial_residueField_tensorProduct [Module.Finite R M]
    (p : PrimeSpectrum R) :
    p ∈ Module.support R M ↔ Nontrivial (p.asIdeal.ResidueField ⊗[R] M) := by
  let K := p.asIdeal.ResidueField
  let e := (AlgebraTensorModule.cancelBaseChange R (Localization.AtPrime p.asIdeal) K K M).symm
  rw [e.nontrivial_congr, Module.mem_support_iff,
    (LocalizedModule.equivTensorProduct p.asIdeal.primeCompl M).nontrivial_congr,
    ← not_iff_not, not_nontrivial_iff_subsingleton, not_nontrivial_iff_subsingleton,
    IsLocalRing.subsingleton_tensorProduct]

open Function in
/--
Given `M₁ → M₂ → M₃ → 0` and `N₁ → N₂ → N₃ → 0`,
if `M₁ ⊗ N₃ → M₂ ⊗ N₃` and `M₂ ⊗ N₁ → M₂ ⊗ N₂` are both injective,
then `M₃ ⊗ N₁ → M₃ ⊗ N₂` is also injective.
-/
/-
**lTensor_injective_of_exact_of_exact_of_rTensor_injective** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：lTensor_injective_of_exact_of_exact_of_rTensor_injective {M₁ M₂ M₃ N₁ N₂ N
₃} [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup
 M₃] [Module R M₃] [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N
₂] [AddCommGroup N₃] [Module R N₃] {f₁ : M₁ ->ₗ[R] M₂} {f₂ : M₂ ->ₗ[R] M₃} {g₁ :
 N₁ ->ₗ[R] N₂} {g₂ : N₂ ->ₗ[R] N₃} (hfexact : Exact f₁ f₂) (hfsurj : Surjective 
f₂) (hgexact : Exact g₁ g₂) (hgsurj : Surjective g₂) (hfinj : Injective (f₁.rTen
sor N₃)) (hginj : Injectiv
参数：hfexact : Exact f₁ f₂；hfsurj : Surjective f₂；hgexact : Exact g₁ g₂；hgsurj : S
urjective g₂；hfinj : Injective (f₁.rTensor N₃)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.rTensor_surjective`：LinearMap.rTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (rTensor Q g)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `Function.Exact.linearMap_comp_eq_zero`：∀ {R : Type u_1} {M : Type u_2} {
N : Type u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [i
nst_2 : AddCommMonoid N] [i…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `LinearMap.rTensor_zero`：rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0

--- 原说明 ---
Given `M₁ → M₂ → M₃ → 0` and `N₁ → N₂ → N₃ → 0`,
if `M₁ ⊗ N₃ → M₂ ⊗ N₃` and `M₂ ⊗ N₁ → M₂ ⊗ N₂` are both injective,
then `M₃ ⊗ N₁ → M₃ ⊗ N₂` is also injective.
-/
theorem lTensor_injective_of_exact_of_exact_of_rTensor_injective
    {M₁ M₂ M₃ N₁ N₂ N₃}
    [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂] [AddCommGroup N₃] [Module R N₃]
    {f₁ : M₁ →ₗ[R] M₂} {f₂ : M₂ →ₗ[R] M₃} {g₁ : N₁ →ₗ[R] N₂} {g₂ : N₂ →ₗ[R] N₃}
    (hfexact : Exact f₁ f₂) (hfsurj : Surjective f₂)
    (hgexact : Exact g₁ g₂) (hgsurj : Surjective g₂)
    (hfinj : Injective (f₁.rTensor N₃)) (hginj : Injective (g₁.lTensor M₂)) :
    Injective (g₁.lTensor M₃) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨x, rfl⟩ := f₂.rTensor_surjective N₁ hfsurj x
  have : f₂.rTensor N₂ (g₁.lTensor M₂ x) = 0 := by
    rw [← hx, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      LinearMap.lTensor_comp_rTensor]
  obtain ⟨y, hy⟩ := (rTensor_exact N₂ hfexact hfsurj _).mp this
  have : g₂.lTensor M₁ y = 0 := by
    apply hfinj
    trans g₂.lTensor M₂ (g₁.lTensor M₂ x)
    · rw [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
        LinearMap.lTensor_comp_rTensor]
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hgexact.linearMap_comp_eq_zero]
    simp
  obtain ⟨z, rfl⟩ := (lTensor_exact _ hgexact hgsurj _).mp this
  obtain rfl : f₁.rTensor N₁ z = x := by
    apply hginj
    simp only [← hy, ← LinearMap.comp_apply, ← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor,
      LinearMap.rTensor_comp_lTensor]
  rw [← LinearMap.comp_apply, ← LinearMap.rTensor_comp, hfexact.linearMap_comp_eq_zero]
  simp

namespace Module

variable [IsLocalRing R]

set_option backward.isDefEq.respectTransparency false in
/-- If `M` is of finite presentation over a local ring `(R, 𝔪, k)` such that
`𝔪 ⊗ M → M` is injective, then every family of elements that is a `k`-basis of
`k ⊗ M` is an `R`-basis of `M`. -/
/-
**Module.exists_basis_of_basis_baseChange** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：exists_basis_of_basis_baseChange [Module.FinitePresentation R M] {ι : Type
*} (v : ι -> M) (hli : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v)) (hsp 
: Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤) (H : Function
.Injective ((𝔪).subtype.rTensor M)) : exists (b : Basis ι R M), forall i, b i = 
v i
参数：v : ι -> M；hli : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v)；hsp : Sub
module.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤；H : Function.Inject
ive ((𝔪).subtype.rTensor M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Module.Finite.finite_basis`：finite_basis [Nontrivial R] {ι} [Module.Fini
te R M] (b : Basis ι R M) : _root_.Finite ι
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `IsLocalRing.span_eq_top_of_tmul_eq_basis`：span_eq_top_of_tmul_eq_basis [
Module.Finite R M] {ι} (f : ι -> M) (b : Basis ι k (k otimes[R] M)) (hb : forall
 i, 1 otimesₜ f i = b i) : Sub…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Finite.of_fg`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submodule R M}, 
N.FG → Mo…
· 使用引理 `Module.FinitePresentation.fg_ker`：Module.FinitePresentation.fg_ker [Modu
le.Finite R M] [h : Module.FinitePresentation R N] (l : M ->ₗ[R] N) (hl : Functi
on.Surjective l) : (Li…
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.subsingleton_iff_eq_bot`：subsingleton_iff_eq_bot : Subsingleto
n p ↔ p = ⊥
· 使用定理 `IsLocalRing.subsingleton_tensorProduct`：subsingleton_tensorProduct [Modu
le.Finite R M] : Subsingleton (k otimes[R] M) ↔ Subsingleton M
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `LinearMap.lTensor_surjective`：LinearMap.lTensor_surjective (hg : Functio
n.Surjective g) : Function.Surjective (lTensor Q g)
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Nat.add_right_inj`：∀ {m k n : ℕ}, n + m = n + k ↔ m = k
· 使用定理 `LinearMap.finrank_range_add_finrank_ker`：finrank_range_add_finrank_ker [
FiniteDimensional K V] (f : V ->ₗ[K] V₂) : finrank K (LinearMap.range f) + finra
nk K (LinearMap.ker f) = finr…
（共 61 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` is of finite presentation over a local ring `(R, 𝔪, k)` such that
`𝔪 ⊗ M → M` is injective, then every family of elements that is a `k`-basis of
`k ⊗ M` is an `R`-basis of `M`.
-/
lemma exists_basis_of_basis_baseChange [Module.FinitePresentation R M]
    {ι : Type*} (v : ι → M) (hli : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v))
    (hsp : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤)
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    ∃ (b : Basis ι R M), ∀ i, b i = v i := by
  let bk : Basis ι k (k ⊗[R] M) := Basis.mk hli (by rw [hsp])
  have : Finite ι := Module.Finite.finite_basis bk
  let : Fintype ι := Fintype.ofFinite ι
  let i := Finsupp.linearCombination R v
  have hi : Surjective i := by
    rw [← LinearMap.range_eq_top, Finsupp.range_linearCombination]
    refine IsLocalRing.span_eq_top_of_tmul_eq_basis (R := R) (f := v) bk
      (fun _ ↦ by simp [bk])
  have : Module.Finite R (LinearMap.ker i) :=
    .of_fg (Module.FinitePresentation.fg_ker i hi)
  -- We claim that `i` is actually a bijection,
  -- hence `v` induces an isomorphism `M ≃[R] Rᴵ` showing that `v` is a basis.
  let iequiv : (ι →₀ R) ≃ₗ[R] M := by
    refine LinearEquiv.ofBijective i ⟨?_, hi⟩
    -- By Nakayama's lemma, it suffices to show that `k ⊗ ker(i) = 0`.
    rw [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
      ← IsLocalRing.subsingleton_tensorProduct (R := R), subsingleton_iff_forall_eq 0]
    have : Function.Surjective (i.baseChange k) := i.lTensor_surjective _ hi
    -- By construction, `k ⊗ i : kᴵ → k ⊗ M` is bijective.
    have hi' : Function.Bijective (i.baseChange k) := by
      refine ⟨?_, this⟩
      rw [← LinearMap.ker_eq_bot (M := k ⊗[R] (ι →₀ R)) (f := i.baseChange k),
        ← Submodule.finrank_eq_zero (R := k) (M := k ⊗[R] (ι →₀ R)),
        ← Nat.add_right_inj (n := Module.finrank k (LinearMap.range <| i.baseChange k)),
        LinearMap.finrank_range_add_finrank_ker (V := k ⊗[R] (ι →₀ R)),
        LinearMap.range_eq_top.mpr this, finrank_top]
      simp only [Module.finrank_tensorProduct, Module.finrank_self,
        Module.finrank_finsupp_self, one_mul, add_zero]
      rw [Module.finrank_eq_card_basis bk]
    -- On the other hand, `m ⊗ M → M` injective => `Tor₁(k, M) = 0` => `k ⊗ ker(i) → kᴵ` injective.
    intro x
    refine lTensor_injective_of_exact_of_exact_of_rTensor_injective
      (N₁ := LinearMap.ker i) (N₂ := ι →₀ R) (N₃ := M)
      (f₁ := (𝔪).subtype) (f₂ := Submodule.mkQ 𝔪)
      (g₁ := (LinearMap.ker i).subtype) (g₂ := i) (LinearMap.exact_subtype_mkQ 𝔪)
      (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_ker_map i) hi H ?_ ?_
    · apply Module.Flat.lTensor_preserves_injective_linearMap
      exact Subtype.val_injective
    · apply hi'.injective
      rw [LinearMap.baseChange_eq_ltensor]
      erw [← LinearMap.comp_apply (i.lTensor k), ← LinearMap.lTensor_comp]
      rw [(LinearMap.exact_subtype_ker_map i).linearMap_comp_eq_zero]
      simp only [LinearMap.lTensor_zero, LinearMap.zero_apply, map_zero]
  use Basis.ofRepr iequiv.symm
  intro j
  simp [iequiv, i]

/--
If `M` is a finitely presented module over a local ring `(R, 𝔪)` such that `m ⊗ M → M` is
injective, then every generating family contains a basis.
-/
/-
**Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective** 是 Mathlib 中的一个
引理，位于命名空间 `Module`。
形式化陈述：exists_basis_of_span_of_maximalIdeal_rTensor_injective [Module.FinitePrese
ntation R M] (H : Function.Injective ((𝔪).subtype.rTensor M)) {ι : Type u} (v : 
ι -> M) (hv : Submodule.span R (Set.range v) = ⊤) : exists (κ : Type u) (a : κ -
> ι) (b : Basis κ R M), forall i, b i = v (a i)
参数：H : Function.Injective ((𝔪).subtype.rTensor M)；v : ι -> M；hv : Submodule.span
 R (Set.range v) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsLocalRing.map_tensorProduct_mk_eq_top`：map_tensorProduct_mk_eq_top {N 
: Submodule R M} [Module.Finite R M] : N.map (TensorProduct.mk R k M 1) = ⊤ ↔ N 
= ⊤
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Submodule.top_coe`：top_coe : ((⊤ : Submodule R M) : Set M) = Set.univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
· 使用定理 `Submodule.span_subset_span`：span_subset_span : ↑(span R s) subseteq (spa
n S s : Set M)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `exists_linearIndependent'`：exists_linearIndependent' (v : ι -> V) : exis
ts (κ : Type u') (a : κ -> ι), Injective a ∧ Submodule.span K (Set.range (v ∘ a)
) = Submodule.s…
· 使用引理 `Module.exists_basis_of_basis_baseChange`：exists_basis_of_basis_baseChang
e [Module.FinitePresentation R M] {ι : Type*} (v : ι -> M) (hli : LinearIndepend
ent k (TensorProduct.mk R k M…

--- 原说明 ---
If `M` is a finitely presented module over a local ring `(R, 𝔪)` such that `m ⊗ 
M → M` is
injective, then every generating family contains a basis.
-/
lemma exists_basis_of_span_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M))
    {ι : Type u} (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ (κ : Type u) (a : κ → ι) (b : Basis κ R M), ∀ i, b i = v (a i) := by
  have := (map_tensorProduct_mk_eq_top (N := Submodule.span R (Set.range v))).mpr hv
  rw [← Submodule.span_image, ← Set.range_comp, eq_top_iff, ← SetLike.coe_subset_coe,
    Submodule.top_coe] at this
  have : Submodule.span k (Set.range (TensorProduct.mk R k M 1 ∘ v)) = ⊤ := by
    rw [eq_top_iff]
    exact Set.Subset.trans this (Submodule.span_subset_span _ _ _)
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' k (TensorProduct.mk R k M 1 ∘ v)
  rw [this] at hsp
  obtain ⟨b, hb⟩ := exists_basis_of_basis_baseChange (v ∘ a) hli hsp H
  use κ, a, b, hb
/-
**Module.exists_basis_of_span_of_flat** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：exists_basis_of_span_of_flat [Module.FinitePresentation R M] [Module.Flat 
R M] {ι : Type u} (v : ι -> M) (hv : Submodule.span R (Set.range v) = ⊤) : exist
s (κ : Type u) (a : κ -> ι) (b : Basis κ R M), forall i, b i = v (a i)
参数：v : ι -> M；hv : Submodule.span R (Set.range v) = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective`：exists_ba
sis_of_span_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M] (H
 : Function.Injective ((𝔪).subtype.rTensor M)) {ι :…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma exists_basis_of_span_of_flat [Module.FinitePresentation R M] [Module.Flat R M]
    {ι : Type u} (v : ι → M) (hv : Submodule.span R (Set.range v) = ⊤) :
    ∃ (κ : Type u) (a : κ → ι) (b : Basis κ R M), ∀ i, b i = v (a i) :=
  exists_basis_of_span_of_maximalIdeal_rTensor_injective
    (Module.Flat.rTensor_preserves_injective_linearMap (𝔪).subtype Subtype.val_injective) v hv

/--
If `M` is a finitely presented module over a local ring `(R, 𝔪)` such that `m ⊗ M → M` is
injective, then `M` is free.
-/
/-
**Module.free_of_maximalIdeal_rTensor_injective** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e`。
形式化陈述：free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M] (H 
: Function.Injective ((𝔪).subtype.rTensor M)) : Module.Free R M
参数：H : Function.Injective ((𝔪).subtype.rTensor M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.exists_basis_of_span_of_maximalIdeal_rTensor_injective`：exists_ba
sis_of_span_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M] (H
 : Function.Injective ((𝔪).subtype.rTensor M)) {ι :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_id`：range_id : range (@id α) = univ
· 使用定理 `Submodule.span_univ`：span_univ : span R (univ : Set M) = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…

--- 原说明 ---
If `M` is a finitely presented module over a local ring `(R, 𝔪)` such that `m ⊗ 
M → M` is
injective, then `M` is free.
-/
theorem free_of_maximalIdeal_rTensor_injective [Module.FinitePresentation R M]
    (H : Function.Injective ((𝔪).subtype.rTensor M)) :
    Module.Free R M := by
  obtain ⟨_, _, b, _⟩ := exists_basis_of_span_of_maximalIdeal_rTensor_injective H id (by simp)
  exact Free.of_basis b

set_option backward.isDefEq.respectTransparency.types false in
/-
**Module.IsLocalRing.linearIndependent_of_flat** 是 Mathlib 中的一个定理，位于命名空间 `Module
.IsLocalRing`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   [inst_3 : IsLocalRing R] [Module.Flat R M] {ι
 : Type u} (v : ι → M),   LinearIndependent (IsLocalRing.ResidueField R) (⇑((Ten
sorProduct.mk R (IsLocalRing.ResidueField R) M) 1) ∘ v) →     LinearIndependent 
R v
参数：v : ι → M；IsLocalRing.ResidueField R；⇑((TensorProduct.mk R (IsLocalRing.Resid
ueField R) M) 1) ∘ v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `Finset.notMem_empty`：notMem_empty (a : α) : a ∉ (∅ : Finset α)
· 使用定理 `Module.Flat.isTrivialRelation_of_sum_smul_eq_zero`：isTrivialRelation_of_
sum_smul_eq_zero [Flat R M] {ι : Type*} [Fintype ι] {f : ι -> R} {x : ι -> M} (h
 : ∑ i, f i • x i = 0) : IsTrivialRelat…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_coe_sort`：∀ {ι : Type u_1} {M : Type u_4} (s : Finset ι) [ins
t : AddCommMonoid M] (f : ι → M), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Finset.mem_insert_self`：mem_insert_self (a : α) (s : Finset α) : a in in
sert a s
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `sum_mem`：∀ {B : Type u_3} {S : B} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : SetLike B M] [AddSubmonoidClass B M]   {ι : Type u_5} {t : Finset…
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsUnit.mul_left_inj`：mul_left_inj (h : IsUnit a) : b * a = c * a ↔ b = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 62 条，此处仅展示前 30 条）
-/
theorem IsLocalRing.linearIndependent_of_flat [Flat R M] {ι : Type u} (v : ι → M)
    (h : LinearIndependent k (TensorProduct.mk R k M 1 ∘ v)) : LinearIndependent R v := by
  rw [linearIndependent_iff']; intro s f hfv i hi
  classical
  induction s using Finset.induction generalizing v i with
  | empty => exact (Finset.notMem_empty _ hi).elim
  | insert n s hn ih => ?_
  rw [← Finset.sum_coe_sort] at hfv
  have ⟨l, a, y, hay, hfa⟩ := Flat.isTrivialRelation_of_sum_smul_eq_zero hfv
  have : v n ∉ 𝔪 • (⊤ : Submodule R M) := by
    simpa only [← LinearMap.ker_tensorProductMk] using! h.ne_zero n
  set n : ↥(insert n s) := ⟨n, Finset.mem_insert_self ..⟩ with n_def
  obtain ⟨j, hj⟩ : ∃ j, IsUnit (a n j) := by
    contrapose! this
    rw [show v n = _ from hay n]
    exact sum_mem fun _ _ ↦ Submodule.smul_mem_smul (this _) ⟨⟩
  let a' (i : ι) : R := if hi : _ then a ⟨i, hi⟩ j else 0
  have a_eq i : a i j = a' i.1 := by simp_rw [a', dif_pos i.2]
  have hfn : f n = -(∑ i ∈ s, f i * a' i) * hj.unit⁻¹ := by
    rw [← hj.mul_left_inj, mul_assoc, hj.val_inv_mul, mul_one, eq_neg_iff_add_eq_zero]
    convert! hfa j
    simp_rw [a_eq, Finset.sum_coe_sort _ (fun i ↦ f i * a' i), s.sum_insert hn, n_def]
  let c (i : ι) : R := -(if i = n then 0 else a' i) * hj.unit⁻¹
  specialize ih (v + (c · • v n)) ?_ ?_
  · convert! (linearIndependent_add_smul_iff (c := Ideal.Quotient.mk _ ∘ c) (i := n.1) ?_).mpr h
    · ext; simp [tmul_add]; rfl
    simp_rw [Function.comp_def, c, if_pos, neg_zero, zero_mul, map_zero]
  · rw [Finset.sum_coe_sort _ (fun i ↦ f i • v i), s.sum_insert hn, add_comm, hfn] at hfv
    simp_rw [Pi.add_apply, smul_add, s.sum_add_distrib, c, smul_smul, ← s.sum_smul, ← mul_assoc,
      ← s.sum_mul, mul_neg, s.sum_neg_distrib, ← hfv]
    congr 4
    exact s.sum_congr rfl fun i hi ↦ by rw [if_neg (ne_of_mem_of_not_mem hi hn)]
  obtain hi | hi := Finset.mem_insert.mp hi
  · rw [hi, hfn, Finset.sum_eq_zero, neg_zero, zero_mul]
    intro i hi; rw [ih i hi, zero_mul]
  · exact ih i hi

set_option backward.isDefEq.respectTransparency.types false in
open Finsupp in
/-
**Module.IsLocalRing.linearCombination_bijective_of_flat** 是 Mathlib 中的一个定理，位于命名
空间 `Module.IsLocalRing`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup
 M] [inst_2 : _root_.Module R M]   [inst_3 : IsLocalRing R] [Module.Finite R M] 
[Module.Flat R M] {ι : Type u} (v : ι → M),   Function.Bijective       ⇑(Finsupp
.linearCombination (IsLocalRing.ResidueField R)           (⇑((TensorProduct.mk R
 (IsLocalRing.ResidueField R) M) 1) ∘ v)) →     Function.Bijective ⇑(Finsupp.lin
earCombination R v)
参数：v : ι → M；Finsupp.linearCombination (IsLocalRing.ResidueField R)           (⇑
((TensorProduct.mk R (IsLocalRing.ResidueField R) M) 1) ∘ v)；Finsupp.linearCombi
nation R v。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.IsLocalRing.linearIndependent_of_flat`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   [inst_3 : IsLocalRing R] [Modul…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Finsupp.range_linearCombination`：range_linearCombination : LinearMap.ran
ge (linearCombination R v) = span R (range v)
· 使用定理 `IsLocalRing.span_eq_top_of_tmul_eq_basis`：span_eq_top_of_tmul_eq_basis [
Module.Finite R M] {ι} (f : ι -> M) (b : Basis ι k (k otimes[R] M)) (hb : forall
 i, 1 otimesₜ f i = b i) : Sub…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLocalRing.linearCombination_bijective_of_flat [Module.Finite R M] [Flat R M] {ι : Type u}
    (v : ι → M) (h : Function.Bijective (linearCombination k (TensorProduct.mk R k M 1 ∘ v))) :
    Function.Bijective (linearCombination R v) := by
  use linearIndependent_of_flat _ h.1
  rw [← LinearMap.range_eq_top, range_linearCombination]
  refine span_eq_top_of_tmul_eq_basis _ (.mk h.1 ?_) fun _ ↦ ?_
  · simpa only [top_le_iff, ← range_linearCombination, LinearMap.range_eq_top] using h.2
  · simp

@[stacks 00NZ]
/-
**Module.free_of_flat_of_isLocalRing** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：free_of_flat_of_isLocalRing [Module.Finite R P] [Flat R P] : Free R P
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Function.Surjective.comp_left`：∀ {α : Sort u} {β : Sort v} {γ : Sort w} 
{g : β → γ}, Function.Surjective g → Function.Surjective fun x => g ∘ x
· 使用定理 `TensorProduct.mk_surjective`：TensorProduct.mk_surjective (h : Function.S
urjective (algebraMap R S)) : Function.Surjective (TensorProduct.mk R S M 1)
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Module.IsLocalRing.linearIndependent_of_flat`：∀ {R : Type u_1} {M : Type
 u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   [inst_3 : IsLocalRing R] [Modul…
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `IsLocalRing.span_eq_top_of_tmul_eq_basis`：span_eq_top_of_tmul_eq_basis [
Module.Finite R M] {ι} (f : ι -> M) (b : Basis ι k (k otimes[R] M)) (hb : forall
 i, 1 otimesₜ f i = b i) : Sub…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
theorem free_of_flat_of_isLocalRing [Module.Finite R P] [Flat R P] : Free R P :=
  let w := Free.chooseBasis k (k ⊗[R] P)
  have ⟨v, eq⟩ := (TensorProduct.mk_surjective R P k Quotient.mk_surjective).comp_left w
  .of_basis <| .mk (IsLocalRing.linearIndependent_of_flat _ (eq ▸ w.linearIndependent)) <| by
    exact (span_eq_top_of_tmul_eq_basis _ w <| congr_fun eq).ge

/--
If `M → N → P → 0` is a presentation of `P` over a local ring `(R, 𝔪, k)` with
`M` finite and `N` finite free, then injectivity of `k ⊗ M → k ⊗ N` implies that `P` is free.
-/
/-
**Module.free_of_lTensor_residueField_injective** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e`。
形式化陈述：free_of_lTensor_residueField_injective (hg : Surjective g) (h : Exact f g)
 [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (hf : Function.Inject
ive (f.lTensor k)) : Module.Free R P
参数：hg : Surjective g；h : Exact f g；hf : Function.Injective (f.lTensor k)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.finitePresentation_of_free_of_surjective`：Module.finitePresentati
on_of_free_of_surjective [Module.Free R M] [Module.Finite R M] (l : M ->ₗ[R] N) 
(hl : Function.Surjective l) (hl' : (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Exact.linearMap_ker_eq`：∀ {R : Type u_1} {M : Type u_2} {N : Ty
pe u_4} {P : Type u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 
: AddCommMonoid N] [i…
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `Module.free_of_maximalIdeal_rTensor_injective`：free_of_maximalIdeal_rTen
sor_injective [Module.FinitePresentation R M] (H : Function.Injective ((𝔪).subty
pe.rTensor M)) : Module.Free R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_inj_iff_rTensor_inj`：lTensor_inj_iff_rTensor_inj : Fun
ction.Injective (lTensor M f) ↔ Function.Injective (rTensor M f)
· 使用定理 `lTensor_injective_of_exact_of_exact_of_rTensor_injective`：lTensor_inject
ive_of_exact_of_exact_of_rTensor_injective {M₁ M₂ M₃ N₁ N₂ N₃} [AddCommGroup M₁]
 [Module R M₁] [AddCommGroup M₂] [Module R M₂]…
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val

--- 原说明 ---
If `M → N → P → 0` is a presentation of `P` over a local ring `(R, 𝔪, k)` with
`M` finite and `N` finite free, then injectivity of `k ⊗ M → k ⊗ N` implies that
 `P` is free.
-/
theorem free_of_lTensor_residueField_injective (hg : Surjective g) (h : Exact f g)
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N]
    (hf : Function.Injective (f.lTensor k)) :
    Module.Free R P := by
  have := Module.finitePresentation_of_free_of_surjective g hg
    (by rw [h.linearMap_ker_eq, LinearMap.range_eq_map]; exact (Module.Finite.fg_top).map f)
  apply free_of_maximalIdeal_rTensor_injective
  rw [← LinearMap.lTensor_inj_iff_rTensor_inj]
  apply lTensor_injective_of_exact_of_exact_of_rTensor_injective
    h hg (LinearMap.exact_subtype_mkQ 𝔪) (Submodule.mkQ_surjective _)
    ((LinearMap.lTensor_inj_iff_rTensor_inj _ _).mp hf)
    (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)

end Module

/--
Given a linear map `l : M → N` over a local ring `(R, 𝔪, k)`
with `M` finite and `N` finite free,
`l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/
/-
**IsLocalRing.split_injective_iff_lTensor_residueField_injective** 是 Mathlib 中的一
个定理，位于命名空间 ``。
形式化陈述：IsLocalRing.split_injective_iff_lTensor_residueField_injective [IsLocalRin
g R] [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (l : M ->ₗ[R] N) 
: (exists l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueFi
eld R))
参数：l : M ->ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Module.free_of_lTensor_residueField_injective`：free_of_lTensor_residueFi
eld_injective (hg : Surjective g) (h : Exact f g) [Module.Finite R M] [Module.Fi
nite R N] [Module.Free R N] (hf : F…
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用引理 `LinearMap.exact_map_mkQ_range`：exact_map_mkQ_range (f : M ->ₗ[R] N) : Ex
act f (Submodule.mkQ (range f))
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用定理 `Function.Exact.split_tfae`：∀ {R : Type u_8} {M : Type u_9} {N : Type u_1
0} {P : Type u_11} [inst : Semiring R] [inst_1 : AddCommGroup M]   [inst_2 : Add
CommGroup N] [i…
· 使用引理 `LinearMap.exact_subtype_mkQ`：exact_subtype_mkQ (Q : Submodule R N) : Exa
ct (Submodule.subtype Q) (Submodule.mkQ Q)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.projective_lifting_property`：projective_lifting_property [h : Pro
jective R P] (f : M ->ₗ[R] N) (g : P ->ₗ[R] N) (hf : Function.Surjective f) : ex
ists h : P ->ₗ[R] M, f ∘…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Projective.of_split`：∀ {R : Type u_1} [inst : Semiring R] {P : Ty
pe u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   {M : Type u_3}
 [inst_3 : AddCo…
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `LinearMap.ker_rangeRestrict`：ker_rangeRestrict : ker f.rangeRestrict = k
er f
· 使用定理 `Submodule.range_subtype`：range_subtype : range p.subtype = p
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用定理 `Function.HasRightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f 
: α → β}, Function.HasRightInverse f → Function.Surjective f
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
Given a linear map `l : M → N` over a local ring `(R, 𝔪, k)`
with `M` finite and `N` finite free,
`l` is a split injection if and only if `k ⊗ l` is a (split) injection.
-/
theorem IsLocalRing.split_injective_iff_lTensor_residueField_injective [IsLocalRing R]
    [Module.Finite R M] [Module.Finite R N] [Module.Free R N] (l : M →ₗ[R] N) :
    (∃ l', l' ∘ₗ l = LinearMap.id) ↔ Function.Injective (l.lTensor (ResidueField R)) := by
  constructor
  · intro ⟨l', hl⟩
    have : l'.lTensor (ResidueField R) ∘ₗ l.lTensor (ResidueField R) = .id := by
      rw [← LinearMap.lTensor_comp, hl, LinearMap.lTensor_id]
    exact Function.HasLeftInverse.injective ⟨_, LinearMap.congr_fun this⟩
  · intro h
    -- By `Module.free_of_lTensor_residueField_injective`, `k ⊗ l` injective => `N ⧸ l(M)` free.
    have := Module.free_of_lTensor_residueField_injective l (LinearMap.range l).mkQ
      (Submodule.mkQ_surjective _) l.exact_map_mkQ_range h
    -- Hence `l(M)` is projective because `0 → l(M) → N → N ⧸ l(M) → 0` splits.
    have : Module.Projective R (LinearMap.range l) := by
      have := (Exact.split_tfae (LinearMap.exact_subtype_mkQ (LinearMap.range l))
        Subtype.val_injective (Submodule.mkQ_surjective _)).out 0 1
      obtain ⟨l', hl'⟩ := this.mp
         (Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _))
      exact Module.Projective.of_split _ _ hl'
    -- Then `0 → ker l → M → l(M) → 0` splits.
    obtain ⟨l', hl'⟩ : ∃ l', l' ∘ₗ (LinearMap.ker l).subtype = LinearMap.id := by
      have : Function.Exact (LinearMap.ker l).subtype
          (l.codRestrict (LinearMap.range l) (LinearMap.mem_range_self l)) := by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype]
      have := (Exact.split_tfae this
        Subtype.val_injective (fun ⟨x, y, e⟩ ↦ ⟨y, Subtype.ext e⟩)).out 0 1
      exact this.mp (Module.projective_lifting_property _ _ (fun ⟨x, y, e⟩ ↦ ⟨y, Subtype.ext e⟩))
    have : Module.Finite R (LinearMap.ker l) := by
      refine Module.Finite.of_surjective l' ?_
      exact Function.HasRightInverse.surjective ⟨_, DFunLike.congr_fun hl'⟩
    -- And tensoring with `k` preserves the injectivity of the first arrow.
    -- That is, `k ⊗ ker l → k ⊗ M` is also injective.
    have H : Function.Injective ((LinearMap.ker l).subtype.lTensor k) := by
      apply_fun (LinearMap.lTensor k) at hl'
      rw [LinearMap.lTensor_comp, LinearMap.lTensor_id] at hl'
      exact Function.HasLeftInverse.injective ⟨l'.lTensor k, DFunLike.congr_fun hl'⟩
    -- But by assumption `k ⊗ M → k ⊗ l(M)` is already injective, so `k ⊗ ker l = 0`.
    have : Subsingleton (k ⊗[R] LinearMap.ker l) := by
      refine (subsingleton_iff_forall_eq 0).mpr fun y ↦ H (h ?_)
      rw [map_zero, map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp,
        l.exact_subtype_ker_map.linearMap_comp_eq_zero, LinearMap.lTensor_zero,
        LinearMap.zero_apply]
    -- By Nakayama's lemma, `l` is injective.
    have : Function.Injective l := by
      rwa [← LinearMap.ker_eq_bot, ← Submodule.subsingleton_iff_eq_bot,
        ← IsLocalRing.subsingleton_tensorProduct (R := R)]
    -- Whence `M ≃ l(M)` is projective and the result follows.
    have := (Exact.split_tfae l.exact_map_mkQ_range this (Submodule.mkQ_surjective _)).out 0 1
    rw [← this]
    exact Module.projective_lifting_property _ _ (Submodule.mkQ_surjective _)

end

namespace Module

open Ideal TensorProduct Submodule

variable (R M) [Finite (MaximalSpectrum R)] [AddCommGroup M] [Module R M]

/-- If `M` is a finite flat module over a commutative semilocal ring `R` that has the same rank `n`
at every maximal ideal, then `M` is free of rank `n`. -/
/-
**Module.nonempty_basis_of_flat_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module`
。
形式化陈述：∀ (R : Type u_1) (M : Type u_2) [inst : CommRing R] [Finite (MaximalSpectr
um R)] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [Module.Finite R
 M] [Module.Flat R M] (n : ℕ),   (∀ (P : MaximalSpectrum R), Module.finrank (R ⧸
 P.asIdeal) (TensorProduct R (R ⧸ P.asIdeal) M) = n) →     Nonempty (Module.Basi
s (Fin n) R M)
参数：R : Type u_1；M : Type u_2；MaximalSpectrum R；n : ℕ；∀ (P : MaximalSpectrum R), 
Module.finrank (R ⧸ P.asIdeal) (TensorProduct R (R ⧸ P.asIdeal) M) = n；Module.Ba
sis (Fin n) R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `MaximalSpectrum.isMaximal`：∀ {R : Type u_1} [inst : CommSemiring R] (sel
f : MaximalSpectrum R), self.asIdeal.IsMaximal
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `bijective_of_isLocalized_maximal`：bijective_of_isLocalized_maximal (H : 
forall (P : Ideal R) [P.IsMaximal], Function.Bijective (map P.primeCompl (f P) (
g P) F)) : Function.Bi…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsLocalizedModuleFinsuppLinearMap`：∀ (R : Type u_1) [inst : CommSemi
ring R] (S : Submonoid R) (M : Type u_3) [inst_1 : AddCommMonoid M]   [inst_2 : 
_root_.Module R M] {M' : Ty…
· 使用定理 `instIsLocalizedModuleLinearMapOfIsLocalization`：∀ {R : Type u_1} [inst :
 CommSemiring R] (S : Submonoid R) (A : Type u_2) [inst_1 : CommSemiring A]   [i
nst_2 : Algebra R A] [IsLocalization…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalizedModule.map_linearCombination`：IsLocalizedModule.map_linearCom
bination {α : Type*} {v : α -> M} [IsLocalizedModule S f] : map S (mapRange.line
arMap (Algebra.linearMap R A)…
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `Module.IsLocalRing.linearCombination_bijective_of_flat`：∀ {R : Type u_1}
 {M : Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.M
odule R M]   [inst_3 : IsLocalRing R] [Modul…
· 使用定理 `Localization.AtPrime.isLocalRing`：∀ {R : Type u_1} [inst : CommSemiring 
R] (P : Ideal R) [hp : P.IsPrime], IsLocalRing (Localization P.primeCompl)
· 使用定理 `Module.Flat.instTensorProduct`：∀ {R : Type u} {M : Type v} {N : Type u_1
} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R
 M] [inst_3 : AddCo…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsLocalRing.instIsScalarTowerResidueField`：∀ (R : Type u_1) [inst : Comm
Ring R] [inst_1 : IsLocalRing R] {R₁ : Type u_4} {R₂ : Type u_5} [inst_2 : CommR
ing R₁]   [inst_3 : CommRing R₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.comp_bijective`：comp_bijective (f : α -> β) (e : β ≃ γ) : Bijectiv
e (e ∘ f) ↔ Bijective f
· 使用定理 `instIsScalarTowerQuotientIdealResidueField`：∀ {R : Type u_1} {A : Type u
_3} [inst : CommRing R] [inst_1 : CommRing A] [inst_2 : Algebra R A] (I : Ideal 
A)   [inst_3 : I.IsPrime], IsSca…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Finsupp.induction_linear`：induction_linear {motive : (ι ->₀ M) -> Prop} 
(f : ι ->₀ M) (zero : motive 0) (add : forall f g : ι ->₀ M, motive f -> motive 
g -> motive (f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
If `M` is a finite flat module over a commutative semilocal ring `R` that has th
e same rank `n`
at every maximal ideal, then `M` is free of rank `n`.
-/
@[stacks 02M9] theorem nonempty_basis_of_flat_of_finrank_eq [Module.Finite R M] [Flat R M]
    (n : ℕ) (rk : ∀ P : MaximalSpectrum R, finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = n) :
    Nonempty (Basis (Fin n) R M) := by
  let := @Quotient.field
  /- For every maximal ideal `P`, `R⧸P ⊗[R] M` is an `n`-dimensional vector space over the field
    `R⧸P` by assumption, so we can choose a basis `b' P` indexed by `Fin n`. -/
  have b' (P) := Module.finBasisOfFinrankEq _ _ (rk P)
  /- By Chinese remainder theorem for modules, there exist `n` elements `b i : M` that reduces
    to `b' P i` modulo each maximal ideal `P`. -/
  choose b hb using fun i ↦ pi_tensorProductMk_quotient_surjective M _
    (fun _ _ ne ↦ isCoprime_of_isMaximal (MaximalSpectrum.ext_iff.ne.mp ne)) (b' · i)
  /- It suffices to show the linear map `Rⁿ → M` induced by `b` is bijective, for which
    it suffices to show `Rₚⁿ → Rₚ ⊗[R] M` is bijective for each maximal ideal `P`. -/
  refine ⟨⟨.symm <| .ofBijective (Finsupp.linearCombination R b) <| bijective_of_isLocalized_maximal
    _ (fun P _ ↦ Finsupp.mapRange.linearMap (Algebra.linearMap R (Localization P.primeCompl)))
    _ (fun P _ ↦ TensorProduct.mk R (Localization P.primeCompl) M 1) _ fun P _ ↦ ?_⟩⟩
  rw [IsLocalizedModule.map_linearCombination, LinearMap.coe_restrictScalars]
  /- Since `M` is finite flat, it suffices to show
    `(Rₚ⧸PRₚ)ⁿ → Rₚ⧸PRₚ ⊗[Rₚ] Rₚ ⊗[R] M ≃ Rₚ⧸PRₚ ⊗[R⧸P] R⧸P ⊗[R] M` is bijective,
    which follows from that `(R⧸P)ⁿ → R⧸P ⊗[R] M` is bijective. -/
  apply IsLocalRing.linearCombination_bijective_of_flat
  rw [← (AlgebraTensorModule.cancelBaseChange _ _ P.ResidueField ..).comp_bijective,
    ← (AlgebraTensorModule.cancelBaseChange R (R ⧸ P) P.ResidueField ..).symm.comp_bijective]
  convert! ((b' ⟨P, ‹_›⟩).repr.lTensor _ ≪≫ₗ finsuppScalarRight _ _ P.ResidueField _).symm.bijective
  refine funext fun r ↦ Finsupp.induction_linear r (by simp) (by simp +contextual) fun _ _ ↦ ?_
  simp [smul_tmul', ← funext_iff.mp (hb _)]
/-
**Module.free_of_flat_of_finrank_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ (R : Type u_1) (M : Type u_2) [inst : CommRing R] [Finite (MaximalSpectr
um R)] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [Module.Finite R
 M] [Module.Flat R M] (n : ℕ),   (∀ (P : MaximalSpectrum R), Module.finrank (R ⧸
 P.asIdeal) (TensorProduct R (R ⧸ P.asIdeal) M) = n) → Module.Free R M
参数：R : Type u_1；M : Type u_2；MaximalSpectrum R；n : ℕ；∀ (P : MaximalSpectrum R), 
Module.finrank (R ⧸ P.asIdeal) (TensorProduct R (R ⧸ P.asIdeal) M) = n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.nonempty_basis_of_flat_of_finrank_eq`：∀ (R : Type u_1) (M : Type 
u_2) [inst : CommRing R] [Finite (MaximalSpectrum R)] [inst_2 : AddCommGroup M] 
  [inst_3 : _root_.Module R M] [M…
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
@[stacks 02M9] theorem free_of_flat_of_finrank_eq [Module.Finite R M] [Flat R M]
    (n : ℕ) (rk : ∀ P : MaximalSpectrum R, finrank (R ⧸ P.1) ((R ⧸ P.1) ⊗[R] M) = n) :
    Free R M :=
  have ⟨b⟩ := nonempty_basis_of_flat_of_finrank_eq R M n rk
  .of_basis b

end Module

