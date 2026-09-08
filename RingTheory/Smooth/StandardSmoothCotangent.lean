/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth
public import Mathlib.RingTheory.Smooth.Kaehler
public import Mathlib.RingTheory.Etale.Basic

/-!
# Cotangent complex of a submersive presentation

Let `P` be a submersive presentation of `S` as an `R`-algebra and
denote by `I` the kernel `R[X] → S`. We show

- `SubmersivePresentation.free_cotangent`: `I ⧸ I ^ 2` is `S`-free on the classes of `P.relation i`.
- `SubmersivePresentation.subsingleton_h1Cotangent`: `H¹(L_{S/R}) = 0`.
- `SubmersivePresentation.free_kaehlerDifferential`: `Ω[S⁄R]` is `S`-free on the images of `dxᵢ`
  where `i ∉ Set.range P.map`.
- `SubmersivePresentation.rank_kaehlerDifferential`: If `S` is non-trivial, the rank of
  `Ω[S⁄R]` is the dimension of `P`.

We also provide the corresponding instances for standard smooth algebras as corollaries.

We keep the notation `I = ker(R[X] → S)` in all docstrings of this file.
-/

@[expose] public section

namespace Algebra

variable {R S ι σ : Type*} [CommRing R] [CommRing S] [Algebra R S]

section

open Extension Module MvPolynomial

namespace PreSubmersivePresentation

/--
Given a pre-submersive presentation, this is the composition
`I ⧸ I ^ 2 → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second direct sum runs over
all `i : σ` induced by the injection `P.map : σ → ι`.

If `P` is submersive, this is an isomorphism. See `SubmersivePresentation.cotangentEquiv`.
-/
/-
**Algebra.PreSubmersivePresentation.cotangentComplexAux** 是 Mathlib 中的一个定义，位于命名空
间 `Algebra.PreSubmersivePresentation`。
形式化陈述：cotangentComplexAux [Finite σ] (P : PreSubmersivePresentation R S ι σ) : P
.toExtension.Cotangent ->ₗ[S] σ -> S
参数：P : PreSubmersivePresentation R S ι σ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…

--- 原说明 ---
Given a pre-submersive presentation, this is the composition
`I ⧸ I ^ 2 → ⊕ S dxᵢ → ⊕ S dxᵢ` where the second direct sum runs over
all `i : σ` induced by the injection `P.map : σ → ι`.

If `P` is submersive, this is an isomorphism. See `SubmersivePresentation.cotang
entEquiv`.
-/
noncomputable def cotangentComplexAux [Finite σ] (P : PreSubmersivePresentation R S ι σ) :
    P.toExtension.Cotangent →ₗ[S] σ → S :=
  Finsupp.linearEquivFunOnFinite S S σ ∘ₗ Finsupp.lcomapDomain _ P.map_inj ∘ₗ
    P.cotangentSpaceBasis.repr.toLinearMap ∘ₗ P.toExtension.cotangentComplex

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.PreSubmersivePresentation.cotangentComplexAux_apply** 是 Mathlib 中的一个引理
，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：cotangentComplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι 
σ) (x : P.ker) (i : σ) : P.cotangentComplexAux (Cotangent.mk x) i = (aeval P.val
) (pderiv (P.map i) x.val)
参数：P : PreSubmersivePresentation R S ι σ；x : P.ker；i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Generators.cotangentSpaceBasis_repr_tmul`：cotangentSpaceBasis_re
pr_tmul (r x i) : P.cotangentSpaceBasis.repr (r otimesₜ[P.Ring] KaehlerDifferent
ial.D R P.Ring x : _) i = r * aeval P.…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentComplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι σ)
    (x : P.ker) (i : σ) :
    P.cotangentComplexAux (Cotangent.mk x) i = (aeval P.val) (pderiv (P.map i) x.val) := by
  dsimp only [cotangentComplexAux, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    cotangentComplex_mk]
  simp only [Generators.toExtension_Ring, Finsupp.lcomapDomain_apply,
    Finsupp.linearEquivFunOnFinite_apply, Finsupp.comapDomain_apply,
    Generators.cotangentSpaceBasis_repr_tmul, one_mul]
/-
**Algebra.PreSubmersivePresentation.cotangentComplexAux_zero_iff** 是 Mathlib 中的一
个引理，位于命名空间 `Algebra.PreSubmersivePresentation`。
形式化陈述：cotangentComplexAux_zero_iff [Finite σ] {P : PreSubmersivePresentation R S
 ι σ} (x : P.ker) : P.cotangentComplexAux (Cotangent.mk x) = 0 ↔ forall i : σ, (
aeval P.val) (pderiv (P.map i) x.val) = 0
参数：x : P.ker。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `Algebra.PreSubmersivePresentation.cotangentComplexAux_apply`：cotangentCo
mplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι σ) (x : P.ker) (i
 : σ) : P.cotangentComplexAux (Cotangent.mk x) i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma cotangentComplexAux_zero_iff [Finite σ] {P : PreSubmersivePresentation R S ι σ} (x : P.ker) :
    P.cotangentComplexAux (Cotangent.mk x) = 0 ↔
      ∀ i : σ, (aeval P.val) (pderiv (P.map i) x.val) = 0 := by
  rw [funext_iff]
  simp_rw [cotangentComplexAux_apply, Pi.zero_apply]

end PreSubmersivePresentation

namespace SubmersivePresentation

variable [Finite σ] (P : SubmersivePresentation R S ι σ)

set_option backward.isDefEq.respectTransparency false in
/-
**Algebra.SubmersivePresentation.cotangentComplexAux_injective** 是 Mathlib 中的一个引
理，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：cotangentComplexAux_injective : Function.Injective P.cotangentComplexAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Algebra.Extension.Cotangent.mk_surjective`：∀ {R : Type u} {S : Type v} [
inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   {P : Algebra.E
xtension R S}, Function.Surject…
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
· 使用定理 `Algebra.Extension.Cotangent.mk_eq_zero_iff`：∀ {R : Type u} {S : Type v} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.Ex
tension R S}   (x : ↥P.ker), Alg…
· 使用定理 `Algebra.Presentation.span_range_relation_eq_ker`：∀ {R : Type u} {S : Typ
e v} {ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2
 : Algebra R S]   (self : Algebra.Pre…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finsupp.mem_ideal_span_range_iff_exists_finsupp`：Finsupp.mem_ideal_span_
range_iff_exists_finsupp {x : R} {v : α -> R} : x in Ideal.span (Set.range v) ↔ 
exists c : α ->₀ R, (c.sum fun i a =>…
· 使用引理 `Algebra.PreSubmersivePresentation.cotangentComplexAux_zero_iff`：cotangen
tComplexAux_zero_iff [Finite σ] {P : PreSubmersivePresentation R S ι σ} (x : P.k
er) : P.cotangentComplexAux (Cotangent.mk x) = 0 ↔ f…
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `Derivation.instAddMonoidHomClass`：∀ {R : Type u_1} {A : Type u_2} {M : T
ype u_4} [inst : CommSemiring R] [inst_1 : CommSemiring A]   [inst_2 : AddCommMo
noid M] [inst_3 : Alge…
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
（共 48 条，此处仅展示前 30 条）
-/
lemma cotangentComplexAux_injective : Function.Injective P.cotangentComplexAux := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨(x : P.ker), rfl⟩ := Cotangent.mk_surjective x
  rw [Submodule.mem_bot, Cotangent.mk_eq_zero_iff]
  rw [LinearMap.mem_ker, P.cotangentComplexAux_zero_iff] at hx
  have : x.val ∈ Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker]
    exact x.property
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.mp this
  have heq (i : σ) :
      aeval P.val (pderiv (P.map i) <| c.sum fun i a ↦ a * P.relation i) = 0 := by
    rw [hc]
    apply hx
  simp only [Finsupp.sum, map_sum, Derivation.leibniz, smul_eq_mul, map_add, map_mul,
    Presentation.aeval_val_relation, zero_mul, add_zero] at heq
  have heq2 : ∑ i ∈ c.support,
      aeval P.val (c i) • (fun j ↦ aeval P.val (pderiv (P.map j) (P.relation i))) = 0 := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    apply heq
  have (i : σ) : aeval P.val (c i) = 0 := by
    have := P.linearIndependent_aeval_val_pderiv_relation
    rw [linearIndependent_iff''] at this
    have := this c.support (fun i ↦ aeval P.val (c i))
      (by intro i; simp only [Finsupp.mem_support_iff, ne_eq, not_not]; intro h; simp [h]) heq2
    exact this i
  change _ ∈ P.ker ^ 2
  rw [← hc]
  apply Ideal.sum_mem
  intro i hi
  rw [pow_two]
  apply Ideal.mul_mem_mul
  · rw [P.ker_eq_ker_aeval_val]
    simpa using this i
  · exact P.relation_mem_ker i

set_option backward.isDefEq.respectTransparency.types false in
/-
**Algebra.SubmersivePresentation.cotangentComplexAux_surjective** 是 Mathlib 中的一个
引理，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：cotangentComplexAux_surjective : Function.Surjective P.cotangentComplexAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `Algebra.Presentation.relation_mem_ker`：relation_mem_ker (i) : P.relation
 i in P.ker
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Algebra.PreSubmersivePresentation.cotangentComplexAux_apply`：cotangentCo
mplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι σ) (x : P.ker) (i
 : σ) : P.cotangentComplexAux (Cotangent.mk x) i …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Algebra.SubmersivePresentation.basisDeriv_apply`：basisDeriv_apply (i j :
 σ) : P.basisDeriv i j = (aeval P.val) (pderiv (P.map j) (P.relation i))
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cotangentComplexAux_surjective : Function.Surjective P.cotangentComplexAux := by
  rw [← LinearMap.range_eq_top, _root_.eq_top_iff, ← P.basisDeriv.span_eq, Submodule.span_le]
  rintro - ⟨i, rfl⟩
  use Cotangent.mk ⟨P.relation i, P.relation_mem_ker i⟩
  ext j
  rw [P.cotangentComplexAux_apply]
  simp

/-- The isomorphism of `S`-modules between `I ⧸ I ^ 2` and `σ → S` given
by `P.relation i ↦ ∂ⱼ (P.relation i)`. -/
@[simps! apply]
/-
**Algebra.SubmersivePresentation.cotangentEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.SubmersivePresentation`。
形式化陈述：cotangentEquiv : P.toExtension.Cotangent ≃ₗ[S] σ -> S
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism of `S`-modules between `I ⧸ I ^ 2` and `σ → S` given
by `P.relation i ↦ ∂ⱼ (P.relation i)`.
-/
noncomputable def cotangentEquiv : P.toExtension.Cotangent ≃ₗ[S] σ → S :=
  LinearEquiv.ofBijective _ ⟨P.cotangentComplexAux_injective, P.cotangentComplexAux_surjective⟩
/-
**Algebra.SubmersivePresentation.cotangentComplex_injective** 是 Mathlib 中的一个引理，位
于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：cotangentComplex_injective : Function.Injective P.toExtension.cotangentCom
plex
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.SubmersivePresentation.cotangentComplexAux_injective`：cotangentC
omplexAux_injective : Function.Injective P.cotangentComplexAux
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…
-/
lemma cotangentComplex_injective : Function.Injective P.toExtension.cotangentComplex := by
  have := P.cotangentComplexAux_injective
  simp only [PreSubmersivePresentation.cotangentComplexAux, LinearMap.coe_comp,
    LinearEquiv.coe_coe] at this
  exact Function.Injective.of_comp (Function.Injective.of_comp <| Function.Injective.of_comp this)

/-- If `P` is a submersive presentation, `H¹` of the associated cotangent complex vanishes. -/
/-
**Algebra.SubmersivePresentation.subsingleton_h1Cotangent** 是 Mathlib 中的一个实例，位于命
名空间 `Algebra.SubmersivePresentation`。
形式化陈述：subsingleton_h1Cotangent : Subsingleton P.toExtension.H1Cotangent
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.Extension.subsingleton_h1Cotangent`：subsingleton_h1Cotangent (P 
: Extension R S) : Subsingleton P.H1Cotangent ↔ Function.Injective P.cotangentCo
mplex
· 使用引理 `Algebra.SubmersivePresentation.cotangentComplex_injective`：cotangentComp
lex_injective : Function.Injective P.toExtension.cotangentComplex

--- 原说明 ---
If `P` is a submersive presentation, `H¹` of the associated cotangent complex va
nishes.
-/
instance subsingleton_h1Cotangent : Subsingleton P.toExtension.H1Cotangent := by
  rw [Algebra.Extension.subsingleton_h1Cotangent]
  exact cotangentComplex_injective P

/-- The classes of `P.relation i` form a basis of `I ⧸ I ^ 2`. -/
@[stacks 00T7 "(3)"]
/-
**Algebra.SubmersivePresentation.basisCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
ra.SubmersivePresentation`。
形式化陈述：basisCotangent : Basis σ S P.toExtension.Cotangent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The classes of `P.relation i` form a basis of `I ⧸ I ^ 2`.
-/
noncomputable def basisCotangent : Basis σ S P.toExtension.Cotangent :=
  P.basisDeriv.map P.cotangentEquiv.symm
/-
**Algebra.SubmersivePresentation.basisCotangent_apply** 是 Mathlib 中的一个引理，位于命名空间 
`Algebra.SubmersivePresentation`。
形式化陈述：basisCotangent_apply (r : σ) : P.basisCotangent r = Extension.Cotangent.mk
 ⟨P.relation r, P.relation_mem_ker r⟩
参数：r : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Algebra.Presentation.relation_mem_ker`：relation_mem_ker (i) : P.relation
 i in P.ker
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用引理 `Algebra.SubmersivePresentation.basisDeriv_apply`：basisDeriv_apply (i j :
 σ) : P.basisDeriv i j = (aeval P.val) (pderiv (P.map j) (P.relation i))
· 使用引理 `Algebra.PreSubmersivePresentation.cotangentComplexAux_apply`：cotangentCo
mplexAux_apply [Finite σ] (P : PreSubmersivePresentation R S ι σ) (x : P.ker) (i
 : σ) : P.cotangentComplexAux (Cotangent.mk x) i …
-/
lemma basisCotangent_apply (r : σ) :
    P.basisCotangent r = Extension.Cotangent.mk ⟨P.relation r, P.relation_mem_ker r⟩ := by
  symm
  apply P.cotangentEquiv.injective
  ext
  simp_rw [basisCotangent, Basis.map_apply, LinearEquiv.apply_symm_apply, basisDeriv_apply]
  apply P.toPreSubmersivePresentation.cotangentComplexAux_apply _ _

@[stacks 00T7 "(3)"]
/-
**Algebra.SubmersivePresentation.free_cotangent** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
ra.SubmersivePresentation`。
形式化陈述：free_cotangent : Module.Free S P.toExtension.Cotangent
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
-/
instance free_cotangent : Module.Free S P.toExtension.Cotangent :=
  Module.Free.of_basis P.basisCotangent

/--
If `P` is a submersive presentation, this is the section of the map
`I ⧸ I ^ 2 → ⊕ S dxᵢ` given by projecting to the summands indexed by `σ` and composing with the
inverse of `P.cotangentEquiv`.

By `SubmersivePresentation.sectionCotangent_comp` this is indeed a section.
-/
/-
**Algebra.SubmersivePresentation.sectionCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Alg
ebra.SubmersivePresentation`。
形式化陈述：sectionCotangent : P.toExtension.CotangentSpace ->ₗ[S] P.toExtension.Cotan
gent
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a submersive presentation, this is the section of the map
`I ⧸ I ^ 2 → ⊕ S dxᵢ` given by projecting to the summands indexed by `σ` and com
posing with the
inverse of `P.cotangentEquiv`.

By `SubmersivePresentation.sectionCotangent_comp` this is indeed a section.
-/
noncomputable def sectionCotangent : P.toExtension.CotangentSpace →ₗ[S] P.toExtension.Cotangent :=
  (cotangentEquiv P).symm ∘ₗ (Finsupp.linearEquivFunOnFinite S S σ).toLinearMap ∘ₗ
    Finsupp.lcomapDomain _ P.map_inj ∘ₗ P.cotangentSpaceBasis.repr.toLinearMap
/-
**Algebra.SubmersivePresentation.sectionCotangent_eq_iff** 是 Mathlib 中的一个定理，位于命名
空间 `Algebra.SubmersivePresentation`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : Finite σ] (P : 
Algebra.SubmersivePresentation R S ι σ)   (x : P.toExtension.CotangentSpace) (y 
: P.toExtension.Cotangent),   P.sectionCotangent x = y ↔ ∀ (i : σ), (P.cotangent
SpaceBasis.repr x) (P.map i) = P.cotangentComplexAux y i
参数：P : Algebra.SubmersivePresentation R S ι σ；x : P.toExtension.CotangentSpace；y
 : P.toExtension.Cotangent；i : σ；P.cotangentSpaceBasis.repr x；P.map i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finsupp.lcomapDomain_apply`：∀ {α : Type u_1} {M : Type u_2} {R : Type u_
5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M]
 {β : Type u_9} …
· 使用定理 `Finsupp.linearEquivFunOnFinite_apply`：∀ (R : Type u_9) (M : Type u_11) (
α : Type u_12) [inst : Finite α] [inst_1 : AddCommMonoid M] [inst_2 : Semiring R
]   [inst_3 : _root_.Modul…
· 使用定理 `Algebra.SubmersivePresentation.cotangentEquiv_apply`：∀ {R : Type u_1} {S
 : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : CommRing R] [inst_1 : CommRin
g S]   [inst_2 : Algebra R S] [inst_3 : F…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sectionCotangent_eq_iff (x : P.toExtension.CotangentSpace) (y : P.toExtension.Cotangent) :
    sectionCotangent P x = y ↔
      ∀ i : σ, P.cotangentSpaceBasis.repr x (P.map i) = (P.cotangentComplexAux y) i := by
  simp only [sectionCotangent, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply]
  rw [← (cotangentEquiv P).injective.eq_iff, funext_iff, LinearEquiv.apply_symm_apply]
  simp
/-
**Algebra.SubmersivePresentation.sectionCotangent_comp** 是 Mathlib 中的一个定理，位于命名空间
 `Algebra.SubmersivePresentation`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : Comm
Ring R] [inst_1 : CommRing S]   [inst_2 : Algebra R S] [inst_3 : Finite σ] (P : 
Algebra.SubmersivePresentation R S ι σ),   P.sectionCotangent ∘ₗ P.toExtension.c
otangentComplex = LinearMap.id
参数：P : Algebra.SubmersivePresentation R S ι σ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.SubmersivePresentation.sectionCotangent_eq_iff`：∀ {R : Type u_1}
 {S : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : CommRing R] [inst_1 : Comm
Ring S]   [inst_2 : Algebra R S] [inst_3 : F…
-/
lemma sectionCotangent_comp :
    sectionCotangent P ∘ₗ P.toExtension.cotangentComplex = LinearMap.id := by
  ext : 1
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
  rw [sectionCotangent_eq_iff]
  intro i
  rfl
/-
**Algebra.SubmersivePresentation.sectionCotangent_zero_of_notMem_range** 是 Mathl
ib 中的一个引理，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：sectionCotangent_zero_of_notMem_range (i : ι) (hi : i ∉ Set.range P.map) :
 (sectionCotangent P) (P.cotangentSpaceBasis i) = 0
参数：i : ι；hi : i ∉ Set.range P.map。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.repr_self`：repr_self : b.repr (b i) = Finsupp.single i 1
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
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
· 使用定理 `Algebra.SubmersivePresentation.sectionCotangent_eq_iff`：∀ {R : Type u_1}
 {S : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : CommRing R] [inst_1 : Comm
Ring S]   [inst_2 : Algebra R S] [inst_3 : F…
-/
lemma sectionCotangent_zero_of_notMem_range (i : ι) (hi : i ∉ Set.range P.map) :
    (sectionCotangent P) (P.cotangentSpaceBasis i) = 0 := by
  classical
  contrapose hi
  rw [sectionCotangent_eq_iff] at hi
  simp only [Basis.repr_self, map_zero, Pi.zero_apply, Finsupp.single_apply] at hi
  grind

/--
Given a submersive presentation of `S` as `R`-algebra, any indexing type `κ` complementary to
the `σ` in `ι` indexes a basis of `Ω[S⁄R]`.
See `SubmersivePresentation.basisKaehler` for the special case `κ = (Set.range P.map)ᶜ`.
-/
/-
**Algebra.SubmersivePresentation.basisKaehlerOfIsCompl** 是 Mathlib 中的一个定义，位于命名空间
 `Algebra.SubmersivePresentation`。
形式化陈述：basisKaehlerOfIsCompl {κ : Type*} {f : κ -> ι} (hf : Function.Injective f)
 (hcompl : IsCompl (Set.range f) (Set.range P.map)) : Basis κ S Ω[S⁄R]
参数：hf : Function.Injective f；hcompl : IsCompl (Set.range f) (Set.range P.map)。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.SubmersivePresentation.sectionCotangent_comp`：∀ {R : Type u_1} {
S : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : F…

--- 原说明 ---
Given a submersive presentation of `S` as `R`-algebra, any indexing type `κ` com
plementary to
the `σ` in `ι` indexes a basis of `Ω[S⁄R]`.
See `SubmersivePresentation.basisKaehler` for the special case `κ = (Set.range P
.map)ᶜ`.
-/
noncomputable def basisKaehlerOfIsCompl {κ : Type*} {f : κ → ι}
    (hf : Function.Injective f) (hcompl : IsCompl (Set.range f) (Set.range P.map)) :
    Basis κ S Ω[S⁄R] := by
  apply P.cotangentSpaceBasis.ofSplitExact (sectionCotangent_comp P)
    Extension.exact_cotangentComplex_toKaehler Extension.toKaehler_surjective hf (b := P.map)
  · intro i
    apply sectionCotangent_zero_of_notMem_range _ _
    simp [← hcompl.compl_eq]
  · simp only [sectionCotangent, LinearMap.coe_comp, Function.comp_assoc, LinearEquiv.coe_coe]
    apply LinearIndependent.map' _ _ P.cotangentEquiv.symm.ker
    convert! (Pi.basisFun S σ).linearIndependent
    classical
    ext i j
    simp only [Function.comp_apply, Basis.repr_self, Finsupp.linearEquivFunOnFinite_apply,
      Pi.basisFun_apply]
    simp [Finsupp.single_eq_pi_single]
  · exact hcompl.2

@[simp]
/-
**Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply** 是 Mathlib 中的一个引理，
位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：basisKaehlerOfIsCompl_apply {κ : Type*} {f : κ -> ι} (hf : Function.Inject
ive f) (hcompl : IsCompl (Set.range f) (Set.range P.map)) (k : κ) : P.basisKaehl
erOfIsCompl hf hcompl k = KaehlerDifferential.D _ _ (P.val (f k))
参数：hf : Function.Injective f；hcompl : IsCompl (Set.range f) (Set.range P.map)；k 
: κ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.SubmersivePresentation.sectionCotangent_comp`：∀ {R : Type u_1} {
S : Type u_2} {ι : Type u_3} {σ : Type u_4} [inst : CommRing R] [inst_1 : CommRi
ng S]   [inst_2 : Algebra R S] [inst_3 : F…
· 使用引理 `Module.Basis.ofSplitExact_apply`：Module.Basis.ofSplitExact_apply (hg : F
unction.Surjective g) (v : Basis ι R M) (hainj : Function.Injective a) (hsa : fo
rall i, s (v (a i)) =…
· 使用引理 `Algebra.Generators.toKaehler_cotangentSpaceBasis`：toKaehler_cotangentSpa
ceBasis (i) : P.toExtension.toKaehler (P.cotangentSpaceBasis i) = D R S (P.val i
)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basisKaehlerOfIsCompl_apply {κ : Type*} {f : κ → ι}
    (hf : Function.Injective f) (hcompl : IsCompl (Set.range f) (Set.range P.map)) (k : κ) :
    P.basisKaehlerOfIsCompl hf hcompl k = KaehlerDifferential.D _ _ (P.val (f k)) := by
  simp [basisKaehlerOfIsCompl]

/-- Given a submersive presentation of `S` as `R`-algebra, the images of `dxᵢ`
for `i` in the complement of `σ` in `ι` form a basis of `Ω[S⁄R]`. -/
@[stacks 00T7 "(2)"]
/-
**Algebra.SubmersivePresentation.basisKaehler** 是 Mathlib 中的一个定义，位于命名空间 `Algebra
.SubmersivePresentation`。
形式化陈述：basisKaehler : Basis ((Set.range P.map)ᶜ : Set _) S Ω[S⁄R]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a submersive presentation of `S` as `R`-algebra, the images of `dxᵢ`
for `i` in the complement of `σ` in `ι` form a basis of `Ω[S⁄R]`.
-/
noncomputable def basisKaehler :
    Basis ((Set.range P.map)ᶜ : Set _) S Ω[S⁄R] :=
  P.basisKaehlerOfIsCompl Subtype.val_injective <| by
    rw [Subtype.range_coe_subtype]
    exact IsCompl.symm isCompl_compl

@[simp]
/-
**Algebra.SubmersivePresentation.basisKaehler_apply** 是 Mathlib 中的一个引理，位于命名空间 `A
lgebra.SubmersivePresentation`。
形式化陈述：basisKaehler_apply (k : ((Set.range P.map)ᶜ : Set _)) : P.basisKaehler k =
 KaehlerDifferential.D _ _ (P.val k)
参数：k : ((Set.range P.map)ᶜ : Set _)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Algebra.SubmersivePresentation.basisKaehlerOfIsCompl_apply`：basisKaehler
OfIsCompl_apply {κ : Type*} {f : κ -> ι} (hf : Function.Injective f) (hcompl : I
sCompl (Set.range f) (Set.range P.map)) (k : κ) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basisKaehler_apply (k : ((Set.range P.map)ᶜ : Set _)) :
    P.basisKaehler k = KaehlerDifferential.D _ _ (P.val k) := by
  simp [basisKaehler]

/-- If `P` is a submersive presentation of `S` as an `R`-algebra, `Ω[S⁄R]` is free. -/
@[stacks 00T7 "(2)"]
/-
**Algebra.SubmersivePresentation.free_kaehlerDifferential** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.SubmersivePresentation`。
形式化陈述：free_kaehlerDifferential (P : SubmersivePresentation R S ι σ) : Module.Fre
e S Ω[S⁄R]
参数：P : SubmersivePresentation R S ι σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_basis`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {ι : Type w}   (b : Module
.Basis ι R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
If `P` is a submersive presentation of `S` as an `R`-algebra, `Ω[S⁄R]` is free.
-/
theorem free_kaehlerDifferential (P : SubmersivePresentation R S ι σ) :
    Module.Free S Ω[S⁄R] :=
  Module.Free.of_basis P.basisKaehler

attribute [local instance] Fintype.ofFinite in
/-- If `P` is a submersive presentation of `S` as an `R`-algebra and `S` is nontrivial,
`Ω[S⁄R]` is free of rank the dimension of `P`, i.e. the number of generators minus the number
of relations. -/
/-
**Algebra.SubmersivePresentation.rank_kaehlerDifferential** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.SubmersivePresentation`。
形式化陈述：rank_kaehlerDifferential [Nontrivial S] [Finite ι] (P : SubmersivePresenta
tion R S ι σ) : Module.rank S Ω[S⁄R] = P.dimension
参数：P : SubmersivePresentation R S ι σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Fintype.card_compl_set`：Fintype.card_compl_set [Fintype α] (s : Set α) [
Fintype s] [Fintype (↥sᶜ : Sort _)] : Fintype.card (↥sᶜ : Sort _) = Fintype.card
 α - Fintype…
· 使用定理 `Set.card_range_of_injective`：card_range_of_injective [Fintype α] {f : α 
-> β} (hf : Injective f) [Fintype (range f)] : Fintype.card (range f) = Fintype.
card α
· 使用定理 `Algebra.PreSubmersivePresentation.map_inj`：∀ {R : Type u} {S : Type v} {
ι : Type w} {σ : Type t} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Alg
ebra R S]   (self : Algebra.Pre…
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `P` is a submersive presentation of `S` as an `R`-algebra and `S` is nontrivi
al,
`Ω[S⁄R]` is free of rank the dimension of `P`, i.e. the number of generators min
us the number
of relations.
-/
theorem rank_kaehlerDifferential [Nontrivial S] [Finite ι]
    (P : SubmersivePresentation R S ι σ) : Module.rank S Ω[S⁄R] = P.dimension := by
  simp only [rank_eq_card_basis P.basisKaehler, Fintype.card_compl_set,
    Presentation.dimension, Nat.card_eq_fintype_card, Set.card_range_of_injective P.map_inj]

end SubmersivePresentation

section LocalizationAway

variable (r : R) [IsLocalization.Away r S]

/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module.Free S (Generators.localizationAway S r).toExtension.Cotangent :=
  inferInstanceAs <|
    Module.Free S ((SubmersivePresentation.localizationAway S r).toExtension.Cotangent)

variable (S) in
/-- The image of `g * X - 1` in `I/I²` if `I` is the kernel of the canonical presentation
of the localization of `S` away from `g`. -/
noncomputable
/-
**Algebra.Generators.cMulXSubOneCotangent** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Gen
erators`。
形式化陈述：{R : Type u_1} →   (S : Type u_2) →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           (r : R) → [inst_3 :
 IsLocalization.Away r S] → (Algebra.Generators.localizationAway S r).toExtensio
n.Cotangent
参数：S : Type u_2；r : R；Algebra.Generators.localizationAway S r。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.Generators.C_mul_X_sub_one_mem_ker`：∀ {R : Type u} {S : Type v} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (r : R)   [inst
_3 : IsLocalization.Away r S],  …
-/
abbrev Generators.cMulXSubOneCotangent : (Generators.localizationAway S r).toExtension.Cotangent :=
  Extension.Cotangent.mk ⟨C r * X () - 1, C_mul_X_sub_one_mem_ker _⟩
/-
**Algebra.Generators.cMulXSubOneCotangent_eq** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
Generators`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (r : R)   [inst_3 : IsLocalization.Away r S],   Algebra.G
enerators.cMulXSubOneCotangent S r =     Algebra.Extension.Cotangent.mk ⟨MvPolyn
omial.C r * MvPolynomial.X () - 1, ⋯⟩
参数：r : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Generators.cMulXSubOneCotangent_eq :
    cMulXSubOneCotangent S r = Extension.Cotangent.mk ⟨C r * X () - 1, C_mul_X_sub_one_mem_ker _⟩ :=
  rfl
/-
**Algebra.SubmersivePresentation.basisCotangent_localizationAway_apply** 是 Mathl
ib 中的一个定理，位于命名空间 `Algebra.SubmersivePresentation`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (r : R)   [inst_3 : IsLocalization.Away r S] (x : Unit), 
  (Algebra.SubmersivePresentation.localizationAway S r).basisCotangent x = Algeb
ra.Generators.cMulXSubOneCotangent S r
参数：r : R；x : Unit；Algebra.SubmersivePresentation.localizationAway S r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.SubmersivePresentation.basisCotangent_apply`：basisCotangent_appl
y (r : σ) : P.basisCotangent r = Extension.Cotangent.mk ⟨P.relation r, P.relatio
n_mem_ker r⟩
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma SubmersivePresentation.basisCotangent_localizationAway_apply (x : Unit) :
    (SubmersivePresentation.localizationAway S r).basisCotangent x =
      Generators.cMulXSubOneCotangent S r :=
  basisCotangent_apply _ _

variable (S) in
/--
The basis of `(g * X - 1) / (g * X - 1)²` given by the image of `g * X - 1`.

This is def-eq to `(SubmersivePresentation.localizationAway T g).basisCotangent`, but
```
(SubmersivePresentation.localizationAway T g).toExtension =
  (Generators.localizationAway T g).toExtension
```
is not reducibly def-eq. Hence using the general `SubmersivePresentation.basisCotangent` leads
to `erw` hell.
-/
noncomputable
/-
**Algebra.Generators.basisCotangentAway** 是 Mathlib 中的一个定义，位于命名空间 `Algebra.Gener
ators`。
形式化陈述：{R : Type u_1} →   (S : Type u_2) →     [inst : CommRing R] →       [inst_
1 : CommRing S] →         [inst_2 : Algebra R S] →           (r : R) →          
   [inst_3 : IsLocalization.Away r S] →               Module.Basis Unit S (Algeb
ra.Generators.localizationAway S r).toExtension.Cotangent
参数：S : Type u_2；r : R；Algebra.Generators.localizationAway S r。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
def Generators.basisCotangentAway (r : R) [IsLocalization.Away r S] :
    Module.Basis Unit S (localizationAway S r).toExtension.Cotangent :=
  (SubmersivePresentation.localizationAway S r).basisCotangent
/-
**Algebra.Generators.basisCotangentAway_apply** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.Generators`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] (r : R)   [inst_3 : IsLocalization.Away r S] (x : Unit), 
  (Algebra.Generators.basisCotangentAway S r) x = Algebra.Generators.cMulXSubOne
Cotangent S r
参数：r : R；x : Unit；Algebra.Generators.basisCotangentAway S r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Algebra.SubmersivePresentation.basisCotangent_apply`：basisCotangent_appl
y (r : σ) : P.basisCotangent r = Extension.Cotangent.mk ⟨P.relation r, P.relatio
n_mem_ker r⟩
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma Generators.basisCotangentAway_apply (x : Unit) :
    basisCotangentAway S r x = cMulXSubOneCotangent S r :=
  SubmersivePresentation.basisCotangent_apply _ _

end LocalizationAway

/-- If `S` is `R`-standard smooth, `Ω[S⁄R]` is a free `S`-module. -/
/-
**Algebra.IsStandardSmooth.free_kaehlerDifferential** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.IsStandardSmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.IsStandardSmooth R S], Module.Free S Ω[S⁄R]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.SubmersivePresentation.free_kaehlerDifferential`：free_kaehlerDif
ferential (P : SubmersivePresentation R S ι σ) : Module.Free S Ω[S⁄R]

--- 原说明 ---
If `S` is `R`-standard smooth, `Ω[S⁄R]` is a free `S`-module.
-/
instance IsStandardSmooth.free_kaehlerDifferential [IsStandardSmooth R S] :
    Module.Free S Ω[S⁄R] := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.free_kaehlerDifferential
/-
**Algebra.IsStandardSmooth.subsingleton_h1Cotangent** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebra.IsStandardSmooth`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.IsStandardSmooth R S], Subsingleton (Algebra.H
1Cotangent R S)
参数：Algebra.H1Cotangent R S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Algebra.Extension.instIsScalarTowerCotangent`：∀ {R : Type u} {S : Type v
} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] {P : Algebra.
Extension R S}   {R₁ : Type u_1} {…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
instance IsStandardSmooth.subsingleton_h1Cotangent [IsStandardSmooth R S] :
    Subsingleton (H1Cotangent R S) := by
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  exact P.equivH1Cotangent.symm.toEquiv.subsingleton

/-- If `S` is non-trivial and `R`-standard smooth of relative dimension, `Ω[S⁄R]` is a free
`S`-module of rank `n`. -/
/-
**Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential** 是 Mathl
ib 中的一个定理，位于命名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Nontrivial S] (n : ℕ)   [Algebra.IsStandardSmoothOfRelat
iveDimension n R S], Module.rank S Ω[S⁄R] = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.SubmersivePresentation.rank_kaehlerDifferential`：rank_kaehlerDif
ferential [Nontrivial S] [Finite ι] (P : SubmersivePresentation R S ι σ) : Modul
e.rank S Ω[S⁄R] = P.dimension

--- 原说明 ---
If `S` is non-trivial and `R`-standard smooth of relative dimension, `Ω[S⁄R]` is
 a free
`S`-module of rank `n`.
-/
theorem IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential [Nontrivial S] (n : ℕ)
    [IsStandardSmoothOfRelativeDimension n R S] :
    Module.rank S Ω[S⁄R] = n := by
  obtain ⟨_, _, _, _, ⟨P, hP⟩⟩ := ‹IsStandardSmoothOfRelativeDimension n R S›
  rw [P.rank_kaehlerDifferential, hP]
/-
**Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth** 是 Mathli
b 中的一个定理，位于命名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] [Nontrivial S]   [Algebra.IsStandardSmooth R S] (n : ℕ), 
Algebra.IsStandardSmoothOfRelativeDimension n R S ↔ Module.rank S Ω[S⁄R] = ↑n
参数：n : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`：∀ 
{R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 
: Algebra R S] [Nontrivial S] (n : ℕ)   [Algebra.IsStandar…
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.SubmersivePresentation.rank_kaehlerDifferential`：rank_kaehlerDif
ferential [Nontrivial S] [Finite ι] (P : SubmersivePresentation R S ι σ) : Modul
e.rank S Ω[S⁄R] = P.dimension
-/
lemma IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth [Nontrivial S]
    [IsStandardSmooth R S] (n : ℕ) :
    IsStandardSmoothOfRelativeDimension n R S ↔ Module.rank S Ω[S⁄R] = n := by
  refine ⟨fun h ↦ IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential _, fun h ↦ ?_⟩
  obtain ⟨_, _, _, _, ⟨P⟩⟩ := ‹IsStandardSmooth R S›
  refine ⟨_, _, _, ‹_›, ⟨P, ?_⟩⟩
  apply Nat.cast_injective (R := Cardinal)
  rwa [← P.rank_kaehlerDifferential]
/-
**Algebra.IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential**
 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsStandardSmoothOfRelativeDimension`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S]   [Algebra.IsStandardSmoothOfRelativeDimension 0 R S], Su
bsingleton Ω[S⁄R]
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth`：∀ (n : ℕ) 
{R : Type u} {S : Type v} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Al
gebra R S]   [H : Algebra.IsStandardSmoothOfRelati…
· 使用引理 `Module.subsingleton_of_rank_zero`：subsingleton_of_rank_zero (h : Module.
rank R M = 0) : Subsingleton M
· 使用定理 `Algebra.IsStandardSmooth.free_kaehlerDifferential`：∀ {R : Type u_1} {S :
 Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S]   [A
lgebra.IsStandardSmooth R S], Module.Fr…
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`：∀ 
{R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 
: Algebra R S] [Nontrivial S] (n : ℕ)   [Algebra.IsStandar…
-/
instance IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential
    [IsStandardSmoothOfRelativeDimension 0 R S] : Subsingleton Ω[S⁄R] := by
  cases subsingleton_or_nontrivial S
  · exact Module.subsingleton S _
  have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
  exact Module.subsingleton_of_rank_zero
    (IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 0)

@[deprecated (since := "2026-05-22")]
alias IsStandardSmoothOfRelationDimension.subsingleton_kaehlerDifferential :=
  IsStandardSmoothOfRelativeDimension.subsingleton_kaehlerDifferential

end

/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [IsStandardSmooth R S] : Smooth R S where
  formallySmooth := by
    rw [Algebra.formallySmooth_iff]
    exact ⟨inferInstance, inferInstance⟩

/-- If `S` is `R`-standard smooth of relative dimension zero, it is étale. -/
/-
**Algebra.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `S` is `R`-standard smooth of relative dimension zero, it is étale.
-/
instance (priority := 900) [IsStandardSmoothOfRelativeDimension 0 R S] : Etale R S where
  finitePresentation := (IsStandardSmoothOfRelativeDimension.isStandardSmooth 0).finitePresentation
  formallyEtale :=
    have : IsStandardSmooth R S := IsStandardSmoothOfRelativeDimension.isStandardSmooth 0
    have : FormallyUnramified R S := ⟨inferInstance⟩
    .of_formallyUnramified_and_formallySmooth

end Algebra

