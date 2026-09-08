/-
Copyright (c) 2026 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.LiesOverInstances
public import Mathlib.RingTheory.RamificationInertia.Inertia

/-!
# Ramification theory of completions of number fields

This file studies the ramification of completions of number fields.

## Main definitions

- `NumberField.InfinitePlace.inertiaDeg` : the inertia degree of a place `w` of `L` over a
  place `v` of `K`, defined as the local degree of the extension of completions at `w` and
  `v` if `w` lies over `v` and zero otherwise.

## Main results

- `NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank` : the degree of `L` over `K` is equal to
  the sum of the inertia degrees of the places of `L` over `v`.

## Tags

number field, infinite places, ramification
-/

@[expose] public section

section infinite_place

namespace NumberField.InfinitePlace

open NumberField.ComplexEmbedding Finset AbsoluteValue.Completion

-- to enable `w.LiesOver v → Algebra v.Completion w.Completion` instance
open scoped NumberField.LiesOver

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (v : InfinitePlace K) {w : InfinitePlace L}

open Completion

/-- If `w` is a ramified place over `v` then `w.Completion` has `v.Completion` dimension two. -/
/-
**NumberField.InfinitePlace.IsRamified.finrank_eq_two** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace.IsRamified`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L]   (v : NumberField.InfinitePlace K) {w : NumberField.InfinitePl
ace L} [inst_3 : w.LiesOver v],   NumberField.InfinitePlace.IsRamified K w → Mod
ule.finrank v.Completion w.Completion = 2
参数：v : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `NumberField.InfinitePlace.isRamified_iff`：isRamified_iff : w.IsRamified 
k ↔ w.IsComplex ∧ (w.comap (algebraMap k K)).IsReal
· 使用定理 `NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
`：extensionEmbedding_liesOver_of_isReal (h : v.IsReal) : ComplexEmbedding.LiesOv
er (extensionEmbedding w) (extensionEmbedding v)
· 使用定理 `NumberField.LiesOver.instIsScalarTowerCompletion`：∀ {K : Type u_1} {L : 
Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   {v : Numb
erField.InfinitePlace K} {w : NumberFi…
· 使用定理 `NumberField.LiesOver.instContinuousSMulCompletion`：∀ {K : Type u_1} {L :
 Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   {v : Num
berField.InfinitePlace K} {w : NumberFi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.LiesOver.comap_eq`：comap_eq : w.comap (algebra
Map K L) = v
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply`：e
xtensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Com
pletion) : (extensionEmbeddingOfIsReal hv x : Complex) = ex…
· 使用定理 `NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding_apply`：
liesOver_extensionEmbedding_apply {φ : w.Completion ->+* Complex} [ComplexEmbedd
ing.LiesOver φ (extensionEmbedding v)] {x : v.Completion} : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.finrank_real_complex`：finrank_real_complex : finrank Real Comple
x = 2

--- 原说明 ---
If `w` is a ramified place over `v` then `w.Completion` has `v.Completion` dimen
sion two.
-/
theorem IsRamified.finrank_eq_two [w.LiesOver v] (h : w.IsRamified K) :
    Module.finrank v.Completion w.Completion = 2 := by
  have H := NumberField.InfinitePlace.isRamified_iff.mp h
  rw [NumberField.InfinitePlace.LiesOver.comap_eq w v] at H
  have := LiesOver.extensionEmbedding_liesOver_of_isReal w H.2
  rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal H.2)
      (ringEquivComplexOfIsComplex H.1) (by ext; simp),
    Complex.finrank_real_complex]

/-- If `w` is an unramified place over `v` then `w.Completion` has `v.Completion` dimension one. -/
/-
**NumberField.InfinitePlace.IsUnramified.finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空
间 `NumberField.InfinitePlace.IsUnramified`。
形式化陈述：∀ {K : Type u_1} {L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_
2 : Algebra K L]   (v : NumberField.InfinitePlace K) {w : NumberField.InfinitePl
ace L} [inst_3 : w.LiesOver v],   NumberField.InfinitePlace.IsUnramified K w → M
odule.finrank v.Completion w.Completion = 1
参数：v : NumberField.InfinitePlace K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NumberField.InfinitePlace.isReal_or_isComplex`：isReal_or_isComplex (w : 
InfinitePlace K) : IsReal w ∨ IsComplex w
· 使用定理 `NumberField.InfinitePlace.LiesOver.extensionEmbedding_liesOver_of_isReal
`：extensionEmbedding_liesOver_of_isReal (h : v.IsReal) : ComplexEmbedding.LiesOv
er (extensionEmbedding w) (extensionEmbedding v)
· 使用定理 `NumberField.LiesOver.instIsScalarTowerCompletion`：∀ {K : Type u_1} {L : 
Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   {v : Numb
erField.InfinitePlace K} {w : NumberFi…
· 使用定理 `NumberField.LiesOver.instContinuousSMulCompletion`：∀ {K : Type u_1} {L :
 Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   {v : Num
berField.InfinitePlace K} {w : NumberFi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `NumberField.InfinitePlace.IsUnramified.liesOver_isReal_over`：∀ {K : Type
 u_4} {L : Type u_5} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] 
  (w : NumberField.InfinitePlace L) (v : NumberFi…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHomCompTriple.comp_eq`：∀ {R₁ : Type u_1} {R₂ : Type u_2} {R₃ : Type 
u_3} {inst : Semiring R₁} {inst_1 : Semiring R₂} {inst_2 : Semiring R₃}   {σ₁₂ :
 R₁ →+* R₂} {σ₂…
· 使用定理 `NumberField.InfinitePlace.Completion.extensionEmbeddingOfIsReal_apply`：e
xtensionEmbeddingOfIsReal_apply {v : InfinitePlace K} (hv : IsReal v) (x : v.Com
pletion) : (extensionEmbeddingOfIsReal hv x : Complex) = ex…
· 使用定理 `NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding_apply`：
liesOver_extensionEmbedding_apply {φ : w.Completion ->+* Complex} [ComplexEmbedd
ing.LiesOver φ (extensionEmbedding v)] {x : v.Completion} : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Module.finrank_self`：finrank_self : finrank R R = 1
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `NumberField.InfinitePlace.LiesOver.embedding_comp_eq_or_conjugate_embedd
ing_comp_eq`：embedding_comp_eq_or_conjugate_embedding_comp_eq : w.embedding.comp
 (algebraMap K L) = v.embedding ∨ (conjugate w.embedding).comp (algebraMa…
· 使用定理 `NumberField.InfinitePlace.Completion.liesOver_extensionEmbedding`：liesOv
er_extensionEmbedding [ContinuousSMul v.Completion w.Completion] [ComplexEmbeddi
ng.LiesOver w.embedding v.embedding] : ComplexEmbeddin…
· 使用定理 `NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under`：isCompl
ex_of_isComplex_under (hv : v.IsComplex) : w.IsComplex
· 使用定理 `Complex.instNontrivial`：Nontrivial ℂ
· 使用定理 `NumberField.InfinitePlace.Completion.liesOver_conjugate_extensionEmbeddi
ng`：liesOver_conjugate_extensionEmbedding [ContinuousSMul v.Completion w.Complet
ion] [ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedd…
· 使用定理 `starRingAut_apply`：∀ {R : Type u} [inst : CommSemiring R] [inst_1 : Star
Ring R] (a : R), starRingAut a = star a

--- 原说明 ---
If `w` is an unramified place over `v` then `w.Completion` has `v.Completion` di
mension one.
-/
theorem IsUnramified.finrank_eq_one [w.LiesOver v] (h : w.IsUnramified K) :
    Module.finrank v.Completion w.Completion = 1 := by
  rcases v.isReal_or_isComplex with (hv | hv)
  · have := LiesOver.extensionEmbedding_liesOver_of_isReal w hv
    rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivRealOfIsReal hv) (ringEquivRealOfIsReal
        (h.liesOver_isReal_over _ _ hv)) (RingHom.ext fun _ ↦ Complex.ofReal_inj.1 <| by simp),
      Module.finrank_self]
  · cases LiesOver.embedding_comp_eq_or_conjugate_embedding_comp_eq w v with
    | inl hl =>
      have : ComplexEmbedding.LiesOver w.embedding v.embedding := ⟨hl⟩
      have := liesOver_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
          (ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)) (by ext; simp),
        Module.finrank_self]
    | inr hr =>
      have : ComplexEmbedding.LiesOver (conjugate w.embedding) v.embedding := ⟨hr⟩
      have := liesOver_conjugate_extensionEmbedding w v
      rw [Algebra.finrank_eq_of_equiv_equiv (ringEquivComplexOfIsComplex hv)
        ((ringEquivComplexOfIsComplex (LiesOver.isComplex_of_isComplex_under _ hv)).trans
          (starRingAut (R := ℂ))) (by ext; simp [← conjugate_coe_eq]),
        Module.finrank_self]

@[deprecated (since := "2026-07-10")] alias Completion.finrank_eq_two_of_isRamified :=
  IsRamified.finrank_eq_two

@[deprecated (since := "2026-07-10")] alias Completion.finrank_eq_one_of_isUnramified :=
  IsUnramified.finrank_eq_one

variable (w) in
/-
**NumberField.InfinitePlace.mult_mul_finrank** 是 Mathlib 中的一个定理，位于命名空间 `NumberFi
eld.InfinitePlace`。
形式化陈述：mult_mul_finrank [w.LiesOver v] : v.mult * Module.finrank v.Completion w.C
ompletion = w.mult
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `AbsoluteValue.LiesOver.comp_eq`：∀ {K : Type u_3} {L : Type u_4} {S : Typ
e u_5} {inst : CommRing K} {inst_1 : IsSimpleRing K} {inst_2 : CommRing L}   {in
st_3 : Algebra K L} …
· 使用引理 `NumberField.InfinitePlace.isUnramified_or_isRamified`：isUnramified_or_is
Ramified : w.IsUnramified k ∨ w.IsRamified k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.IsUnramified.finrank_eq_one`：∀ {K : Type u_1} 
{L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v :
 NumberField.InfinitePlace K) {w : NumberFi…
· 使用定理 `NumberField.InfinitePlace.IsUnramified.eq`：∀ {k : Type u_1} [inst : Fiel
d k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : NumberField
.InfinitePlace K},   NumberFiel…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `NumberField.InfinitePlace.IsRamified.finrank_eq_two`：∀ {K : Type u_1} {L
 : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v : N
umberField.InfinitePlace K) {w : NumberFi…
· 使用定理 `NumberField.InfinitePlace.IsReal.mult_eq_one`：∀ {K : Type u_1} [inst : F
ield K] {w : NumberField.InfinitePlace K}, w.IsReal → w.mult = 1
· 使用定理 `NumberField.InfinitePlace.IsRamified.isReal`：∀ {k : Type u_1} [inst : Fi
eld k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : NumberFie
ld.InfinitePlace K}, NumberField.…
· 使用定理 `NumberField.InfinitePlace.IsComplex.mult_eq_two`：∀ {K : Type u_1} [inst 
: Field K] {w : NumberField.InfinitePlace K}, w.IsComplex → w.mult = 2
· 使用定理 `NumberField.InfinitePlace.IsRamified.isComplex`：∀ {k : Type u_1} [inst :
 Field k] {K : Type u_2} [inst_1 : Field K] [inst_2 : Algebra k K]   {w : Number
Field.InfinitePlace K}, NumberField.…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem mult_mul_finrank [w.LiesOver v] :
    v.mult * Module.finrank v.Completion w.Completion = w.mult := by
  have hv : v = w.comap (algebraMap K L) := Subtype.ext ‹w.LiesOver v›.comp_eq.symm
  rcases w.isUnramified_or_isRamified K with h | h
  · rw [h.finrank_eq_one v, hv, h.eq, mul_one]
  · rw [h.finrank_eq_two v, hv, h.isReal.mult_eq_one, h.isComplex.mult_eq_two, one_mul]

open Completion

variable (w)

open scoped Classical in
/-- The inertia degree of `w` over `v`. -/
/-
**NumberField.InfinitePlace.inertiaDeg** 是 Mathlib 中的一个定义，位于命名空间 `NumberField.In
finitePlace`。
形式化陈述：{K : Type u_1} →   {L : Type u_2} →     [inst : Field K] →       [inst_1 :
 Field L] → [Algebra K L] → NumberField.InfinitePlace K → NumberField.InfinitePl
ace L → ℕ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inertia degree of `w` over `v`.
-/
protected noncomputable def inertiaDeg : ℕ :=
  if _ : w.LiesOver v then (⊥ : Ideal w.Completion).inertiaDeg v.Completion else 0
/-
**NumberField.InfinitePlace.inertiaDeg_of_liesOver** 是 Mathlib 中的一个定理，位于命名空间 `Nu
mberField.InfinitePlace`。
形式化陈述：inertiaDeg_of_liesOver [w.LiesOver v] : v.inertiaDeg w = (⊥ : Ideal w.Comp
letion).inertiaDeg v.Completion
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inertiaDeg_of_liesOver [w.LiesOver v] :
    v.inertiaDeg w = (⊥ : Ideal w.Completion).inertiaDeg v.Completion := by
  simp only [InfinitePlace.inertiaDeg, dif_pos]
/-
**NumberField.InfinitePlace.inertiaDeg_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 `Num
berField.InfinitePlace`。
形式化陈述：inertiaDeg_eq_finrank [w.LiesOver v] : v.inertiaDeg w = Module.finrank v.C
ompletion w.Completion
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NumberField.InfinitePlace.inertiaDeg_of_liesOver`：inertiaDeg_of_liesOver
 [w.LiesOver v] : v.inertiaDeg w = (⊥ : Ideal w.Completion).inertiaDeg v.Complet
ion
· 使用定理 `instFaithfulSMul_1`：∀ (R : Type u_1) (A : Type u_2) [inst : CommRing R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] [IsSimpleRing R]   [Nontrivial A], 
Faithful…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Ideal.inertiaDeg_eq_of_isMaximal`：inertiaDeg_eq_of_isMaximal [q.LiesOver
 p] [p.IsMaximal] [q.IsMaximal] : q.inertiaDeg R = Module.finrank (R ⧸ p) (S ⧸ q
)
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `instIsArtinianOfIsSemisimpleModuleOfFinite`：∀ {R : Type u_1} [inst : Rin
g R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Is
SemisimpleModule R M] [Module.Fi…
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Algebra.finrank_eq_of_equiv_equiv`：finrank_eq_of_equiv_equiv {R₀ S₀ : Ty
pe*} [CommSemiring R₀] [Semiring S₀] [Algebra R₀ S₀] {R₁ S₁ : Type*} [CommSemiri
ng R₁] [Semiring S₁] [A…
· 使用定理 `Ideal.Quotient.ringHom_ext`：ringHom_ext [NonAssocSemiring S] ⦃f g : R ⧸ 
I ->+* S⦄ (h : f.comp (mk I) = g.comp (mk I)) : f = g
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `NumberField.InfinitePlace.Completion.ext`：∀ {K : Type u_1} [inst : Field
 K] {v : NumberField.InfinitePlace K} {x y : v.Completion},   x.toCompletion = y
.toCompletion → x = y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem inertiaDeg_eq_finrank [w.LiesOver v] :
    v.inertiaDeg w = Module.finrank v.Completion w.Completion := by
  rw [inertiaDeg_of_liesOver, Ideal.inertiaDeg_eq_of_isMaximal ⊥]
  exact Algebra.finrank_eq_of_equiv_equiv (RingEquiv.quotientBot v.Completion)
    (RingEquiv.quotientBot w.Completion) (by ext; simp [RingHom.algebraMap_toAlgebra])

variable {v w} in
/-
**NumberField.InfinitePlace.inertiaDeg_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：inertiaDeg_eq_one (hw : w in unramifiedPlacesOver L v) : v.inertiaDeg w = 
1
参数：hw : w in unramifiedPlacesOver L v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `NumberField.InfinitePlace.inertiaDeg_eq_finrank`：inertiaDeg_eq_finrank [
w.LiesOver v] : v.inertiaDeg w = Module.finrank v.Completion w.Completion
· 使用定理 `NumberField.InfinitePlace.IsUnramified.finrank_eq_one`：∀ {K : Type u_1} 
{L : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v :
 NumberField.InfinitePlace K) {w : NumberFi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inertiaDeg_eq_one (hw : w ∈ unramifiedPlacesOver L v) : v.inertiaDeg w = 1 :=
  have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_one v ▸ inertiaDeg_eq_finrank v w

variable {v w} in
/-
**NumberField.InfinitePlace.inertiaDeg_eq_two** 是 Mathlib 中的一个定理，位于命名空间 `NumberF
ield.InfinitePlace`。
形式化陈述：inertiaDeg_eq_two (hw : w in ramifiedPlacesOver L v) : v.inertiaDeg w = 2
参数：hw : w in ramifiedPlacesOver L v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `NumberField.InfinitePlace.inertiaDeg_eq_finrank`：inertiaDeg_eq_finrank [
w.LiesOver v] : v.inertiaDeg w = Module.finrank v.Completion w.Completion
· 使用定理 `NumberField.InfinitePlace.IsRamified.finrank_eq_two`：∀ {K : Type u_1} {L
 : Type u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   (v : N
umberField.InfinitePlace K) {w : NumberFi…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem inertiaDeg_eq_two (hw : w ∈ ramifiedPlacesOver L v) : v.inertiaDeg w = 2 :=
  have := (Set.mem_ofPred.1 hw).1; hw.2.finrank_eq_two v ▸ inertiaDeg_eq_finrank v w

variable (K L) in
open scoped Classical in
open Finset Set in
/-- The degree of `L` over `K` is equal to the sum of the inertia degrees of the places over `v`. -/
/-
**NumberField.InfinitePlace.sum_inertiaDeg_eq_finrank** 是 Mathlib 中的一个定理，位于命名空间 
`NumberField.InfinitePlace`。
形式化陈述：sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] : ∑ w in v.place
sOver L, v.inertiaDeg w = Module.finrank K L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NumberField.InfinitePlace.union_ramifiedPlacesOver_unramifiedPlacesOver`
：union_ramifiedPlacesOver_unramifiedPlacesOver : (ramifiedPlacesOver L v) union 
(unramifiedPlacesOver L v) = placesOver L v
· 使用定理 `Set.toFinset_union`：toFinset_union [Fintype (s union t : Set _)] : (s un
ion t).toFinset = s.toFinset union t.toFinset
· 使用定理 `Finset.sum_union`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   Disjoint s₁ s₂ → ∑
 x ∈ s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_toFinset`：disjoint_toFinset [Fintype s] [Fintype t] : Disjo
int s.toFinset t.toFinset ↔ Disjoint s t
· 使用定理 `NumberField.InfinitePlace.disjoint_ramifiedPlacesOver_unramifiedPlacesOv
er`：disjoint_ramifiedPlacesOver_unramifiedPlacesOver : Disjoint (ramifiedPlacesO
ver L v) (unramifiedPlacesOver L v)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `NumberField.InfinitePlace.inertiaDeg_eq_two`：inertiaDeg_eq_two (hw : w i
n ramifiedPlacesOver L v) : v.inertiaDeg w = 2
· 使用定理 `NumberField.InfinitePlace.inertiaDeg_eq_one`：inertiaDeg_eq_one (hw : w i
n unramifiedPlacesOver L v) : v.inertiaDeg w = 1
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `NumberField.InfinitePlace.unramifedPlacesOver_ncard_add_eq_finrank`：unra
mifedPlacesOver_ncard_add_eq_finrank [NumberField K] [NumberField L] : (unramifi
edPlacesOver L v).ncard + 2 * (ramifiedPlacesOver L v).n…
· 使用定理 `Set.ncard_eq_toFinset_card'`：ncard_eq_toFinset_card' (s : Set α) [Fintyp
e s] : s.ncard = s.toFinset.card
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The degree of `L` over `K` is equal to the sum of the inertia degrees of the pla
ces over `v`.
-/
theorem sum_inertiaDeg_eq_finrank [NumberField K] [NumberField L] :
    ∑ w ∈ v.placesOver L, v.inertiaDeg w = Module.finrank K L := by
  rw [← union_ramifiedPlacesOver_unramifiedPlacesOver L v, toFinset_union,
    sum_union (Set.disjoint_toFinset.2 <| disjoint_ramifiedPlacesOver_unramifiedPlacesOver L v),
    sum_congr rfl (fun _ h ↦ inertiaDeg_eq_two (by simpa using h)),
    sum_congr rfl (fun _ h ↦ inertiaDeg_eq_one (by simpa using h)), sum_const, add_comm]
  simp [← unramifedPlacesOver_ncard_add_eq_finrank L v, mul_comm, ncard_eq_toFinset_card']

end NumberField.InfinitePlace

end infinite_place

