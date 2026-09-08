/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Unramified.Basic

/-!

# Formal-unramification of finite products of rings

## Main result

- `Algebra.FormallyUnramified.pi_iff`: If `I` is finite, `Π i : I, A i` is `R`-formally-smooth
  if and only if each `A i` is `R`-formally-smooth.

-/

public section

namespace Algebra.FormallyUnramified

variable {R : Type*} {I : Type*} [Finite I] (f : I → Type*)
variable [CommRing R] [∀ i, CommRing (f i)] [∀ i, Algebra R (f i)]

/-
**Algebra.FormallyUnramified.pi_iff** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FormallyU
nramified`。
形式化陈述：pi_iff : FormallyUnramified R (forall i, f i) ↔ forall i, FormallyUnramifi
ed R (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.FormallyUnramified.of_surjective`：of_surjective [FormallyUnramif
ied R A] (f : A ->ₐ[R] B) (H : Function.Surjective f) : FormallyUnramified R B
· 使用定理 `Function.surjective_eval`：surjective_eval {α : Sort u} {β : α -> Sort v}
 [h : forall a, Nonempty (β a)] (a : α) : Surjective (eval a : (forall a, β a) -
> β a)
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.FormallyUnramified.iff_comp_injective`：iff_comp_injective : Form
allyUnramified R A ↔ forall ⦃B : Type u⦄ [CommRing B], forall [Algebra R B] (I :
 Ideal B) (_ : I ^ 2 = ⊥), Function…
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.univ_sum_single`：∀ {I : Type u_7} [inst : DecidableEq I] {M : I →
 Type u_8} [inst_1 : (i : I) → AddCommMonoid (M i)] [inst_2 : Fintype I]   (f : 
(i : I) → M …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Ideal.Quotient.eq_zero_iff_mem`：eq_zero_iff_mem : mk I a = 0 ↔ a in I
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Ideal.mem_bot`：mem_bot {x : R} : x in (⊥ : Ideal R) ↔ x = 0
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用引理 `IsIdempotentElem.mul`：mul (ha : IsIdempotentElem a) (hb : IsIdempotentEl
em b) : IsIdempotentElem (a * b)
· 使用引理 `IsIdempotentElem.map`：map {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHo
mClass F M N] {e : M} (he : IsIdempotentElem e) (f : F) : IsIdempotentElem (f e)
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
（共 58 条，此处仅展示前 30 条）
-/
theorem pi_iff :
    FormallyUnramified R (∀ i, f i) ↔ ∀ i, FormallyUnramified R (f i) := by
  classical
  cases nonempty_fintype I
  constructor
  · intro _ i
    exact FormallyUnramified.of_surjective (Pi.evalAlgHom R f i) (Function.surjective_eval i)
  · intro H
    rw [iff_comp_injective]
    intro B _ _ J hJ f₁ f₂ e
    ext g
    rw [← Finset.univ_sum_single g, map_sum, map_sum]
    refine Finset.sum_congr rfl ?_
    rintro x -
    have hf : ∀ x, f₁ x - f₂ x ∈ J := by
      intro g
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
      exact AlgHom.congr_fun e g
    let e : ∀ i, f i := Pi.single x 1
    have he : IsIdempotentElem e := by simp [IsIdempotentElem, e, ← Pi.single_mul]
    have h₁ : (f₁ e) * (1 - f₂ e) = 0 := by
      rw [← Ideal.mem_bot, ← hJ, ← ((he.map f₁).mul (he.map f₂).one_sub).eq, ← pow_two]
      apply Ideal.pow_mem_pow
      convert! Ideal.mul_mem_left _ (f₁ e) (hf e) using 1
      rw [mul_sub, mul_sub, mul_one, (he.map f₁).eq]
    have h₂ : (f₂ e) * (1 - f₁ e) = 0 := by
      rw [← Ideal.mem_bot, ← hJ, ← ((he.map f₂).mul (he.map f₁).one_sub).eq, ← pow_two]
      apply Ideal.pow_mem_pow
      convert! Ideal.mul_mem_left _ (-f₂ e) (hf e) using 1
      rw [neg_mul, mul_sub, mul_sub, mul_one, neg_sub, (he.map f₂).eq]
    have H : f₁ e = f₂ e := by
      trans f₁ e * f₂ e
      · rw [← sub_eq_zero, ← h₁, mul_sub, mul_one]
      · rw [eq_comm, ← sub_eq_zero, ← h₂, mul_sub, mul_one, mul_comm]
    let J' := Ideal.span {1 - f₁ e}
    let f₁' : f x →ₐ[R] B ⧸ J' := by
      apply AlgHom.ofLinearMap
        (((Ideal.Quotient.mkₐ R J').comp f₁).toLinearMap.comp (LinearMap.single _ _ x))
      · simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, LinearMap.coe_single,
          Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [eq_comm, ← sub_eq_zero, ← (Ideal.Quotient.mk J').map_one, ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      · intro r s; simp [Pi.single_mul]
    let f₂' : f x →ₐ[R] B ⧸ J' := by
      apply AlgHom.ofLinearMap
        (((Ideal.Quotient.mkₐ R J').comp f₂).toLinearMap.comp (LinearMap.single _ _ x))
      · simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, LinearMap.coe_single,
          Function.comp_apply, AlgHom.toLinearMap_apply, Ideal.Quotient.mkₐ_eq_mk]
        rw [eq_comm, ← sub_eq_zero, ← (Ideal.Quotient.mk J').map_one, ← map_sub,
          Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, H]
      · intro r s; simp [Pi.single_mul]
    suffices f₁' = f₂' by
      have := AlgHom.congr_fun this (g x)
      simp only [AlgHom.comp_toLinearMap, AlgHom.ofLinearMap_apply, LinearMap.coe_comp,
        LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply, ← map_sub,
        Ideal.Quotient.mkₐ_eq_mk, ← sub_eq_zero (b := Ideal.Quotient.mk J' _), f₁', f₂',
        Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, J'] at this
      obtain ⟨c, hc⟩ := this
      apply_fun (f₁ e * ·) at hc
      rwa [← mul_assoc, mul_sub, mul_sub, mul_one, (he.map f₁).eq, sub_self, zero_mul,
        ← map_mul, H, ← map_mul, ← Pi.single_mul, one_mul, sub_eq_zero] at hc
    apply FormallyUnramified.comp_injective (I := J.map (algebraMap _ _))
    · rw [← Ideal.map_pow, hJ, Ideal.map_bot]
    · ext r
      rw [← sub_eq_zero]
      simp only [Ideal.Quotient.algebraMap_eq, AlgHom.coe_comp, Ideal.Quotient.mkₐ_eq_mk,
        Function.comp_apply, ← map_sub, Ideal.Quotient.eq_zero_iff_mem, f₁', f₂',
        AlgHom.comp_toLinearMap, AlgHom.ofLinearMap_apply, LinearMap.coe_comp,
        LinearMap.coe_single, Function.comp_apply, AlgHom.toLinearMap_apply,
        Ideal.Quotient.mkₐ_eq_mk]
      exact Ideal.mem_map_of_mem (Ideal.Quotient.mk J') (hf (Pi.single x r))
/-
**Algebra.FormallyUnramified.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra.FormallyUnramif
ied`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, FormallyUnramified R (f i)] : FormallyUnramified R (Π i, f i) :=
  (pi_iff _).mpr ‹_›

end Algebra.FormallyUnramified

