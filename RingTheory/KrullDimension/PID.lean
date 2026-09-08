/-
Copyright (c) 2025 Jingting Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jingting Wang
-/
module

public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# The Krull dimension of a principal ideal domain

In this file, we proved some results about the dimension of a principal ideal domain.
-/

public section

/-
**IsPrincipalIdealRing.krullDimLE_one** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.krullDimLE_one (R : Type*) [CommRing R] [IsPrincipalI
dealRing R] : Ring.KrullDimLE 1 R
参数：R : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Ring.krullDimLE_one_iff`：Ring.krullDimLE_one_iff : Ring.KrullDimLE 1 R ↔
 forall I : Ideal R, I.IsPrime -> I in minimalPrimes R ∨ I.IsMaximal
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_minimal_iff_exists_lt`：not_minimal_iff_exists_lt (hx : P x) : ¬ Mini
mal P x ↔ exists y, y < x ∧ P y
· 使用定理 `Set.notMem_ofPred_iff`：notMem_ofPred_iff {a : α} {p : α -> Prop} : a ∉ {
 x | p x } ↔ ¬p a
· 使用引理 `minimalPrimes_eq_minimals`：minimalPrimes_eq_minimals : minimalPrimes R =
 {x | Minimal Ideal.IsPrime x}
· 使用定理 `IsPrincipalIdealRing.of_surjective`：IsPrincipalIdealRing.of_surjective [
IsPrincipalIdealRing R] (f : F) (hf : Function.Surjective f) : IsPrincipalIdealR
ing S
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mk_surjective`：mk_surjective : Function.Surjective (mk I)
· 使用定理 `Ideal.map_isPrime_of_surjective`：map_isPrime_of_surjective {f : F} (hf :
 Function.Surjective f) {I : Ideal R} [H : IsPrime I] (hk : RingHom.ker f <= I) 
: IsPrime (map f I)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.mk_ker`：mk_ker {I : Ideal R} [I.IsTwoSided] : ker (Quotient.mk I) 
= I
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `IsPrime.to_maximal_ideal`：to_maximal_ideal [CommRing R] [IsDomain R] [Is
PrincipalIdealRing R] {S : Ideal R} [hpi : IsPrime S] (hS : S != ⊥) : IsMaximal 
S
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.map_eq_bot_iff_le_ker`：map_eq_bot_iff_le_ker {I : Ideal R} (f : F)
 : I.map f = ⊥ ↔ I <= RingHom.ker f
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `Ideal.comap_isMaximal_of_surjective`：comap_isMaximal_of_surjective (hf :
 Function.Surjective f) {K : Ideal S} [H : IsMaximal K] : IsMaximal (comap f K)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Ideal.comap_map_of_surjective'`：comap_map_of_surjective' (f : F) (hf : F
unction.Surjective f) (I : Ideal R) : (I.map f).comap f = I ⊔ RingHom.ker f
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
-/
instance IsPrincipalIdealRing.krullDimLE_one (R : Type*) [CommRing R]
    [IsPrincipalIdealRing R] : Ring.KrullDimLE 1 R := by
  refine Ring.krullDimLE_one_iff.2 fun I hI ↦ or_iff_not_imp_left.2 fun hI' ↦ ?_
  rw [minimalPrimes_eq_minimals, Set.notMem_ofPred_iff, not_minimal_iff_exists_lt hI] at hI'
  obtain ⟨P, hlt, hP⟩ := hI'
  have := IsPrincipalIdealRing.of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  have : (I.map (Ideal.Quotient.mk P)).IsMaximal := by
    have := Ideal.map_isPrime_of_surjective (f := Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      (I := I) (by simpa using hlt.le)
    refine IsPrime.to_maximal_ideal ?_
    rw [ne_eq, Ideal.map_eq_bot_iff_le_ker, Ideal.mk_ker]
    exact hlt.not_ge
  have := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
    (K := I.map (Ideal.Quotient.mk P))
  simpa [Ideal.comap_map_of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective,
    hlt.le] using this
/-
**IsPrincipalIdealRing.ringKrullDim_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomai
n R] [IsPrincipalIdealRing R] (h : ¬ IsField R) : ringKrullDim R = 1
参数：R : Type*；h : ¬ IsField R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_le_of_not_lt`：eq_of_le_of_not_lt (h₁ : a <= b) (h₂ : ¬a < b) : a =
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Ring.krullDimLE_iff`：Ring.krullDimLE_iff {n : Nat} : KrullDimLE n R ↔ ri
ngKrullDim R <= n
· 使用定理 `Order.le_of_lt_succ`：le_of_lt_succ {a b : α} : a < succ b -> a <= b
· 使用引理 `Ring.KrullDimLE.isField_of_isDomain`：Ring.KrullDimLE.isField_of_isDomain
 [IsDomain R] : IsField R
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
-/
theorem IsPrincipalIdealRing.ringKrullDim_eq_one (R : Type*) [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (h : ¬ IsField R) : ringKrullDim R = 1 := by
  apply eq_of_le_of_not_lt ?_ fun h' ↦ h ?_
  · rw [← Nat.cast_one, ← Ring.krullDimLE_iff]
    infer_instance
  · have h'' : ringKrullDim R ≤ 0 := Order.le_of_lt_succ h'
    rw [← Nat.cast_zero, ← Ring.krullDimLE_iff] at h''
    exact Ring.KrullDimLE.isField_of_isDomain

/-- In a PID that is not a field, every maximal ideal has height one. -/
/-
**IsPrincipalIdealRing.height_eq_one_of_isMaximal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsPrincipalIdealRing.height_eq_one_of_isMaximal {R : Type*} [CommRing R] [
IsDomain R] [IsPrincipalIdealRing R] (m : Ideal R) [m.IsMaximal] (h : ¬ IsField 
R) : m.height = 1
参数：m : Ideal R；h : ¬ IsField R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsPrincipalIdealRing.ringKrullDim_eq_one`：IsPrincipalIdealRing.ringKrull
Dim_eq_one (R : Type*) [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] (h : ¬
 IsField R) : ringKrullDim R =…
· 使用引理 `Ideal.height_le_ringKrullDim_of_ne_top`：Ideal.height_le_ringKrullDim_of_
ne_top {I : Ideal R} (h : I != ⊤) : I.height <= ringKrullDim R
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Ideal.height_bot`：Ideal.height_bot [Nontrivial R] : (⊥ : Ideal R).height
 = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `Ideal.height_add_one_le_of_lt_of_isPrime`：Ideal.height_add_one_le_of_lt_
of_isPrime {I J : Ideal R} [I.IsPrime] [J.IsPrime] (h : I < J) : I.height + 1 <=
 J.height
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Ideal.bot_lt_of_maximal`：bot_lt_of_maximal (M : Ideal R) [hm : M.IsMaxim
al] (non_field : ¬IsField R) : ⊥ < M

--- 原说明 ---
In a PID that is not a field, every maximal ideal has height one.
-/
lemma IsPrincipalIdealRing.height_eq_one_of_isMaximal {R : Type*} [CommRing R] [IsDomain R]
    [IsPrincipalIdealRing R] (m : Ideal R) [m.IsMaximal] (h : ¬ IsField R) :
    m.height = 1 := by
  refine le_antisymm ?_ ?_
  · suffices h : (m.height : WithBot ℕ∞) ≤ 1 by norm_cast at h
    rw [← IsPrincipalIdealRing.ringKrullDim_eq_one _ h]
    exact Ideal.height_le_ringKrullDim_of_ne_top Ideal.IsPrime.ne_top'
  · apply le_of_eq_of_le _ (Ideal.height_add_one_le_of_lt_of_isPrime (Ideal.bot_lt_of_maximal m h))
    simp
