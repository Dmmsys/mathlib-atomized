/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.RingTheory.Ideal.Over

/-! # Lemmas about `primesOver` in quotient rings. -/

@[expose] public section

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]

/-- Given a prime `P` of `R` and an ideal `I` in an `R`-algebra `S`.
Suppose we can find a prime `P'` over `P`, not containing `I`,
then the number of primes of `S / I` over `P`
is strictly less than primes of `S` over `P` (provided they are finite).

The lemma is stated in terms of surjections for syntactic generality. -/
/-
**Ideal.ncard_primesOver_lt_of_not_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.ncard_primesOver_lt_of_not_le (f : S ->ₐ[R] T) (Hf : Function.Surjec
tive f) (P : Ideal R) (P' : Ideal S) [P'.IsPrime] [P'.LiesOver P] (hkP' : ¬ Ring
Hom.ker f.toRingHom <= P') (H : (P.primesOver S).Finite) : (P.primesOver T).ncar
d < (P.primesOver S).ncard
参数：f : S ->ₐ[R] T；Hf : Function.Surjective f；P : Ideal R；P' : Ideal S；hkP' : ¬ R
ingHom.ker f.toRingHom <= P'；H : (P.primesOver S).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ncard_image_of_injective`：ncard_image_of_injective (s : Set α) (H : 
f.Injective) : (f '' s).ncard = s.ncard
· 使用定理 `Ideal.comap_injective_of_surjective`：comap_injective_of_surjective : Inj
ective (comap f)
· 使用定理 `Set.ncard_lt_ncard`：ncard_lt_ncard (h : s ⊂ t) (ht : t.Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.ssubset_iff_exists`：ssubset_iff_exists {s t : Set α} : s ⊂ t ↔ s sub
seteq t ∧ exists x in t, x ∉ s
· 使用定理 `Ideal.IsPrime.comap`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : 
Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S] (f : F)   {K : Ideal 
S} [inst_…
· 使用定理 `Ideal.ker_le_comap`：ker_le_comap {K : Ideal S} (f : F) : RingHom.ker f <
= comap f K

--- 原说明 ---
Given a prime `P` of `R` and an ideal `I` in an `R`-algebra `S`.
Suppose we can find a prime `P'` over `P`, not containing `I`,
then the number of primes of `S / I` over `P`
is strictly less than primes of `S` over `P` (provided they are finite).

The lemma is stated in terms of surjections for syntactic generality.
-/
lemma Ideal.ncard_primesOver_lt_of_not_le
    (f : S →ₐ[R] T) (Hf : Function.Surjective f)
    (P : Ideal R) (P' : Ideal S) [P'.IsPrime] [P'.LiesOver P]
    (hkP' : ¬ RingHom.ker f.toRingHom ≤ P') (H : (P.primesOver S).Finite) :
    (P.primesOver T).ncard < (P.primesOver S).ncard := by
  rw [← Set.ncard_image_of_injective _ (Ideal.comap_injective_of_surjective _ Hf)]
  refine Set.ncard_lt_ncard (Set.ssubset_iff_exists.mpr ⟨?_, P', ⟨‹_›, ‹_›⟩, ?_⟩) H
  · rintro _ ⟨q, ⟨_, _⟩, rfl⟩
    exact ⟨inferInstance, inferInstanceAs ((q.comap f).LiesOver _)⟩
  · rintro ⟨q, ⟨_, _⟩, rfl⟩; exact hkP' (Ideal.ker_le_comap _)
/-
**Ideal.ncard_primesOver_quotient_singleton_lt_of_notMem** 是 Mathlib 中的一个引理，位于命名
空间 ``。
形式化陈述：Ideal.ncard_primesOver_quotient_singleton_lt_of_notMem (P : Ideal R) (e : 
S) (P' : Ideal S) [P'.IsPrime] [P'.LiesOver P] (heP' : e ∉ P') (H : (P.primesOve
r S).Finite) : (P.primesOver (S ⧸ Ideal.span {e})).ncard < (P.primesOver S).ncar
d
参数：P : Ideal R；e : S；P' : Ideal S；heP' : e ∉ P'；H : (P.primesOver S).Finite。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Ideal.ncard_primesOver_lt_of_not_le`：Ideal.ncard_primesOver_lt_of_not_le
 (f : S ->ₐ[R] T) (Hf : Function.Surjective f) (P : Ideal R) (P' : Ideal S) [P'.
IsPrime] [P'.LiesOver P] …
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.Quotient.mkₐ_surjective`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : 
CommSemiring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst
_3 : I.IsTwoSided],…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.Quotient.mkₐ_ker`：∀ (R₁ : Type u_1) {A : Type u_3} [inst : CommSem
iring R₁] [inst_1 : Ring A] [inst_2 : Algebra R₁ A] (I : Ideal A)   [inst_3 : I.
IsTwoSided],…
-/
lemma Ideal.ncard_primesOver_quotient_singleton_lt_of_notMem
    (P : Ideal R) (e : S) (P' : Ideal S) [P'.IsPrime] [P'.LiesOver P]
    (heP' : e ∉ P') (H : (P.primesOver S).Finite) :
    (P.primesOver (S ⧸ Ideal.span {e})).ncard < (P.primesOver S).ncard :=
  Ideal.ncard_primesOver_lt_of_not_le _ (Ideal.Quotient.mkₐ_surjective R _) _ P' (by simpa) H
