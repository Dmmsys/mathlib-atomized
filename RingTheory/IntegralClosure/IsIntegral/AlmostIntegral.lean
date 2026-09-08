/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.FieldTheory.Minpoly.Basic
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.FractionRing

/-! # Almost integral elements -/

@[expose] public section

section

open scoped nonZeroDivisors

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

variable (R) in
/-- An element `s` in an `R`-algebra is almost integral if there exists `r ∈ R⁰` such that
`r • s ^ n ∈ R` for all `n`. -/
@[stacks 00GW]
/-
**IsAlmostIntegral** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsAlmostIntegral (s : S) : Prop
参数：s : S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element `s` in an `R`-algebra is almost integral if there exists `r ∈ R⁰` suc
h that
`r • s ^ n ∈ R` for all `n`.
-/
def IsAlmostIntegral (s : S) : Prop := ∃ r ∈ R⁰, ∀ n, r • s ^ n ∈ (algebraMap R S).range

variable (R S) in
/-- The complete integral closure is the subalgebra of almost integral elements. -/
@[stacks 00GX "Part 1"]
/-
**completeIntegralClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completeIntegralClosure : Subalgebra R S where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete integral closure is the subalgebra of almost integral elements.
-/
def completeIntegralClosure : Subalgebra R S where
  carrier := { s | IsAlmostIntegral R s }
  mul_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n ↦ ?_⟩
    rw [mul_pow, mul_smul_mul_comm]
    exact mul_mem (hr' _) (hs' _)
  add_mem' := by
    rintro a b ⟨r, hr, hr'⟩ ⟨s, hs, hs'⟩
    refine ⟨r * s, mul_mem hr hs, fun n ↦ ?_⟩
    simp only [add_pow, Finset.smul_sum, ← smul_mul_assoc _ (_ * _),
      ← smul_mul_smul_comm _ (a ^ _)]
    exact sum_mem fun i _ ↦ mul_mem (mul_mem (hr' _) (hs' _)) (by simp)
  algebraMap_mem' r := ⟨1, one_mem _, by simp [← map_pow]⟩
/-
**mem_completeIntegralClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_completeIntegralClosure {x : S} : x in completeIntegralClosure R S ↔ I
sAlmostIntegral R x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_completeIntegralClosure {x : S} :
    x ∈ completeIntegralClosure R S ↔ IsAlmostIntegral R x := .rfl
/-
**IsIntegral.isAlmostIntegral_of_exists_smul_mem_range** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：IsIntegral.isAlmostIntegral_of_exists_smul_mem_range {s : S} (H : IsIntegr
al R s) (h : exists t in R⁰, t • s in (algebraMap R S).range) : IsAlmostIntegral
 R s
参数：H : IsIntegral R s；h : exists t in R⁰, t • s in (algebraMap R S).range。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `pow_mem`：∀ {M : Type u_3} {A : Type u_4} [inst : Monoid M] [inst_1 : Set
Like A M] [SubmonoidClass A M] {S : A} {x : M},   x ∈ S → ∀ (n : ℕ), x ^ n ∈ …
· 使用定理 `Submonoid.instSubmonoidClass`：∀ {M : Type u_1} [inst : MulOneClass M], S
ubmonoidClass (Submonoid M) M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Subalgebra.smul_mem`：smul_mem {x : A} (hx : x in S) (r : R) : r • x in S
· 使用定理 `Subalgebra.pow_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R] 
[inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A)   {x : A}, x ∈
 S → ∀ (…
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `Polynomial.coeff_natDegree`：coeff_natDegree : coeff p (natDegree p) = le
adingCoeff p
· 使用定理 `add_eq_zero_iff_eq_neg'`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G},
 a + b = 0 ↔ b = -a
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Polynomial.aeval_eq_sum_range`：aeval_eq_sum_range [Algebra R S] {p : R[X
]} (x : S) : aeval x p = ∑ i in Finset.range (p.natDegree + 1), p.coeff i • x ^ 
i
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用引理 `Finset.mul_sum`：mul_sum (s : Finset ι) (f : ι -> R) (a : R) : a * ∑ i in
 s, f i = ∑ i in s, a * f i
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `mul_smul_comm`：mul_smul_comm [Mul β] [SMul α β] [SMulCommClass α β β] (s
 : α) (x y : β) : x * s • y = s • (x * y)
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `NegMemClass.neg_mem`：∀ {S : Type u_3} {G : outParam (Type u_4)} {inst : 
Neg G} {inst_1 : SetLike S G} [self : NegMemClass S G] {s : S}   {x : G}, x ∈ s 
→ -x ∈ s
（共 35 条，此处仅展示前 30 条）
-/
lemma IsIntegral.isAlmostIntegral_of_exists_smul_mem_range
    {s : S} (H : IsIntegral R s) (h : ∃ t ∈ R⁰, t • s ∈ (algebraMap R S).range) :
    IsAlmostIntegral R s := by
  obtain ⟨b, hb', hb⟩ :
      ∃ b ∈ R⁰, ∀ i < (minpoly R s).natDegree, (b • s ^ i) ∈ (algebraMap R S).range := by
    obtain ⟨t, ht, ht'⟩ := h
    refine ⟨t ^ (minpoly R s).natDegree, pow_mem ht _, fun i hi ↦ ?_⟩
    rw [← Nat.sub_add_cancel hi.le, pow_add, mul_smul, ← smul_pow]
    exact (AlgHom.range (Algebra.ofId _ _)).smul_mem (Subalgebra.pow_mem _ ht' _) _
  refine ⟨b, hb', fun n ↦ ?_⟩
  induction n using Nat.strong_induction_on with | h n IH =>
  obtain hn | hn := lt_or_ge n (minpoly R s).natDegree
  · exact hb _ (by simpa)
  have := minpoly.aeval R s
  rw [Polynomial.aeval_eq_sum_range, Finset.sum_range_succ, add_eq_zero_iff_eq_neg',
    Polynomial.coeff_natDegree, minpoly.monic H, one_smul] at this
  rw [← Nat.sub_add_cancel hn, pow_add, this, mul_neg, smul_neg, Finset.mul_sum, Finset.smul_sum]
  simp_rw [mul_smul_comm, ← pow_add, smul_comm b]
  refine neg_mem (sum_mem fun i hi ↦ (AlgHom.range (Algebra.ofId _ _)).smul_mem (IH _ ?_) _)
  simp only [Finset.mem_range] at hi
  lia
/-
**IsIntegral.isAlmostIntegral_of_isLocalization** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegral.isAlmostIntegral_of_isLocalization {s : S} (H : IsIntegral R s)
 (M : Submonoid R) (hM : M <= R⁰) [IsLocalization M S] : IsAlmostIntegral R s
参数：H : IsIntegral R s；M : Submonoid R；hM : M <= R⁰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用引理 `IsIntegral.isAlmostIntegral_of_exists_smul_mem_range`：IsIntegral.isAlmos
tIntegral_of_exists_smul_mem_range {s : S} (H : IsIntegral R s) (h : exists t in
 R⁰, t • s in (algebraMap R S).range) : Is…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalization.smul_mk'_self`：∀ {R : Type u_1} [inst : CommSemiring R] {
M : Submonoid R} {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
-/
lemma IsIntegral.isAlmostIntegral_of_isLocalization
    {s : S} (H : IsIntegral R s) (M : Submonoid R) (hM : M ≤ R⁰) [IsLocalization M S] :
    IsAlmostIntegral R s := by
  obtain ⟨s, t, rfl⟩ := IsLocalization.exists_mk'_eq M s
  exact H.isAlmostIntegral_of_exists_smul_mem_range ⟨t, hM t.2, by simp⟩

@[stacks 00GX "Part 2"]
/-
**IsIntegral.isAlmostIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegral.isAlmostIntegral [IsFractionRing R S] {s : S} (H : IsIntegral R
 s) : IsAlmostIntegral R s
参数：H : IsIntegral R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIntegral.isAlmostIntegral_of_isLocalization`：IsIntegral.isAlmostIntegr
al_of_isLocalization {s : S} (H : IsIntegral R s) (M : Submonoid R) (hM : M <= R
⁰) [IsLocalization M S] : IsAlmostI…
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma IsIntegral.isAlmostIntegral [IsFractionRing R S]
    {s : S} (H : IsIntegral R s) : IsAlmostIntegral R s :=
  H.isAlmostIntegral_of_isLocalization _ le_rfl
/-
**integralClosure_le_completeIntegralClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：integralClosure_le_completeIntegralClosure [IsFractionRing R S] : integral
Closure R S <= completeIntegralClosure R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsIntegral.isAlmostIntegral`：IsIntegral.isAlmostIntegral [IsFractionRing
 R S] {s : S} (H : IsIntegral R s) : IsAlmostIntegral R s
-/
lemma integralClosure_le_completeIntegralClosure [IsFractionRing R S] :
    integralClosure R S ≤ completeIntegralClosure R S :=
  fun _ h ↦ h.isAlmostIntegral
/-
**IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap** 是 Mathlib 中的一个引理，位于命
名空间 ``。
形式化陈述：IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap {s : S} (H : IsAlm
ostIntegral R s) [IsNoetherianRing R] (H' : R⁰ <= S⁰.comap (algebraMap R S)) : I
sIntegral R s
参数：H : IsAlmostIntegral R s；H' : R⁰ <= S⁰.comap (algebraMap R S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower`：∀ {R : Type u_1} {R' : Type u_2} {M :
 Type u_3} {X : Type u_4} [inst : Monoid M] {S : Submonoid M}   [inst_1 : OreLoc
alization.OreSet S] [in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_span`：adjoin_eq_span : Subalgebra.toSubmodule (adjoin 
R s) = span R (Submonoid.closure s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.powers_eq_closure`：powers_eq_closure (n : M) : powers n = clos
ure {n}
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `Localization.mk_eq_mk'`：mk_eq_mk'_apply (x y) : mk x y = IsLocalization.
mk' (Localization M) x y
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsLocalization.mk'_spec'_mk`：∀ {R : Type u_1} [inst : CommSemiring R] {M
 : Submonoid R} (S : Type u_2) [inst_1 : CommSemiring S]   [inst_2 : Algebra R S
] [inst_3 : IsLoc…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `IsScalarTower.algebraMap_apply`：algebraMap_apply (x : R) : algebraMap R 
A x = algebraMap S A (algebraMap R S x)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
（共 37 条，此处仅展示前 30 条）
-/
lemma IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap
    {s : S} (H : IsAlmostIntegral R s) [IsNoetherianRing R]
    (H' : R⁰ ≤ S⁰.comap (algebraMap R S)) : IsIntegral R s := by
  obtain ⟨r, hr, hr'⟩ := H
  let f : Algebra.adjoin R {s} →ₗ[R]
      Submodule.span R {Localization.Away.invSelf (algebraMap R S r)} :=
    (IsScalarTower.toAlgHom R S (Localization.Away (algebraMap R S r))).toLinearMap.restrict
      (p := (Algebra.adjoin R {s}).toSubmodule) <| by
    change (Algebra.adjoin R {s}).toSubmodule ≤ (Submodule.span _ _).comap _
    rw [Algebra.adjoin_eq_span, ← Submonoid.powers_eq_closure, Submodule.span_le]
    rintro _ ⟨n, rfl⟩
    obtain ⟨a, ha⟩ := hr' n
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    suffices algebraMap _ _ (s ^ n) * algebraMap _ _ ((algebraMap R S) r) *
        Localization.Away.invSelf ((algebraMap R S) r) = algebraMap S _ (s ^ n) by
      simpa [Algebra.smul_def, IsScalarTower.algebraMap_apply R S (Localization.Away _),
        ha, mul_assoc, mul_left_comm] using this
    simp [mul_assoc, Localization.Away.invSelf, Localization.mk_eq_mk']
  have : Function.Injective f := by
    have : Function.Injective (algebraMap S (Localization.Away (algebraMap R S r))) := by
      apply IsLocalization.injective (M := .powers (algebraMap R S r))
      exact Submonoid.powers_le.mpr (H' hr)
    exact fun x y e ↦ Subtype.ext (this congr($e))
  have : (Algebra.adjoin R {s}).toSubmodule.FG := by
    rw [← Module.Finite.iff_fg]
    exact .of_injective f this
  exact .of_mem_of_fg _ this _ (Algebra.self_mem_adjoin_singleton R s)

@[stacks 00GX "Part 3"]
/-
**IsAlmostIntegral.isIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAlmostIntegral.isIntegral [IsNoetherianRing R] [IsDomain S] [FaithfulSMu
l R S] {s : S} (H : IsAlmostIntegral R s) : IsIntegral R s
参数：H : IsAlmostIntegral R s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsDomain.of_faithfulSMul`：IsDomain.of_faithfulSMul [IsDomain A] : IsDoma
in R
· 使用引理 `IsAlmostIntegral.isIntegral_of_nonZeroDivisors_le_comap`：IsAlmostIntegra
l.isIntegral_of_nonZeroDivisors_le_comap {s : S} (H : IsAlmostIntegral R s) [IsN
oetherianRing R] (H' : R⁰ <= S⁰.comap (algebr…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma IsAlmostIntegral.isIntegral [IsNoetherianRing R] [IsDomain S] [FaithfulSMul R S]
    {s : S} (H : IsAlmostIntegral R s) : IsIntegral R s := by
  have := IsDomain.of_faithfulSMul R S
  exact H.isIntegral_of_nonZeroDivisors_le_comap fun _ ↦ by simp
/-
**isAlmostIntegral_iff_isIntegral** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isAlmostIntegral_iff_isIntegral [IsNoetherianRing R] [IsDomain R] [IsFract
ionRing R S] {s : S} : IsAlmostIntegral R s ↔ IsIntegral R s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAlmostIntegral.isIntegral`：IsAlmostIntegral.isIntegral [IsNoetherianRi
ng R] [IsDomain S] [FaithfulSMul R S] {s : S} (H : IsAlmostIntegral R s) : IsInt
egral R s
· 使用定理 `IsFractionRing.isDomain`：∀ (A : Type u_4) [inst : CommRing A] {K : Type 
u_5} [inst_1 : CommRing K] [inst_2 : Algebra A K] [IsFractionRing A K]   [IsDoma
in A], IsDoma…
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用引理 `IsIntegral.isAlmostIntegral`：IsIntegral.isAlmostIntegral [IsFractionRing
 R S] {s : S} (H : IsIntegral R s) : IsAlmostIntegral R s
-/
lemma isAlmostIntegral_iff_isIntegral [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S]
    {s : S} : IsAlmostIntegral R s ↔ IsIntegral R s :=
  letI := IsFractionRing.isDomain R (K := S)
  ⟨IsAlmostIntegral.isIntegral, IsIntegral.isAlmostIntegral⟩
/-
**completeIntegralClosure_eq_integralClosure** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completeIntegralClosure_eq_integralClosure [IsNoetherianRing R] [IsDomain 
R] [IsFractionRing R S] : completeIntegralClosure R S = integralClosure R S
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用引理 `isAlmostIntegral_iff_isIntegral`：isAlmostIntegral_iff_isIntegral [IsNoet
herianRing R] [IsDomain R] [IsFractionRing R S] {s : S} : IsAlmostIntegral R s ↔
 IsIntegral R s
-/
lemma completeIntegralClosure_eq_integralClosure
    [IsNoetherianRing R] [IsDomain R] [IsFractionRing R S] :
    completeIntegralClosure R S = integralClosure R S :=
  SetLike.ext fun _ ↦ isAlmostIntegral_iff_isIntegral

end

