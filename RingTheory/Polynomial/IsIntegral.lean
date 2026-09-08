/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.Data.Multiset.Fintype
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.AlmostIntegral

/-!

# Results about coefficients of polynomials being integral

## Main results
- `Polynomial.isIntegral_coeff_of_dvd`: If a monic polynomial `p` divides another monic polynomial
  with integral coefficients, then the coefficients of `p` are themselves integral.
- `Polynomial.isIntegral_iff_isIntegral_coeff`:
  `p : S[X]` is integral over `R[X]` iff the coefficients of `p` are integral over `R`.
- `MvPolynomial.isIntegral_iff_isIntegral_coeff`: `p : MvPolynomial σ S` is integral over
  `MvPolynomial σ R` iff the coefficients of `p` are integral over `R`.
- We also provide the instance `[IsIntegrallyClosed R] : IsIntegrallyClosed R[X]`.

-/

public section

variable {R S ι : Type*} [CommRing R] [CommRing S] [Algebra R S]

namespace Polynomial

/-
**Polynomial.isIntegral_coeff_prod** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isIntegral_coeff_prod (s : Finset ι) (p : ι -> S[X]) (H : forall i in s, f
orall j, IsIntegral R ((p i).coeff j)) (j : Nat) : IsIntegral R ((s.prod p).coef
f j)
参数：s : Finset ι；p : ι -> S[X]；H : forall i in s, forall j, IsIntegral R ((p i).c
oeff j)；j : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst : De
cidableEq α],   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → motive s → motive 
(inser…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
· 使用定理 `apply_ite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst 
: Decidable P] (x y : α),   f (if P then x else y) = if P then f x else f y
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `IsIntegral.sum`：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (
h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma isIntegral_coeff_prod
    (s : Finset ι) (p : ι → S[X]) (H : ∀ i ∈ s, ∀ j, IsIntegral R ((p i).coeff j)) (j : ℕ) :
    IsIntegral R ((s.prod p).coeff j) := by
  classical
  induction s using Finset.induction generalizing j with
  | empty => simp [coeff_one, apply_ite, isIntegral_zero, isIntegral_one]
  | insert a s has IH =>
    rw [Finset.prod_insert has, coeff_mul]
    exact IsIntegral.sum _ fun i hi ↦ .mul (H _ (by simp) _) (IH (fun _ _ ↦ H _ (by aesop)) _)
/-
**Polynomial.isIntegral_coeff_of_factors** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isIntegral_coeff_of_factors (p : S[X]) (hpmon : IsIntegral R p.leadingCoef
f) (hp : p.Splits) (hpr : forall x, p.IsRoot x -> IsIntegral R x) (i : Nat) : Is
Integral R (p.coeff i)
参数：p : S[X]；hpmon : IsIntegral R p.leadingCoeff；hp : p.Splits；hpr : forall x, p.
IsRoot x -> IsIntegral R x；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.splits_iff_exists_multiset`：splits_iff_exists_multiset : Spli
ts f ↔ exists m : Multiset R, f = C f.leadingCoeff * (m.map (X - C ·)).prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.prod_eq_prod_coe`：prod_eq_prod_coe [CommMonoid α] (m : Multiset
 α) : m.prod = ∏ x : m, (x : α)
· 使用定理 `Polynomial.coeff_C_mul`：coeff_C_mul (p : R[X]) : coeff (C a * p) n = a *
 coeff p n
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用引理 `Polynomial.isIntegral_coeff_prod`：isIntegral_coeff_prod (s : Finset ι) (
p : ι -> S[X]) (H : forall i in s, forall j, IsIntegral R ((p i).coeff j)) (j : 
Nat) : IsIntegral R ((…
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_multiset_prod`：eval_multiset_prod (s : Multiset R[X]) (x
 : R) : eval x s.prod = (s.map (eval x)).prod
· 使用引理 `Multiset.prod_eq_zero`：prod_eq_zero (h : (0 : M₀) in s) : s.prod = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Multiset.map_map`：map_map (g : β -> γ) (f : α -> β) (s : Multiset α) : m
ap g (map f s) = map (g ∘ f) s
· 使用定理 `Multiset.map_congr`：map_congr {f g : α -> β} {s t : Multiset α} : s = t 
-> (forall x in t, f x = g x) -> map f s = map g t
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Multiset.mem_map`：mem_map {f : α -> β} {b : β} {s : Multiset α} : b in m
ap f s ↔ exists a, a in s ∧ f a = b
· 使用定理 `Multiset.count_pos`：count_pos {a : α} {s : Multiset α} : 0 < count a s ↔
 a in s
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Polynomial.coeff_sub`：coeff_sub (p q : R[X]) (n : Nat) : coeff (p - q) n
 = coeff p n - coeff q n
· 使用定理 `Polynomial.coeff_X`：coeff_X : coeff (X : R[X]) n = if 1 = n then 1 else 
0
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
（共 35 条，此处仅展示前 30 条）
-/
lemma isIntegral_coeff_of_factors (p : S[X])
    (hpmon : IsIntegral R p.leadingCoeff) (hp : p.Splits)
    (hpr : ∀ x, p.IsRoot x → IsIntegral R x) (i : ℕ) :
    IsIntegral R (p.coeff i) := by
  classical
  obtain ⟨m, hm⟩ := Polynomial.splits_iff_exists_multiset.mp hp
  rw [hm, Multiset.prod_eq_prod_coe, coeff_C_mul]
  refine .mul hpmon (isIntegral_coeff_prod _ _ ?_ _)
  have H {x} (hx : x ∈ m) : p.IsRoot x := by
    rw [IsRoot, hm, eval_mul, eval_multiset_prod, Multiset.prod_eq_zero, mul_zero]
    simpa [sub_eq_zero]
  rintro ⟨a, ⟨i, hi⟩⟩ -
  obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.mp (Multiset.count_pos.mp (i.zero_le.trans_lt hi))
  simp [coeff_X, coeff_C, IsIntegral.sub, apply_ite (IsIntegral R),
    isIntegral_one, isIntegral_zero, hpr x (H hx)]

open scoped TensorProduct in
@[stacks 00H6 "(1)"]
/-
**Polynomial.isIntegral_coeff_of_dvd** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isIntegral_coeff_of_dvd (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic
) (H : q ∣ p.map (algebraMap R S)) (i : Nat) : IsIntegral R (q.coeff i)
参数：p : R[X]；q : S[X]；hp : p.Monic；hq : q.Monic；H : q ∣ p.map (algebraMap R S)；i 
: Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用引理 `Polynomial.Monic.exists_splits_map`：Polynomial.Monic.exists_splits_map.{
u} {R : Type u} [CommRing R] [Nontrivial R] {p : R[X]} (hp : p.Monic) : exists (
S : Type u) (_ : CommRin…
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isIntegral_algHom_iff`：isIntegral_algHom_iff (f : A ->ₐ[R] B) (hf : Func
tion.Injective f) {x : A} : IsIntegral R (f x) ↔ IsIntegral R x
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.coe_toAlgHom'`：coe_toAlgHom' : (toAlgHom R S A : S -> A) =
 algebraMap S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用引理 `Polynomial.isIntegral_coeff_of_factors`：isIntegral_coeff_of_factors (p :
 S[X]) (hpmon : IsIntegral R p.leadingCoeff) (hp : p.Splits) (hpr : forall x, p.
IsRoot x -> IsIntegral R x) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Polynomial.Monic.map`：∀ {R : Type u} {S : Type v} [inst : Semiring R] {p
 : Polynomial R} [inst_1 : Semiring S] (f : R →+* S),   p.Monic → (Polynomial.ma
p f p).Mon…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_map_algebraMap`：aeval_map_algebraMap (x : B) (p : R[X])
 : aeval x (map (algebraMap R A) p) = aeval x p
· 使用定理 `Polynomial.aeval_eq_zero_of_dvd_aeval_eq_zero`：aeval_eq_zero_of_dvd_aeva
l_eq_zero {x : B} (h₁ : p ∣ q) (h₂ : aeval x p = 0) : aeval x q = 0
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isIntegral_coeff_of_dvd (p : R[X]) (q : S[X]) (hp : p.Monic) (hq : q.Monic)
    (H : q ∣ p.map (algebraMap R S)) (i : ℕ) : IsIntegral R (q.coeff i) := by
  nontriviality S
  obtain ⟨T, _, _, _, _, _, hqT⟩ := hq.exists_splits_map
  algebraize [(algebraMap S T).comp (algebraMap R S)]
  refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom R S T)
    (FaithfulSMul.algebraMap_injective S _)).mp ?_
  rw [IsScalarTower.coe_toAlgHom', ← coeff_map]
  refine Polynomial.isIntegral_coeff_of_factors _ (by simp [hq.map, isIntegral_one]) hqT ?_ i
  intro x hx
  exact ⟨p, hp, by simpa using! aeval_eq_zero_of_dvd_aeval_eq_zero (x := x) H (by simp_all)⟩

end Polynomial

section

open scoped nonZeroDivisors

open Polynomial

attribute [local instance] Polynomial.algebra

@[stacks 00H0 "(1)"]
/-
**IsAlmostIntegral.coeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsAlmostIntegral.coeff [IsDomain R] [FaithfulSMul R S] {p : S[X]} (hp : Is
AlmostIntegral R[X] p) (i : Nat) : IsAlmostIntegral R (p.coeff i)
参数：hp : IsAlmostIntegral R[X] p；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.instNoZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [NoZer
oDivisors R], NoZeroDivisors (Polynomial R)
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff_map_of_injective`：leadingCoeff_map_of_injective 
{f : R ->+* S} (hf : Function.Injective f) (p : Polynomial R) : (p.map f).leadin
gCoeff = f p.leadingCoeff
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Polynomial.leadingCoeff_pow'`：leadingCoeff_pow' : leadingCoeff p ^ n != 
0 -> leadingCoeff (p ^ n) = leadingCoeff p ^ n
· 使用定理 `Polynomial.leadingCoeff_mul'`：leadingCoeff_mul' (h : leadingCoeff p * le
adingCoeff q != 0) : leadingCoeff (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Polynomial.natDegree_eq_zero`：natDegree_eq_zero {p : R[X]} : p.natDegree
 = 0 ↔ exists x, C x = p
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Subalgebra.zero_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A] (S : Subalgebra R A),   0 ∈ S
（共 58 条，此处仅展示前 30 条）
-/
lemma IsAlmostIntegral.coeff [IsDomain R] [FaithfulSMul R S]
    {p : S[X]} (hp : IsAlmostIntegral R[X] p) (i : ℕ) :
    IsAlmostIntegral R (p.coeff i) := by
  have H {q : S[X]} (hq : IsAlmostIntegral R[X] q) : IsAlmostIntegral R q.leadingCoeff := by
    obtain ⟨p, hp, hp'⟩ := hq
    refine ⟨p.leadingCoeff, by simpa using hp, fun n ↦ ?_⟩
    obtain ⟨r, hr⟩ := hp' n
    simp only [Algebra.smul_def, algebraMap_def, coe_mapRingHom] at hr ⊢
    by_cases h : algebraMap R S p.leadingCoeff * q.leadingCoeff ^ n = 0
    · simp [h]
    have h' : q.leadingCoeff ^ n ≠ 0 := by aesop
    use r.leadingCoeff
    simp only [← leadingCoeff_map_of_injective (FaithfulSMul.algebraMap_injective R S), hr] at h ⊢
    rw [← leadingCoeff_pow' h'] at h ⊢
    rw [leadingCoeff_mul' h]
  induction hn : p.natDegree using Nat.strong_induction_on generalizing p with | h n IH =>
  by_cases hp' : p.natDegree = 0
  · obtain ⟨p, rfl⟩ := natDegree_eq_zero.mp hp'
    simp only [coeff_C]
    split_ifs with h
    · simpa using H hp
    · exact (completeIntegralClosure R S).zero_mem
  by_cases hi : i = p.natDegree
  · simp [hi, H hp]
  have : IsAlmostIntegral R[X] p.eraseLead := by
    rw [← self_sub_monomial_natDegree_leadingCoeff, ← mem_completeIntegralClosure,
      ← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S), ← Polynomial.map_pow]
    refine sub_mem hp (mul_mem ?_ (algebraMap_mem (R := R[X]) _ _))
    obtain ⟨r, hr, hr'⟩ := H hp
    refine ⟨C r, by simpa using hr, fun n ↦ ?_⟩
    obtain ⟨s, hs⟩ := hr' n
    exact ⟨C s, by simp [Algebra.smul_def, hs]⟩
  simpa [hi, eraseLead_coeff_of_ne] using
    IH (p := p.eraseLead) _ (p.eraseLead_natDegree_le.trans_lt (by lia)) this rfl

@[stacks 00H0 "(2)"]
/-
**IsIntegral.coeff** 是 Mathlib 中的一个定理，位于命名空间 `IsIntegral`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [inst_1 : CommRing S] 
[inst_2 : Algebra R S] {p : Polynomial S},   IsIntegral (Polynomial R) p → ∀ (i 
: ℕ), IsIntegral R (p.coeff i)
参数：Polynomial R；i : ℕ；p.coeff i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_subsingleton`：∀ (R : Type u_1) (M : Type u_2) [Subsingle
ton R] [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M], IsNoetherian…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Polynomial.eval_eq_sum_range`：eval_eq_sum_range {p : R[X]} (x : R) : p.e
val x = ∑ i in Finset.range (p.natDegree + 1), p.coeff i * x ^ i
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `Polynomial.Monic.add_of_right`：∀ {R : Type u} [inst : Semiring R] {p q :
 Polynomial R}, q.Monic → p.degree < q.degree → (p + q).Monic
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.Monic.leadingCoeff`：∀ {R : Type u} [inst : Semiring R] {p : P
olynomial R}, p.Monic → p.leadingCoeff = 1
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.degree_lt_degree`：degree_lt_degree (h : natDegree p < natDegr
ee q) : degree p < degree q
（共 78 条，此处仅展示前 30 条）
-/
protected lemma IsIntegral.coeff
    {p : S[X]} (hp : IsIntegral R[X] p) (i : ℕ) : IsIntegral R (p.coeff i) := by
  nontriviality R
  nontriviality S
  obtain rfl | hp0 := eq_or_ne p 0; · simp [isIntegral_zero]
  let q := minpoly R[X] p
  let m := (q.support.sup fun i ↦ (q.coeff i).natDegree) + p.natDegree + 1
  have hm₁ (i) : (q.coeff i).natDegree < m := by
    by_cases hi : i ∈ q.support
    · exact (Finset.le_sup (f := fun i ↦ (q.coeff i).natDegree) hi).trans_lt (by lia)
    · simp_all [m]
  have hm₁' : (q.eval (X ^ m)).Monic := by
    rw [eval_eq_sum_range, Finset.sum_range_succ]
    refine .add_of_right (by simp [q, minpoly.monic hp, ← pow_mul]) (degree_lt_degree ?_)
    refine lt_of_lt_of_eq (b := m * q.natDegree) ?_ (by simp [q, minpoly.monic hp, ← pow_mul])
    refine (natDegree_sum_le ..).trans_lt ((Finset.fold_max_lt _).mpr
      ⟨by simpa using ⟨by lia, minpoly.natDegree_pos hp⟩, fun i hi ↦ ?_⟩)
    dsimp
    simp only [Finset.mem_range] at hi
    grw [← pow_mul, natDegree_mul_le, natDegree_X_pow, ← Nat.add_one_le_iff.mpr hi]
    have := hm₁ i
    lia
  have hm₂ : p.natDegree < m := by grind
  have h₀ : algebraMap R[X] S[X] X = X := by simp
  have : (((taylor (X ^ m)) q).map (algebraMap R[X] S[X])).IsRoot (p - X ^ m) := by
    simpa [-algebraMap_def, q, h₀] using
      ((q.map (algebraMap _ _)).taylor_eval (X ^ m) (p - X ^ m) :)
  have : X ^ m - p ∣ (eval (X ^ m) q).map (algebraMap _ _) := by
    change X ^ m - p ∣ Algebra.ofId R[X] S[X] _
    rw [← coe_aeval_eq_eval, ← aeval_algHom_apply, ← neg_dvd, neg_sub]
    simpa [Polynomial.taylor_coeff_zero, -algebraMap_def, h₀] using this.dvd_coeff_zero
  have := (isIntegral_coeff_of_dvd _ _ hm₁'
    ((monic_X_pow _).sub_of_left (by simpa [← natDegree_lt_iff_degree_lt, hp0])) this i).neg
  obtain hi | hi := le_or_gt i p.natDegree
  · simpa [show i ≠ m by lia] using this
  · simp [coeff_eq_zero_of_natDegree_lt hi, isIntegral_zero]

@[deprecated (since := "2026-01-01")]
alias IsIntegral.coeff_of_exists_smul_mem_lifts := IsIntegral.coeff

@[deprecated (since := "2026-01-01")] alias IsIntegral.coeff_of_isFractionRing := IsIntegral.coeff
/-
**Polynomial.isIntegral_iff_isIntegral_coeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Polynomial.isIntegral_iff_isIntegral_coeff {f : S[X]} : IsIntegral R[X] f 
↔ forall n, IsIntegral R (f.coeff n)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.coeff`：∀ {R : Type u_1} {S : Type u_2} [inst : CommRing R] [i
nst_1 : CommRing S] [inst_2 : Algebra R S] {p : Polynomial S},   IsIntegral (Pol
ynomia…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `Polynomial.sum.eq_1`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} [
inst_1 : AddCommMonoid S] (p : Polynomial R) (f : ℕ → R → S),   p.sum f = ∑ n ∈ 
p.support…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `IsIntegral.sum`：IsIntegral.sum {α : Type*} {s : Finset α} (f : α -> A) (
h : forall x in s, IsIntegral R (f x)) : IsIntegral R (∑ x in s, f x)
· 使用定理 `IsIntegral.mul`：∀ {R : Type u_1} {A : Type u_2} [inst : CommRing R] [ins
t_1 : CommRing A] [inst_2 : Algebra R A] {x y : A},   IsIntegral R x → IsIntegra
l R …
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `IsIntegral.pow`：IsIntegral.pow {x : B} (h : IsIntegral R x) (n : Nat) : 
IsIntegral R (x ^ n)
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
-/
theorem Polynomial.isIntegral_iff_isIntegral_coeff {f : S[X]} :
    IsIntegral R[X] f ↔ ∀ n, IsIntegral R (f.coeff n) := by
  refine ⟨IsIntegral.coeff, fun H ↦ ?_⟩
  rw [← f.sum_monomial_eq, Polynomial.sum]
  simp only [← C_mul_X_pow_eq_monomial, ← map_X (algebraMap R S)]
  exact .sum _ fun i _ ↦ ((H i).map (CAlgHom (R := R))).tower_top.mul (.pow isIntegral_algebraMap _)
/-
**IsIntegral.of_aeval_monic_of_isIntegral_coeff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIntegral.of_aeval_monic_of_isIntegral_coeff {R A : Type*} [CommRing R] [
CommRing A] [Algebra R A] {x : A} {p : A[X]} (monic : p.Monic) (deg : p.natDegre
e != 0) (hx : IsIntegral R (eval x p)) (hp : forall i, IsIntegral R (p.coeff i))
 : IsIntegral R x
参数：monic : p.Monic；deg : p.natDegree != 0；hx : IsIntegral R (eval x p)；hp : fora
ll i, IsIntegral R (p.coeff i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.lifts_and_natDegree_eq_and_monic`：lifts_and_natDegree_eq_and_
monic {p : S[X]} (hlifts : p in lifts f) (hp : p.Monic) : exists q : R[X], map f
 q = p ∧ q.natDegree = p.natDegre…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.lifts_iff_coeff_lifts`：lifts_iff_coeff_lifts (p : S[X]) : p i
n lifts f ↔ forall n : Nat, p.coeff n in Set.range f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Subalgebra.setRange_algebraMap`：setRange_algebraMap {R A : Type*} [CommS
emiring R] [CommSemiring A] [Algebra R A] (S : Subalgebra R A) : Set.range (alge
braMap S A) = (S : S…
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsIntegral.of_aeval_monic`：IsIntegral.of_aeval_monic {x : A} {p : R[X]} 
(monic : p.Monic) (deg : p.natDegree != 0) (hx : IsIntegral R (aeval x p)) : IsI
ntegral R x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
-/
lemma IsIntegral.of_aeval_monic_of_isIntegral_coeff {R A : Type*} [CommRing R] [CommRing A]
    [Algebra R A] {x : A} {p : A[X]} (monic : p.Monic) (deg : p.natDegree ≠ 0)
    (hx : IsIntegral R (eval x p)) (hp : ∀ i, IsIntegral R (p.coeff i)) : IsIntegral R x := by
  obtain ⟨q, hqp, hdeg, hq⟩ :=
    lifts_and_natDegree_eq_and_monic (p := p) (f := algebraMap (integralClosure R A) _)
    (p.lifts_iff_coeff_lifts.mpr (by simpa)) monic
  exact isIntegral_trans _ (.of_aeval_monic hq (hdeg ▸ deg)
    (by simpa [← eval_map_algebraMap, hqp] using hx.tower_top))

@[stacks 030A]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] :
    IsIntegrallyClosed R[X] := by
  let K := FractionRing R
  have : IsIntegrallyClosed K[X] := UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn R[X] K[X] from .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ K[X]
  refine isIntegrallyClosedIn_iff.mpr ⟨map_injective _ (IsFractionRing.injective _ _), ?_⟩
  refine fun {p} hp ↦ (lifts_iff_coeff_lifts _).mpr fun n ↦ ?_
  exact IsIntegrallyClosed.isIntegral_iff.mp (hp.coeff _)

end

attribute [local instance] MvPolynomial.algebraMvPolynomial in
attribute [-simp] AlgEquiv.symm_toRingEquiv in
/-
**MvPolynomial.isIntegral_iff_isIntegral_coeff.** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem MvPolynomial.isIntegral_iff_isIntegral_coeff.{w} {σ : Type w} {f : MvPolynomial σ S} :
    IsIntegral (MvPolynomial σ R) f ↔ ∀ n, IsIntegral R (f.coeff n) := by
  refine ⟨fun H n ↦ ?mp, fun H ↦ ?mpr⟩
  case mpr =>
    rw [← f.support_sum_monomial_coeff]
    simp_rw [monomial_eq]
    refine IsIntegral.sum _ fun n _ ↦ .mul ((H n).map (Algebra.ofId _ _)).tower_top
      (.prod _ fun i _ ↦ .pow ?_ _)
    convert! isIntegral_algebraMap (x := MvPolynomial.X i)
    simp only [algebraMap_def, map_X]
  unfold IsIntegral at H
  wlog hσ : Finite σ generalizing σ
  · obtain ⟨g, hg⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range (τ := f.vars) f _
      Subtype.val_injective (by simp)
    by_cases hn : n ∈ Set.range (Finsupp.mapDomain ((↑) : f.vars → σ))
    · obtain ⟨n, rfl⟩ := hn
      simp_rw [← hg, coeff_rename_mapDomain _ Subtype.val_injective]
      exact this (f := g) (RingHom.IsIntegralElem.of_map
        (g := (rename ((↑) : f.vars → σ)).toRingHom) (rename_injective _ Subtype.val_injective)
        (.of_comp (f := (killCompl (f := ((↑) : f.vars → σ)) Subtype.val_injective).toRingHom) <| by
        simp only [AlgHom.toRingHom_eq_coe, algebraMap_def, RingHom.coe_coe, hg]
        convert!
          H.map
            ((rename Subtype.val).comp
                (killCompl (f := ((↑) : f.vars → σ)) Subtype.val_injective)).toRingHom
        · exact RingHom.ext (by simp [MvPolynomial.killCompl_map])
        · nth_rw 1 12 [← hg]; simp)) n (.of_fintype _)
    · rw [← hg, coeff_rename_eq_zero _ _ _ (by grind)]
      exact isIntegral_zero
  revert f n
  apply Finite.induction_empty_option _ _ _ σ
  · intro α β e IH f H n
    have := @IH (rename e.symm f) (.of_map (g := (rename e).toRingHom)
      (rename_injective _ e.injective) <| .of_comp (f := (rename e.symm).toRingHom)
        (by convert H <;> aesop)) (n.embDomain e.symm)
    simpa [Finsupp.embDomain_eq_mapDomain, coeff_rename_mapDomain _ e.symm.injective] using! this
  · intro f H n
    refine .of_map (g := (isEmptyAlgEquiv _ PEmpty).symm.toRingHom)
      (isEmptyAlgEquiv _ PEmpty).symm.injective
      (.of_comp (f := (isEmptyAlgEquiv _ PEmpty).toRingHom) ?_)
    convert! H
    · ext r m <;> simp [Subsingleton.elim m 0, C, X, monomial, coeff, map]
    · obtain rfl := Subsingleton.elim n 0
      have : constantCoeff = (isEmptyAlgEquiv S PEmpty).toRingHom := by aesop
      simpa [-EmbeddingLike.apply_eq_iff_eq, -isEmptyAlgEquiv_apply] using!
        congr((isEmptyAlgEquiv S PEmpty.{w + 1}).symm ($this f))
  · intro α _ IH f H n
    have := IH (IsIntegral.coeff (R := MvPolynomial α R)
      (p := optionEquivLeft _ _ f) (.of_map
      (g := (optionEquivLeft _ _).symm.toRingHom) (optionEquivLeft _ _).symm.injective
      (.of_comp (f := (optionEquivLeft _ _).toRingHom) (by
        convert! H
        · ext i m
          · aesop
          · cases i <;> aesop
        · aesop))) (n .none)) n.some
    rwa [optionEquivLeft_coeff_some_coeff_none] at this

end

