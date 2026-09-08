/-
Copyright (c) 2021 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Quasispectrum
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Spectrum mapping theorem

This file develops and proves the spectral mapping theorem for polynomials over algebraically closed
fields. In particular, if `a` is an element of a `𝕜`-algebra `A` where `𝕜` is a field, and
`p : 𝕜[X]` is a polynomial, then the spectrum of `Polynomial.aeval a p` contains the image of the
spectrum of `a` under `(fun k ↦ Polynomial.eval k p)`. When `𝕜` is algebraically closed,
these are in fact equal (assuming either that the spectrum of `a` is nonempty or the polynomial
has positive degree), which is the **spectral mapping theorem**.

In addition, this file contains the fact that every element of a finite-dimensional nontrivial
algebra over an algebraically closed field has nonempty spectrum. In particular, this is used in
`Module.End.exists_eigenvalue` to show that every linear map from a vector space to itself has an
eigenvalue.

## Main statements

* `spectrum.subset_polynomial_aeval`, `spectrum.map_polynomial_aeval_of_degree_pos`,
  `spectrum.map_polynomial_aeval_of_nonempty`: variations on the **spectral mapping theorem**.
* `spectrum.nonempty_of_isAlgClosed_of_finiteDimensional`: the spectrum is nonempty for any
  element of a nontrivial finite-dimensional algebra over an algebraically closed field.

## Notation

* `σ a` : `spectrum R a` of `a : A`
-/

public section

namespace spectrum

open Set Polynomial

open scoped Pointwise Polynomial

universe u v

section ScalarRing

variable {R : Type u} {A : Type v}
variable [CommRing R] [Ring A] [Algebra R A]

local notation "σ" => spectrum R
local notation "↑ₐ" => algebraMap R A

/-
**spectrum.exists_mem_of_not_isUnit_aeval_prod** 是 Mathlib 中的一个定理，位于命名空间 `spectr
um`。
形式化陈述：exists_mem_of_not_isUnit_aeval_prod [IsDomain R] {p : R[X]} {a : A} (h : ¬
IsUnit (aeval a (Multiset.map (fun x : R => X - C x) p.roots).prod)) : exists k 
: R, k in σ a ∧ eval k p = 0
参数：h : ¬IsUnit (aeval a (Multiset.map (fun x : R => X - C x) p.roots).prod)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `List.prod_isUnit`：∀ {M : Type u_4} [inst : Monoid M] {L : List M}, (∀ m 
∈ L, IsUnit m) → IsUnit L.prod
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_list_prod`：map_list_prod {F : Type*} [FunLike F M N] [MonoidHomClass
 F M N] (f : F) (l : List M) : f l.prod = (l.map f).prod
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Multiset.prod_toList`：prod_toList (s : Multiset M) : s.toList.prod = s.p
rod
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用定理 `IsUnit.sub_iff`：IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsU
nit (y - x)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_roots'`：mem_roots' : a in p.roots ↔ p != 0 ∧ IsRoot p a
-/
theorem exists_mem_of_not_isUnit_aeval_prod [IsDomain R] {p : R[X]} {a : A}
    (h : ¬IsUnit (aeval a (Multiset.map (fun x : R => X - C x) p.roots).prod)) :
    ∃ k : R, k ∈ σ a ∧ eval k p = 0 := by
  rw [← Multiset.prod_toList, map_list_prod] at h
  replace h := mt List.prod_isUnit h
  simp only [not_forall, exists_prop, aeval_C, Multiset.mem_toList, List.mem_map, aeval_X,
    exists_exists_and_eq_and, Multiset.mem_map, map_sub] at h
  rcases h with ⟨r, r_mem, r_nu⟩
  exact ⟨r, by rwa [mem_iff, ← IsUnit.sub_iff], (mem_roots'.1 r_mem).2⟩

end ScalarRing

section ScalarField

variable {𝕜 : Type u} {A : Type v}
variable [Field 𝕜] [Ring A] [Algebra 𝕜 A]

local notation "σ" => spectrum 𝕜
local notation "↑ₐ" => algebraMap 𝕜 A

open Polynomial

/-- Half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degree_pos` and
`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically closed. -/
/-
**spectrum.subset_polynomial_aeval** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：subset_polynomial_aeval (a : A) (p : 𝕜[X]) : (eval · p) '' σ a subseteq σ 
(aeval a p)
参数：a : A；p : 𝕜[X]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `neg_mul_neg`：neg_mul_neg (a b : α) : -a * -b = a * b
· 使用定理 `Polynomial.mul_div_eq_iff_isRoot`：mul_div_eq_iff_isRoot : (X - C a) * (p
 / (X - C a)) = p ↔ IsRoot p a
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x

--- 原说明 ---
Half of the spectral mapping theorem for polynomials. We prove it separately
because it holds over any field, whereas `spectrum.map_polynomial_aeval_of_degre
e_pos` and
`spectrum.map_polynomial_aeval_of_nonempty` need the field to be algebraically c
losed.
-/
theorem subset_polynomial_aeval (a : A) (p : 𝕜[X]) : (eval · p) '' σ a ⊆ σ (aeval a p) := by
  rintro _ ⟨k, hk, rfl⟩
  let q := C (eval k p) - p
  have hroot : IsRoot q k := by simp only [q, eval_C, eval_sub, sub_self, IsRoot.def]
  rw [← mul_div_eq_iff_isRoot, ← neg_mul_neg, neg_sub] at hroot
  have aeval_q_eq : ↑ₐ (eval k p) - aeval a p = aeval a q := by
    simp only [q, aeval_C, map_sub]
  rw [mem_iff, aeval_q_eq, ← hroot, aeval_mul]
  have hcomm := (Commute.all (C k - X) (-(q / (X - C k)))).map (aeval a : 𝕜[X] →ₐ[𝕜] A)
  apply mt fun h => (hcomm.isUnit_mul_iff.mp h).1
  simpa only [aeval_X, aeval_C, map_sub] using! hk

/-- The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p > 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right-hand side,
assuming `[Nontrivial A]`, is `{k}` where `p = Polynomial.C k`. -/
/-
**spectrum.map_polynomial_aeval_of_degree_pos** 是 Mathlib 中的一个定理，位于命名空间 `spectru
m`。
形式化陈述：map_polynomial_aeval_of_degree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hde
g : 0 < degree p) : σ (aeval a p) = (eval · p) '' σ a
参数：a : A；p : 𝕜[X]；hdeg : 0 < degree p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Splits.eq_prod_roots`：∀ {R : Type u_1} [inst : CommRing R] {f
 : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f = Polynomial.C f.leadingC
oeff * (Multiset.map …
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits
· 使用定理 `Polynomial.ne_zero_of_degree_gt`：ne_zero_of_degree_gt {n : WithBot Nat} 
(h : n < degree p) : p != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_sub_eq_right_of_degree_lt`：degree_sub_eq_right_of_degr
ee_lt (h : degree p < degree q) : degree (p - q) = degree q
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.leadingCoeff_ne_zero`：leadingCoeff_ne_zero : leadingCoeff p !
= 0 ↔ p != 0
· 使用定理 `Units.isUnit`：∀ {M : Type u_1} [inst : Monoid M] (u : Mˣ), IsUnit ↑u
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `spectrum.exists_mem_of_not_isUnit_aeval_prod`：exists_mem_of_not_isUnit_a
eval_prod [IsDomain R] {p : R[X]} {a : A} (h : ¬IsUnit (aeval a (Multiset.map (f
un x : R => X - C x) p.roots).prod…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_and`：∀ {a b : Prop}, ¬(a ∧ b) ↔ a → ¬b
· 使用定理 `Commute.isUnit_mul_iff`：Commute.isUnit_mul_iff (h : Commute a b) : IsUni
t (a * b) ↔ IsUnit a ∧ IsUnit b
· 使用定理 `Commute.map`：∀ {F : Type u_1} {M : Type u_2} {N : Type u_3} [inst : Mul 
M] [inst_1 : Mul N] {x y : M} [inst_2 : FunLike F M N]   [MulHomClass F M N], Co
m…
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
The *spectral mapping theorem* for polynomials.  Note: the assumption `degree p 
> 0`
is necessary in case `σ a = ∅`, for then the left-hand side is `∅` and the right
-hand side,
assuming `[Nontrivial A]`, is `{k}` where `p = Polynomial.C k`.
-/
theorem map_polynomial_aeval_of_degree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hdeg : 0 < degree p) : σ (aeval a p) = (eval · p) '' σ a := by
  -- handle the easy direction via `spectrum.subset_polynomial_aeval`
  refine Set.eq_of_subset_of_subset (fun k hk => ?_) (subset_polynomial_aeval a p)
  -- write `C k - p` product of linear factors and a constant; show `C k - p ≠ 0`.
  have hprod := (IsAlgClosed.splits (C k - p)).eq_prod_roots
  have h_ne : C k - p ≠ 0 := ne_zero_of_degree_gt <| by
    rwa [degree_sub_eq_right_of_degree_lt (lt_of_le_of_lt degree_C_le hdeg)]
  have lead_ne := leadingCoeff_ne_zero.mpr h_ne
  have lead_unit := (Units.map ↑ₐ.toMonoidHom (Units.mk0 _ lead_ne)).isUnit
  /- leading coefficient is a unit so product of linear factors is not a unit;
    apply `exists_mem_of_not_is_unit_aeval_prod`. -/
  have p_a_eq : aeval a (C k - p) = ↑ₐ k - aeval a p := by
    simp only [aeval_C, map_sub]
  rw [mem_iff, ← p_a_eq, hprod, aeval_mul,
    ((Commute.all _ _).map (aeval a : 𝕜[X] →ₐ[𝕜] A)).isUnit_mul_iff, aeval_C] at hk
  replace hk := exists_mem_of_not_isUnit_aeval_prod (not_and.mp hk lead_unit)
  rcases hk with ⟨r, r_mem, r_ev⟩
  exact ⟨r, r_mem, symm (by simpa [eval_sub, eval_C, sub_eq_zero] using r_ev)⟩

/-- In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive. -/
/-
**spectrum.map_polynomial_aeval_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`
。
形式化陈述：map_polynomial_aeval_of_nonempty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hnon 
: (σ a).Nonempty) : σ (aeval a p) = (fun k => eval k p) '' σ a
参数：a : A；p : 𝕜[X]；hnon : (σ a).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.aeval_C`：aeval_C (r : R) : aeval x (C r) = algebraMap R A r
· 使用定理 `spectrum.scalar_eq`：scalar_eq [Nontrivial A] (k : 𝕜) : σ (↑ₐ k) = {k}
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `Set.Nonempty.image_const`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s
.Nonempty → ∀ (a : β), (fun x => a) '' s = {a}
· 使用定理 `spectrum.map_polynomial_aeval_of_degree_pos`：map_polynomial_aeval_of_deg
ree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hdeg : 0 < degree p) : σ (aeval a p)
 = (eval · p) '' σ a

--- 原说明 ---
In this version of the spectral mapping theorem, we assume the spectrum
is nonempty instead of assuming the degree of the polynomial is positive.
-/
theorem map_polynomial_aeval_of_nonempty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X])
    (hnon : (σ a).Nonempty) : σ (aeval a p) = (fun k => eval k p) '' σ a := by
  nontriviality A
  refine Or.elim (le_or_gt (degree p) 0) (fun h => ?_) (map_polynomial_aeval_of_degree_pos a p)
  rw [eq_C_of_degree_le_zero h]
  simp only [eval_C, aeval_C, scalar_eq, Set.Nonempty.image_const hnon]

/-- A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for convenience. -/
/-
**spectrum.pow_image_subset** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：pow_image_subset (a : A) (n : Nat) : (fun x => x ^ n) '' σ a subseteq σ (a
 ^ n)
参数：a : A；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `spectrum.subset_polynomial_aeval`：subset_polynomial_aeval (a : A) (p : 𝕜
[X]) : (eval · p) '' σ a subseteq σ (aeval a p)

--- 原说明 ---
A specialization of `spectrum.subset_polynomial_aeval` to monic monomials for co
nvenience.
-/
theorem pow_image_subset (a : A) (n : ℕ) : (fun x => x ^ n) '' σ a ⊆ σ (a ^ n) := by
  simpa only [eval_X_pow, aeval_X_pow] using subset_polynomial_aeval a (X ^ n : 𝕜[X])
/-
**spectrum.pow_mem_pow** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：pow_mem_pow (a : A) (n : Nat) {k : 𝕜} (hk : k in σ a) : k ^ n in σ (a ^ n)
参数：a : A；n : Nat；hk : k in σ a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `spectrum.pow_image_subset`：pow_image_subset (a : A) (n : Nat) : (fun x =
> x ^ n) '' σ a subseteq σ (a ^ n)
-/
theorem pow_mem_pow (a : A) (n : ℕ) {k : 𝕜} (hk : k ∈ σ a) : k ^ n ∈ σ (a ^ n) :=
  pow_image_subset a n ⟨k, ⟨hk, rfl⟩⟩

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
/-
**spectrum.map_pow_of_pos** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：map_pow_of_pos [IsAlgClosed 𝕜] (a : A) {n : Nat} (hn : 0 < n) : σ (a ^ n) 
= (· ^ n) '' σ a
参数：a : A；hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `spectrum.map_polynomial_aeval_of_degree_pos`：map_polynomial_aeval_of_deg
ree_pos [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hdeg : 0 < degree p) : σ (aeval a p)
 = (eval · p) '' σ a
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `WithBot.instIsOrderedRing`：∀ {α : Type u_1} [inst : DecidableEq α] [inst
_1 : CommSemiring α] [inst_2 : PartialOrder α] [IsOrderedRing α]   [inst_4 : Can
onicallyOrdered…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomia
ls for
convenience.
-/
theorem map_pow_of_pos [IsAlgClosed 𝕜] (a : A) {n : ℕ} (hn : 0 < n) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_X_pow]
    using map_polynomial_aeval_of_degree_pos a (X ^ n : 𝕜[X]) (by rwa [degree_X_pow, Nat.cast_pos])

/-- A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomials for
convenience. -/
/-
**spectrum.map_pow_of_nonempty** 是 Mathlib 中的一个定理，位于命名空间 `spectrum`。
形式化陈述：map_pow_of_nonempty [IsAlgClosed 𝕜] {a : A} (ha : (σ a).Nonempty) (n : Nat
) : σ (a ^ n) = (· ^ n) '' σ a
参数：ha : (σ a).Nonempty；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.aeval_X_pow`：aeval_X_pow {n : Nat} : aeval x ((X : R[X]) ^ n)
 = x ^ n
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Polynomial.eval_X_pow`：eval_X_pow {x : R} (n : Nat) : (X ^ n : R[X]).eva
l x = x ^ n
· 使用定理 `spectrum.map_polynomial_aeval_of_nonempty`：map_polynomial_aeval_of_nonem
pty [IsAlgClosed 𝕜] (a : A) (p : 𝕜[X]) (hnon : (σ a).Nonempty) : σ (aeval a p) =
 (fun k => eval k p) '' σ a

--- 原说明 ---
A specialization of `spectrum.map_polynomial_aeval_of_nonempty` to monic monomia
ls for
convenience.
-/
theorem map_pow_of_nonempty [IsAlgClosed 𝕜] {a : A} (ha : (σ a).Nonempty) (n : ℕ) :
    σ (a ^ n) = (· ^ n) '' σ a := by
  simpa only [aeval_X_pow, eval_X_pow] using map_polynomial_aeval_of_nonempty a (X ^ n) ha

variable (𝕜)

-- We will use this both to show eigenvalues exist, and to prove Schur's lemma.
/-- Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum. -/
/-
**spectrum.nonempty_of_isAlgClosed_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空
间 `spectrum`。
形式化陈述：nonempty_of_isAlgClosed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A
] [I : FiniteDimensional 𝕜 A] (a : A) : (σ a).Nonempty
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isIntegral_of_noetherian`：isIntegral_of_noetherian (_ : IsNoetherian R B
) (x : B) : IsIntegral R x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsNoetherian.iff_fg`：iff_fg : IsNoetherian K V ↔ Module.Finite K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `spectrum.exists_mem_of_not_isUnit_aeval_prod`：exists_mem_of_not_isUnit_a
eval_prod [IsDomain R] {p : R[X]} {a : A} (h : ¬IsUnit (aeval a (Multiset.map (f
un x : R => X - C x) p.roots).prod…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Polynomial.Splits.eq_prod_roots_of_monic`：∀ {R : Type u_1} [inst : CommR
ing R] {f : Polynomial R} [inst_1 : IsDomain R],   f.Splits → f.Monic → f = (Mul
tiset.map (fun x => Polynomial…
· 使用定理 `IsAlgClosed.splits`：∀ {k : Type u} {inst : Field k} [self : IsAlgClosed 
k] (p : Polynomial k), p.Splits

--- 原说明 ---
Every element `a` in a nontrivial finite-dimensional algebra `A`
over an algebraically closed field `𝕜` has non-empty spectrum.
-/
theorem nonempty_of_isAlgClosed_of_finiteDimensional [IsAlgClosed 𝕜] [Nontrivial A]
    [I : FiniteDimensional 𝕜 A] (a : A) : (σ a).Nonempty := by
  obtain ⟨p, ⟨h_mon, h_eval_p⟩⟩ := isIntegral_of_noetherian (IsNoetherian.iff_fg.2 I) a
  have nu : ¬IsUnit (aeval a p) := by rw [← aeval_def] at h_eval_p; rw [h_eval_p]; simp
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic h_mon] at nu
  obtain ⟨k, hk, _⟩ := exists_mem_of_not_isUnit_aeval_prod nu
  exact ⟨k, hk⟩

end ScalarField

end spectrum

open Polynomial in
/-
**IsIdempotentElem.spectrum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.spectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A
] [Algebra 𝕜 A] {p : A} (hp : IsIdempotentElem p) : spectrum 𝕜 p subseteq {0, 1}
参数：𝕜 : Type*；hp : IsIdempotentElem p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `spectrum.subset_polynomial_aeval`：subset_polynomial_aeval (a : A) (p : 𝕜
[X]) : (eval · p) '' σ a subseteq σ (aeval a p)
· 使用引理 `eq_zero_or_one_of_sq_eq_self`：eq_zero_or_one_of_sq_eq_self [MonoidWithZe
ro M₀] [IsRightCancelMulZero M₀] {x : M₀} (hx : x ^ 2 = x) : x = 0 ∨ x = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.eval_sub`：eval_sub (p q : R[X]) (x : R) : (p - q).eval x = p.
eval x - q.eval x
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.aeval_sub`：aeval_sub {p q : R[X]} [Ring A] [Algebra R A] (x :
 A) : aeval x (p - q) = aeval x p - aeval x q
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Polynomial.aeval_X`：aeval_X : aeval x (X : R[X]) = x
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用引理 `IsIdempotentElem.eq`：eq (ha : IsIdempotentElem a) : a * a = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `spectrum.zero_eq`：zero_eq [Nontrivial A] : σ (0 : A) = {0}
-/
theorem IsIdempotentElem.spectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {p : A} (hp : IsIdempotentElem p) : spectrum 𝕜 p ⊆ {0, 1} := by
  nontriviality A
  apply Set.image_subset_iff.mp (spectrum.subset_polynomial_aeval p (X ^ 2 - X)) |>.trans
  refine fun a ha => eq_zero_or_one_of_sq_eq_self ?_
  simpa [pow_two p, hp.eq, sub_eq_zero] using ha
/-
**IsIdempotentElem.finite_spectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.finite_spectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A
] [Algebra 𝕜 A] {p : A} (hp : IsIdempotentElem p) : (spectrum 𝕜 p).Finite
参数：𝕜 : Type*；hp : IsIdempotentElem p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.encard_pair`：encard_pair {x y : α} (hne : x != y) : ({x, y} : Set α)
.encard = 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.finite_of_encard_le_coe`：finite_of_encard_le_coe {k : Nat} (h : s.en
card <= k) : s.Finite
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `IsIdempotentElem.spectrum_subset`：IsIdempotentElem.spectrum_subset (𝕜 : 
Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {p : A} (hp : IsIdempotentEl
em p) : spectrum 𝕜 p s…
-/
lemma IsIdempotentElem.finite_spectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A]
    {p : A} (hp : IsIdempotentElem p) : (spectrum 𝕜 p).Finite :=
  have : ({0, 1} : Set 𝕜).encard = (2 : ℕ) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.spectrum_subset 𝕜))

open Unitization in
/-
**IsIdempotentElem.quasispectrum_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.quasispectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [N
onUnitalRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A}
 (hp : IsIdempotentElem p) : quasispectrum 𝕜 p subseteq {0, 1}
参数：𝕜 : Type*；hp : IsIdempotentElem p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIdempotentElem.spectrum_subset`：IsIdempotentElem.spectrum_subset (𝕜 : 
Type*) {A : Type*} [Field 𝕜] [Ring A] [Algebra 𝕜 A] {p : A} (hp : IsIdempotentEl
em p) : spectrum 𝕜 p s…
· 使用定理 `Unitization.IsIdempotentElem.inr`：∀ (R : Type u_1) {A : Type u_2} [inst 
: MulZeroClass R] [inst_1 : AddZeroClass A] [inst_2 : Mul A]   [inst_3 : SMulWit
hZero R A] {a : A}, Is…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
-/
theorem IsIdempotentElem.quasispectrum_subset (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
    [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A} (hp : IsIdempotentElem p) :
    quasispectrum 𝕜 p ⊆ {0, 1} :=
  quasispectrum_eq_spectrum_inr' 𝕜 𝕜 p ▸ (hp.inr _ |>.spectrum_subset _)
/-
**IsIdempotentElem.finite_quasispectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsIdempotentElem.finite_quasispectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [N
onUnitalRing A] [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A}
 (hp : IsIdempotentElem p) : (quasispectrum 𝕜 p).Finite
参数：𝕜 : Type*；hp : IsIdempotentElem p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.encard_pair`：encard_pair {x y : α} (hne : x != y) : ({x, y} : Set α)
.encard = 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.finite_of_encard_le_coe`：finite_of_encard_le_coe {k : Nat} (h : s.en
card <= k) : s.Finite
· 使用定理 `Set.encard_le_encard`：encard_le_encard (h : s subseteq t) : s.encard <= 
t.encard
· 使用定理 `IsIdempotentElem.quasispectrum_subset`：IsIdempotentElem.quasispectrum_su
bset (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A] [Module 𝕜 A] [IsScalarT
ower 𝕜 A A] [SMulCommClass …
-/
theorem IsIdempotentElem.finite_quasispectrum (𝕜 : Type*) {A : Type*} [Field 𝕜] [NonUnitalRing A]
    [Module 𝕜 A] [IsScalarTower 𝕜 A A] [SMulCommClass 𝕜 A A] {p : A} (hp : IsIdempotentElem p) :
    (quasispectrum 𝕜 p).Finite :=
  have : ({0, 1} : Set 𝕜).encard = (2 : ℕ) := Set.encard_pair (by simp)
  Set.finite_of_encard_le_coe (this ▸ Set.encard_le_encard (hp.quasispectrum_subset 𝕜))
