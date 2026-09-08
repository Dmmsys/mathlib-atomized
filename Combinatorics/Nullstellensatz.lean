/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/
module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Data.Finsupp.MonomialOrder.DegLex
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.MvPolynomial.Groebner
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.MonomialOrder.DegLex

/-! # Alon's Combinatorial Nullstellensatz

This is a formalization of Noga Alon's Combinatorial Nullstellensatz. It follows [Alon_1999].

We consider a family `S : σ → Finset R` of finite subsets of a domain `R`
and a multivariate polynomial `f` in `MvPolynomial σ R`.
The combinatorial Nullstellensatz gives combinatorial constraints for
the vanishing of `f` at any `x : σ → R` such that `x s ∈ S s` for all `s`.

- `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset` :
  if `f` vanishes at any such point and `f.degreeOf s < #(S s)` for all `s`,
  then `f = 0`.

- `combinatorial_nullstellensatz_exists_linearCombination`
  If `f` vanishes at every such point, then it can be written as a linear combination
  `f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h`,
  for some `h : σ →₀ MvPolynomial σ R` such that
  `((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

- `combinatorial_nullstellensatz_exists_eval_nonzero`
  a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
  `f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
  there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

## TODO

- Applications
- relation with Schwartz–Zippel lemma, as in [Rote_2023]

## References

- [Alon, *Combinatorial Nullstellensatz*][Alon_1999]

- [Rote, *The Generalized Combinatorial Lasoń-Alon-Zippel-Schwartz
  Nullstellensatz Lemma*][Rote_2023]

-/

public section

open Finsupp

open scoped Finset

variable {R : Type*} [CommRing R]

namespace MvPolynomial

open Finsupp Function

/-- A multivariate polynomial that vanishes on a large product finset is the zero polynomial. -/
/-
**MvPolynomial.eq_zero_of_eval_zero_at_prod_finset** 是 Mathlib 中的一个定理，位于命名空间 `Mv
Polynomial`。
形式化陈述：eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R] (P
 : MvPolynomial σ R) (S : σ -> Finset R) (Hdeg : forall i, P.degreeOf i < #(S i)
) (Heval : forall (x : σ -> R), (forall i, x i in S i) -> eval x P = 0) : P = 0
参数：P : MvPolynomial σ R；S : σ -> Finset R；Hdeg : forall i, P.degreeOf i < #(S i)
；Heval : forall (x : σ -> R), (forall i, x i in S i) -> eval x P = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.induction_empty_option`：Finite.induction_empty_option {P : Type u
 -> Prop} (of_equiv : forall {α β}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h
_option : forall {α…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `MvPolynomial.degreeOf_rename_of_injective`：degreeOf_rename_of_injective 
{p : MvPolynomial σ R} {f : σ -> τ} (h : Function.Injective f) (i : σ) : degreeO
f (f i) (rename f p) = degreeOf…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.eval_rename`：eval_rename (g : τ -> R) (p : MvPolynomial σ R
) : eval g (rename k p) = eval (g ∘ k) p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.rename_injective`：rename_injective (f : σ -> τ) (hf : Funct
ion.Injective f) : Function.Injective (rename f : MvPolynomial σ R -> MvPolynomi
al τ R)
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `RingHom.injective_iff_ker_eq_bot`：injective_iff_ker_eq_bot : Function.In
jective f ↔ ker f = ⊥
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `MvPolynomial.eval_C`：eval_C : forall a, eval f (C a) = a
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用引理 `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'`：eq_zero_of_nat
Degree_lt_card_of_eval_eq_zero' {R} [CommRing R] [IsDomain R] (p : R[X]) (s : Fi
nset R) (heval : forall i in s, p.eval i = 0) …
· 使用定理 `MvPolynomial.optionEquivLeft_elim_eval`：optionEquivLeft_elim_eval (s : S
₁ -> R) (y : R) (f : MvPolynomial (Option S₁) R) : eval (fun x => Option.elim x 
y s) f = Polynomial.eval y (…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
A multivariate polynomial that vanishes on a large product finset is the zero po
lynomial.
-/
theorem eq_zero_of_eval_zero_at_prod_finset {σ : Type*} [Finite σ] [IsDomain R]
    (P : MvPolynomial σ R) (S : σ → Finset R)
    (Hdeg : ∀ i, P.degreeOf i < #(S i))
    (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x P = 0) :
    P = 0 := by
  induction σ using Finite.induction_empty_option with
  | @of_equiv σ τ e h =>
    suffices MvPolynomial.rename e.symm P = 0 by
      have that := MvPolynomial.rename_injective (R := R) e.symm (e.symm.injective)
      rw [RingHom.injective_iff_ker_eq_bot] at that
      rwa [← RingHom.mem_ker, that] at this
    apply h _ (fun i ↦ S (e i))
    · intro i
      convert! Hdeg (e i)
      conv_lhs => rw [← e.symm_apply_apply i, degreeOf_rename_of_injective e.symm.injective]
    · intro x hx
      simp only [MvPolynomial.eval_rename]
      apply Heval
      intro s
      simp only [Function.comp_apply]
      convert! hx (e.symm s)
      simp only [Equiv.apply_symm_apply]
  | h_empty =>
    suffices P = C (constantCoeff P) by
      specialize Heval default (fun i ↦ PEmpty.elim i)
      rw [this, eval_C] at Heval
      rw [this, Heval, C_0]
    ext m
    suffices m = 0 by simp [this, ← constantCoeff_eq]
    ext d; exact PEmpty.elim d
  | @h_option σ _ h =>
    set Q := optionEquivLeft R σ P with hQ
    suffices Q = 0 by
      rw [← AlgEquiv.symm_apply_apply (optionEquivLeft R σ) P, ← hQ, this, map_zero]
    have Heval' (x : σ → R) (hx : ∀ i, x i ∈ S (some i)) : Polynomial.map (eval x) Q = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ (S none)
      · intro y hy
        rw [← optionEquivLeft_elim_eval]
        apply Heval
        simp only [Option.forall, Option.elim_none, hy, Option.elim_some, hx, implies_true,
          and_self]
      · apply lt_of_le_of_lt _ (Hdeg none)
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro d hd
        simp only [hQ]
        rw [MvPolynomial.coeff_eval_eq_eval_coeff]
        convert! map_zero (MvPolynomial.eval x)
        ext m
        simp only [coeff_zero]
        set n := (embDomain Function.Embedding.some m).update none d with hn
        rw [eq_option_embedding_update_none_iff] at hn
        rw [← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none]
        by_contra hm
        apply not_le.mpr hd
        rw [MvPolynomial.degreeOf_eq_sup]
        rw [← ne_eq, ← MvPolynomial.mem_support_iff] at hm
        convert! Finset.le_sup hm
        exact hn.1.symm
    ext m d
    simp only [Polynomial.coeff_zero, coeff_zero]
    suffices Q.coeff m = 0 by simp only [this, coeff_zero]
    apply h _ (fun i ↦ S (some i))
    · intro i
      apply lt_of_le_of_lt _ (Hdeg (some i))
      simp only [degreeOf_eq_sup, Finset.sup_le_iff, mem_support_iff, ne_eq]
      intro e he
      set n := (embDomain Function.Embedding.some e).update none m with hn
      rw [eq_option_embedding_update_none_iff] at hn
      rw [hQ, ← hn.1, ← hn.2, optionEquivLeft_coeff_some_coeff_none, ← ne_eq,
        ← MvPolynomial.mem_support_iff] at he
      convert! Finset.le_sup he
      rw [← hn.2, some_apply]
    · intro x hx
      specialize Heval' x hx
      rw [Polynomial.ext_iff] at Heval'
      simpa only [Polynomial.coeff_map, Polynomial.coeff_zero] using Heval' m

open MonomialOrder

/- Here starts the actual proof of the combinatorial Nullstellensatz -/

variable {σ : Type*}

/-- The polynomial in `X i` that vanishes at all elements of `S`. -/
/-
**MvPolynomial.Alon.P** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polynomial in `X i` that vanishes at all elements of `S`.
-/
private noncomputable def Alon.P (S : Finset R) (i : σ) : MvPolynomial σ R :=
  ∏ r ∈ S, (X i - C r)

/-- The degree of `Alon.P S i` with respect to `X i` is the cardinality of `S`,
  and `0` otherwise. -/
/-
**MvPolynomial.Alon.degree_P** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The degree of `Alon.P S i` with respect to `X i` is the cardinality of `S`,
  and `0` otherwise.
-/
private theorem Alon.degree_P [Nontrivial R] (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.degree (Alon.P S i) = single i #S := by
  simp only [P]
  rw [degree_prod_of_regular]
  · simp [Finset.sum_congr rfl (fun r _ ↦ m.degree_X_sub_C i r)]
  · intro r _
    rw [m.monic_X_sub_C]
    exact isRegular_one

/-- The leading coefficient of `Alon.P S i` is `1`. -/
/-
**MvPolynomial.Alon.monic_P** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The leading coefficient of `Alon.P S i` is `1`.
-/
private theorem Alon.monic_P (m : MonomialOrder σ) (S : Finset R) (i : σ) :
    m.Monic (P S i) :=
  Monic.prod (fun r _ ↦ m.monic_X_sub_C i r)

/-- The support of `Alon.P S i` is the set of exponents of the form `single i e`,
  for `e ≤ S.card`. -/
/-
**MvPolynomial.Alon.of_mem_P_support** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The support of `Alon.P S i` is the set of exponents of the form `single i e`,
  for `e ≤ S.card`.
-/
private lemma Alon.of_mem_P_support {ι : Type*} (i : ι) (S : Finset R) (m : ι →₀ ℕ)
    (hm : m ∈ (Alon.P S i).support) :
    ∃ e ≤ S.card, m = single i e := by
  classical
  have hP : Alon.P S i = .rename (fun _ ↦ i) (Alon.P S ()) := by simp [Alon.P]
  rw [hP, support_rename_of_injective (Function.injective_of_subsingleton _)] at hm
  simp only [Finset.mem_image, mem_support_iff, ne_eq] at hm
  obtain ⟨e, he, hm⟩ := hm
  have : Nontrivial R := nontrivial_of_ne _ _ he
  refine ⟨e (), ?_, ?_⟩
  · suffices e ≼[lex] single () #S by
      simpa [MonomialOrder.lex_le_iff_of_unique] using this
    rw [← Alon.degree_P]
    apply MonomialOrder.le_degree
    rw [mem_support_iff]
    convert! he
  · rw [← hm]
    ext j
    by_cases hj : j = i
    · rw [hj, mapDomain_apply (Function.injective_of_subsingleton _), single_eq_same]
    · rw [mapDomain_of_notMem_range, single_eq_of_ne hj]
      simp [Set.range_const, Set.mem_singleton_iff, hj]

variable [Finite σ]

/-- The **Combinatorial Nullstellensatz**.

If `f` vanishes at every point `x : σ → R` such that `x s ∈ S s` for all `s`,
then it can be written as a linear combination
`f = linearCombination (MvPolynomial σ R) (fun i ↦ (∏ r ∈ S i, (X i - C r))) h`,
for some `h : σ →₀ MvPolynomial σ R` such that
`((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

[Alon_1999], theorem 1. -/
/-
**MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination** 是 Mathli
b 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：combinatorial_nullstellensatz_exists_linearCombination [IsDomain R] (S : σ
 -> Finset R) (Sne : forall i, (S i).Nonempty) (f : MvPolynomial σ R) (Heval : f
orall (x : σ -> R), (forall i, x i in S i) -> eval x f = 0) : exists (h : σ ->₀ 
MvPolynomial σ R), (forall i, ((∏ s in S i, (X i - C s)) * h i).totalDegree <= f
.totalDegree) ∧ f = linearCombination (MvPolynomial σ R) (fun i => ∏ r in S i, (
X i - C r)) h
参数：S : σ -> Finset R；Sne : forall i, (S i).Nonempty；f : MvPolynomial σ R；Heval :
 forall (x : σ -> R), (forall i, x i in S i) -> eval x f = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `isWellOrder_gt`：∀ {α : Type u} [inst : LinearOrder α] [WellFoundedGT α],
 IsWellOrder α fun x1 x2 => x2 < x1
· 使用定理 `Finite.to_wellFoundedGT`：∀ {α : Type u_1} [Finite α] [inst : Preorder α]
, WellFoundedGT α
· 使用定理 `MonomialOrder.div`：div {ι : Type*} {b : ι -> MvPolynomial σ R} (hb : for
all i, IsUnit (m.leadingCoeff (b i))) (f : MvPolynomial σ R) : exists (g : ι ->₀
 (MvPol…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MonomialOrder.Monic.leadingCoeff_eq_one`：∀ {σ : Type u_1} {m : MonomialO
rder σ} {R : Type u_2} [inst : CommSemiring R] {f : MvPolynomial σ R},   m.Monic
 f → m.leadingCoeff f = 1
· 使用定理 `_private.Mathlib.Combinatorics.Nullstellensatz.0.MvPolynomial.Alon.monic
_P`：∀ {R : Type u_1} [inst : CommRing R] {σ : Type u_2} (m : MonomialOrder σ) (S
 : Finset R) (i : σ),   m.Monic (MvPolynomial.Alon.P✝ S i)
· 使用定理 `MvPolynomial.eq_zero_of_eval_zero_at_prod_finset`：eq_zero_of_eval_zero_a
t_prod_finset {σ : Type*} [Finite σ] [IsDomain R] (P : MvPolynomial σ R) (S : σ 
-> Finset R) (Hdeg : forall i, P.degre…
· 使用定理 `MvPolynomial.degreeOf_eq_sup`：degreeOf_eq_sup (n : σ) (f : MvPolynomial 
σ R) : degreeOf n f = f.support.sup fun m => m n
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `_private.Mathlib.Combinatorics.Nullstellensatz.0.MvPolynomial.Alon.degre
e_P`：∀ {R : Type u_1} [inst : CommRing R] {σ : Type u_2} [Nontrivial R] (m : Mon
omialOrder σ) (S : Finset R) (i : σ),   m.degree (MvPolynomial.Al…
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `sub_eq_iff_eq_add'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a - b = c ↔ a = b + c
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
· 使用定理 `neg_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a =
 0 ↔ a = 0
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `map_finsuppSum`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} {P : Typ
e u_11} [inst : Zero M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMonoid P] 
{H :…
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
The **Combinatorial Nullstellensatz**.

If `f` vanishes at every point `x : σ → R` such that `x s ∈ S s` for all `s`,
then it can be written as a linear combination
`f = linearCombination (MvPolynomial σ R) (fun i ↦ (∏ r ∈ S i, (X i - C r))) h`,
for some `h : σ →₀ MvPolynomial σ R` such that
`((∏ r ∈ S s, (X i - C r)) * h i).totalDegree ≤ f.totalDegree` for all `s`.

[Alon_1999], theorem 1.
-/
theorem combinatorial_nullstellensatz_exists_linearCombination
    [IsDomain R] (S : σ → Finset R) (Sne : ∀ i, (S i).Nonempty)
    (f : MvPolynomial σ R) (Heval : ∀ (x : σ → R), (∀ i, x i ∈ S i) → eval x f = 0) :
    ∃ (h : σ →₀ MvPolynomial σ R),
      (∀ i, ((∏ s ∈ S i, (X i - C s)) * h i).totalDegree ≤ f.totalDegree) ∧
      f = linearCombination (MvPolynomial σ R) (fun i ↦ ∏ r ∈ S i, (X i - C r)) h := by
  let : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  obtain ⟨h, r, hf, hh, hr⟩ := degLex.div (b := fun i ↦ Alon.P (S i) i)
      (fun i ↦ by simp only [(Alon.monic_P ..).leadingCoeff_eq_one, isUnit_one]) f
  use h
  suffices r = 0 by
    rw [this, add_zero] at hf
    exact ⟨fun i ↦ degLex_totalDegree_monotone (hh i), hf⟩
  apply eq_zero_of_eval_zero_at_prod_finset r S
  · intro i
    rw [degreeOf_eq_sup, Finset.sup_lt_iff (by simp [Sne i])]
    aesop (add simp [Alon.degree_P])
  · intro x hx
    rw [Iff.symm sub_eq_iff_eq_add'] at hf
    rw [← hf, map_sub, Heval x hx, zero_sub, neg_eq_zero,
      linearCombination_apply, map_finsuppSum, Finsupp.sum, Finset.sum_eq_zero]
    intro i _
    rw [smul_eq_mul, map_mul]
    convert! mul_zero _
    rw [Alon.P, _root_.map_prod]
    apply Finset.prod_eq_zero (hx i)
    simp

/-- The **Combinatorial Nullstellensatz**.

Given a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
`f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s ≠ 0`.

[Alon_1999], theorem 2 -/
/-
**MvPolynomial.combinatorial_nullstellensatz_exists_eval_nonzero** 是 Mathlib 中的一
个定理，位于命名空间 `MvPolynomial`。
形式化陈述：combinatorial_nullstellensatz_exists_eval_nonzero [IsDomain R] (f : MvPoly
nomial σ R) (t : σ ->₀ Nat) (ht : f.coeff t != 0) (ht' : f.totalDegree = t.degre
e) (S : σ -> Finset R) (htS : forall i, t i < #(S i)) : exists s : σ -> R, (fora
ll i, s i in S i) ∧ eval s f != 0
参数：f : MvPolynomial σ R；t : σ ->₀ Nat；ht : f.coeff t != 0；ht' : f.totalDegree = 
t.degree；S : σ -> Finset R；htS : forall i, t i < #(S i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `MvPolynomial.combinatorial_nullstellensatz_exists_linearCombination`：com
binatorial_nullstellensatz_exists_linearCombination [IsDomain R] (S : σ -> Finse
t R) (Sne : forall i, (S i).Nonempty) (f : MvPolynomial σ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `_private.Mathlib.Combinatorics.Nullstellensatz.0.MvPolynomial.Alon.of_me
m_P_support`：∀ {R : Type u_1} [inst : CommRing R] {ι : Type u_3} (i : ι) (S : Fi
nset R),   ∀ m ∈ (MvPolynomial.Alon.P✝ S i).support, ∃ e ≤ S.card, m = fu…
· 使用定理 `MvPolynomial.coeff_eq_zero_of_totalDegree_lt`：coeff_eq_zero_of_totalDegr
ee_lt {f : MvPolynomial σ R} {d : σ ->₀ Nat} (h : f.totalDegree < ∑ i in d.suppo
rt, d i) : coeff d f = 0
· 使用定理 `Finsupp.degree_apply`：degree_apply (d : σ ->₀ R) : degree d = ∑ i in d.s
upport, d i
· 使用定理 `lt_of_add_lt_add_right`：∀ {α : Type u_1} [inst : Add α] [inst_1 : LT α] 
[i : AddRightReflectLT α] {a b c : α}, b + a < c + a → b < c
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The **Combinatorial Nullstellensatz**.

Given a multi-index `t : σ →₀ ℕ` such that `t s < (S s).card` for all `s`,
`f.totalDegree = t.degree` and `f.coeff t ≠ 0`,
there exists a point `x : σ → R` such that `x s ∈ S s` for all `s` and `f.eval s
 ≠ 0`.

[Alon_1999], theorem 2
-/
theorem combinatorial_nullstellensatz_exists_eval_nonzero [IsDomain R]
    (f : MvPolynomial σ R)
    (t : σ →₀ ℕ) (ht : f.coeff t ≠ 0) (ht' : f.totalDegree = t.degree)
    (S : σ → Finset R) (htS : ∀ i, t i < #(S i)) :
    ∃ s : σ → R, (∀ i, s i ∈ S i) ∧ eval s f ≠ 0 := by
  let _ : LinearOrder σ := WellOrderingRel.isWellOrder.linearOrder
  by_contra! Heval
  apply ht
  obtain ⟨h, hh, hf⟩ := combinatorial_nullstellensatz_exists_linearCombination S
    (fun i ↦ by rw [← Finset.card_pos]; exact Nat.zero_lt_of_lt (htS i)) f Heval
  rw [hf]
  rw [linearCombination_apply, Finsupp.sum, coeff_sum]
  apply Finset.sum_eq_zero
  intro i _
  set g := h i * Alon.P (S i) i with hg
  by_cases hi : h i = 0
  · simp [hi]
  have : g.totalDegree ≤ f.totalDegree := by
    rw [hg, mul_comm]
    exact hh i
  -- one could simplify this by proving `totalDegree_mul_eq` (at least in a domain)
  rw [hg, ← degree_degLexDegree,
    degree_mul_of_isRegular_right hi (by simp only [(Alon.monic_P ..).leadingCoeff_eq_one,
      isRegular_one]),
    Alon.degree_P, map_add, degree_degLexDegree, degree_single, ht'] at this
  rw [smul_eq_mul, coeff_mul, Finset.sum_eq_zero]
  rintro ⟨p, q⟩ hpq
  simp only [Finset.mem_antidiagonal] at hpq
  simp only [mul_eq_zero, Classical.or_iff_not_imp_right]
  rw [← ne_eq, ← mem_support_iff]
  intro hq
  obtain ⟨e, hq', hq⟩ := Alon.of_mem_P_support _ _ _ hq
  apply coeff_eq_zero_of_totalDegree_lt
  rw [← Finsupp.degree_apply]
  apply lt_of_add_lt_add_right (lt_of_le_of_lt this _)
  rw [← hpq, map_add, add_lt_add_iff_left, hq, degree_single]
  apply lt_of_le_of_lt _ (htS i)
  simp [← hpq, hq]

end MvPolynomial

