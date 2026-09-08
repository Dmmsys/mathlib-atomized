/-
Copyright (c) 2025 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Johan Commelin, Andrew Yang
-/
module

public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.Nilpotent

/-!
# Irreducibility of linear and quadratic polynomials

* `MvPolynomial.irreducible_of_totalDegree_eq_one`:
  a multivariate polynomial of `totalDegree` one is irreducible
  if its coefficients are relatively prime.

* For `c : n →₀ R`, `MvPolynomial.sumSMulX c` is the linear polynomial
  $\sum_i c_i X_i$ of $R[X_1\dots,X_n]$.

* `MvPolynomial.irreducible_sumSMulX` : if the support of `c` is nontrivial,
  if `R` is a domain,
  and if the only common divisors to all `c i` are units,
  then `MvPolynomial.sumSMulX c` is irreducible.

* For `c : n →₀ R`, `MvPolynomial.sumXSMulY c` is the quadratic polynomial
  $\sum_i c_i X_i Y_i$ of $R[X_1\dots,X_n,Y_1,\dots,Y_n]$.
  It is constructed as an object of `MvPolynomial (n ⊕ n) R`,
  the first component of `n ⊕ n` represents the `X` indeterminates,
  and the second component represents the `Y` indeterminates.

* `MvPolynomial.irreducible_sumSMulXSMulY` :
  if the support of `c` is nontrivial,
  the ring `R` is a domain,
  and the only divisors common to all `c i` are units,
  then `MvPolynomial.sumSMulXSMulY c` is irreducible.

## TODO

* Treat the case of diagonal quadratic polynomials,
  $ \sum c_i X_i ^ 2$. For irreducibility, one will need that
  there are at least 3 nonzero values of `c`,
  and that the only common divisors to all `c i` are units.

* Addition of quadratic polynomial of both kinds are relevant too.

* Prove, over a field, that a polynomial of degree at most 2 whose quadratic
  part has rank at least 3 is irreducible.

* Cases of ranks 1 and 2 can be treated as well, but the answer depends
  on the terms of degree 0 and 1.
  Eg, $X^2-Y$ is irreducible, but $X^2$, $X^2-1$, $X^2-Y^2$ are not.
  And $X^2+Y^2$ is irreducible over the reals but not over the complex numbers.

-/

@[expose] public section

namespace MvPolynomial

open scoped Polynomial

section

variable {n : Type*} {R : Type*} [CommRing R]

open scoped Polynomial in
attribute [local simp] MvPolynomial.optionEquivLeft_X_none in -- tag simp globally?
/-
**MvPolynomial.irreducible_mul_X_add** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：irreducible_mul_X_add {n : Type*} {R : Type*} [CommRing R] [IsDomain R] (f
 g : MvPolynomial n R) (i : n) (hf0 : f != 0) (hif : i ∉ f.vars) (hig : i ∉ g.va
rs) (h : IsRelPrime f g) : Irreducible (f * X i + g)
参数：f g : MvPolynomial n R；i : n；hf0 : f != 0；hif : i ∉ f.vars；hig : i ∉ g.vars；h
 : IsRelPrime f g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `MvPolynomial.ext`：ext (p q : MvPolynomial σ R) : (forall m, coeff m p = 
coeff m q) -> p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.CAlgHom_apply`：∀ {R : Type u} {A : Type z} [inst : CommSemiri
ng R] [inst_1 : Semiring A] [inst_2 : Algebra R A] (a : A),   Polynomial.CAlgHom
 a = Polynomia…
· 使用引理 `MvPolynomial.optionEquivLeft_symm_C_X`：optionEquivLeft_symm_C_X (x : S₁)
 : (optionEquivLeft R S₁).symm (.C (X x)) = .X (.some x)
· 使用定理 `MvPolynomial.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Typ
e u_4) [inst : CommSemiring R] (f : σ ≃ τ) (a : MvPolynomial σ R),   (MvPolynomi
al.renameEquiv R f) …
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
· 使用定理 `Equiv.optionSubtypeNe_apply`：∀ {α : Type u_1} [inst : DecidableEq α] (a 
: α) (a_1 : Option { y // y ≠ a }),   (Equiv.optionSubtypeNe a) a_1 = a_1.casesO
n' a Subtype.val
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.exists_rename_eq_of_vars_subset_range`：exists_rename_eq_of_
vars_subset_range (p : MvPolynomial σ R) (f : τ -> σ) (hfi : Injective f) (hf : 
↑p.vars subseteq Set.range f) : exists q…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Irreducible.of_map`：Irreducible.of_map [FunLike F M N] [MonoidHomClass F
 M N] [IsLocalHom f] (hfx : Irreducible (f x)) : Irreducible x where not_isUnit 
hu
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `isLocalHom_equiv`：∀ {F : Type u_1} {M : Type u_3} {N : Type u_4} [inst :
 Monoid M] [inst_1 : Monoid N] [inst_2 : EquivLike F M N]   [MulEquivClass F M N
] (f :…
· 使用定理 `RingEquivClass.toMulEquivClass`：∀ {F : Type u_7} {R : Type u_8} {S : Typ
e u_9} {inst : Mul R} {inst_1 : Add R} {inst_2 : Mul S} {inst_3 : Add S}   {inst
_4 : EquivLike F R S…
· 使用定理 `AlgEquivClass.toRingEquivClass`：∀ {F : Type u_1} {R : outParam (Type u_2
)} {A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}  
 {inst_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
（共 51 条，此处仅展示前 30 条）
-/
lemma irreducible_mul_X_add {n : Type*} {R : Type*} [CommRing R] [IsDomain R]
    (f g : MvPolynomial n R) (i : n) (hf0 : f ≠ 0) (hif : i ∉ f.vars) (hig : i ∉ g.vars)
    (h : IsRelPrime f g) :
    Irreducible (f * X i + g) := by
  classical
  let S := MvPolynomial { j // j ≠ i } R
  let e : MvPolynomial n R ≃ₐ[R] S[X] :=
    (renameEquiv R (Equiv.optionSubtypeNe i).symm).trans (optionEquivLeft R _)
  have he : e.symm.toAlgHom.comp Polynomial.CAlgHom = rename (↑) := by ext; simp [e, S]
  obtain ⟨f, rfl⟩ : f ∈ (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  obtain ⟨g, rfl⟩ : g ∈ (e.symm.toAlgHom.comp Polynomial.CAlgHom).range :=
    he ▸ exists_rename_eq_of_vars_subset_range _ _ Subtype.val_injective (by simpa [Set.subset_def])
  refine .of_map (f := e) ?_
  simpa [e, S] using Polynomial.irreducible_C_mul_X_add_C (by aesop)
    (IsRelPrime.of_map Polynomial.C (IsRelPrime.of_map e.symm h))

/-- A multivariate polynomial `f` whose support is nontrivial,
such that some variable `i` appears with exponent `1` in one nontrivial monomial,
whose monomials have disjoint supports, and which is primitive, is irreducible. -/
/-
**MvPolynomial.irreducible_of_disjoint_support** 是 Mathlib 中的一个引理，位于命名空间 `MvPoly
nomial`。
形式化陈述：irreducible_of_disjoint_support [IsDomain R] {f : MvPolynomial n R} (nontr
ivial : f.support.Nontrivial) {d : n ->₀ Nat} (hd : d in f.support) {i : n} (hdi
 : d i = 1) (disjoint : (f.support : Set (n ->₀ Nat)).PairwiseDisjoint Finsupp.s
upport) (isPrimitive : forall r, (forall d, r ∣ f.coeff d) -> IsUnit r) : Irredu
cible f
参数：nontrivial : f.support.Nontrivial；hd : d in f.support；hdi : d i = 1；disjoint 
: (f.support : Set (n ->₀ Nat)).PairwiseDisjoint Finsupp.support；isPrimitive : f
orall r, (forall d, r ∣ f.coeff d) -> IsUnit r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finsupp.erase_add_single`：erase_add_single (a : ι) (f : ι ->₀ M) : f.era
se a + single a (f a) = f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvPolynomial.monomial_add_single`：monomial_add_single : monomial (s + Fi
nsupp.single n e) a = monomial s a * X n ^ e
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MvPolynomial.coeff_sub`：coeff_sub (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p - q) = coeff m p - coeff m q
· 使用定理 `MvPolynomial.coeff_monomial`：coeff_monomial [DecidableEq σ] (m n) (a) : 
coeff m (monomial n a : MvPolynomial σ R) = if n = m then a else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_add_ite`：∀ {α : Type u_2} (P : Prop) [inst : Decidable P] [inst_1 : 
Add α] (a b c d : α),   ((if P then a else b) + if P then c else d) = if P then 
a…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用引理 `MvPolynomial.irreducible_mul_X_add`：irreducible_mul_X_add {n : Type*} {R
 : Type*} [CommRing R] [IsDomain R] (f g : MvPolynomial n R) (i : n) (hf0 : f !=
 0) (hif : i ∉ f.vars) (…
· 使用定理 `MvPolynomial.vars_monomial`：vars_monomial (h : r != 0) : (monomial s r).
vars = s.support
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finsupp.support_erase`：support_erase [DecidableEq α] {a : α} {f : α ->₀ 
M} : (f.erase a).support = f.support.erase a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_iff_ne`：disjoint_iff_ne : Disjoint s t ↔ forall a in s, 
forall b in t, a != b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
A multivariate polynomial `f` whose support is nontrivial,
such that some variable `i` appears with exponent `1` in one nontrivial monomial
,
whose monomials have disjoint supports, and which is primitive, is irreducible.
-/
lemma irreducible_of_disjoint_support [IsDomain R]
    {f : MvPolynomial n R}
    (nontrivial : f.support.Nontrivial)
    {d : n →₀ ℕ} (hd : d ∈ f.support) {i : n} (hdi : d i = 1)
    (disjoint : (f.support : Set (n →₀ ℕ)).PairwiseDisjoint Finsupp.support)
    (isPrimitive : ∀ r, (∀ d, r ∣ f.coeff d) → IsUnit r) :
    Irreducible f := by
  classical
  have hfd : f.coeff d ≠ 0 := by simpa using hd
  let d₀ := d.erase i
  let φ : MvPolynomial n R := monomial d₀ (f.coeff d)
  let ψ : MvPolynomial n R := f - φ * X i
  have hf : f = φ * X i + ψ := by grind only
  have hφ : φ * X i = monomial d (f.coeff d) := by
    nth_rw 1 [← Finsupp.erase_add_single i d]; simp [φ, monomial_add_single, hdi, d₀]
  have hdψ (k) : ψ.coeff k = if d = k then 0 else f.coeff k := by
    simp +contextual [ψ, hφ, sub_eq_iff_eq_add, ite_add_ite]
  rw [hf]
  apply irreducible_mul_X_add
  · grind only [monomial_eq_zero]
  · simp [φ, hfd, d₀, hdi]
  · suffices ∀ x, d ≠ x → x ∈ f.support → i ∉ x.support by
      simpa [mem_vars_iff_mem_support, hdψ] using this
    exact fun x hxd hx hix ↦
      Finset.disjoint_iff_ne.mp (disjoint hd hx hxd) i (by simp [hdi]) _ hix rfl
  · rintro p hpφ ⟨q, hq⟩
    obtain ⟨m, b, hm, hb, rfl⟩ := (dvd_monomial_iff_exists hfd).mp hpφ
    obtain ⟨d₂, hd₂, H⟩ := nontrivial.exists_ne d
    obtain rfl : m = 0 := by
      have aux : coeff d₂ ψ ≠ 0 := by simpa [hdψ, H.symm] using hd₂
      simp only [hq, coeff_monomial_mul', ne_eq, ite_eq_right_iff, Classical.not_imp] at aux
      simpa using disjoint hd₂ hd H (Finsupp.support_mono aux.1)
        ((Finsupp.support_mono hm).trans (d.support.erase_subset i))
    have hb' : IsUnit b := isPrimitive _ fun k ↦
      if hk : k = d then hk ▸ hb else hf ▸ by simp [hq, hφ, Ne.symm hk]
    simpa

end

section
/-! ## The quadratic polynomial $$\sum_{i=1}^n X_i Y_i$$. -/

open Polynomial

variable {n : Type*} {R : Type*} [CommRing R]

/-
**MvPolynomial.irreducible_of_totalDegree_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `MvPo
lynomial`。
形式化陈述：irreducible_of_totalDegree_eq_one [IsDomain R] {p : MvPolynomial n R} (hp 
: p.totalDegree = 1) (hp' : forall x, (forall i, x ∣ p.coeff i) -> IsUnit x) : I
rreducible p where not_isUnit H
参数：hp : p.totalDegree = 1；hp' : forall x, (forall i, x ∣ p.coeff i) -> IsUnit x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPolynomial.isUnit_iff_totalDegree_of_isReduced`：isUnit_iff_totalDegree
_of_isReduced [IsReduced R] : IsUnit P ↔ IsUnit (P.coeff 0) ∧ P.totalDegree = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `MvPolynomial.totalDegree_zero`：totalDegree_zero : (0 : MvPolynomial σ R)
.totalDegree = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.totalDegree_mul_of_isDomain`：totalDegree_mul_of_isDomain {f
 g : MvPolynomial σ R} (hf : f != 0) (hg : g != 0) : totalDegree (f * g) = total
Degree f + totalDegree g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff_eq_C`：totalDegree_eq_zero_iff_eq_C 
{p : MvPolynomial σ R} : p.totalDegree = 0 ↔ p = C (p.coeff 0)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MvPolynomial.instIsLocalHomRingHomC`：∀ {σ : Type u_1} {R : Type u_2} [in
st : CommRing R], IsLocalHom MvPolynomial.C
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `MvPolynomial.coeff_C_mul`：coeff_C_mul (m) (a : R) (p : MvPolynomial σ R)
 : coeff m (C a * p) = a * coeff m p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
-/
theorem irreducible_of_totalDegree_eq_one
    [IsDomain R] {p : MvPolynomial n R} (hp : p.totalDegree = 1)
    (hp' : ∀ x, (∀ i, x ∣ p.coeff i) → IsUnit x) :
    Irreducible p where
  not_isUnit H := by
    simp [(MvPolynomial.isUnit_iff_totalDegree_of_isReduced.mp H).2] at hp
  isUnit_or_isUnit a b hab := by
    wlog hle : a.totalDegree ≤ b.totalDegree generalizing a b
    · exact (this b a (by rw [hab, mul_comm]) (by lia)).symm
    obtain rfl | ha₀ := eq_or_ne a 0; · simp_all
    obtain rfl | hb₀ := eq_or_ne b 0; · simp_all
    have : a.totalDegree + b.totalDegree = 1 := by
      simpa [totalDegree_mul_of_isDomain, ha₀, hb₀, hp] using congr(($hab).totalDegree).symm
    obtain ⟨r, rfl⟩ : ∃ r, a = C r := ⟨_, (totalDegree_eq_zero_iff_eq_C (p := a)).mp (by lia)⟩
    simp [hp' r fun i ↦ by simp [hab]]

variable (c : n →₀ R)

#adaptation_note /-- Needed after leanprover/lean4#12564.
Named to avoid collision with `MvPolynomial.instModule` from `Mathlib.RingTheory.MvPolynomial`. -/
/-
**MvPolynomial.instModuleSelf** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：instModuleSelf : Module R (MvPolynomial n R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Needed after leanprover/lean4#12564.
Named to avoid collision with `MvPolynomial.instModule` from `Mathlib.RingTheory
.MvPolynomial`.
-/
noncomputable instance instModuleSelf : Module R (MvPolynomial n R) :=
  inferInstanceAs <| Module R (AddMonoidAlgebra R (n →₀ ℕ))

/-- The linear polynomial $$\sum_i c_i X_i$$. -/
/-
**MvPolynomial.sumSMulX** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：sumSMulX : (n ->₀ R) ->ₗ[R] MvPolynomial n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The linear polynomial $$\sum_i c_i X_i$$.
-/
noncomputable def sumSMulX :
    (n →₀ R) →ₗ[R] MvPolynomial n R :=
  Finsupp.linearCombination R X
/-
**MvPolynomial.coeff_sumSMulX** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：coeff_sumSMulX (i : n) : (sumSMulX c).coeff (Finsupp.single i 1) = c i
参数：i : n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.sumSMulX.eq_1`：∀ {n : Type u_1} {R : Type u_2} [inst : Comm
Ring R], MvPolynomial.sumSMulX = Finsupp.linearCombination R MvPolynomial.X
· 使用定理 `Finsupp.linearCombination_apply`：linearCombination_apply (l : α ->₀ R) :
 linearCombination R v l = l.sum fun i a => a • v i
· 使用定理 `Finsupp.sum.eq_1`：∀ {α : Type u_1} {M : Type u_8} {N : Type u_10} [inst 
: Zero M] [inst_1 : AddCommMonoid N] (f : α →₀ M) (g : α → M → N),   f.sum g = ∑
 a ∈ f…
· 使用定理 `MvPolynomial.coeff_sum`：coeff_sum {X : Type*} (s : Finset X) (f : X -> M
vPolynomial σ R) (m : σ ->₀ Nat) : coeff m (∑ x in s, f x) = ∑ x in s, coeff m (
f x)
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `MvPolynomial.coeff_smul`：coeff_smul {S₁ : Type*} [SMulZeroClass S₁ R] (m
 : σ ->₀ Nat) (C : S₁) (p : MvPolynomial σ R) : coeff m (C • p) = C • coeff m p
· 使用定理 `MvPolynomial.coeff_X`：coeff_X [DecidableEq σ] (i : σ) (m) : coeff m (X i
 : MvPolynomial σ R) = if Finsupp.single i 1 = m then 1 else 0
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finsupp.single_left_inj`：single_left_inj (h : b != 0) : single a b = sin
gle a' b ↔ a = a'
· 使用定理 `Nat.one_ne_zero`：1 ≠ 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `MvPolynomial.coeff_single_X`：coeff_single_X [DecidableEq σ] (s s' : σ) (
n : Nat) : (X s).coeff (R
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem coeff_sumSMulX (i : n) :
    (sumSMulX c).coeff (Finsupp.single i 1) = c i := by
  classical
  rw [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum]
  rw [Finset.sum_eq_single i _ (by simp)]
  · simp
  intro j hj hji
  rw [coeff_smul, coeff_X, if_neg]
  · simp
  · rwa [Finsupp.single_left_inj Nat.one_ne_zero]
/-
**MvPolynomial.irreducible_sumSMulX** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：irreducible_sumSMulX [IsDomain R] (hc_nonempty : c.support.Nonempty) (hc_g
cd : forall r, (forall i, r ∣ c i) -> IsUnit r) : Irreducible (sumSMulX c)
参数：hc_nonempty : c.support.Nonempty；hc_gcd : forall r, (forall i, r ∣ c i) -> Is
Unit r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.irreducible_of_totalDegree_eq_one`：irreducible_of_totalDegr
ee_eq_one [IsDomain R] {p : MvPolynomial n R} (hp : p.totalDegree = 1) (hp' : fo
rall x, (forall i, x ∣ p.coeff i) ->…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `MvPolynomial.totalDegree_finsetSum_le`：totalDegree_finsetSum_le {ι : Typ
e*} {s : Finset ι} {f : ι -> MvPolynomial σ R} {d : Nat} (hf : forall i in s, (f
 i).totalDegree <= d) : (s.…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `MvPolynomial.totalDegree_smul_le`：totalDegree_smul_le [CommSemiring S] [
DistribMulAction R S] (a : R) (f : MvPolynomial σ S) : (a • f).totalDegree <= f.
totalDegree
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.totalDegree_X`：totalDegree_X {R} [CommSemiring R] [Nontrivi
al R] (s : σ) : (X s : MvPolynomial σ R).totalDegree = 1
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `MvPolynomial.totalDegree_eq_zero_iff`：totalDegree_eq_zero_iff (p : MvPol
ynomial σ R) : p.totalDegree = 0 ↔ forall (m : σ ->₀ Nat) (_ : m in p.support) (
x : σ), m x = 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `MvPolynomial.mem_support_iff`：mem_support_iff {p : MvPolynomial σ R} {m 
: σ ->₀ Nat} : m in p.support ↔ p.coeff m != 0
· 使用定理 `MvPolynomial.coeff_sumSMulX`：coeff_sumSMulX (i : n) : (sumSMulX c).coeff
 (Finsupp.single i 1) = c i
-/
theorem irreducible_sumSMulX [IsDomain R]
    (hc_nonempty : c.support.Nonempty)
    (hc_gcd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sumSMulX c) := by
  apply irreducible_of_totalDegree_eq_one
  · apply le_antisymm
    · simp only [sumSMulX, Finsupp.linearCombination_apply, Finsupp.sum]
      apply totalDegree_finsetSum_le
      intros
      apply le_trans (totalDegree_smul_le ..)
      simp
    · rw [← not_lt, Nat.lt_one_iff, totalDegree_eq_zero_iff]
      intro h
      obtain ⟨i, hi⟩ := hc_nonempty
      simp only [Finsupp.mem_support_iff] at hi
      specialize h (Finsupp.single i 1) (by
        rwa [mem_support_iff, coeff_sumSMulX]) i
      simp only [Finsupp.single_eq_same, one_ne_zero] at h
  · intro r hr
    apply hc_gcd
    intro i
    simpa [coeff_sumSMulX] using hr (Finsupp.single i 1)

/-- The quadratic polynomial $$\sum_i c_i X_i Y_i$$. -/
/-
**MvPolynomial.sumSMulXSMulY** 是 Mathlib 中的一个定义，位于命名空间 `MvPolynomial`。
形式化陈述：sumSMulXSMulY : (n ->₀ R) ->ₗ[R] MvPolynomial (n oplus n) R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quadratic polynomial $$\sum_i c_i X_i Y_i$$.
-/
noncomputable def sumSMulXSMulY :
    (n →₀ R) →ₗ[R] MvPolynomial (n ⊕ n) R :=
  Finsupp.linearCombination R (fun i ↦ X (.inl i) * X (.inr i))

variable (c : n →₀ R)

set_option backward.isDefEq.respectTransparency false in
/-
**MvPolynomial.irreducible_sumSMulXSMulY** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial
`。
形式化陈述：irreducible_sumSMulXSMulY [IsDomain R] (hc : c.support.Nontrivial) (h_dvd 
: forall r, (forall i, r ∣ c i) -> IsUnit r) : Irreducible (sumSMulXSMulY c)
参数：hc : c.support.Nontrivial；h_dvd : forall r, (forall i, r ∣ c i) -> IsUnit r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.single_apply`：single_apply [Decidable (a = a')] : single a b a' 
= if a = a' then b else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sum.inl.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : α), (Sum.inl val
 = Sum.inl val_1) = (val = val_1)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Sum.inr.injEq`：∀ {α : Type u} {β : Type v} (val val_1 : β), (Sum.inr val
 = Sum.inr val_1) = (val = val_1)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finsupp.sum_single`：sum_single [AddCommMonoid M] (f : α ->₀ M) : f.sum s
ingle = f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPolynomial.monomial_mul`：monomial_mul {s s' : σ ->₀ Nat} {a b : R} : m
onomial s a * monomial s' b = monomial (s + s') (a * b)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.smul_monomial`：smul_monomial {S₁ : Type*} [SMulZeroClass S₁
 R] (r : S₁) : r • monomial s a = monomial s (r • a)
· 使用定理 `Finsupp.sum_embDomain`：∀ {α : Type u_1} {β : Type u_7} {M : Type u_8} {N
 : Type u_10} [inst : Zero M] [inst_1 : AddCommMonoid N] {v : α →₀ M}   {f : α ↪
 β} {g : β …
· 使用定理 `AddMonoidAlgebra.ofCoeff_finsuppSum`：∀ {R : Type u_1} {M : Type u_4} {N 
: Type u_5} {ι : Type u_7} [inst : Semiring R] [inst_1 : AddCommMonoid N]   (f :
 ι →₀ N) (g : ι → N → M →…
· 使用定理 `Finsupp.embDomain_apply`：embDomain_apply (f : α ↪ β) (v : α ->₀ M) (b : 
β) : embDomain f v b = if h : exists a, f a = b then v h.choose else 0
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
（共 50 条，此处仅展示前 30 条）
-/
theorem irreducible_sumSMulXSMulY [IsDomain R]
    (hc : c.support.Nontrivial)
    (h_dvd : ∀ r, (∀ i, r ∣ c i) → IsUnit r) :
    Irreducible (sumSMulXSMulY c) := by
  classical
  let ι : n ↪ ((n ⊕ n) →₀ ℕ) :=
    ⟨fun i ↦ .single (.inl i) 1 + .single (.inr i) 1,
     fun i j ↦ by simp +contextual [Finsupp.ext_iff, Finsupp.single_apply, ite_eq_iff']⟩
  have aux : sumSMulXSMulY c = .ofCoeff (c.embDomain ι) := by
    rw [← Finsupp.sum_single (Finsupp.embDomain _ _)]
    simp [Finsupp.sum_embDomain, sumSMulXSMulY, X, monomial_mul,
      Finsupp.linearCombination_apply, smul_monomial, ι]
    rfl
  have hcoeff (i : n) : coeff (ι i) (sumSMulXSMulY c) = c i := by
    simp [aux, coeff, Finsupp.embDomain_apply]
  have hsupp : (sumSMulXSMulY c).support = c.support.map ι := by
    simp [aux, support, Finsupp.support_embDomain]
  obtain ⟨a, ha⟩ := hc.nonempty
  apply irreducible_of_disjoint_support (d := ι a) (i := .inl a)
  · rwa [hsupp, Finset.map_nontrivial]
  · rwa [MvPolynomial.mem_support_iff, hcoeff, ← Finsupp.mem_support_iff]
  · simp [ι]
  · rw [hsupp, Finset.coe_map, ι.injective.injOn.pairwiseDisjoint_image]
    suffices (c.support : Set n).PairwiseDisjoint fun x ↦ {Sum.inl x, Sum.inr x} by
      simpa [ι, Function.comp_def, Finsupp.support_add_eq, Finsupp.support_single]
    simp [Set.PairwiseDisjoint, Set.Pairwise, ne_comm]
  · intro r hr
    apply h_dvd
    intro i
    simpa [hcoeff] using hr (ι i)

end

end MvPolynomial

