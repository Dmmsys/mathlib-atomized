/-
Copyright (c) 2026 Bingyu Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca, Bingyu Xia
-/
module

public import Mathlib.Order.Filter.TendstoCofinite
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Renaming variables of power series

This file establishes the `rename` operation on multivariate power series
under a map with finite fibers, which modifies the set of variables.

Unlike polynomials, renaming variables in power series requires a finiteness condition
on the map `f : σ → τ` between the index types. Specifically, we require that `f` has
finite fibers, which is formalized as `Filter.TendstoCofinite f`.
To see why this is necessary, consider a map from infinitely many variables to a single
variable sending each `X_i` to `X`. The sum `X_0 + X_1 + ⋯` is a valid power series in
`ℤ⟦X_0, X_1, ...⟧`, but we cannot rename each `X_i` to `X` since its image `X + X + ⋯`
would have an infinite coefficient for `X`.

To avoid writing this assumption everywhere, we usually work with the typeclass assumption
`Filter.TendstoCofinite f`. Note that this holds automatically if `f` is injective
or if `σ` is finite.

This file is patterned after `Mathlib/Algebra/MvPolynomial/Rename.lean`.

## Main declarations

* `MvPowerSeries.rename`
* `MvPowerSeries.renameEquiv`
* `MvPowerSeries.killCompl`

-/

@[expose] public section

noncomputable section

open Finsupp Filter

variable {σ τ γ R S : Type*} (f : σ → τ) (g : τ → γ) [TendstoCofinite f]

namespace MvPowerSeries

section Semiring

variable [Semiring R] [Semiring S]

/-- Implementation detail for `rename`. Use `MvPowerSeries.rename` instead. -/
/-
**MvPowerSeries.renameFun** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：renameFun : MvPowerSeries σ R -> MvPowerSeries τ R
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M

--- 原说明 ---
Implementation detail for `rename`. Use `MvPowerSeries.rename` instead.
-/
def renameFun : MvPowerSeries σ R → MvPowerSeries τ R :=
  TendstoCofinite.mapDomain (Finsupp.mapDomain f)
/-
**MvPowerSeries.coeff_renameFun** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma coeff_renameFun {p : MvPowerSeries σ R} {x : τ →₀ ℕ} : (renameFun f p).coeff x =
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sum (p.coeff ·) :=
  rfl
/-
**MvPowerSeries.renameFun_monomial** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma renameFun_monomial (x : σ →₀ ℕ) (r : R) :
    renameFun f (monomial x r) = monomial (mapDomain f x) r := by
  classical
  ext; simp [coeff_renameFun, coeff_monomial, eq_comm]
/-
**MvPowerSeries.renameFunAux** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem renameFunAux [DecidableEq σ] (x : τ →₀ ℕ) :
    {p : (σ →₀ ℕ) × (σ →₀ ℕ) × (σ →₀ ℕ) | (p.1).mapDomain f = x ∧
      p.2 ∈ Finset.antidiagonal p.1}.Finite := by
  apply Set.Finite.subset
    (s := ↑((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sup
    (fun y ↦ Finset.product {y} (Finset.antidiagonal y))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind
/-
**MvPowerSeries.renameFunAux'** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem renameFunAux' [DecidableEq τ] (x : τ →₀ ℕ) :
    {p : ((τ →₀ ℕ) × (τ →₀ ℕ)) × (σ →₀ ℕ) × (σ →₀ ℕ) | p.1 ∈ Finset.antidiagonal x
      ∧ p.2 ∈ (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) p.1.1).toFinset ×ˢ
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) p.1.2).toFinset}.Finite := by
  classical
  apply Set.Finite.subset (s := ↑((Finset.antidiagonal x).sup (fun q ↦ Finset.product {q}
    ((TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.1).toFinset ×ˢ
      (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) q.2).toFinset))))
  · exact Finset.finite_toSet ..
  · intro; simp
    grind
/-
**MvPowerSeries.renameFunAuxImage** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem renameFunAuxImage [DecidableEq σ] [DecidableEq τ] (x : τ →₀ ℕ) :
    (renameFunAux' f x).toFinset.image (fun (_, b) ↦ (b.1 + b.2, b)) =
      (renameFunAux f x).toFinset := by
  ext ⟨_, _, _⟩
  simp; grind [Finsupp.mapDomain_add]

open Finset in
/-
**MvPowerSeries.renameFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem renameFun_mul (p q : MvPowerSeries σ R) :
    renameFun f (p * q) = renameFun f p * renameFun f q := by
  classical
  ext x
  simp only [coeff_renameFun, coeff_mul, sum_mul_sum, ← sum_product']
  rw [← sum_finset_product' (renameFunAux f x).toFinset _ _ (by simp),
    ← sum_finset_product' (renameFunAux' f x).toFinset _ _ (by simp),
    ← renameFunAuxImage f x, sum_image fun _ ↦ by simp; grind]

end Semiring

section CommSemiring

variable [CommSemiring R] [CommSemiring S]

/-- Rename all the variables in a multivariable power series by a map with finite fibers. -/
@[no_expose]
/-
**MvPowerSeries.rename** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：rename : MvPowerSeries σ R ->ₐ[R] MvPowerSeries τ R where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Rename all the variables in a multivariable power series by a map with finite fi
bers.
-/
def rename : MvPowerSeries σ R →ₐ[R] MvPowerSeries τ R where
  toFun := renameFun f
  map_one' := renameFun_monomial f 0 1
  map_mul' := renameFun_mul f
  map_zero' := by ext; simp [coeff_renameFun]
  map_add' _ _ := by ext; simp [coeff_renameFun, Finset.sum_add_distrib]
  commutes' := renameFun_monomial f 0
/-
**MvPowerSeries.coeff_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_rename (p : MvPowerSeries σ R) (x : τ ->₀ Nat) : coeff x (rename f p
) = (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset
.sum (p.coeff ·)
参数：p : MvPowerSeries σ R；x : τ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeff_rename (p : MvPowerSeries σ R) (x : τ →₀ ℕ) : coeff x (rename f p) =
    (TendstoCofinite.finite_preimage_singleton (Finsupp.mapDomain f) x).toFinset.sum
      (p.coeff ·) := by rfl
/-
**MvPowerSeries.rename_monomial** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_monomial (x : σ ->₀ Nat) (r : R) : rename f (monomial x r) = monomi
al (mapDomain f x) r
参数：x : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Rename.0.MvPowerSeries.renameF
un_monomial`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u_4} (f : σ → τ) [inst : 
Filter.TendstoCofinite f] [inst_1 : Semiring R]   (x : σ →₀ ℕ) (r : R),  …
-/
theorem rename_monomial (x : σ →₀ ℕ) (r : R) : rename f (monomial x r) =
    monomial (mapDomain f x) r := renameFun_monomial f ..

@[simp]
/-
**MvPowerSeries.coeff_embDomain_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`
。
形式化陈述：coeff_embDomain_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (x : σ ->₀ Nat)
 : coeff (embDomain e x) (rename e p) = p.coeff x
参数：e : σ ↪ τ；p : MvPowerSeries σ R；x : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.TendstoCofinite.embedding`：embedding (e : α ↪ β) : TendstoCofinit
e e
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem coeff_embDomain_rename (e : σ ↪ τ) (p : MvPowerSeries σ R) (x : σ →₀ ℕ) :
    coeff (embDomain e x) (rename e p) = p.coeff x := by
  rw [coeff_rename, Finset.sum_eq_single x _ (by simp [← embDomain_eq_mapDomain])]
  simpa using fun _ h h' ↦ by simp [← embDomain_eq_mapDomain, embDomain_inj, h'] at h
/-
**MvPowerSeries.coeff_rename_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_rename_eq_zero (p : MvPowerSeries σ R) {x : τ ->₀ Nat} (h' : x ∉ Set
.range (Finsupp.mapDomain f)) : (rename f p).coeff x = 0
参数：p : MvPowerSeries σ R；h' : x ∉ Set.range (Finsupp.mapDomain f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `Set.toFinset_congr`：toFinset_congr {s t : Set α} [Fintype s] [Fintype t]
 (h : s = t) : toFinset s = toFinset t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.preimage_singleton_eq_empty`：preimage_singleton_eq_empty {f : α -> β
} {y : β} : f ⁻¹' {y} = ∅ ↔ y ∉ range f
· 使用定理 `Set.toFinset_empty`：toFinset_empty [Fintype (∅ : Set α)] : (∅ : Set α).t
oFinset = ∅
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_rename_eq_zero (p : MvPowerSeries σ R) {x : τ →₀ ℕ}
    (h' : x ∉ Set.range (Finsupp.mapDomain f)) : (rename f p).coeff x = 0 := by
  simp [coeff_rename, Set.Finite.toFinset, Set.preimage_singleton_eq_empty.mpr h']

@[simp]
/-
**MvPowerSeries.rename_C** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_C (r : R) : rename f (C r : MvPowerSeries σ R) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.rename_monomial`：rename_monomial (x : σ ->₀ Nat) (r : R) :
 rename f (monomial x r) = monomial (mapDomain f x) r
-/
theorem rename_C (r : R) : rename f (C r : MvPowerSeries σ R) = C r := rename_monomial f 0 r

@[simp]
/-
**MvPowerSeries.rename_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i)
参数：i : σ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `MvPowerSeries.rename_monomial`：rename_monomial (x : σ ->₀ Nat) (r : R) :
 rename f (monomial x r) = monomial (mapDomain f x) r
-/
theorem rename_X (i : σ) : rename f (X i : MvPowerSeries σ R) = X (f i) := by
  simpa using! rename_monomial f (single i 1) 1

@[simp]
/-
**MvPowerSeries.rename_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_rename [TendstoCofinite g] (p : MvPowerSeries σ R) : rename g (rena
me f p) = rename (g ∘ f) p
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用引理 `Filter.TendstoCofinite.comp`：comp [TendstoCofinite g] [TendstoCofinite f
] : TendstoCofinite (g ∘ f)
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_finset_product'`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_
5} [inst : AddCommMonoid β] (r : Finset (γ × α)) (s : Finset γ)   (t : γ → Finse
t α),   (∀ (p : …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Finset.sum_image`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_4} [inst :
 AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι]   {s : Finset κ} {g : κ →
 ι}, S…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem rename_rename [TendstoCofinite g] (p : MvPowerSeries σ R) :
    rename g (rename f p) = rename (g ∘ f) p := by
  classical
  ext y; simp only [coeff_rename]
  rw [← Finset.sum_finset_product' ((TendstoCofinite.finite_preimage_singleton
    (Finsupp.mapDomain (g ∘ f)) y).toFinset.image (fun u ↦ (Finsupp.mapDomain f u, u))) _ _
      (by simp; grind [mapDomain_comp]), Finset.sum_image (by simp)]
/-
**MvPowerSeries.rename_comp_rename** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_comp_rename [TendstoCofinite g] : (rename (R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用引理 `Filter.TendstoCofinite.comp`：comp [TendstoCofinite g] [TendstoCofinite f
] : TendstoCofinite (g ∘ f)
· 使用定理 `MvPowerSeries.rename_rename`：rename_rename [TendstoCofinite g] (p : MvPo
werSeries σ R) : rename g (rename f p) = rename (g ∘ f) p
-/
lemma rename_comp_rename [TendstoCofinite g] :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  AlgHom.ext fun p ↦ rename_rename f g p

@[simp]
/-
**MvPowerSeries.rename_id** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_id : rename id = AlgHom.id R (MvPowerSeries σ R)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用引理 `Filter.TendstoCofinite.id`：id : TendstoCofinite (id : α -> α)
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finsupp.mapDomain_id`：mapDomain_id : mapDomain id v = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem rename_id : rename id = AlgHom.id R (MvPowerSeries σ R) := by
  ext _ y
  simpa [coeff_rename] using Finset.sum_eq_single y (by simp) (by simp)
/-
**MvPowerSeries.rename_id_apply** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_id_apply (p : MvPowerSeries σ R) : rename id p = p
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `Filter.TendstoCofinite.id`：id : TendstoCofinite (id : α -> α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.rename_id`：rename_id : rename id = AlgHom.id R (MvPowerSer
ies σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma rename_id_apply (p : MvPowerSeries σ R) : rename id p = p := by simp

@[simp]
/-
**MvPowerSeries.constantCoeff_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：constantCoeff_rename (p : MvPowerSeries σ R) : constantCoeff (rename f p) 
= constantCoeff p
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.coeff_zero_eq_constantCoeff_apply`：coeff_zero_eq_constantC
oeff_apply (φ : MvPowerSeries σ R) : coeff (0 : σ ->₀ Nat) φ = constantCoeff φ
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
-/
theorem constantCoeff_rename (p : MvPowerSeries σ R) :
    constantCoeff (rename f p) = constantCoeff p := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_rename, Finset.sum_eq_single 0 (by
      simp [mapDomain_apply_eq_zero_iff_of_subsingletonAddUnits]) (by simp)]
/-
**MvPowerSeries.rename_injective** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_injective (e : σ ↪ τ) : Function.Injective (rename (R
参数：e : σ ↪ τ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.TendstoCofinite.embedding`：embedding (e : α ↪ β) : TendstoCofinit
e e
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_embDomain_rename`：coeff_embDomain_rename (e : σ ↪ τ)
 (p : MvPowerSeries σ R) (x : σ ->₀ Nat) : coeff (embDomain e x) (rename e p) = 
p.coeff x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MvPowerSeries.ext_iff`：∀ {σ : Type u_1} {R : Type u_2} [inst : Semiring 
R] {φ ψ : MvPowerSeries σ R},   φ = ψ ↔ ∀ (n : σ →₀ ℕ), (MvPowerSeries.coeff n) 
φ = (MvPowe…
-/
theorem rename_injective (e : σ ↪ τ) : Function.Injective (rename (R := R) e) := by
  intro _ _ h; ext x
  simpa using MvPowerSeries.ext_iff.mp h (embDomain e x)
/-
**MvPowerSeries.rename_inj** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_inj (e : σ ↪ τ) (p q : MvPowerSeries σ R) : rename e p = rename e q
 ↔ p = q
参数：e : σ ↪ τ；p q : MvPowerSeries σ R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `Filter.TendstoCofinite.embedding`：embedding (e : α ↪ β) : TendstoCofinit
e e
· 使用定理 `MvPowerSeries.rename_injective`：rename_injective (e : σ ↪ τ) : Function.
Injective (rename (R
-/
theorem rename_inj (e : σ ↪ τ) (p q : MvPowerSeries σ R) :
    rename e p = rename e q ↔ p = q := (rename_injective e).eq_iff
/-
**MvPowerSeries.rename_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_map (φ : R ->+* S) (p : MvPowerSeries σ R) : rename f (map φ p) = m
ap φ (rename f p)
参数：φ : R ->+* S；p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem rename_map (φ : R →+* S) (p : MvPowerSeries σ R) :
    rename f (map φ p) = map φ (rename f p) := by
  ext; simp [coeff_rename]
/-
**MvPowerSeries.rename_coe** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_coe (p : MvPolynomial σ R) : rename f (p : MvPowerSeries σ R) = p.r
ename f
参数：p : MvPolynomial σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.induction_on`：induction_on {motive : MvPolynomial σ R -> Pr
op} (p : MvPolynomial σ R) (C : forall a, motive (C a)) (add : forall p q, motiv
e p -> motive q…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.coe_C`：coe_C (a : R) : ((C a : MvPolynomial σ R) : MvPowerS
eries σ R) = MvPowerSeries.C a
· 使用定理 `MvPowerSeries.rename_C`：rename_C (r : R) : rename f (C r : MvPowerSeries
 σ R) = C r
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `MvPolynomial.coe_mul`：coe_mul : ((φ * ψ : MvPolynomial σ R) : MvPowerSer
ies σ R) = φ * ψ
· 使用定理 `MvPolynomial.coe_X`：coe_X (s : σ) : ((X s : MvPolynomial σ R) : MvPowerS
eries σ R) = MvPowerSeries.X s
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `MvPowerSeries.rename_X`：rename_X (i : σ) : rename f (X i : MvPowerSeries
 σ R) = X (f i)
· 使用定理 `MvPolynomial.rename_X`：rename_X (f : σ -> τ) (i : σ) : rename f (X i : M
vPolynomial σ R) = X (f i)
-/
theorem rename_coe (p : MvPolynomial σ R) : rename f (p : MvPowerSeries σ R) = p.rename f := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P n hP => simp only [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul, hP, rename_X,
    MvPolynomial.rename_X]

variable (R) in
/-- `rename` is an equivalence when the underlying map is an equivalence. -/
@[simps apply]
/-
**MvPowerSeries.renameEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R where 
__
参数：e : σ ≃ τ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Filter.TendstoCofinite.equiv`：equiv (e : α ≃ β) : TendstoCofinite e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`rename` is an equivalence when the underlying map is an equivalence.
-/
def renameEquiv (e : σ ≃ τ) : MvPowerSeries σ R ≃ₐ[R] MvPowerSeries τ R where
  __ := rename e
  invFun := rename e.symm
  left_inv _ := by simp
  right_inv _ := by simp

@[simp]
/-
**MvPowerSeries.renameEquiv_refl** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.TendstoCofinite.equiv`：equiv (e : α ≃ β) : TendstoCofinite e
· 使用定理 `MvPowerSeries.renameEquiv_apply`：∀ {σ : Type u_1} {τ : Type u_2} (R : Ty
pe u_4) [inst : CommSemiring R] (e : σ ≃ τ) (a : MvPowerSeries σ R),   (MvPowerS
eries.renameEquiv R e…
· 使用定理 `MvPowerSeries.rename_id`：rename_id : rename id = AlgHom.id R (MvPowerSer
ies σ R)
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem renameEquiv_refl : renameEquiv R (Equiv.refl σ) = AlgEquiv.refl := AlgEquiv.ext (by simp)

@[simp]
/-
**MvPowerSeries.renameEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.sy
mm
参数：f : σ ≃ τ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem renameEquiv_symm (f : σ ≃ τ) : (renameEquiv R f).symm = renameEquiv R f.symm := rfl

@[simp]
/-
**MvPowerSeries.renameEquiv_trans** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ γ) : (renameEquiv R e).trans (renam
eEquiv R f) = renameEquiv R (e.trans f)
参数：e : σ ≃ τ；f : τ ≃ γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `MvPowerSeries.rename_rename`：rename_rename [TendstoCofinite g] (p : MvPo
werSeries σ R) : rename g (rename f p) = rename (g ∘ f) p
· 使用引理 `Filter.TendstoCofinite.equiv`：equiv (e : α ≃ β) : TendstoCofinite e
-/
theorem renameEquiv_trans (e : σ ≃ τ) (f : τ ≃ γ) : (renameEquiv R e).trans (renameEquiv R f) =
    renameEquiv R (e.trans f) := AlgEquiv.ext (rename_rename e f)

variable {e : σ ↪ τ}

/-- Implementation detail for `killCompl`. Use `MvPowerSeries.killCompl` instead. -/
/-
**MvPowerSeries.killComplFun** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：killComplFun (e : σ ↪ τ) (p : MvPowerSeries τ R) : MvPowerSeries σ R
参数：e : σ ↪ τ；p : MvPowerSeries τ R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Implementation detail for `killCompl`. Use `MvPowerSeries.killCompl` instead.
-/
def killComplFun (e : σ ↪ τ) (p : MvPowerSeries τ R) : MvPowerSeries σ R :=
  fun x ↦ coeff (embDomain e x) p
/-
**MvPowerSeries.coeff_killComplFun** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem coeff_killComplFun (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
    coeff x (killComplFun e p) = coeff (embDomain e x) p := rfl
/-
**MvPowerSeries.killComplFun_monomial_embDomain** 是 Mathlib 中的一个定理，位于命名空间 `MvPow
erSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem killComplFun_monomial_embDomain (x : σ →₀ ℕ) (r : R) :
    killComplFun e (monomial (embDomain e x) r) = monomial x r := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial, embDomain_inj]
/-
**MvPowerSeries.killComplFun_monomial_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPower
Series`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem killComplFun_monomial_eq_zero {x : τ →₀ ℕ} (r : R)
    (h : x ∉ Set.range (embDomain e)) : killComplFun e (monomial x r) = 0 := by
  classical
  ext; simp [coeff_killComplFun, coeff_monomial]
  grind
/-
**MvPowerSeries.killComplFun_mul** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem killComplFun_mul (p q : MvPowerSeries τ R) :
    killComplFun e (p * q) = killComplFun e p * killComplFun e q := by
  classical
  ext
  simp [coeff_killComplFun, coeff_mul, ← image_prodMap_embDomain_antidiagonal, Finset.sum_image
    ((Function.Injective.injOn (Prod.map_injective.mpr ⟨embDomain_injective e,
      embDomain_injective e⟩)))]

/-- Given an embedding `e : σ ↪ τ`, `MvPowerSeries.killComplFun e` is the function from
`R⟦τ⟧` to `R⟦σ⟧` that is left inverse to `rename e.injective.fiberFinite : R⟦σ⟧ → R⟦τ⟧`
and sends the variables in the complement of the range of `e` to `0`. -/
@[no_expose]
/-
**MvPowerSeries.killCompl** 是 Mathlib 中的一个定义，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl (e : σ ↪ τ) : MvPowerSeries τ R ->ₐ[R] MvPowerSeries σ R where t
oFun
参数：e : σ ↪ τ。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Rename.0.MvPowerSeries.killCom
plFun_mul`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [inst : CommSemiring R
] {e : σ ↪ τ} (p q : MvPowerSeries τ R),   MvPowerSeries.killComplFun e…

--- 原说明 ---
Given an embedding `e : σ ↪ τ`, `MvPowerSeries.killComplFun e` is the function f
rom
`R⟦τ⟧` to `R⟦σ⟧` that is left inverse to `rename e.injective.fiberFinite : R⟦σ⟧ 
→ R⟦τ⟧`
and sends the variables in the complement of the range of `e` to `0`.
-/
def killCompl (e : σ ↪ τ) : MvPowerSeries τ R →ₐ[R] MvPowerSeries σ R where
  toFun := killComplFun e
  map_one' := by simpa using! killComplFun_monomial_embDomain 0 1
  map_mul' := killComplFun_mul
  map_zero' := by ext; simp [coeff_killComplFun]
  map_add' _ _ := by ext; simp [coeff_killComplFun]
  commutes' := by simpa using! killComplFun_monomial_embDomain 0
/-
**MvPowerSeries.coeff_killCompl** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：coeff_killCompl (p : MvPowerSeries τ R) (x : σ ->₀ Nat) : coeff x (killCom
pl e p) = coeff (embDomain e x) p
参数：p : MvPowerSeries τ R；x : σ ->₀ Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coeff_killCompl (p : MvPowerSeries τ R) (x : σ →₀ ℕ) :
    coeff x (killCompl e p) = coeff (embDomain e x) p := by rfl
/-
**MvPowerSeries.killCompl_monomial_embDomain** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerS
eries`。
形式化陈述：killCompl_monomial_embDomain (x : σ ->₀ Nat) (r : R) : killCompl e (monomi
al (embDomain e x) r) = monomial x r
参数：x : σ ->₀ Nat；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Rename.0.MvPowerSeries.killCom
plFun_monomial_embDomain`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [inst :
 CommSemiring R] {e : σ ↪ τ} (x : σ →₀ ℕ) (r : R),   MvPowerSeries.killComplFun 
e ((Mv…
-/
lemma killCompl_monomial_embDomain (x : σ →₀ ℕ) (r : R) :
    killCompl e (monomial (embDomain e x) r) = monomial x r :=
  killComplFun_monomial_embDomain x r
/-
**MvPowerSeries.killCompl_monomial_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSer
ies`。
形式化陈述：killCompl_monomial_eq_zero {x : τ ->₀ Nat} (r : R) (h : x ∉ Set.range (emb
Domain e)) : killCompl e (monomial x r) = 0
参数：r : R；h : x ∉ Set.range (embDomain e)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.RingTheory.MvPowerSeries.Rename.0.MvPowerSeries.killCom
plFun_monomial_eq_zero`：∀ {σ : Type u_1} {τ : Type u_2} {R : Type u_4} [inst : C
ommSemiring R] {e : σ ↪ τ} {x : τ →₀ ℕ} (r : R),   x ∉ Set.range (Finsupp.embDom
ain …
-/
lemma killCompl_monomial_eq_zero {x : τ →₀ ℕ} (r : R)
    (h : x ∉ Set.range (embDomain e)) : killCompl e (monomial x r) = 0 :=
  killComplFun_monomial_eq_zero r h

@[simp]
/-
**MvPowerSeries.killCompl_C** 是 Mathlib 中的一个引理，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl_C (r : R) : killCompl e (C r) = C r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MvPowerSeries.killCompl_monomial_embDomain`：killCompl_monomial_embDomain
 (x : σ ->₀ Nat) (r : R) : killCompl e (monomial (embDomain e x) r) = monomial x
 r
-/
lemma killCompl_C (r : R) : killCompl e (C r) = C r := by
  simpa using killCompl_monomial_embDomain 0 r

@[simp]
/-
**MvPowerSeries.killCompl_X** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl_X (i : σ) : killCompl (R
参数：i : σ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.coeff_killCompl`：coeff_killCompl (p : MvPowerSeries τ R) (
x : σ ->₀ Nat) : coeff x (killCompl e p) = coeff (embDomain e x) p
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem killCompl_X (i : σ) : killCompl (R := R) e (X (e i)) = X i := by
  classical
  ext; simp [coeff_X, coeff_killCompl, ← embDomain_single]
/-
**MvPowerSeries.killCompl_X_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl_X_eq_zero {t : τ} (h : t ∉ Set.range e) : killCompl (R
参数：h : t ∉ Set.range e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Finsupp.mem_range_embDomain_iff`：mem_range_embDomain_iff [AddCommMonoid 
M] (f : α ↪ β) (x : β ->₀ M) : x in Set.range (embDomain f) ↔ ↑x.support subsete
q Set.range f
· 使用定理 `Finsupp.support_single`：∀ {α : Type u_1} {M : Type u_5} [inst : Zero M] 
{b : M} (a : α), b ≠ 0 → (fun₀ | a => b).support = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `MvPowerSeries.killCompl_monomial_eq_zero`：killCompl_monomial_eq_zero {x 
: τ ->₀ Nat} (r : R) (h : x ∉ Set.range (embDomain e)) : killCompl e (monomial x
 r) = 0
-/
theorem killCompl_X_eq_zero {t : τ} (h : t ∉ Set.range e) :
    killCompl (R := R) e (X t) = 0 := by
  replace h : single t 1 ∉ Set.range (embDomain e) := by
    rwa [mem_range_embDomain_iff, support_single _ (by simp), Finset.coe_singleton,
      Set.singleton_subset_iff]
  simpa using! killCompl_monomial_eq_zero (1 : R) h
/-
**MvPowerSeries.killCompl_comp_rename** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl_comp_rename : (killCompl e).comp (rename e) = AlgHom.id R _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用引理 `Filter.TendstoCofinite.embedding`：embedding (e : α ↪ β) : TendstoCofinit
e e
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.coeff_killCompl`：coeff_killCompl (p : MvPowerSeries τ R) (
x : σ ->₀ Nat) : coeff x (killCompl e p) = coeff (embDomain e x) p
· 使用定理 `MvPowerSeries.coeff_embDomain_rename`：coeff_embDomain_rename (e : σ ↪ τ)
 (p : MvPowerSeries σ R) (x : σ ->₀ Nat) : coeff (embDomain e x) (rename e p) = 
p.coeff x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem killCompl_comp_rename : (killCompl e).comp (rename e) = AlgHom.id R _ := by
  ext; simp [coeff_killCompl]

@[simp]
/-
**MvPowerSeries.killCompl_rename_app** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl_rename_app (p : MvPowerSeries σ R) : killCompl e (rename e p) = 
p
参数：p : MvPowerSeries σ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用引理 `Filter.TendstoCofinite.embedding`：embedding (e : α ↪ β) : TendstoCofinit
e e
· 使用定理 `MvPowerSeries.killCompl_comp_rename`：killCompl_comp_rename : (killCompl 
e).comp (rename e) = AlgHom.id R _
-/
theorem killCompl_rename_app (p : MvPowerSeries σ R) : killCompl e (rename e p) = p :=
  AlgHom.congr_fun (killCompl_comp_rename) p
/-
**MvPowerSeries.killCompl_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：killCompl_map (φ : R ->+* S) (p : MvPowerSeries τ R) : killCompl e (map φ 
p) = map φ (killCompl e p)
参数：φ : R ->+* S；p : MvPowerSeries τ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MvPowerSeries.coeff_killCompl`：coeff_killCompl (p : MvPowerSeries τ R) (
x : σ ->₀ Nat) : coeff x (killCompl e p) = coeff (embDomain e x) p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem killCompl_map (φ : R →+* S) (p : MvPowerSeries τ R) :
    killCompl e (map φ p) = map φ (killCompl e p) := by
  ext; simp [coeff_killCompl]

end CommSemiring

section CommRing

variable {R : Type*} [CommRing R] (p : MvPowerSeries σ R)

/-
**MvPowerSeries.HasSubst.X_comp** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries.HasSubs
t`。
形式化陈述：∀ {σ : Type u_1} {τ : Type u_2} (f : σ → τ) [Filter.TendstoCofinite f] {R 
: Type u_6} [inst : CommRing R],   MvPowerSeries.HasSubst (MvPowerSeries.X ∘ f)
参数：f : σ → τ；MvPowerSeries.X ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.constantCoeff_X`：constantCoeff_X (s : σ) : constantCoeff (
R
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.biUnion'`：∀ {α : Type u} {ι : Type u_1} {s : Set ι},   s.Fini
te →     ∀ {t : (i : ι) → i ∈ s → Set α}, (∀ (i : ι) (hi : i ∈ s), (t i hi).Fini
te) → (⋃ …
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MvPowerSeries.coeff_X`：coeff_X [DecidableEq σ] (n : σ ->₀ Nat) (s : σ) :
 coeff n (X s : MvPowerSeries σ R) = if n = single s 1 then 1 else 0
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
-/
lemma HasSubst.X_comp : HasSubst (X ∘ f : σ → MvPowerSeries τ R) where
  const_coeff := by simp
  coeff_zero d := Set.Finite.subset (d.support.finite_toSet.biUnion'
    (fun i _ ↦ TendstoCofinite.finite_preimage_singleton f i)) (fun x => by
      contrapose; intro _ _; classical simp_all [coeff_X])

set_option backward.isDefEq.respectTransparency.types false in
/-
**MvPowerSeries.rename_eq_subst** 是 Mathlib 中的一个定理，位于命名空间 `MvPowerSeries`。
形式化陈述：rename_eq_subst : rename f p = p.subst (X ∘ f)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPowerSeries.ext`：ext {φ ψ : MvPowerSeries σ R} (h : forall n : σ ->₀ N
at, coeff n φ = coeff n ψ) : φ = ψ
· 使用定理 `Filter.TendstoCofinite.finite_preimage_singleton`：∀ {α : Type u_1} {β : 
Type u_2} (f : α → β) [Filter.TendstoCofinite f] (b : β), (f ⁻¹' {b}).Finite
· 使用定理 `Finsupp.mapDomain_tendstoCofinite`：Finsupp.mapDomain_tendstoCofinite [Te
ndstoCofinite f] : TendstoCofinite (mapDomain (M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPowerSeries.coeff_rename`：coeff_rename (p : MvPowerSeries σ R) (x : τ 
->₀ Nat) : coeff x (rename f p) = (TendstoCofinite.finite_preimage_singleton (Fi
nsupp.mapDomain …
· 使用定理 `MvPowerSeries.coeff_subst`：coeff_subst (ha : HasSubst a) (f : MvPowerSer
ies σ R) (e : τ ->₀ Nat) : coeff e (subst a f) = finsum (fun d => coeff d f • (c
oeff e (d.prod …
· 使用定理 `MvPowerSeries.HasSubst.X_comp`：∀ {σ : Type u_1} {τ : Type u_2} (f : σ → 
τ) [Filter.TendstoCofinite f] {R : Type u_6} [inst : CommRing R],   MvPowerSerie
s.HasSubst (MvPower…
· 使用定理 `MvPowerSeries.coeff_subst_finite`：coeff_subst_finite (ha : HasSubst a) (
f : MvPowerSeries σ R) (e : τ ->₀ Nat) : (fun d => coeff d f • (coeff e (d.prod 
fun s e => (a s) ^ e))…
· 使用定理 `finsum_eq_sum`：∀ {α : Type u_1} {M : Type u_5} [inst : AddCommMonoid M] 
(f : α → M) (hf : Function.HasFiniteSupport f),   ∑ᶠ (i : α), f i = ∑ i ∈ Set.Fi
nit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPowerSeries.eq_of_coeff_monomial_ne_zero`：eq_of_coeff_monomial_ne_zero
 {m n : σ ->₀ Nat} {a : R} (h : coeff m (monomial n a) != 0) : m = n
· 使用定理 `right_ne_zero_of_mul`：right_ne_zero_of_mul : a * b != 0 -> b != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_subset_zero_on_sdiff`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ 
: Finset ι} [inst : AddCommMonoid M] {f g : ι → M} [inst_1 : DecidableEq ι],   s
₁ ⊆ s₂ → (∀ x ∈ s₂ \ …
· 使用定理 `Set.Finite.toFinset_mono`：∀ {α : Type u} {s t : Set α} {hs : s.Finite} {
ht : t.Finite}, s ⊆ t → hs.toFinset ⊆ ht.toFinset
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `MvPowerSeries.coeff_monomial_same`：coeff_monomial_same (n : σ ->₀ Nat) (
a : R) : coeff n (monomial n a) = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem rename_eq_subst : rename f p = p.subst (X ∘ f) := by
  classical
  ext n
  rw [coeff_rename, coeff_subst (HasSubst.X_comp _) p n, finsum_eq_sum _
    (coeff_subst_finite (HasSubst.X_comp _) p n)]
  have (d : σ →₀ ℕ) (hd : (coeff d) p * (coeff n) (d.prod fun s e ↦ X (f s) ^ e) ≠ 0) :
      mapDomain f d = n := by
    simp_rw [← monomial_mapDomain_apply_one] at hd
    exact (eq_of_coeff_monomial_ne_zero (right_ne_zero_of_mul hd)).symm
  refine (Finset.sum_subset_zero_on_sdiff ?_ ?_ (fun x hx => ?_)).symm
  · exact Set.Finite.toFinset_mono this
  · simp +contextual [← monomial_mapDomain_apply_one]
  · simp only [Set.Finite.mem_toFinset] at hx
    simp [← this _ hx, ← monomial_mapDomain_apply_one, coeff_monomial_same]

end CommRing

end MvPowerSeries

