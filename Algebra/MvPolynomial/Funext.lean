/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Polynomial
public import Mathlib.Algebra.MvPolynomial.Rename

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `MvPolynomial.funext`: two polynomials `φ ψ : MvPolynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/

public section

namespace MvPolynomial

variable {R : Type*} [CommRing R] [IsDomain R]

/-
**MvPolynomial.funext_fin** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem funext_fin {n : ℕ} {p : MvPolynomial (Fin n) R}
    (s : Fin n → Set R) (hs : ∀ i, (s i).Infinite)
    (h : ∀ x ∈ Set.pi .univ s, eval x p = 0) : p = 0 := by
  induction n with
  | zero =>
    apply (MvPolynomial.isEmptyRingEquiv R (Fin 0)).injective
    simpa [constantCoeff, coeff] using h 0 finZeroElim
  | succ n ih =>
    apply (finSuccEquiv R n).injective
    rw [map_zero]
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply ((hs 0).image (C_injective ..).injOn).mono
    rintro _ ⟨r, hr, rfl⟩
    refine ih (s ·.succ) (fun _ ↦ hs _) fun x hx ↦ ?_
    rw [eval_polynomial_eval_finSuccEquiv]
    exact h _ fun i _ ↦ i.cases (by simpa [eval_C] using hr) (by simpa using hx)

section

variable {σ : Type*} {p q : MvPolynomial σ R} (s : σ → Set R) (hs : ∀ i, (s i).Infinite)
include hs

/-- Two multivariate polynomials over an integral domain are equal
if they are equal when evaluated anywhere in a box with infinite sides. -/
/-
**MvPolynomial.funext_set** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：funext_set (h : forall x in Set.pi .univ s, eval x p = eval x q) : p = q
参数：h : forall x in Set.pi .univ s, eval x p = eval x q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.exists_fin_rename`：exists_fin_rename (p : MvPolynomial σ R)
 : exists (n : Nat) (f : Fin n -> σ) (_hf : Injective f) (q : MvPolynomial (Fin 
n) R), p = rename f …
· 使用定理 `_private.Mathlib.Algebra.MvPolynomial.Funext.0.MvPolynomial.funext_fin`：
∀ {R : Type u_1} [inst : CommRing R] [IsDomain R] {n : ℕ} {p : MvPolynomial (Fin
 n) R} (s : Fin n → Set R),   (∀ (i : Fin n), (s i).Infinite…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.eval₂Hom_rename`：eval₂Hom_rename : eval₂Hom f g (rename k p
) = eval₂Hom f (g ∘ k) p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.extend_comp`：extend_comp (hf : Injective f) (g : α -> γ) (e' : 
β -> γ) : extend f g e' ∘ f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Set.Infinite.nonempty`：∀ {α : Type u} {s : Set α}, s.Infinite → s.Nonemp
ty
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0

--- 原说明 ---
Two multivariate polynomials over an integral domain are equal
if they are equal when evaluated anywhere in a box with infinite sides.
-/
theorem funext_set (h : ∀ x ∈ Set.pi .univ s, eval x p = eval x q) :
    p = q := by
  suffices ∀ p, (∀ x ∈ Set.pi .univ s, eval x p = 0) → p = 0 by
    rw [← sub_eq_zero, this (p - q)]
    intro x hx
    simp_rw [map_sub, h x hx, sub_self]
  intro p h
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p
  suffices p = 0 by rw [this, map_zero]
  refine funext_fin (s ∘ f) (fun _ ↦ hs _) fun x hx ↦ ?_
  choose g hg using fun i ↦ (hs i).nonempty
  convert! h (Function.extend f x g) fun i _ ↦ ?_
  · simp only [eval, eval₂Hom_rename, Function.extend_comp hf]
  obtain ⟨i, rfl⟩ | nex := em (∃ x, f x = i)
  · rw [hf.extend_apply]; exact hx _ ⟨⟩
  · simp_rw [Function.extend, dif_neg nex, hg]
/-
**MvPolynomial.funext_set_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：funext_set_iff : p = q ↔ (forall x in Set.pi .univ s, eval x p = eval x q)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.funext_set`：funext_set (h : forall x in Set.pi .univ s, eva
l x p = eval x q) : p = q
-/
theorem funext_set_iff : p = q ↔ (∀ x ∈ Set.pi .univ s, eval x p = eval x q) :=
  ⟨by rintro rfl _ _; rfl, funext_set s hs⟩

end

variable [Infinite R]

/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
/-
**MvPolynomial.funext** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：funext {σ : Type*} {p q : MvPolynomial σ R} (h : forall x : σ -> R, eval x
 p = eval x q) : p = q
参数：h : forall x : σ -> R, eval x p = eval x q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.funext_set`：funext_set (h : forall x in Set.pi .univ s, eva
l x p = eval x q) : p = q
· 使用定理 `Set.infinite_univ`：infinite_univ [h : Infinite α] : (@univ α).Infinite

--- 原说明 ---
Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variabl
es.
-/
theorem funext {σ : Type*} {p q : MvPolynomial σ R}
    (h : ∀ x : σ → R, eval x p = eval x q) :
    p = q :=
  funext_set _ (fun _ ↦ Set.infinite_univ) fun _ _ ↦ h _
/-
**MvPolynomial.funext_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：funext_iff {σ : Type*} {p q : MvPolynomial σ R} : p = q ↔ forall x : σ -> 
R, eval x p = eval x q
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `MvPolynomial.funext`：funext {σ : Type*} {p q : MvPolynomial σ R} (h : fo
rall x : σ -> R, eval x p = eval x q) : p = q
-/
theorem funext_iff {σ : Type*} {p q : MvPolynomial σ R} :
    p = q ↔ ∀ x : σ → R, eval x p = eval x q :=
  ⟨by rintro rfl; simp only [forall_const], funext⟩

end MvPolynomial

