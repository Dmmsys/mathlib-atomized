/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.ModelTheory.Definability
public import Mathlib.RingTheory.MvPolynomial.FreeCommRing
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.ModelTheory.Algebra.Ring.FreeCommRing

/-!

# Definable Subsets in the language of rings

This file proves that the set of zeros of a multivariable polynomial is a definable subset.

-/

public section

namespace FirstOrder

namespace Ring

open MvPolynomial Language BoundedFormula

/-
**FirstOrder.Ring.mvPolynomial_zeroLocus_definable** 是 Mathlib 中的一个定理，位于命名空间 `Fi
rstOrder.Ring`。
形式化陈述：mvPolynomial_zeroLocus_definable {ι K : Type*} [Field K] [CompatibleRing K
] (S : Finset (MvPolynomial ι K)) : Set.Definable (⋃ p in S, p.coeff '' p.suppor
t : Set K) Language.ring (zeroLocus K (Ideal.span (S : Set (MvPolynomial ι K))))
参数：S : Finset (MvPolynomial ι K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.definable_iff_exists_formula_sum`：definable_iff_exists_formula_sum :
 A.Definable L s ↔ exists φ : L.Formula (A oplus α), s = {v | φ.Realize (Sum.eli
m (↑) v)}
· 使用定理 `MvPolynomial.zeroLocus_span`：zeroLocus_span (S : Set (MvPolynomial σ k))
 : zeroLocus K (Ideal.span S) = { x | forall p in S, aeval x p = 0 }
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FirstOrder.Language.BoundedFormula.iInf.congr_simp`：∀ {L : FirstOrder.La
nguage} {α : Type u'} {β : Type v'} {n : ℕ} [inst : Finite β] (f f_1 : β → L.Bou
ndedFormula α n),   f = f_1 → FirstOrder…
· 使用定理 `FirstOrder.Language.Term.relabel_relabel`：relabel_relabel (f : α -> β) (
g : β -> γ) (t : L.Term α) : (t.relabel f).relabel g = t.relabel (g ∘ f)
· 使用定理 `FirstOrder.Language.Term.realize_relabel`：realize_relabel {t : L.Term α}
 {g : α -> β} {v : β -> M} : (t.relabel g).realize v = t.realize (v ∘ g)
· 使用定理 `FirstOrder.Ring.realize_termOfFreeCommRing`：realize_termOfFreeCommRing (
p : FreeCommRing α) (v : α -> R) : (termOfFreeCommRing p).realize v = FreeCommRi
ng.lift v p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `FirstOrder.Ring.lift_genericPolyMap`：lift_genericPolyMap [DecidableEq κ]
 [CommRing R] [DecidableEq R] (monoms : ι -> Finset (κ ->₀ Nat)) (f : (i : ι) × 
{ x // x in monoms i } op…
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
· 使用定理 `FirstOrder.Ring.MvPolynomialSupportLEEquiv_symm_apply_coeff`：MvPolynomia
lSupportLEEquiv_symm_apply_coeff [DecidableEq κ] [CommRing R] [DecidableEq R] (p
 : ι -> MvPolynomial κ R) : (mvPolynomialSupportL…
· 使用定理 `FirstOrder.Ring.realize_zero`：realize_zero (v : α -> R) : Term.realize v
 (0 : ring.Term α) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mvPolynomial_zeroLocus_definable {ι K : Type*} [Field K]
    [CompatibleRing K] (S : Finset (MvPolynomial ι K)) :
    Set.Definable (⋃ p ∈ S, p.coeff '' p.support : Set K) Language.ring
      (zeroLocus K (Ideal.span (S : Set (MvPolynomial ι K)))) := by
  rw [Set.definable_iff_exists_formula_sum]
  let p' := genericPolyMap (fun p : S => p.1.support)
  let := Classical.decEq ι
  let := Classical.decEq K
  rw [MvPolynomial.zeroLocus_span]
  refine ⟨BoundedFormula.iInf
      (fun i : S => Term.equal
        ((termOfFreeCommRing (p' i)).relabel
          (Sum.map (fun p => ⟨p.1.1.coeff p.2.1, by
            simp only [Set.mem_iUnion]
            exact ⟨p.1.1, p.1.2, Set.mem_image_of_mem _ p.2.2⟩⟩) id)) 0), ?_⟩
  simp [Formula.Realize, Term.equal, Function.comp_def, p', MvPolynomial.aeval_eq_eval₂Hom]

end Ring

end FirstOrder

