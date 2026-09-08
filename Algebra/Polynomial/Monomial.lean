/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Kim Morrison, Jens Wagemaker
-/
module

public import Mathlib.Algebra.Group.Nat.Hom
public import Mathlib.Algebra.Polynomial.Basic

/-!
# Univariate monomials
-/

public section


noncomputable section

namespace Polynomial

universe u

variable {R : Type u} {a b : R} {m n : ℕ}
variable [Semiring R] {p q r : R[X]}

/-
**Polynomial.monomial_one_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_one_eq_iff [Nontrivial R] {i j : Nat} : (monomial i 1 : R[X]) = m
onomial j 1 ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.ofFinsupp.injEq`：∀ {R : Type u_1} [inst : Semiring R] (toFins
upp toFinsupp_1 : AddMonoidAlgebra R ℕ),   ({ toFinsupp := toFinsupp } = { toFin
supp := toFinsup…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `AddMonoidAlgebra.of_injective`：of_injective [Nontrivial R] [AddZeroClass
 M] : Function.Injective (of R M)
-/
theorem monomial_one_eq_iff [Nontrivial R] {i j : ℕ} :
    (monomial i 1 : R[X]) = monomial j 1 ↔ i = j := by
  simp_rw [← ofFinsupp_single, ofFinsupp.injEq]
  exact AddMonoidAlgebra.of_injective.eq_iff
/-
**Polynomial.infinite** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：infinite [Nontrivial R] : Infinite R[X]
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Infinite.of_injective`：of_injective {α β} [Infinite β] (f : β -> α) (hf 
: Injective f) : Infinite α
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
instance infinite [Nontrivial R] : Infinite R[X] :=
  Infinite.of_injective (fun i => monomial i 1) fun m n h => by simpa [monomial_one_eq_iff] using h
/-
**Polynomial.card_support_le_one_iff_monomial** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：card_support_le_one_iff_monomial {f : R[X]} : Finset.card f.support <= 1 ↔
 exists n a, f = monomial n a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_le_one_iff_subset_singleton`：card_le_one_iff_subset_singleto
n [Nonempty α] : #s <= 1 ↔ exists x : α, s subseteq {x}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.coeff_monomial_same`：coeff_monomial_same (n : Nat) (c : R) : 
(monomial n c).coeff n = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.notMem_support_iff`：notMem_support_iff : n ∉ p.support ↔ p.co
eff n = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_singleton`：mem_singleton {a b : α} : b in ({a} : Finset α) ↔ 
b = a
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用定理 `Finset.card_le_card`：card_le_card : s subseteq t -> #s <= #t
· 使用定理 `Polynomial.support_monomial_subset`：support_monomial_subset (n) (a : R) 
: (monomial n a).support subseteq singleton n
-/
theorem card_support_le_one_iff_monomial {f : R[X]} :
    Finset.card f.support ≤ 1 ↔ ∃ n a, f = monomial n a := by
  constructor
  · intro H
    rw [Finset.card_le_one_iff_subset_singleton] at H
    rcases H with ⟨n, hn⟩
    refine ⟨n, f.coeff n, ?_⟩
    ext i
    by_cases hi : i = n
    · simp [hi]
    · have : f.coeff i = 0 := by
        rw [← notMem_support_iff]
        exact fun hi' => hi (Finset.mem_singleton.1 (hn hi'))
      simp [this, Ne.symm hi, coeff_monomial]
  · rintro ⟨n, a, rfl⟩
    rw [← Finset.card_singleton n]
    apply Finset.card_le_card
    exact support_monomial_subset _ _
/-
**Polynomial.ringHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ringHom_ext {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : forall a, f (C a) =
 g (C a)) (h₂ : f X = g X) : f = g
参数：h₁ : forall a, f (C a) = g (C a)；h₂ : f X = g X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidAlgebra.ringHom_ext'`：ringHom_ext' [Semiring S] [AddMonoid M] {
f g : R[M] ->+* S} (h₁ : f.comp singleZeroRingHom = g.comp singleZeroRingHom) (h
_of : (f : R[M] ->*…
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AddMonoidAlgebra.singleZeroRingHom_apply`：∀ {R : Type u_1} {M : Type u_4
} [inst : Semiring R] [inst_1 : AddZeroClass M] (a : R),   AddMonoidAlgebra.sing
leZeroRingHom a = (↑(AddMonoid…
· 使用定理 `AddMonoidAlgebra.singleAddHom_apply`：∀ {R : Type u_1} {M : Type u_4} [in
st : Semiring R] (m : M) (r : R),   (AddMonoidAlgebra.singleAddHom m) r = AddMon
oidAlgebra.single m r
· 使用定理 `Polynomial.toFinsuppIso_symm_apply`：∀ (R : Type u) [inst : Semiring R] (
toFinsupp : AddMonoidAlgebra R ℕ),   (Polynomial.toFinsuppIso R).symm toFinsupp 
= { toFinsupp := toFinsu…
· 使用定理 `Polynomial.ofFinsupp_single`：ofFinsupp_single (n : Nat) (r : R) : (⟨.sin
gle n r⟩ : R[X]) = monomial n r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `MonoidHom.ext_mnat`：MonoidHom.ext_mnat ⦃f g : Multiplicative Nat ->* M⦄ 
(h : f (Multiplicative.ofAdd 1) = g (Multiplicative.ofAdd 1)) : f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `RingHom.comp_assoc`：comp_assoc {δ} {_ : NonAssocSemiring δ} (f : α ->+* 
β) (g : β ->+* γ) (h : γ ->+* δ) : (h.comp g).comp f = h.comp (g.comp f)
· 使用定理 `RingEquiv.symm_apply_apply`：symm_apply_apply (e : R ≃+* S) : forall x, e
.symm (e x) = x
-/
theorem ringHom_ext {S} [Semiring S] {f g : R[X] →+* S} (h₁ : ∀ a, f (C a) = g (C a))
    (h₂ : f X = g X) : f = g := by
  set f' := f.comp (toFinsuppIso R).symm.toRingHom with hf'
  set g' := g.comp (toFinsuppIso R).symm.toRingHom with hg'
  have A : f' = g' := by
    ext
    · simp [f', g', h₁, RingEquiv.toRingHom_eq_coe]
    simpa using! h₂
  have B : f = f'.comp (toFinsuppIso R) := by
    rw [hf', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  have C' : g = g'.comp (toFinsuppIso R) := by
    rw [hg', RingHom.comp_assoc]
    ext x
    simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.symm_apply_apply, Function.comp_apply,
      RingHom.coe_comp, RingEquiv.coe_toRingHom]
  rw [B, C', A]

@[ext high]
/-
**Polynomial.ringHom_ext'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：ringHom_ext' {S} [Semiring S] {f g : R[X] ->+* S} (h₁ : f.comp C = g.comp 
C) (h₂ : f X = g X) : f = g
参数：h₁ : f.comp C = g.comp C；h₂ : f X = g X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ringHom_ext`：ringHom_ext {S} [Semiring S] {f g : R[X] ->+* S}
 (h₁ : forall a, f (C a) = g (C a)) (h₂ : f X = g X) : f = g
· 使用定理 `RingHom.congr_fun`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring
 α} {x_1 : NonAssocSemiring β} {f g : α →+* β},   f = g → ∀ (x_2 : α), f x_2 = g
 x_2
-/
theorem ringHom_ext' {S} [Semiring S] {f g : R[X] →+* S} (h₁ : f.comp C = g.comp C)
    (h₂ : f X = g X) : f = g :=
  ringHom_ext (RingHom.congr_fun h₁) h₂

end Polynomial

