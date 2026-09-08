/-
Copyright (c) 2023 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.RingTheory.FreeCommRing

/-!

# Constructing Ring terms from MvPolynomial

This file provides tools for constructing ring terms that can be evaluated to particular
`MvPolynomial`s. The main motivation is in model theory. It can be used to construct first-order
formulas whose realization is a property of an `MvPolynomial`

## Main definitions

* `FirstOrder.Ring.genericPolyMap` is a function that given a finite set of monomials
  `monoms : ι → Finset (κ →₀ ℕ)` returns a function `ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ)`
  such that `genericPolyMap monoms i` is a ring term that can be evaluated to a polynomial
  `p : MvPolynomial κ R` such that `p.support ⊆ monoms i`.

-/

@[expose] public section

assert_not_exists Cardinal

variable {ι κ R : Type*}

namespace FirstOrder

namespace Ring

open MvPolynomial FreeCommRing

/-- Given a finite set of monomials `monoms : ι → Finset (κ →₀ ℕ)`, the
`genericPolyMap monoms` is an indexed collection of elements of the `FreeCommRing`,
that can be evaluated to any collection `p : ι → MvPolynomial κ R` of
polynomials such that `∀ i, (p i).support ⊆ monoms i`. -/
/-
**FirstOrder.Ring.genericPolyMap** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrder.Ring`。
形式化陈述：genericPolyMap (monoms : ι -> Finset (κ ->₀ Nat)) : ι -> FreeCommRing ((Σ 
i : ι, monoms i) oplus κ)
参数：monoms : ι -> Finset (κ ->₀ Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a finite set of monomials `monoms : ι → Finset (κ →₀ ℕ)`, the
`genericPolyMap monoms` is an indexed collection of elements of the `FreeCommRin
g`,
that can be evaluated to any collection `p : ι → MvPolynomial κ R` of
polynomials such that `∀ i, (p i).support ⊆ monoms i`.
-/
noncomputable def genericPolyMap (monoms : ι → Finset (κ →₀ ℕ)) :
    ι → FreeCommRing ((Σ i : ι, monoms i) ⊕ κ) :=
  fun i => (monoms i).attach.sum
    (fun m => FreeCommRing.of (Sum.inl ⟨i, m⟩) *
      Finsupp.prod m.1 (fun j n => FreeCommRing.of (Sum.inr j) ^ n))

/-- Collections of `MvPolynomial`s, `p : ι → MvPolynomial κ R` such
that `∀ i, (p i).support ⊆ monoms i` can be identified with functions
`(Σ i, monoms i) → R` by using the coefficient function -/
/-
**FirstOrder.Ring.mvPolynomialSupportLEEquiv** 是 Mathlib 中的一个定义，位于命名空间 `FirstOrd
er.Ring`。
形式化陈述：mvPolynomialSupportLEEquiv [DecidableEq κ] [CommRing R] [DecidableEq R] (m
onoms : ι -> Finset (κ ->₀ Nat)) : { p : ι -> MvPolynomial κ R // forall i, (p i
).support subseteq monoms i } ≃ ((Σ i, monoms i) -> R)
参数：monoms : ι -> Finset (κ ->₀ Nat)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Collections of `MvPolynomial`s, `p : ι → MvPolynomial κ R` such
that `∀ i, (p i).support ⊆ monoms i` can be identified with functions
`(Σ i, monoms i) → R` by using the coefficient function
-/
noncomputable def mvPolynomialSupportLEEquiv
    [DecidableEq κ] [CommRing R] [DecidableEq R]
    (monoms : ι → Finset (κ →₀ ℕ)) :
    { p : ι → MvPolynomial κ R // ∀ i, (p i).support ⊆ monoms i } ≃
      ((Σ i, monoms i) → R) :=
  { toFun := fun p i => (p.1 i.1).coeff i.2,
    invFun p := ⟨fun i => .ofCoeff
      { toFun := fun m => if hm : m ∈ monoms i then p ⟨i, ⟨m, hm⟩⟩ else 0
        support := {m ∈ monoms i | ∃ hm : m ∈ monoms i, p ⟨i, ⟨m, hm⟩⟩ ≠ 0},
        mem_support_toFun := by simp },
      fun i => Finset.filter_subset _ _⟩,
    left_inv := fun p => by
      ext i m
      simp only [coeff, ne_eq, exists_prop, dite_eq_ite, Finsupp.coe_mk, ite_eq_left_iff]
      intro hm
      have : m ∉ (p.1 i).support := fun h => hm (p.2 i h)
      simpa [coeff, eq_comm, MvPolynomial.mem_support_iff] using this
    right_inv := fun p => by ext; simp [coeff] }

@[simp]
/-
**FirstOrder.Ring.MvPolynomialSupportLEEquiv_symm_apply_coeff** 是 Mathlib 中的一个定理
，位于命名空间 `FirstOrder.Ring`。
形式化陈述：MvPolynomialSupportLEEquiv_symm_apply_coeff [DecidableEq κ] [CommRing R] [
DecidableEq R] (p : ι -> MvPolynomial κ R) : (mvPolynomialSupportLEEquiv (fun i 
=> (p i).support)).symm (fun i => (p i.1).coeff i.2.1) = ⟨p, fun _ => Finset.Sub
set.refl _⟩
参数：p : ι -> MvPolynomial κ R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Finset.Subset.refl`：∀ {α : Type u_1} (s : Finset α), s ⊆ s
-/
theorem MvPolynomialSupportLEEquiv_symm_apply_coeff [DecidableEq κ] [CommRing R] [DecidableEq R]
    (p : ι → MvPolynomial κ R) : (mvPolynomialSupportLEEquiv (fun i => (p i).support)).symm
      (fun i => (p i.1).coeff i.2.1) = ⟨p, fun _ => Finset.Subset.refl _⟩ :=
  (mvPolynomialSupportLEEquiv (R := R) (fun i : ι => (p i).support)).symm_apply_apply
    ⟨p, fun _ => Finset.Subset.refl _⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**FirstOrder.Ring.lift_genericPolyMap** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.Ring
`。
形式化陈述：lift_genericPolyMap [DecidableEq κ] [CommRing R] [DecidableEq R] (monoms :
 ι -> Finset (κ ->₀ Nat)) (f : (i : ι) × { x // x in monoms i } oplus κ -> R) (i
 : ι) : FreeCommRing.lift f (genericPolyMap monoms i) = MvPolynomial.eval (f ∘ S
um.inr) (((mvPolynomialSupportLEEquiv monoms).symm (f ∘ Sum.inl)).1 i)
参数：monoms : ι -> Finset (κ ->₀ Nat)；f : (i : ι) × { x // x in monoms i } oplus κ
 -> R；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FreeCommRing.lift_of`：lift_of (x : α) : lift f (of x) = f x
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finsupp.mk.congr_simp`：∀ {α : Type u_9} {M : Type u_10} [inst : Zero M] 
(support support_1 : Finset α) (e_support : support = support_1)   (toFun toFun_
1 : α → M) …
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `map_prod`：map_prod [CommMonoid M] [CommMonoid N] {G : Type*} [FunLike G 
M N] [MonoidHomClass G M N] (g : G) (f : ι -> M) (s : Finset ι) : g (∏ x in s,…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
（共 39 条，此处仅展示前 30 条）
-/
theorem lift_genericPolyMap [DecidableEq κ] [CommRing R]
    [DecidableEq R] (monoms : ι → Finset (κ →₀ ℕ))
    (f : (i : ι) × { x // x ∈ monoms i } ⊕ κ → R) (i : ι) :
    FreeCommRing.lift f (genericPolyMap monoms i) =
      MvPolynomial.eval (f ∘ Sum.inr)
        (((mvPolynomialSupportLEEquiv monoms).symm
          (f ∘ Sum.inl)).1 i) := by
  simp only [genericPolyMap, map_sum, map_mul, lift_of, support,
    mvPolynomialSupportLEEquiv, coeff, Finset.sum_filter, MvPolynomial.eval_eq,
    ne_eq, Function.comp, Equiv.coe_fn_symm_mk, Finsupp.coe_mk]
  conv_rhs => rw [← Finset.sum_attach]
  refine Finset.sum_congr rfl ?_
  intro m _
  simp only [Finsupp.prod, map_prod, map_pow, lift_of, Subtype.coe_eta, Finset.coe_mem,
    exists_prop, true_and, dite_eq_ite, ite_true, ite_not]
  split_ifs with h0 <;> simp_all

end Ring

end FirstOrder

