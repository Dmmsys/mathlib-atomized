/-
Copyright (c) 2025 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.SimpleRing.Basic
public import Mathlib.RingTheory.TwoSidedIdeal.Operations

/-!
# Simplicity is preserved by ring isomorphisms/surjective ring homomorphisms

If `R` is a simple (non-assoc) ring and there exists surjective `f : R →+* S` where `S` is
nontrivial, then `S` is also simple.
If `R` is a simple (non-unital non-assoc) ring then any ring isomorphic to `R` is also simple.
-/

public section

namespace IsSimpleRing

/-
**IsSimpleRing.of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpleRing`。
形式化陈述：of_surjective {R S : Type*} [NonAssocRing R] [NonAssocRing S] [Nontrivial 
S] (f : R ->+* S) (h : IsSimpleRing R) (hf : Function.Surjective f) : IsSimpleRi
ng S where simple
参数：f : R ->+* S；h : IsSimpleRing R；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isSimpleOrder`：isSimpleOrder [BoundedOrder α] [BoundedOrder β] 
[h : IsSimpleOrder β] (f : α ≃o β) : IsSimpleOrder α
· 使用定理 `IsSimpleRing.simple`：∀ {R : Type u_1} {inst : NonUnitalNonAssocRing R} [
self : IsSimpleRing R], IsSimpleOrder (TwoSidedIdeal R)
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
-/
lemma of_surjective {R S : Type*} [NonAssocRing R] [NonAssocRing S] [Nontrivial S]
    (f : R →+* S) (h : IsSimpleRing R) (hf : Function.Surjective f) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder (RingEquiv.ofBijective f
    ⟨RingHom.injective f, hf⟩).symm.mapTwoSidedIdeal
/-
**IsSimpleRing.of_ringEquiv** 是 Mathlib 中的一个引理，位于命名空间 `IsSimpleRing`。
形式化陈述：of_ringEquiv {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRin
g S] (f : R ≃+* S) (h : IsSimpleRing R) : IsSimpleRing S where simple
参数：f : R ≃+* S；h : IsSimpleRing R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderIso.isSimpleOrder`：isSimpleOrder [BoundedOrder α] [BoundedOrder β] 
[h : IsSimpleOrder β] (f : α ≃o β) : IsSimpleOrder α
· 使用定理 `IsSimpleRing.simple`：∀ {R : Type u_1} {inst : NonUnitalNonAssocRing R} [
self : IsSimpleRing R], IsSimpleOrder (TwoSidedIdeal R)
-/
lemma of_ringEquiv {R S : Type*} [NonUnitalNonAssocRing R] [NonUnitalNonAssocRing S]
    (f : R ≃+* S) (h : IsSimpleRing R) : IsSimpleRing S where
  simple := OrderIso.isSimpleOrder f.symm.mapTwoSidedIdeal

end IsSimpleRing

open TwoSidedIdeal in
/-
**isSimpleRing_iff_isTwoSided_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSimpleRing_iff_isTwoSided_imp {R : Type*} [Ring R] : IsSimpleRing R ↔ No
ntrivial R ∧ forall I : Ideal R, I.IsTwoSided -> I = ⊥ ∨ I = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.nontrivial_congr`：nontrivial_congr {α β} (e : α ≃ β) : Nontrivial 
α ↔ Nontrivial β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `OrderIso.injective`：∀ {α : Type u_2} {β : Type u_3} [inst : LE α] [inst_
1 : LE β] (e : α ≃o β), Function.Injective ⇑e
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderIso.apply_symm_apply`：apply_symm_apply (e : α ≃o β) (x : β) : e (e.
symm x) = x
· 使用定理 `TwoSidedIdeal.orderIsoIsTwoSided_apply_coe`：∀ {R : Type u_1} [inst : Rin
g R] (I : TwoSidedIdeal R), ↑(TwoSidedIdeal.orderIsoIsTwoSided I) = TwoSidedIdea
l.asIdeal I
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isSimpleRing_iff_isTwoSided_imp {R : Type*} [Ring R] :
    IsSimpleRing R ↔ Nontrivial R ∧ ∀ I : Ideal R, I.IsTwoSided → I = ⊥ ∨ I = ⊤ := by
  let e := orderIsoIsTwoSided (R := R)
  simp_rw [isSimpleRing_iff, isSimpleOrder_iff, orderIsoRingCon.toEquiv.nontrivial_congr,
    RingCon.nontrivial_iff, e.forall_congr_left, Subtype.forall, ← e.injective.eq_iff]
  simp [e, Subtype.ext_iff]
