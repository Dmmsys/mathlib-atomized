/-
Copyright (c) 2022 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.RingTheory.Algebraic.Defs

/-!
# Cardinality of algebraic extensions

This file contains results on cardinality of algebraic extensions.
-/

public section


universe u v

open Cardinal Module
open scoped Polynomial

namespace Algebra.IsAlgebraic

variable (R : Type u) [CommRing R] [IsDomain R] (L : Type v) [CommRing L] [IsDomain L] [Algebra R L]
variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

/-
**Algebra.IsAlgebraic.lift_cardinalMk_le_sigma_polynomial** 是 Mathlib 中的一个定理，位于命
名空间 `Algebra.IsAlgebraic`。
形式化陈述：lift_cardinalMk_le_sigma_polynomial : lift.{u} #L <= #(Σ p : R[X], { x : L
 // x in p.aroots L })
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Cardinal.lift_mk_le_lift_mk_of_injective`：lift_mk_le_lift_mk_of_injectiv
e {α : Type u} {β : Type v} {f : α -> β} (hf : Injective f) : Cardinal.lift.{v} 
(#α) <= Cardinal.lift.{u} (#β)
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.map_ne_zero_iff`：∀ {R : Type u} {S : Type v} [inst : Semiring
 R] {p : Polynomial R} [inst_1 : Semiring S] {f : R →+* S},   Function.Injective
 ⇑f → (Polynomia…
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_roots`：mem_roots (hp : p != 0) : a in p.roots ↔ IsRoot p 
a
· 使用定理 `Polynomial.IsRoot.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polynomi
al R) (a : R), p.IsRoot a = (Polynomial.eval a p = 0)
· 使用定理 `Polynomial.eval_map`：eval_map (x : S) : (p.map f).eval x = p.eval₂ f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_def`：aeval_def (p : R[X]) : aeval x p = eval₂ (algebraM
ap R A) x p
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.heq_iff_coe_eq`：heq_iff_coe_eq (h : forall x, p x ↔ q x) {a1 : {
 x // p x }} {a2 : { x // q x }} : a1 ≍ a2 ↔ (a1 : α) = (a2 : α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aroots.congr_simp`：∀ {T : Type w} [inst : CommRing T] (p p_1 
: Polynomial T),   p = p_1 →     ∀ (S : Type u_1) [inst_1 : CommRing S] [inst_2 
: IsDomain S] [ins…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
-/
theorem lift_cardinalMk_le_sigma_polynomial :
    lift.{u} #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) := by
  have := @lift_mk_le_lift_mk_of_injective L (Σ p : R[X], {x : L | x ∈ p.aroots L})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      ⟨p.1, x, by
        dsimp
        have := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
        rw [Polynomial.mem_roots this, Polynomial.IsRoot, Polynomial.eval_map,
          ← Polynomial.aeval_def, p.2.2]⟩)
    fun x y => by
      intro h
      simp only [Set.coe_ofPred, ne_eq, Set.mem_ofPred_eq, Sigma.mk.inj_iff] at h
      refine (Subtype.heq_iff_coe_eq ?_).1 h.2
      simp only [h.1, forall_true_iff]
  rwa [lift_umax, lift_id'.{v}] at this
/-
**Algebra.IsAlgebraic.lift_cardinalMk_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.
IsAlgebraic`。
形式化陈述：lift_cardinalMk_le_max : lift.{u} #L <= lift.{v} #R ⊔ ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.lift_cardinalMk_le_sigma_polynomial`：lift_cardinalMk
_le_sigma_polynomial : lift.{u} #L <= #(Σ p : R[X], { x : L // x in p.aroots L }
)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `Cardinal.sum_le_sum`：sum_le_sum {ι} (f g : ι -> Cardinal) (H : forall i,
 f i <= g i) : sum f <= sum g
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.Finite.lt_aleph0`：∀ {α : Type u} {S : Set α}, S.Finite → Cardinal.mk
 ↑S < Cardinal.aleph0
· 使用定理 `Multiset.finite_toSet`：finite_toSet (s : Multiset α) : { x | x in s }.Fi
nite
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Cardinal.mul_le_max`：mul_le_max (a b : Cardinal) : a * b <= max (max a b
) ℵ₀
· 使用定理 `sup_le_sup`：sup_le_sup (h₁ : a <= b) (h₂ : c <= d) : a ⊔ c <= b ⊔ d
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Cardinal.lift_max`：lift_max {a b : Cardinal} : lift.{u, v} (max a b) = m
ax (lift.{u, v} a) (lift.{u, v} b)
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_cardinalMk_le_max : lift.{u} #L ≤ lift.{v} #R ⊔ ℵ₀ :=
  calc
    lift.{u} #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) :=
      lift_cardinalMk_le_sigma_polynomial R L
    _ = Cardinal.sum fun p : R[X] => #{x : L | x ∈ p.aroots L} := by
      rw [← mk_sigma]; rfl
    _ ≤ Cardinal.sum.{u, v} fun _ : R[X] => ℵ₀ :=
      (sum_le_sum _ _ fun _ => (Multiset.finite_toSet _).lt_aleph0.le)
    _ = lift.{v} #(R[X]) * ℵ₀ := by rw [sum_const, lift_aleph0]
    _ ≤ lift.{v} (#R ⊔ ℵ₀) ⊔ ℵ₀ ⊔ ℵ₀ := (mul_le_max _ _).trans <| by
      gcongr; simp only [lift_le, Polynomial.cardinalMk_le_max]
    _ = _ := by simp

variable (L : Type u) [CommRing L] [IsDomain L] [Algebra R L]
variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]
/-
**Algebra.IsAlgebraic.cardinalMk_le_sigma_polynomial** 是 Mathlib 中的一个定理，位于命名空间 `
Algebra.IsAlgebraic`。
形式化陈述：cardinalMk_le_sigma_polynomial : #L <= #(Σ p : R[X], { x : L // x in p.aro
ots L })
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Algebra.IsAlgebraic.lift_cardinalMk_le_sigma_polynomial`：lift_cardinalMk
_le_sigma_polynomial : lift.{u} #L <= #(Σ p : R[X], { x : L // x in p.aroots L }
)
-/
theorem cardinalMk_le_sigma_polynomial :
    #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) := by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L

/-- The cardinality of an algebraic extension is at most the maximum of the cardinality
of the base ring or `ℵ₀`. -/
@[stacks 09GK]
/-
**Algebra.IsAlgebraic.cardinalMk_le_max** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.IsAlg
ebraic`。
形式化陈述：cardinalMk_le_max : #L <= max #R ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Algebra.IsAlgebraic.lift_cardinalMk_le_max`：lift_cardinalMk_le_max : lif
t.{u} #L <= lift.{v} #R ⊔ ℵ₀

--- 原说明 ---
The cardinality of an algebraic extension is at most the maximum of the cardinal
ity
of the base ring or `ℵ₀`.
-/
theorem cardinalMk_le_max : #L ≤ max #R ℵ₀ := by
  simpa only [lift_id] using lift_cardinalMk_le_max R L

end Algebra.IsAlgebraic

