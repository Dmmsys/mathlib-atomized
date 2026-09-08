/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Deepro Choudhury
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Module.Equiv.Basic

/-!

# Additional results about finite spanning sets in linear algebra

-/

public section

open Set Function
open Submodule (span)

set_option backward.isDefEq.respectTransparency false in
/-- A linear equivalence which preserves a finite spanning set must have finite order. -/
/-
**LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo** 是 Mathlib 中的一个引理
，位于命名空间 ``。
形式化陈述：LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo {R M : Type*} 
[Semiring R] [AddCommMonoid M] [Module R M] {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : 
span R Φ = ⊤) {e : M ≃ₗ[R] M} (he : MapsTo e Φ Φ) : IsOfFinOrder e
参数：hΦ₁ : Φ.Finite；hΦ₂ : span R Φ = ⊤；he : MapsTo e Φ Φ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.Finite.injOn_iff_bijOn_of_mapsTo`：∀ {α : Type u} {s : Set α} {f : α 
→ α}, s.Finite → Set.MapsTo f s s → (Set.InjOn f s ↔ Set.BijOn f s s)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用引理 `isOfFinOrder_of_finite`：isOfFinOrder_of_finite (x : G) : IsOfFinOrder x
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `mul_left_iterate`：∀ {M : Type u_4} [inst : Monoid M] (a : M) (n : ℕ), (f
un x => a * x)^[n] = fun x => a ^ n * x
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `LinearEquiv.pow_apply`：pow_apply (e : M ≃ₗ[R] M) (n : Nat) (m : M) : (e 
^ n) m = e^[n] m
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.MapsTo.coe_iterate_restrict`：∀ {α : Type u_1} {s : Set α} {f : α → α
} (h : Set.MapsTo f s s) (x : ↑s) (k : ℕ),   ↑((Set.MapsTo.restrict f s s h)^[k]
 x) = f^[k] ↑x
· 使用定理 `Equiv.congr_fun`：∀ {α : Sort u} {β : Sort v} {f g : α ≃ β}, f = g → ∀ (x
 : α), f x = g x
· 使用定理 `Equiv.Perm.coe_pow`：∀ {α : Type u_4} (f : Equiv.Perm α) (n : ℕ), ⇑(f ^ n
) = (⇑f)^[n]
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `Equiv.Perm.coe_one`：∀ {α : Type u_4}, ⇑1 = id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A linear equivalence which preserves a finite spanning set must have finite orde
r.
-/
lemma LinearEquiv.isOfFinOrder_of_finite_of_span_eq_top_of_mapsTo
    {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {Φ : Set M} (hΦ₁ : Φ.Finite) (hΦ₂ : span R Φ = ⊤) {e : M ≃ₗ[R] M} (he : MapsTo e Φ Φ) :
    IsOfFinOrder e := by
  replace he : BijOn e Φ Φ := (hΦ₁.injOn_iff_bijOn_of_mapsTo he).mp e.injective.injOn
  let e' := he.equiv
  have : Finite Φ := finite_coe_iff.mpr hΦ₁
  obtain ⟨k, hk₀, hk⟩ := isOfFinOrder_of_finite e'
  refine ⟨k, hk₀, ?_⟩
  ext m
  have hm : m ∈ span R Φ := hΦ₂ ▸ Submodule.mem_top
  simp only [mul_left_iterate, mul_one, LinearEquiv.coe_one, id_eq]
  refine Submodule.span_induction (fun x hx ↦ ?_) (by simp)
    (fun x y _ _ hx hy ↦ by simp [map_add, hx, hy]) (fun t x _ hx ↦ by simp [hx]) hm
  rw [LinearEquiv.pow_apply, ← he.1.coe_iterate_restrict ⟨x, hx⟩ k]
  replace hk : (e') ^ k = 1 := by simpa [IsPeriodicPt, IsFixedPt] using hk
  replace hk := Equiv.congr_fun hk ⟨x, hx⟩
  rwa [Equiv.Perm.coe_one, id_eq, Subtype.ext_iff, Equiv.Perm.coe_pow] at hk
