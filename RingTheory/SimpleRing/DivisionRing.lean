/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edison Xie
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Simple
public import Mathlib.RingTheory.SimpleModule.Basic

/-!

## Simple modules over division rings
This file contains some results about simple modules over division rings.

# Main results

* `DivisionRing.nonempty_linearEquiv_of_isSimpleModule` : There is an unique simple module over
  a division ring, up to isomorphism.
* `isSimpleModule_iff_eq_zero_or_injective` : A module is simple if and only if it is nontrivial
  and every linear map from it is either zero or injective, this is the module analogue of
  `RingHom.injective`
* `IsSimpleModule.obj_of_isEquivalence` : If `M` is a simple module over a ring `R`, and
  `e : ModuleCat R ⥤ ModuleCat S` is an equivalence of categories,
  then `e(M)` is a simple module over `S`.

## Tags
Noncommutative algebra, simple module, division ring

-/

@[expose] public section

universe u v

open CategoryTheory

variable (R S : Type*) [DivisionRing R] [DivisionRing S] (e : ModuleCat R ≌ ModuleCat S)

/-
**DivisionRing.nonempty_linearEquiv_of_isSimpleModule** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：DivisionRing.nonempty_linearEquiv_of_isSimpleModule (N : Type*) [AddCommGr
oup N] [Module S N] [IsSimpleModule S N] : Nonempty (N ≃ₗ[S] S)
参数：N : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isSimpleModule_iff_quot_maximal`：isSimpleModule_iff_quot_maximal : IsSim
pleModule R M ↔ exists I : Ideal R, I.IsMaximal ∧ Nonempty (M ≃ₗ[R] R ⧸ I)
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
-/
lemma DivisionRing.nonempty_linearEquiv_of_isSimpleModule (N : Type*) [AddCommGroup N]
    [Module S N] [IsSimpleModule S N] : Nonempty (N ≃ₗ[S] S) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹_›
  exact ⟨e ≪≫ₗ I.quotEquivOfEqBot ((eq_bot_or_eq_top I).resolve_right hI.ne_top)⟩
/-
**isSimpleModule_iff_eq_zero_or_injective** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isSimpleModule_iff_eq_zero_or_injective (R : Type u) (M : Type v) [Ring R]
 [AddCommGroup M] [Module R M] : IsSimpleModule R M ↔ (Nontrivial M ∧ forall (N 
: Type v) [AddCommGroup N] [Module R N] (f : M ->ₗ[R] N), f = 0 ∨ Function.Injec
tive f)
参数：R : Type u；M : Type v。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.nontrivial_iff`：nontrivial_iff : Nontrivial (Submodule R M) ↔ 
Nontrivial M
· 使用定理 `IsSimpleOrder.toNontrivial`：∀ {α : Type u_4} {inst : LE α} {inst_1 : Bou
ndedOrder α} [self : IsSimpleOrder α], Nontrivial α
· 使用定理 `IsSimpleModule.toIsSimpleOrder`：∀ {R : Type u_2} {inst : Ring R} {M : Ty
pe u_4} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : IsSimpl
eModule R M], IsSimp…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsSimpleOrder.eq_bot_or_eq_top`：∀ {α : Type u_4} {inst : LE α} {inst_1 :
 BoundedOrder α} [self : IsSimpleOrder α] (a : α), a = ⊥ ∨ a = ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isSimpleModule_iff`：∀ (R : Type u_2) [inst : Ring R] (M : Type u_4) [ins
t_1 : AddCommGroup M] [inst_2 : _root_.Module R M],   IsSimpleModule R M ↔ IsSim
pleOrder…
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
lemma isSimpleModule_iff_eq_zero_or_injective (R : Type u) (M : Type v) [Ring R] [AddCommGroup M]
    [Module R M] : IsSimpleModule R M ↔ (Nontrivial M ∧ ∀ (N : Type v) [AddCommGroup N]
    [Module R N] (f : M →ₗ[R] N), f = 0 ∨ Function.Injective f) :=
  ⟨fun hM ↦ ⟨Submodule.nontrivial_iff _|>.1 hM.1.1, fun N _ _ f ↦ hM.1.2 (LinearMap.ker f)|>.elim
    (fun h ↦ Or.inr <| by rwa [LinearMap.ker_eq_bot] at h) (fun h ↦ Or.inl <|by simp_all)⟩,
  fun ⟨hM1, hM2⟩ ↦ isSimpleModule_iff R M|>.2 ⟨fun p ↦ (hM2 (M ⧸ p) p.mkQ).elim
  (fun h ↦ Or.inr <| by simpa [Submodule.ext_iff, LinearMap.ext_iff] using h)
  (fun h ↦ Or.inl <| eq_bot_iff.2 fun x hx ↦ h (by simp [hx]))⟩⟩
/-
**IsSimpleModule.obj_of_isEquivalence** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSimpleModule.obj_of_isEquivalence {R S : Type*} [Ring R] [Ring S] (e : M
oduleCat R ⥤ ModuleCat S) [e.IsEquivalence] (M : ModuleCat R) [IsSimpleModule R 
M] : IsSimpleModule S (e.obj M)
参数：e : ModuleCat R ⥤ ModuleCat S；M : ModuleCat R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `simple_iff_isSimpleModule'`：simple_iff_isSimpleModule' (M : ModuleCat R)
 : Simple M ↔ IsSimpleModule R M
· 使用定理 `CategoryTheory.simple_obj`：simple_obj {D : Type*} [Category* D] [HasZero
Morphisms D] (F : C ⥤ D) [F.IsEquivalence] (X : C) [Simple X] : Simple (F.obj X)
-/
lemma IsSimpleModule.obj_of_isEquivalence
    {R S : Type*} [Ring R] [Ring S] (e : ModuleCat R ⥤ ModuleCat S)
    [e.IsEquivalence] (M : ModuleCat R) [IsSimpleModule R M] :
    IsSimpleModule S (e.obj M) := by
  rw [← simple_iff_isSimpleModule'] at *
  exact simple_obj e M
