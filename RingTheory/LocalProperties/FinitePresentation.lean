/-
Copyright (c) 2026 Sihan Su. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sihan Su, Yongle Hu, Yi Song
-/
module

public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Finiteness

/-!
# `Module.FinitePresentation` is a local property

In this file, we prove that `Module.FinitePresentation` is a local property.

## Main results
* `Module.FinitePresentation.of_localizationSpan` : If there exists a set `{ r }` of `R` that
  generates the unit ideal and such that `Mᵣ` is a finitely presented `Rᵣ`-module for each `r`,
  then `M` is a finitely presented `R`-module.
-/

public section

variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] (s : Set R)

/-
**Module.FinitePresentation.of_localizationSpan'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.FinitePresentation.of_localizationSpan' (hs : Ideal.span s = ⊤) {Mₚ
 : forall (_ : s), Type*} [forall (g : s), AddCommGroup (Mₚ g)] [forall (g : s),
 Module R (Mₚ g)] {Rₚ : forall (_ : s), Type*} [forall (g : s), CommRing (Rₚ g)]
 [forall (g : s), Algebra R (Rₚ g)] [forall (g : s), IsLocalization.Away g.val (
Rₚ g)] [forall (g : s), Module (Rₚ g) (Mₚ g)] [forall (g : s), IsScalarTower R (
Rₚ g) (Mₚ g)] (ϕ : forall (g : s), M ->ₗ[R] Mₚ g) [forall (g : s), IsLocalizedMo
dule (Submonoid.powers g.v
参数：hs : Ideal.span s = ⊤；_ : s；g : s；Mₚ g；g : s；Mₚ g；_ : s；g : s；Rₚ g；g : s；Rₚ g
；g : s；Rₚ g；g : s；Rₚ g；Mₚ g；g : s；Rₚ g；Mₚ g；ϕ : forall (g : s), M ->ₗ[R] Mₚ g；g 
: s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.of_localizationSpan'`：of_localizationSpan' (t : Set R) (ht
 : Ideal.span t = ⊤) {Mₚ : forall (_ : t), Type*} [forall (g : t), AddCommMonoid
 (Mₚ g)] [forall (g : t)…
· 使用定理 `instFiniteOfFinitePresentation`：∀ (R : Type u_1) (M : Type u_2) [inst : 
Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [h : Modul
e.FinitePresentation…
· 使用引理 `Module.Finite.exists_fin'`：exists_fin' [Module.Finite R M] : exists (n :
 Nat) (f : (Fin n -> R) ->ₗ[R] M), Surjective f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.FinitePresentation.fg_ker_iff`：Module.FinitePresentation.fg_ker_i
ff [Module.FinitePresentation R M] (l : M ->ₗ[R] N) (hl : Function.Surjective l)
 : Submodule.FG (LinearMap…
· 使用定理 `instFinitePresentation`：∀ {R : Type u_1} [inst : Ring R], Module.FiniteP
resentation R R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Submodule.of_localizationSpan'`：∀ {R : Type u} [inst : CommSemiring R] {
M : Type v} [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : Submo
dule R M} (s : Set R…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.localized'_ker_eq_ker_localizedMap`：∀ {R : Type u_1} (S : Type
 u_2) {M : Type u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiri
ng S]   [inst_2 : AddCommMonoid M]…
· 使用引理 `Module.FinitePresentation.fg_ker`：Module.FinitePresentation.fg_ker [Modu
le.Finite R M] [h : Module.FinitePresentation R N] (l : M ->ₗ[R] N) (hl : Functi
on.Surjective l) : (Li…
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.localized'_range_eq_range_localizedMap`：∀ {R : Type u_1} (S : 
Type u_2) {M : Type u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSe
miring S]   [inst_2 : AddCommMonoid M]…
· 使用定理 `Submodule.localized'.congr_simp`：∀ {R : Type u_1} (S : Type u_2) {M : Ty
pe u_3} {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst
_2 : AddCommMonoid M]…
· 使用定理 `Submodule.localized'_top`：∀ {R : Type u_1} (S : Type u_2) {M : Type u_3}
 {N : Type u_4} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : Ad
dCommMonoid M]…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Module.FinitePresentation.of_localizationSpan' (hs : Ideal.span s = ⊤)
    {Mₚ : ∀ (_ : s), Type*} [∀ (g : s), AddCommGroup (Mₚ g)] [∀ (g : s), Module R (Mₚ g)]
    {Rₚ : ∀ (_ : s), Type*} [∀ (g : s), CommRing (Rₚ g)] [∀ (g : s), Algebra R (Rₚ g)]
    [∀ (g : s), IsLocalization.Away g.val (Rₚ g)]
    [∀ (g : s), Module (Rₚ g) (Mₚ g)] [∀ (g : s), IsScalarTower R (Rₚ g) (Mₚ g)]
    (ϕ : ∀ (g : s), M →ₗ[R] Mₚ g) [∀ (g : s), IsLocalizedModule (Submonoid.powers g.val) (ϕ g)]
    (h : ∀ (g : s), Module.FinitePresentation (Rₚ g) (Mₚ g)) :
    Module.FinitePresentation R M := by
  have : Module.Finite R M :=
    Module.Finite.of_localizationSpan' (Rₚ := Rₚ) s hs ϕ (fun _ ↦ inferInstance)
  obtain ⟨n, f, fsurj⟩ := Module.Finite.exists_fin' R M
  rw [← Module.FinitePresentation.fg_ker_iff f fsurj]
  refine f.ker.of_localizationSpan' s hs (Rₚ := Rₚ)
    (fun g ↦ TensorProduct.mk R (Rₚ g) (Fin n → R) 1) (fun g ↦ ?_)
  rw [LinearMap.localized'_ker_eq_ker_localizedMap (Rₚ g) (Submonoid.powers g.1) _ (ϕ g) f]
  apply Module.FinitePresentation.fg_ker
  rw [← LinearMap.range_eq_top] at fsurj ⊢
  simp [← LinearMap.localized'_range_eq_range_localizedMap (Rₚ g) (Submonoid.powers g.1), fsurj]

/-- If there exists a set `{ r }` of `R` that generates the unit ideal and such that
  `Mᵣ` is a finitely presented `Rᵣ`-module for each `r`, then `M` is a finitely presented
  `R`-module. -/
/-
**Module.FinitePresentation.of_localizationSpan** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.FinitePresentation.of_localizationSpan (hs : Ideal.span s = ⊤) (h :
 forall g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModul
e.Away g.1 M)) : Module.FinitePresentation R M
参数：hs : Ideal.span s = ⊤；h : forall g : s, Module.FinitePresentation (Localizati
on.Away g.1) (LocalizedModule.Away g.1 M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.FinitePresentation.of_localizationSpan'`：Module.FinitePresentatio
n.of_localizationSpan' (hs : Ideal.span s = ⊤) {Mₚ : forall (_ : s), Type*} [for
all (g : s), AddCommGroup (Mₚ g)] [f…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `OreLocalization.instIsScalarTower_1`：∀ {R : Type u_1} {M : Type u_3} {X 
: Type u_4} [inst : Monoid M] {S : Submonoid M} [inst_1 : OreLocalization.OreSet
 S]   [inst_2 : MulAction…

--- 原说明 ---
If there exists a set `{ r }` of `R` that generates the unit ideal and such that
  `Mᵣ` is a finitely presented `Rᵣ`-module for each `r`, then `M` is a finitely 
presented
  `R`-module.
-/
theorem Module.FinitePresentation.of_localizationSpan (hs : Ideal.span s = ⊤)
    (h : ∀ g : s, Module.FinitePresentation (Localization.Away g.1) (LocalizedModule.Away g.1 M)) :
    Module.FinitePresentation R M :=
  of_localizationSpan' s hs (fun g ↦ LocalizedModule.mkLinearMap (Submonoid.powers g.1) M) h
