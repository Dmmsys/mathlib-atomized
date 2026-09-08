/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.Module.Submodule.Bilinear

/-!
# Finitely generated submodules and bilinear maps

-/

public section

open Function (Surjective)

namespace Submodule

section Map₂

variable {R M N P : Type*}
variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
variable [Module R M] [Module R N] [Module R P]

/-
**Submodule.FG.map** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type u_4} [inst_3 : Semi
ring S] [inst_4 : AddCommMonoid P] [inst_5 : _root_.Module S P]   {σ : R →+* S} 
[inst_6 : RingHomSurjective σ] (f : M →ₛₗ[σ] P) {N : Submodule R M}, N.FG → (Sub
module.map f N).FG
参数：f : M →ₛₗ[σ] P；Submodule.map f N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_image`：span_image [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂
] M₂) : span R₂ (f '' s) = map f (span R s)
-/
theorem FG.map₂ (f : M →ₗ[R] N →ₗ[R] P) {p : Submodule R M} {q : Submodule R N} (hp : p.FG)
    (hq : q.FG) : (map₂ f p q).FG :=
  let ⟨sm, hfm, hm⟩ := fg_def.1 hp
  let ⟨sn, hfn, hn⟩ := fg_def.1 hq
  fg_def.2
    ⟨Set.image2 (fun m n => f m n) sm sn, hfm.image2 _ hfn,
      map₂_span_span R f sm sn ▸ hm ▸ hn ▸ rfl⟩

end Map₂

end Submodule

