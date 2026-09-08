/-
Copyright (c) 2026 Yongle Hu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongle Hu
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.RingTheory.Finiteness.Small

/-!
# Stably free modules

## Main definition
* `IsStablyFree`: A module `M` over a ring `R` is called stably free if there exists a finite free
  `R`-module `N` such that `M ⊕ N` is free.
-/

public section

universe u v w

namespace Module

/-- A module `M` over a ring `R` is called stably free if there exists a finite free `R`-module `N`
such that `M ⊕ N` is free.

The underlying constructor is marked as private. The intended constructor of `IsStablyFree` is
`IsStablyFree.of_free_prod`, and use `IsStablyFree.exist_free_prod` to extract the property from
`IsStablyFree`. -/
@[stacks 0BC3 "(2)"]
/-
**Module.IsStablyFree** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → [inst : Ring R] → (M : Type u_1) → [inst_1 : AddCommGroup M
] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module `M` over a ring `R` is called stably free if there exists a finite free
 `R`-module `N`
such that `M ⊕ N` is free.

The underlying constructor is marked as private. The intended constructor of `Is
StablyFree` is
`IsStablyFree.of_free_prod`, and use `IsStablyFree.exist_free_prod` to extract t
he property from
`IsStablyFree`.
-/
class IsStablyFree (R : Type u) [Ring R] (M : Type*) [AddCommGroup M] [Module R M] : Prop where
  private exist_free_prod' : ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N)
    (_ : Module.Finite R N) (_ : Free R N), Free R (M × N)

variable (R : Type u) [Ring R] (M : Type v) [AddCommGroup M] [Module R M]
  (N : Type w) [AddCommGroup N] [Module R N]
/-
**Module.IsStablyFree.exist_free_prod** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStably
Free`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M]   [Module.IsStablyFree R M], ∃ N x x_1, ∃ (_ : Module.F
inite R N) (_ : Module.Free R N), Module.Free R (M × N)
参数：R : Type u；M : Type v；_ : Module.Finite R N；_ : Module.Free R N；M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Algebra.Module.StablyFree.Basic.0.Module.IsStablyFree.e
xist_free_prod'`：∀ {R : Type u} {inst : Ring R} {M : Type u_1} {inst_1 : AddComm
Group M} {inst_2 : _root_.Module R M}   [self : Module.IsStablyFree R M], ∃ N…
-/
theorem IsStablyFree.exist_free_prod [IsStablyFree R M] :
    ∃ (N : Type u) (_ : AddCommGroup N) (_ : Module R N) (_ : Module.Finite R N) (_ : Free R N),
      Free R (M × N) :=
  IsStablyFree.exist_free_prod'

variable {R M N} in
/-
**Module.IsStablyFree.equiv** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFree`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M : Type v} [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M] {N : Type w}   [inst_3 : AddCommGroup N] [inst_4 : _roo
t_.Module R N] (e : M ≃ₗ[R] N) [Module.IsStablyFree R M],   Module.IsStablyFree 
R N
参数：e : M ≃ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsStablyFree.exist_free_prod`：∀ (R : Type u) [inst : Ring R] (M :
 Type v) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [Module.IsStab
lyFree R M], ∃ N x x_1, ∃…
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
-/
theorem IsStablyFree.equiv (e : M ≃ₗ[R] N) [IsStablyFree R M] : IsStablyFree R N := by
  obtain ⟨P, hPc, hPm, hPfin, hPfree, _⟩ := IsStablyFree.exist_free_prod R M
  exact ⟨P, hPc, hPm, hPfin, hPfree, Free.of_equiv (e.prodCongr (LinearEquiv.refl R P))⟩

variable {R M N} in
/-
**Module.IsStablyFree.equiv_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFree`。
形式化陈述：∀ {R : Type u} [inst : Ring R] {M : Type v} [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M] {N : Type w}   [inst_3 : AddCommGroup N] [inst_4 : _roo
t_.Module R N] (e : M ≃ₗ[R] N),   Module.IsStablyFree R M ↔ Module.IsStablyFree 
R N
参数：e : M ≃ₗ[R] N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsStablyFree.equiv`：∀ {R : Type u} [inst : Ring R] {M : Type v} [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {N : Type w}   [inst_3 : A
ddCommGroup N] …
-/
theorem IsStablyFree.equiv_iff (e : M ≃ₗ[R] N) : IsStablyFree R M ↔ IsStablyFree R N :=
  ⟨fun h ↦ h.equiv e, fun h ↦ h.equiv e.symm⟩
/-
**Module.IsStablyFree.ulift** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFree`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M]   [Module.IsStablyFree R M], Module.IsStablyFree R (ULi
ft.{w, v} M)
参数：R : Type u；M : Type v；ULift.{w, v} M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsStablyFree.equiv`：∀ {R : Type u} [inst : Ring R] {M : Type v} [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {N : Type w}   [inst_3 : A
ddCommGroup N] …
-/
instance IsStablyFree.ulift [IsStablyFree R M] : IsStablyFree R (ULift.{w} M) :=
  IsStablyFree.equiv ULift.moduleEquiv.symm
/-
**Module.IsStablyFree.of_ulift** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFree`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M]   [Module.IsStablyFree R (ULift.{w, v} M)], Module.IsSt
ablyFree R M
参数：R : Type u；M : Type v；ULift.{w, v} M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsStablyFree.equiv`：∀ {R : Type u} [inst : Ring R] {M : Type v} [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {N : Type w}   [inst_3 : A
ddCommGroup N] …
-/
theorem IsStablyFree.of_ulift [IsStablyFree R (ULift.{w} M)] : IsStablyFree R M :=
  IsStablyFree.equiv ULift.moduleEquiv
/-
**Module.IsStablyFree.shrink** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFree`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M]   [inst_3 : Small.{w, v} M] [Module.IsStablyFree R M], 
Module.IsStablyFree R (Shrink.{w, v} M)
参数：R : Type u；M : Type v；Shrink.{w, v} M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsStablyFree.equiv`：∀ {R : Type u} [inst : Ring R] {M : Type v} [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {N : Type w}   [inst_3 : A
ddCommGroup N] …
-/
instance IsStablyFree.shrink [Small.{w, v} M] [IsStablyFree R M] : IsStablyFree R (Shrink.{w} M) :=
  IsStablyFree.equiv (Shrink.linearEquiv R M).symm
/-
**Module.IsStablyFree.of_shrink** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFree`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M]   [inst_3 : Small.{w, v} M] [Module.IsStablyFree R (Shr
ink.{w, v} M)], Module.IsStablyFree R M
参数：R : Type u；M : Type v；Shrink.{w, v} M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsStablyFree.equiv`：∀ {R : Type u} [inst : Ring R] {M : Type v} [
inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {N : Type w}   [inst_3 : A
ddCommGroup N] …
-/
theorem IsStablyFree.of_shrink [Small.{w, v} M] [IsStablyFree R (Shrink.{w} M)] :
    IsStablyFree R M :=
  IsStablyFree.equiv (Shrink.linearEquiv R M)
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Free R M] : IsStablyFree R M :=
  ⟨PUnit, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
/-
**Module.IsStablyFree.of_free_prod** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFre
e`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M] (N : Type w)   [inst_3 : AddCommGroup N] [inst_4 : _roo
t_.Module R N] [Module.Finite R N] [Module.Free R N] [Module.Free R (M × N)],   
Module.IsStablyFree R M
参数：R : Type u；M : Type v；N : Type w；M × N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Finite.small`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Small.{u, u_1} R] [M
odule.Fin…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
-/
theorem IsStablyFree.of_free_prod [Module.Finite R N] [Free R N] [Free R (M × N)] :
    IsStablyFree R M :=
  have : Small.{u} N := Module.Finite.small.{u} R N
  let +nondep eN : N ≃ₗ[R] Shrink.{u} N := (Shrink.linearEquiv R N).symm
  ⟨Shrink.{u} N, inferInstance, inferInstance, Module.Finite.equiv eN,
    Free.of_equiv eN, Free.of_equiv ((LinearEquiv.refl R M).prodCongr eN)⟩
/-
**Module.IsStablyFree.of_free_prod'** 是 Mathlib 中的一个定理，位于命名空间 `Module.IsStablyFr
ee`。
形式化陈述：∀ (R : Type u) [inst : Ring R] (M : Type v) [inst_1 : AddCommGroup M] [ins
t_2 : _root_.Module R M] (N : Type w)   [inst_3 : AddCommGroup N] [inst_4 : _roo
t_.Module R N] [Module.Finite R N] [Module.Free R N] [Module.Free R (N × M)],   
Module.IsStablyFree R M
参数：R : Type u；M : Type v；N : Type w；N × M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `Module.IsStablyFree.of_free_prod`：∀ (R : Type u) [inst : Ring R] (M : Ty
pe v) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] (N : Type w)   [ins
t_3 : AddCommGroup N] …
-/
theorem IsStablyFree.of_free_prod' [Module.Finite R N] [Free R N] [Free R (N × M)] :
    IsStablyFree R M :=
  have : Free R (M × N) := Free.of_equiv (LinearEquiv.prodComm R N M)
  .of_free_prod R M N
/-
**Module.** 是 Mathlib 中的一个实例，位于命名空间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsStablyFree R M] : Projective R M := by
  obtain ⟨N, _, _, _, _, _⟩ := IsStablyFree.exist_free_prod R M
  exact Projective.of_split (LinearMap.inl R M N) (LinearMap.fst R M N) (LinearMap.ext fun _ ↦ rfl)

end Module

