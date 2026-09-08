/-
Copyright (c) 2025 Antoine Chambert-Loir, María-Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, Maria-Inés de Frutos-Fernandez
-/
module

public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.RingTheory.FiniteType
public import Mathlib.LinearAlgebra.DFinsupp
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Cardinality
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.Data.DFinsupp.Small

/-! # Smallness properties of modules and algebras -/

public section

universe u

namespace Submodule

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-
**Submodule.small_sup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：small_sup {P Q : Submodule R M} [smallP : Small.{u} P] [smallQ : Small.{u}
 Q] : Small.{u} (P ⊔ Q : Submodule R M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.sup_eq_range`：sup_eq_range (p q : Submodule R M) : p ⊔ q = ran
ge (p.subtype.coprod q.subtype)
-/
instance small_sup {P Q : Submodule R M} [smallP : Small.{u} P] [smallQ : Small.{u} Q] :
    Small.{u} (P ⊔ Q : Submodule R M) := by
  rw [Submodule.sup_eq_range]
  exact small_range _
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SemilatticeSup {P : Submodule R M // Small.{u} P} where
  sup := fun P Q ↦ ⟨P.val ⊔ Q.val, small_sup (smallP := P.property) (smallQ := Q.property)⟩
  le_sup_left := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_left
  le_sup_right := fun P Q ↦ by rw [← Subtype.coe_le_coe]; exact le_sup_right
  sup_le := fun _ _ _ hPR hQR ↦ by
    rw [← Subtype.coe_le_coe] at hPR hQR ⊢
    exact sup_le hPR hQR
/-
**Submodule.** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited {P : Submodule R M // Small.{u} P} where
  default := ⟨⊥, inferInstance⟩
/-
**Submodule.small_iSup** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：small_iSup {ι : Type*} {P : ι -> Submodule R M} [Small.{u} ι] [forall i, S
mall.{u} (P i)] : Small.{u} (iSup P : Submodule R M)
参数：P i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.iSup_eq_range_dfinsupp_lsum`：iSup_eq_range_dfinsupp_lsum (p : 
ι -> Submodule R N) : iSup p = LinearMap.range (DFinsupp.lsum Nat fun i => (p i)
.subtype)
-/
instance small_iSup
    {ι : Type*} {P : ι → Submodule R M} [Small.{u} ι] [∀ i, Small.{u} (P i)] :
    Small.{u} (iSup P : Submodule R M) := by
  classical
  rw [iSup_eq_range_dfinsupp_lsum]
  apply small_range
/-
**Submodule.FG.small** 是 Mathlib 中的一个定理，位于命名空间 `Submodule.FG`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [inst_1 : AddCommMonoi
d M] [inst_2 : _root_.Module R M]   [Small.{u, u_1} R] (P : Submodule R M), P.FG
 → Small.{u, u_2} ↥P
参数：P : Submodule R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.fg_iff_exists_fin_generating_family`：fg_iff_exists_fin_generat
ing_family {N : Submodule R M} : N.FG ↔ exists (n : Nat) (s : Fin n -> M), span 
R (range s) = N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.range_linearCombination`：Fintype.range_linearCombination : Linea
rMap.range (Fintype.linearCombination R v) = Submodule.span R (Set.range v)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
theorem FG.small [Small.{u} R] (P : Submodule R M) (hP : P.FG) : Small.{u} P := by
  rw [fg_iff_exists_fin_generating_family] at hP
  obtain ⟨n, s, rfl⟩ := hP
  rw [← Fintype.range_linearCombination]
  apply small_range

variable (R M) in
/-
**Submodule._root_.Module.Finite.small** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Module.Finite.small [Small.{u} R] [Module.Finite R M] : Small.{u} M := by
  have : Small.{u} (⊤ : Submodule R M) :=
    FG.small _ (Module.finite_def.mp inferInstance)
  rwa [← small_univ_iff]
/-
**Submodule.small_span_singleton** 是 Mathlib 中的一个实例，位于命名空间 `Submodule`。
形式化陈述：small_span_singleton [Small.{u} R] (m : M) : Small.{u} (span R {m})
参数：m : M。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.FG.small`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Small.{u, u_1} R] (P 
: Submod…
· 使用定理 `Submodule.fg_span_singleton`：fg_span_singleton (x : M) : FG (R ∙ x)
-/
instance small_span_singleton [Small.{u} R] (m : M) :
    Small.{u} (span R {m}) := FG.small _ (fg_span_singleton _)
/-
**Submodule.small_span** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：small_span [Small.{u} R] (s : Set M) [Small.{u} s] : Small.{u} (span R s)
参数：s : Set M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem small_span [Small.{u} R] (s : Set M) [Small.{u} s] :
    Small.{u} (span R s) := by
  suffices span R s = iSup (fun i : s ↦ span R ({(↑i : M)} : Set M)) by
    rw [this]
    apply small_iSup
  simp [← Submodule.span_iUnion]

end Submodule

variable {R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]

namespace Algebra

open MvPolynomial AlgHom

/-
**Algebra.small_adjoin** 是 Mathlib 中的一个实例，位于命名空间 `Algebra`。
形式化陈述：small_adjoin [Small.{u} R] {s : Set S} [Small.{u} s] : Small.{u} (adjoin R
 s : Subalgebra R S)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.adjoin_eq_range`：∀ (R : Type u) {S₁ : Type v} [inst : CommSemiri
ng R] [inst_1 : CommSemiring S₁] [inst_2 : Algebra R S₁] (s : Set S₁),   Algebra
.adjoin R s =…
· 使用定理 `MvPolynomial.instSmall`：∀ {σ : Type u_1} {R : Type u_2} [inst : CommSemi
ring R] [Small.{u, u_2} R] [Small.{u, u_1} σ],   Small.{u, max u_2 u_1} (MvPolyn
omial σ R)
-/
instance small_adjoin [Small.{u} R] {s : Set S} [Small.{u} s] :
    Small.{u} (adjoin R s : Subalgebra R S) := by
  rw [Algebra.adjoin_eq_range]
  apply small_range
/-
**Algebra._root_.Subalgebra.FG.small** 是 Mathlib 中的一个定理，位于命名空间 `Algebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Subalgebra.FG.small [Small.{u} R] {A : Subalgebra R S} (fgS : A.FG) :
    Small.{u} A := by
  obtain ⟨s, hs, rfl⟩ := fgS
  exact small_adjoin
/-
**Algebra.FiniteType.small** 是 Mathlib 中的一个定理，位于命名空间 `Algebra.FiniteType`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemiring R] [inst_1 : CommSemi
ring S] [inst_2 : Algebra R S]   [Small.{u, u_1} R] [Algebra.FiniteType R S], Sm
all.{u, u_2} S
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.FG.small`：∀ {R : Type u_1} {S : Type u_2} [inst : CommSemirin
g R] [inst_1 : CommSemiring S] [inst_2 : Algebra R S]   [Small.{u, u_1} R] {A : 
Subalgebr…
· 使用定理 `Algebra.FiniteType.out`：∀ {R : Type uR} {A : Type uA} {inst : CommSemiri
ng R} {inst_1 : Semiring A} {inst_2 : Algebra R A}   [self : Algebra.FiniteType 
R A], ⊤.FG
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `small_univ_iff`：small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α
-/
theorem FiniteType.small [Small.{u} R] [Algebra.FiniteType R S] :
    Small.{u} S := by
  have : Small.{u} (⊤ : Subalgebra R S) :=
    Subalgebra.FG.small Algebra.FiniteType.out
  rwa [← small_univ_iff]

end Algebra

