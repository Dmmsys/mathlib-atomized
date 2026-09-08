/-
Copyright (c) 2020 Alexander Bentkamp. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Bentkamp
-/
module

public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.GeneralLinearGroup.Basic
public import Mathlib.RingTheory.Nilpotent.Basic
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.Tactic.Peel

/-!
# Eigenvectors and eigenvalues

This file defines eigenspaces, eigenvalues, and eigenvectors, as well as their generalized
counterparts. We follow Axler's approach [axler2024] because it allows us to derive many properties
without choosing a basis and without using matrices.

An eigenspace of a linear map `f` for a scalar `μ` is the kernel of the map `(f - μ • id)`. The
nonzero elements of an eigenspace are eigenvectors `x`. They have the property `f x = μ • x`. If
there are eigenvectors for a scalar `μ`, the scalar `μ` is called an eigenvalue.

There is no consensus in the literature whether `0` is an eigenvector. Our definition of
`HasEigenvector` permits only nonzero vectors. For an eigenvector `x` that may also be `0`, we
write `x ∈ f.eigenspace μ`.

A generalized eigenspace of a linear map `f` for a natural number `k` and a scalar `μ` is the kernel
of the map `(f - μ • id) ^ k`. The nonzero elements of a generalized eigenspace are generalized
eigenvectors `x`. If there are generalized eigenvectors for a natural number `k` and a scalar `μ`,
the scalar `μ` is called a generalized eigenvalue.

The fact that the eigenvalues are the roots of the minimal polynomial is proved in
`LinearAlgebra.Eigenspace.Minpoly`.

The existence of eigenvalues over an algebraically closed field
(and the fact that the generalized eigenspaces then span) is deferred to
`LinearAlgebra.Eigenspace.IsAlgClosed`.

## References

* [Sheldon Axler, *Linear Algebra Done Right*][axler2024]
* https://en.wikipedia.org/wiki/Eigenvalues_and_eigenvectors

## Tags

eigenspace, eigenvector, eigenvalue, eigen
-/

@[expose] public section


universe u v w

namespace Module

namespace End

open Module Set

variable {K R : Type v} {V M : Type w} [CommRing R] [AddCommGroup M] [Module R M] [Field K]
  [AddCommGroup V] [Module K V]

/-- The submodule `genEigenspace f μ k` for a linear map `f`, a scalar `μ`,
and a number `k : ℕ∞` is the kernel of `(f - μ • id) ^ k` if `k` is a natural number,
or the union of all these kernels if `k = ∞`. (`k = ∞` corresponds to Def 8.19 of [axler2024].)
A generalized eigenspace for some exponent `k` is contained in
the generalized eigenspace for exponents larger than `k`. -/
/-
**Module.End.genEigenspace** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：genEigenspace (f : End R M) (μ : R) : Nat∞ ->o Submodule R M where toFun k
参数：f : End R M；μ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule `genEigenspace f μ k` for a linear map `f`, a scalar `μ`,
and a number `k : ℕ∞` is the kernel of `(f - μ • id) ^ k` if `k` is a natural nu
mber,
or the union of all these kernels if `k = ∞`. (`k = ∞` corresponds to Def 8.19 o
f [axler2024].)
A generalized eigenspace for some exponent `k` is contained in
the generalized eigenspace for exponents larger than `k`.
-/
def genEigenspace (f : End R M) (μ : R) : ℕ∞ →o Submodule R M where
  toFun k := ⨆ l : ℕ, ⨆ _ : l ≤ k, LinearMap.ker ((f - μ • 1) ^ l)
  monotone' _ _ hkl := biSup_mono fun _ hi ↦ hi.trans hkl

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.mem_genEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：mem_genEigenspace {f : End R M} {μ : R} {k : Nat∞} {x : M} : x in f.genEig
enspace μ k ↔ exists l : Nat, l <= k ∧ x in LinearMap.ker ((f - μ • 1) ^ l)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.iterateKer_coe`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : M →ₗ[R] M) 
(n : ℕ), f.ite…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `Submodule.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [Nonempty ι] (S
 : ι -> Submodule R M) (H : Directed (· <= ·) S) {x} : x in iSup S ↔ exists i, x
 in S i
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_genEigenspace {f : End R M} {μ : R} {k : ℕ∞} {x : M} :
    x ∈ f.genEigenspace μ k ↔ ∃ l : ℕ, l ≤ k ∧ x ∈ LinearMap.ker ((f - μ • 1) ^ l) := by
  have : Nonempty {l : ℕ // l ≤ k} := ⟨⟨0, zero_le⟩⟩
  have : Directed (ι := { i : ℕ // i ≤ k }) (· ≤ ·) fun i ↦ LinearMap.ker ((f - μ • 1) ^ (i : ℕ)) :=
    Monotone.directed_le fun m n h ↦ by simpa using (f - μ • 1).iterateKer.monotone h
  simp_rw [genEigenspace, OrderHom.coe_mk, LinearMap.mem_ker, iSup_subtype',
    Submodule.mem_iSup_of_directed _ this, LinearMap.mem_ker, Subtype.exists, exists_prop]
/-
**Module.End.genEigenspace_directed** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_directed {f : End R M} {μ : R} {k : Nat∞} : Directed (· <= ·
) (fun l : {l : Nat // l <= k} => f.genEigenspace μ l)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `Monotone.directed_le`：Monotone.directed_le [Preorder α] [IsDirectedOrder
 α] [Preorder β] {f : α -> β} : Monotone f -> Directed (· <= ·) f
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Monotone.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preorder
 α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Monot
one…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
-/
lemma genEigenspace_directed {f : End R M} {μ : R} {k : ℕ∞} :
    Directed (· ≤ ·) (fun l : {l : ℕ // l ≤ k} ↦ f.genEigenspace μ l) := by
  have aux : Monotone ((↑) : {l : ℕ // l ≤ k} → ℕ∞) := fun x y h ↦ by simpa using h
  exact ((genEigenspace f μ).monotone.comp aux).directed_le
/-
**Module.End.mem_genEigenspace_nat** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：mem_genEigenspace_nat {f : End R M} {μ : R} {k : Nat} {x : M} : x in f.gen
Eigenspace μ k ↔ x in LinearMap.ker ((f - μ • 1) ^ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.mem_genEigenspace`：mem_genEigenspace {f : End R M} {μ : R} {k
 : Nat∞} {x : M} : x in f.genEigenspace μ k ↔ exists l : Nat, l <= k ∧ x in Line
arMap.ker ((f - μ …
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
lemma mem_genEigenspace_nat {f : End R M} {μ : R} {k : ℕ} {x : M} :
    x ∈ f.genEigenspace μ k ↔ x ∈ LinearMap.ker ((f - μ • 1) ^ k) := by
  rw [mem_genEigenspace]
  constructor
  · rintro ⟨l, hl, hx⟩
    simp only [Nat.cast_le] at hl
    exact (f - μ • 1).iterateKer.monotone hl hx
  · intro hx
    exact ⟨k, le_rfl, hx⟩
/-
**Module.End.mem_genEigenspace_top** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：mem_genEigenspace_top {f : End R M} {μ : R} {x : M} : x in f.genEigenspace
 μ ⊤ ↔ exists k : Nat, x in LinearMap.ker ((f - μ • 1) ^ k)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_genEigenspace_top {f : End R M} {μ : R} {x : M} :
    x ∈ f.genEigenspace μ ⊤ ↔ ∃ k : ℕ, x ∈ LinearMap.ker ((f - μ • 1) ^ k) := by
  simp [mem_genEigenspace]
/-
**Module.End.genEigenspace_nat** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_nat {f : End R M} {μ : R} {k : Nat} : f.genEigenspace μ k = 
LinearMap.ker ((f - μ • 1) ^ k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma genEigenspace_nat {f : End R M} {μ : R} {k : ℕ} :
    f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k) := by
  ext; simp [mem_genEigenspace_nat]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.genEigenspace_eq_iSup_genEigenspace_nat** 是 Mathlib 中的一个引理，位于命名空间 `
Module.End`。
形式化陈述：genEigenspace_eq_iSup_genEigenspace_nat (f : End R M) (μ : R) (k : Nat∞) :
 f.genEigenspace μ k = ⨆ l : {l : Nat // l <= k}, f.genEigenspace μ l
参数：f : End R M；μ : R；k : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma genEigenspace_eq_iSup_genEigenspace_nat (f : End R M) (μ : R) (k : ℕ∞) :
    f.genEigenspace μ k = ⨆ l : {l : ℕ // l ≤ k}, f.genEigenspace μ l := by
  simp_rw [genEigenspace_nat, genEigenspace, OrderHom.coe_mk, iSup_subtype]
/-
**Module.End.genEigenspace_top** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_top (f : End R M) (μ : R) : f.genEigenspace μ ⊤ = ⨆ k : Nat,
 f.genEigenspace μ k
参数：f : End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_eq_iSup_genEigenspace_nat`：genEigenspace_eq_iSu
p_genEigenspace_nat (f : End R M) (μ : R) (k : Nat∞) : f.genEigenspace μ k = ⨆ l
 : {l : Nat // l <= k}, f.genEigenspace …
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma genEigenspace_top (f : End R M) (μ : R) :
    f.genEigenspace μ ⊤ = ⨆ k : ℕ, f.genEigenspace μ k := by
  rw [genEigenspace_eq_iSup_genEigenspace_nat, iSup_subtype]
  simp only [le_top, iSup_pos]
/-
**Module.End.genEigenspace_one** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_one {f : End R M} {μ : R} : f.genEigenspace μ 1 = LinearMap.
ker (f - μ • 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
lemma genEigenspace_one {f : End R M} {μ : R} :
    f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1) := by
  rw [← Nat.cast_one, genEigenspace_nat, pow_one]

@[simp]
/-
**Module.End.mem_genEigenspace_one** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：mem_genEigenspace_one {f : End R M} {μ : R} {x : M} : x in f.genEigenspace
 μ 1 ↔ f x = μ • x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_one`：genEigenspace_one {f : End R M} {μ : R} : 
f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1)
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `Module.End.one_apply`：one_apply (x : M) : (1 : Module.End R M) x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_genEigenspace_one {f : End R M} {μ : R} {x : M} :
    x ∈ f.genEigenspace μ 1 ↔ f x = μ • x := by
  rw [genEigenspace_one, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, LinearMap.smul_apply, Module.End.one_apply]

-- `simp` can prove this using `genEigenspace_zero`
/-
**Module.End.mem_genEigenspace_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：mem_genEigenspace_zero {f : End R M} {μ : R} {x : M} : x in f.genEigenspac
e μ 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Module.End.mem_genEigenspace_nat`：mem_genEigenspace_nat {f : End R M} {μ
 : R} {k : Nat} {x : M} : x in f.genEigenspace μ k ↔ x in LinearMap.ker ((f - μ 
• 1) ^ k)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `Module.End.one_apply`：one_apply (x : M) : (1 : Module.End R M) x = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_genEigenspace_zero {f : End R M} {μ : R} {x : M} :
    x ∈ f.genEigenspace μ 0 ↔ x = 0 := by
  rw [← Nat.cast_zero, mem_genEigenspace_nat, pow_zero, LinearMap.mem_ker, Module.End.one_apply]

@[simp]
/-
**Module.End.genEigenspace_zero** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_zero {f : End R M} {μ : R} : f.genEigenspace μ 0 = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用引理 `Module.End.mem_genEigenspace_zero`：mem_genEigenspace_zero {f : End R M} 
{μ : R} {x : M} : x in f.genEigenspace μ 0 ↔ x = 0
-/
lemma genEigenspace_zero {f : End R M} {μ : R} :
    f.genEigenspace μ 0 = ⊥ := by
  ext; apply mem_genEigenspace_zero

@[simp]
/-
**Module.End.genEigenspace_zero_nat** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_zero_nat (f : End R M) (k : Nat) : f.genEigenspace 0 k = Lin
earMap.ker (f ^ k)
参数：f : End R M；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma genEigenspace_zero_nat (f : End R M) (k : ℕ) :
    f.genEigenspace 0 k = LinearMap.ker (f ^ k) := by
  ext; simp [mem_genEigenspace_nat]

/-- Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`,
and let `μ : R` and `k : ℕ∞` be given.
Then `x : M` satisfies `HasUnifEigenvector f μ k x` if
`x ∈ f.genEigenspace μ k` and `x ≠ 0`.

For `k = 1`, this means that `x` is an eigenvector of `f` with eigenvalue `μ`. -/
/-
**Module.End.HasUnifEigenvector** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：HasUnifEigenvector (f : End R M) (μ : R) (k : Nat∞) (x : M) : Prop
参数：f : End R M；μ : R；k : Nat∞；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`,
and let `μ : R` and `k : ℕ∞` be given.
Then `x : M` satisfies `HasUnifEigenvector f μ k x` if
`x ∈ f.genEigenspace μ k` and `x ≠ 0`.

For `k = 1`, this means that `x` is an eigenvector of `f` with eigenvalue `μ`.
-/
def HasUnifEigenvector (f : End R M) (μ : R) (k : ℕ∞) (x : M) : Prop :=
  x ∈ f.genEigenspace μ k ∧ x ≠ 0

/-- Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`.
Then `μ : R` and `k : ℕ∞` satisfy `HasUnifEigenvalue f μ k` if
`f.genEigenspace μ k ≠ ⊥`.

For `k = 1`, this means that `μ` is an eigenvalue of `f`. -/
/-
**Module.End.HasUnifEigenvalue** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：HasUnifEigenvalue (f : End R M) (μ : R) (k : Nat∞) : Prop
参数：f : End R M；μ : R；k : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`.
Then `μ : R` and `k : ℕ∞` satisfy `HasUnifEigenvalue f μ k` if
`f.genEigenspace μ k ≠ ⊥`.

For `k = 1`, this means that `μ` is an eigenvalue of `f`.
-/
def HasUnifEigenvalue (f : End R M) (μ : R) (k : ℕ∞) : Prop :=
  f.genEigenspace μ k ≠ ⊥

/-- Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`.
For `k : ℕ∞`, we define `UnifEigenvalues f k` to be the type of all
`μ : R` that satisfy `f.HasUnifEigenvalue μ k`.

For `k = 1` this is the type of all eigenvalues of `f`. -/
/-
**Module.End.UnifEigenvalues** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：UnifEigenvalues (f : End R M) (k : Nat∞) : Type _
参数：f : End R M；k : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `M` be an `R`-module, and `f` an `R`-linear endomorphism of `M`.
For `k : ℕ∞`, we define `UnifEigenvalues f k` to be the type of all
`μ : R` that satisfy `f.HasUnifEigenvalue μ k`.

For `k = 1` this is the type of all eigenvalues of `f`.
-/
def UnifEigenvalues (f : End R M) (k : ℕ∞) : Type _ :=
  { μ : R // f.HasUnifEigenvalue μ k }

/-- The underlying value of a bundled eigenvalue. -/
@[coe]
/-
**Module.End.UnifEigenvalues.val** 是 Mathlib 中的一个定义，位于命名空间 `Module.End.UnifEigen
values`。
形式化陈述：{R : Type v} →   {M : Type w} →     [inst : CommRing R] →       [inst_1 : 
AddCommGroup M] →         [inst_2 : _root_.Module R M] → (f : Module.End R M) → 
(k : ℕ∞) → f.UnifEigenvalues k → R
参数：f : Module.End R M；k : ℕ∞。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying value of a bundled eigenvalue.
-/
def UnifEigenvalues.val (f : Module.End R M) (k : ℕ∞) : UnifEigenvalues f k → R := Subtype.val

@[simp]
/-
**Module.End.UnifEigenvalues.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.UnifEi
genvalues`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {k : ℕ∞} (h : f.HasU
nifEigenvalue μ k), ↑f k ⟨μ, h⟩ = μ
参数：h : f.HasUnifEigenvalue μ k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma UnifEigenvalues.val_mk {f : End R M} {μ : R} {k : ℕ∞} (h : f.HasUnifEigenvalue μ k) :
    UnifEigenvalues.val f k ⟨μ, h⟩ = μ := rfl

@[simp]
/-
**Module.End.UnifEigenvalues.mk_val** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.UnifEi
genvalues`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {k : ℕ∞} (μ : f.UnifEigenval
ues k), ⟨↑f k μ, ⋯⟩ = μ
参数：μ : f.UnifEigenvalues k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma UnifEigenvalues.mk_val {f : End R M} {k : ℕ∞} (μ : UnifEigenvalues f k) :
    ⟨μ.val, μ.property⟩ = μ := rfl
/-
**Module.End.UnifEigenvalues.instCoeOut** 是 Mathlib 中的一个定义，位于命名空间 `Module.End.Un
ifEigenvalues`。
形式化陈述：{R : Type v} →   {M : Type w} →     [inst : CommRing R] →       [inst_1 : 
AddCommGroup M] →         [inst_2 : _root_.Module R M] → {f : Module.End R M} → 
(k : ℕ∞) → CoeOut (f.UnifEigenvalues k) R
参数：k : ℕ∞；f.UnifEigenvalues k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UnifEigenvalues.instCoeOut {f : Module.End R M} (k : ℕ∞) :
    CoeOut (UnifEigenvalues f k) R where
  coe := UnifEigenvalues.val f k
/-
**Module.End.UnivEigenvalues.instDecidableEq** 是 Mathlib 中的一个定义，位于命名空间 `Module.E
nd.UnivEigenvalues`。
形式化陈述：{R : Type v} →   {M : Type w} →     [inst : CommRing R] →       [inst_1 : 
AddCommGroup M] →         [inst_2 : _root_.Module R M] →           [DecidableEq 
R] → (f : Module.End R M) → (k : ℕ∞) → DecidableEq (f.UnifEigenvalues k)
参数：f : Module.End R M；k : ℕ∞；f.UnifEigenvalues k。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance UnivEigenvalues.instDecidableEq [DecidableEq R] (f : Module.End R M) (k : ℕ∞) :
    DecidableEq (UnifEigenvalues f k) :=
  inferInstanceAs (DecidableEq (Subtype (fun x : R ↦ f.HasUnifEigenvalue x k)))
/-
**Module.End.HasUnifEigenvector.hasUnifEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Mod
ule.End.HasUnifEigenvector`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {k : ℕ∞} {x : M}, f.
HasUnifEigenvector μ k x → f.HasUnifEigenvalue μ k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.HasUnifEigenvalue.eq_1`：∀ {R : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.
End R M) (μ : R) (k : ℕ…
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
-/
lemma HasUnifEigenvector.hasUnifEigenvalue {f : End R M} {μ : R} {k : ℕ∞} {x : M}
    (h : f.HasUnifEigenvector μ k x) : f.HasUnifEigenvalue μ k := by
  rw [HasUnifEigenvalue, Submodule.ne_bot_iff]
  use x; exact h
/-
**Module.End.HasUnifEigenvector.apply_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.
End.HasUnifEigenvector`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {x : M}, f.HasUnifEi
genvector μ 1 x → f x = μ • x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Module.End.mem_genEigenspace_one`：mem_genEigenspace_one {f : End R M} {μ
 : R} {x : M} : x in f.genEigenspace μ 1 ↔ f x = μ • x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
lemma HasUnifEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M}
    (hx : f.HasUnifEigenvector μ 1 x) : f x = μ • x :=
  mem_genEigenspace_one.mp hx.1
/-
**Module.End.HasUnifEigenvector.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.
HasUnifEigenvector`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {v : M}, f.HasUnifEi
genvector μ 1 v → ∀ (n : ℕ), (f ^ n) v = μ ^ n • v
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Module.End.HasUnifEigenvector.apply_eq_smul`：∀ {R : Type v} {M : Type w}
 [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f
 : Module.End R M} {μ : R} {x : M…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
-/
lemma HasUnifEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasUnifEigenvector μ 1 v)
    (n : ℕ) : (f ^ n) v = μ ^ n • v := by
  induction n <;> simp [*, pow_succ f, hv.apply_eq_smul, smul_smul, pow_succ' μ]
/-
**Module.End.HasUnifEigenvalue.exists_hasUnifEigenvector** 是 Mathlib 中的一个定理，位于命名
空间 `Module.End.HasUnifEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {k : ℕ∞}, f.HasUnifE
igenvalue μ k → ∃ v, f.HasUnifEigenvector μ k v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_mem_ne_zero_of_ne_bot`：exists_mem_ne_zero_of_ne_bot {p 
: Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0
-/
theorem HasUnifEigenvalue.exists_hasUnifEigenvector
    {f : End R M} {μ : R} {k : ℕ∞} (hμ : f.HasUnifEigenvalue μ k) :
    ∃ v, f.HasUnifEigenvector μ k v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ
/-
**Module.End.HasUnifEigenvalue.pow** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.HasUnif
Eigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R}, f.HasUnifEigenvalue
 μ 1 → ∀ (n : ℕ), (f ^ n).HasUnifEigenvalue (μ ^ n) 1
参数：n : ℕ；f ^ n；μ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.HasUnifEigenvalue.eq_1`：∀ {R : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.
End R M) (μ : R) (k : ℕ…
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Module.End.HasUnifEigenvalue.exists_hasUnifEigenvector`：∀ {R : Type v} {
M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Modul
e R M]   {f : Module.End R M} {μ : R} {k : ℕ…
· 使用定理 `Module.End.HasUnifEigenvector.pow_apply`：∀ {R : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : M
odule.End R M} {μ : R} {v : M…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma HasUnifEigenvalue.pow {f : End R M} {μ : R} (h : f.HasUnifEigenvalue μ 1) (n : ℕ) :
    (f ^ n).HasUnifEigenvalue (μ ^ n) 1 := by
  rw [HasUnifEigenvalue, Submodule.ne_bot_iff]
  obtain ⟨m : M, hm⟩ := h.exists_hasUnifEigenvector
  exact ⟨m, by simpa [mem_genEigenspace_one] using hm.pow_apply n, hm.2⟩

/-- A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`. -/
/-
**Module.End.HasUnifEigenvalue.isNilpotent_of_isNilpotent** 是 Mathlib 中的一个定理，位于命
名空间 `Module.End.HasUnifEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] [IsDomain R]   [Module.IsTorsionFree R M] {f : Modu
le.End R M}, IsNilpotent f → ∀ {μ : R}, f.HasUnifEigenvalue μ 1 → IsNilpotent μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.exists_hasUnifEigenvector`：∀ {R : Type v} {
M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Modul
e R M]   {f : Module.End R M} {μ : R} {k : ℕ…
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Module.End.HasUnifEigenvector.pow_apply`：∀ {R : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : M
odule.End R M} {μ : R} {v : M…

--- 原说明 ---
A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`.
-/
lemma HasUnifEigenvalue.isNilpotent_of_isNilpotent [IsDomain R] [IsTorsionFree R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasUnifEigenvalue μ 1) :
    IsNilpotent μ := by
  obtain ⟨m : M, hm⟩ := hf.exists_hasUnifEigenvector
  obtain ⟨n : ℕ, hn : f ^ n = 0⟩ := hfn
  exact ⟨n, by simpa [hn, hm.2, eq_comm (a := (0 : M))] using hm.pow_apply n⟩
/-
**Module.End.HasUnifEigenvalue.mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `Module.En
d.HasUnifEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R}, f.HasUnifEigenvalue
 μ 1 → μ ∈ spectrum R f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用定理 `Module.End.HasUnifEigenvalue.exists_hasUnifEigenvector`：∀ {R : Type v} {
M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Modul
e R M]   {f : Module.End R M} {μ : R} {k : ℕ…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `LinearEquiv.ker`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ : T
ype u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCommMonoid M]
 [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.HasUnifEigenvector.apply_eq_smul`：∀ {R : Type v} {M : Type w}
 [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f
 : Module.End R M} {μ : R} {x : M…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
lemma HasUnifEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasUnifEigenvalue f μ 1) :
    μ ∈ spectrum R f := by
  refine spectrum.mem_iff.mpr fun h_unit ↦ ?_
  set f' := LinearMap.GeneralLinearGroup.toLinearEquiv h_unit.unit
  rcases hμ.exists_hasUnifEigenvector with ⟨v, hv⟩
  refine hv.2 ((LinearMap.ker_eq_bot'.mp f'.ker) v (?_ : μ • v - f v = 0))
  rw [hv.apply_eq_smul, sub_self]
/-
**Module.End.hasUnifEigenvalue_iff_mem_spectrum** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.End`。
形式化陈述：hasUnifEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {
μ : K} : f.HasUnifEigenvalue μ 1 ↔ μ in spectrum K f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.mem_iff`：mem_iff {r : R} {a : A} : r in σ a ↔ ¬IsUnit (↑ₐ r - a
)
· 使用定理 `IsUnit.sub_iff`：IsUnit.sub_iff [Ring α] {x y : α} : IsUnit (x - y) ↔ IsU
nit (y - x)
· 使用定理 `LinearMap.isUnit_iff_ker_eq_bot`：isUnit_iff_ker_eq_bot [FiniteDimensiona
l K V] (f : V ->ₗ[K] V) : IsUnit f ↔ (LinearMap.ker f) = ⊥
· 使用定理 `Module.End.HasUnifEigenvalue.eq_1`：∀ {R : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.
End R M) (μ : R) (k : ℕ…
· 使用引理 `Module.End.genEigenspace_one`：genEigenspace_one {f : End R M} {μ : R} : 
f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1)
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasUnifEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasUnifEigenvalue μ 1 ↔ μ ∈ spectrum K f := by
  rw [spectrum.mem_iff, IsUnit.sub_iff, LinearMap.isUnit_iff_ker_eq_bot,
    HasUnifEigenvalue, genEigenspace_one, ne_eq, not_iff_not]
  simp [Submodule.ext_iff, LinearMap.mem_ker]

alias ⟨_, HasUnifEigenvalue.of_mem_spectrum⟩ := hasUnifEigenvalue_iff_mem_spectrum

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**Module.End.genEigenspace_div** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_div (f : End K V) (a b : K) (hb : b != 0) : genEigenspace f 
(a / b) 1 = LinearMap.ker (b • f - a • 1)
参数：f : End K V；a b : K；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Module.End.genEigenspace_one`：genEigenspace_one {f : End R M} {μ : R} : 
f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1)
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `LinearMap.ker_smul`：ker_smul (f : V ->ₗ[K] V₂) (a : K) (h : a != 0) : ke
r (a • f) = ker f
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `smul_inv_smul₀`：smul_inv_smul₀ (ha : a != 0) (x : β) : a • a⁻¹ • x = x
-/
lemma genEigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    genEigenspace f (a / b) 1 = LinearMap.ker (b • f - a • 1) :=
  calc
    genEigenspace f (a / b) 1 = genEigenspace f (b⁻¹ * a) 1 := by rw [div_eq_mul_inv, mul_comm]
    _ = LinearMap.ker (f - (b⁻¹ * a) • 1)     := by rw [genEigenspace_one]
    _ = LinearMap.ker (f - b⁻¹ • a • 1)       := by rw [smul_smul]
    _ = LinearMap.ker (b • (f - b⁻¹ • a • 1)) := by rw [LinearMap.ker_smul _ b hb]
    _ = LinearMap.ker (b • f - a • 1)         := by rw [smul_sub, smul_inv_smul₀ hb]

/-- The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `k ∈ ℕ∞`
is the range of `(f - μ • id) ^ k` if `k` is a natural number,
or the infimum of these ranges if `k = ∞`. -/
/-
**Module.End.genEigenrange** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：genEigenrange (f : End R M) (μ : R) (k : Nat∞) : Submodule R M
参数：f : End R M；μ : R；k : Nat∞。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generalized eigenrange for a linear map `f`, a scalar `μ`, and an exponent `
k ∈ ℕ∞`
is the range of `(f - μ • id) ^ k` if `k` is a natural number,
or the infimum of these ranges if `k = ∞`.
-/
def genEigenrange (f : End R M) (μ : R) (k : ℕ∞) : Submodule R M :=
  ⨅ l : ℕ, ⨅ (_ : l ≤ k), LinearMap.range ((f - μ • 1) ^ l)
/-
**Module.End.genEigenrange_nat** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenrange_nat {f : End R M} {μ : R} {k : Nat} : f.genEigenrange μ k = 
LinearMap.range ((f - μ • 1) ^ k)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
-/
lemma genEigenrange_nat {f : End R M} {μ : R} {k : ℕ} :
    f.genEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k) := by
  ext x
  simp only [genEigenrange, Nat.cast_le, Submodule.mem_iInf, LinearMap.mem_range]
  constructor
  · intro h
    exact h _ le_rfl
  · rintro ⟨x, rfl⟩ i hi
    have : k = i + (k - i) := by lia
    rw [this, pow_add]
    exact ⟨_, rfl⟩

/-- The exponent of a generalized eigenvalue is never 0. -/
/-
**Module.End.HasUnifEigenvalue.exp_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.End
.HasUnifEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {k : ℕ}, f.HasUnifEi
genvalue μ ↑k → k ≠ 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Module.End.genEigenspace_zero`：genEigenspace_zero {f : End R M} {μ : R} 
: f.genEigenspace μ 0 = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The exponent of a generalized eigenvalue is never 0.
-/
lemma HasUnifEigenvalue.exp_ne_zero {f : End R M} {μ : R} {k : ℕ}
    (h : f.HasUnifEigenvalue μ k) : k ≠ 0 := by
  rintro rfl
  simp [HasUnifEigenvalue, Nat.cast_zero, genEigenspace_zero] at h

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
/-
**Module.End.maxUnifEigenspaceIndex** 是 Mathlib 中的一个定义，位于命名空间 `Module.End`。
形式化陈述：maxUnifEigenspaceIndex (f : End R M) (μ : R)
参数：f : End R M；μ : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` 
is the
maximal generalized eigenspace, then this value is the least such `k`. If not, t
his value is not
meaningful.
-/
noncomputable def maxUnifEigenspaceIndex (f : End R M) (μ : R) :=
  monotonicSequenceLimitIndex <| (f.genEigenspace μ).comp <| WithTop.coeOrderHom.toOrderHom

set_option backward.isDefEq.respectTransparency false in
/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
/-
**Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex** 是 Mathlib 中的一个引理，位于命名
空间 `Module.End`。
形式化陈述：genEigenspace_top_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R 
M) (μ : R) : genEigenspace f μ ⊤ = f.genEigenspace μ (maxUnifEigenspaceIndex f μ
)
参数：f : End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `WellFoundedGT.iSup_eq_monotonicSequenceLimit`：WellFoundedGT.iSup_eq_mono
tonicSequenceLimit [CompleteLattice α] [WellFoundedGT α] (a : Nat ->o α) : iSup 
a = monotonicSequenceLimit a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_pos`：iSup_pos {p : Prop} {f : p -> α} (hp : p) : ⨆ h : p, f h = f h
p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `OrderHom.comp_coe`：∀ {α : Type u_2} {β : Type u_3} {γ : Type u_4} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Preorder γ]   (g : β →o γ) (f : α 
→o β), …
· 使用引理 `iSup_prod'`：iSup_prod' (f : β -> γ -> α) : (⨆ i, ⨆ j, f i j) = ⨆ x : β ×
 γ, f x.1 x.2
· 使用定理 `iSup_subtype'`：iSup_subtype' {p : ι -> Prop} {f : forall i, p i -> α} : 
⨆ (i) (h), f i h = ⨆ x : Subtype p, f x x.property
· 使用定理 `sSup_range`：sSup_range : sSup (range f) = iSup f
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
For an endomorphism of a Noetherian module, the maximal eigenspace is always of 
the form kernel
`(f - μ • id) ^ k` for some `k`.
-/
lemma genEigenspace_top_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) :
    genEigenspace f μ ⊤ = f.genEigenspace μ (maxUnifEigenspaceIndex f μ) := by
  have := WellFoundedGT.iSup_eq_monotonicSequenceLimit <|
    (f.genEigenspace μ).comp <| WithTop.coeOrderHom.toOrderHom
  convert! this using 1
  simp only [genEigenspace, OrderHom.coe_mk, le_top, iSup_pos, OrderHom.comp_coe,
    Function.comp_def]
  rw [iSup_prod', iSup_subtype', ← sSup_range, ← sSup_range]
  congr 1
  aesop
/-
**Module.End.genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex** 是 Mathlib 中
的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex [IsNoetherian R M] (
f : End R M) (μ : R) (k : Nat∞) : f.genEigenspace μ k <= f.genEigenspace μ (maxU
nifEigenspaceIndex f μ)
参数：f : End R M；μ : R；k : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex`：genEigenspace_to
p_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) : genEigens
pace f μ ⊤ = f.genEigenspace μ (maxUnifEigen…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
lemma genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M)
    (μ : R) (k : ℕ∞) :
    f.genEigenspace μ k ≤ f.genEigenspace μ (maxUnifEigenspaceIndex f μ) := by
  rw [← genEigenspace_top_eq_maxUnifEigenspaceIndex]
  exact (f.genEigenspace μ).monotone le_top

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
/-
**Module.End.genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le** 是 Mat
hlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le [IsNoetherian 
R M] (f : End R M) (μ : R) {k : Nat} (hk : maxUnifEigenspaceIndex f μ <= k) : f.
genEigenspace μ k = f.genEigenspace μ (maxUnifEigenspaceIndex f μ)
参数：f : End R M；μ : R；hk : maxUnifEigenspaceIndex f μ <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Module.End.genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex`：genEig
enspace_le_genEigenspace_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M)
 (μ : R) (k : Nat∞) : f.genEigenspace μ k <= f.genEige…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
Generalized eigenspaces for exponents at least `finrank K V` are equal to each o
ther.
-/
theorem genEigenspace_eq_genEigenspace_maxUnifEigenspaceIndex_of_le [IsNoetherian R M]
    (f : End R M) (μ : R) {k : ℕ} (hk : maxUnifEigenspaceIndex f μ ≤ k) :
    f.genEigenspace μ k = f.genEigenspace μ (maxUnifEigenspaceIndex f μ) :=
  le_antisymm
    (genEigenspace_le_genEigenspace_maxUnifEigenspaceIndex _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)

/-- A generalized eigenvalue for some exponent `k` is also
a generalized eigenvalue for exponents larger than `k`. -/
/-
**Module.End.HasUnifEigenvalue.le** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.HasUnifE
igenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {k m : ℕ∞}, k ≤ m → 
f.HasUnifEigenvalue μ k → f.HasUnifEigenvalue μ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f

--- 原说明 ---
A generalized eigenvalue for some exponent `k` is also
a generalized eigenvalue for exponents larger than `k`.
-/
lemma HasUnifEigenvalue.le {f : End R M} {μ : R} {k m : ℕ∞}
    (hm : k ≤ m) (hk : f.HasUnifEigenvalue μ k) :
    f.HasUnifEigenvalue μ m := by
  unfold HasUnifEigenvalue at *
  contrapose hk
  rw [← le_bot_iff, ← hk]
  exact (f.genEigenspace _).monotone hm

/-- A generalized eigenvalue for some exponent `k` is also
a generalized eigenvalue for positive exponents. -/
/-
**Module.End.HasUnifEigenvalue.lt** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.HasUnifE
igenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {k m : ℕ∞}, 0 < m → 
f.HasUnifEigenvalue μ k → f.HasUnifEigenvalue μ m
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.le`：∀ {R : Type v} {M : Type w} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.En
d R M} {μ : R} {k m :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Order.one_le_iff_pos`：one_le_iff_pos [AddMonoidWithOne α] [ZeroLEOneClas
s α] [NeZero (1 : α)] [SuccAddOrder α] : 1 <= x ↔ 0 < x
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `Module.End.mem_genEigenspace`：mem_genEigenspace {f : End R M} {μ : R} {k
 : Nat∞} {x : M} : x in f.genEigenspace μ k ↔ exists l : Nat, l <= k ∧ x in Line
arMap.ker ((f - μ …
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Module.End.coe_pow`：coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `Function.Injective.iterate`：∀ {α : Type u} {f : α → α}, Function.Injecti
ve f → ∀ (n : ℕ), Function.Injective f^[n]
· 使用引理 `Module.End.genEigenspace_one`：genEigenspace_one {f : End R M} {μ : R} : 
f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1)

--- 原说明 ---
A generalized eigenvalue for some exponent `k` is also
a generalized eigenvalue for positive exponents.
-/
lemma HasUnifEigenvalue.lt {f : End R M} {μ : R} {k m : ℕ∞}
    (hm : 0 < m) (hk : f.HasUnifEigenvalue μ k) :
    f.HasUnifEigenvalue μ m := by
  apply HasUnifEigenvalue.le (k := 1) (Order.one_le_iff_pos.mpr hm)
  intro contra; apply hk
  rw [genEigenspace_one, LinearMap.ker_eq_bot] at contra
  rw [eq_bot_iff]
  intro x hx
  rw [mem_genEigenspace] at hx
  rcases hx with ⟨l, -, hx⟩
  rwa [LinearMap.ker_eq_bot.mpr] at hx
  rw [Module.End.coe_pow (f - μ • 1) l]
  exact Function.Injective.iterate contra l

/-- Generalized eigenvalues are actually just eigenvalues. -/
@[simp]
/-
**Module.End.hasUnifEigenvalue_iff_hasUnifEigenvalue_one** 是 Mathlib 中的一个引理，位于命名
空间 `Module.End`。
形式化陈述：hasUnifEigenvalue_iff_hasUnifEigenvalue_one {f : End R M} {μ : R} {k : Nat
∞} (hk : 0 < k) : f.HasUnifEigenvalue μ k ↔ f.HasUnifEigenvalue μ 1
参数：hk : 0 < k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.lt`：∀ {R : Type v} {M : Type w} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.En
d R M} {μ : R} {k m :…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
Generalized eigenvalues are actually just eigenvalues.
-/
lemma hasUnifEigenvalue_iff_hasUnifEigenvalue_one {f : End R M} {μ : R} {k : ℕ∞} (hk : 0 < k) :
    f.HasUnifEigenvalue μ k ↔ f.HasUnifEigenvalue μ 1 :=
  ⟨HasUnifEigenvalue.lt zero_lt_one, HasUnifEigenvalue.lt hk⟩
/-
**Module.End.maxUnifEigenspaceIndex_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 `Module
.End`。
形式化陈述：maxUnifEigenspaceIndex_le_finrank [FiniteDimensional K V] (f : End K V) (μ
 : K) : maxUnifEigenspaceIndex f μ <= finrank K V
参数：f : End K V；μ : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sInf_le`：∀ {s : Set ℕ} {m : ℕ}, m ∈ s → sInf s ≤ m
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `OrderEmbedding.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorde
r α] [inst_1 : Preorder β] (f : α ↪o β), Monotone ⇑f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `Module.End.ker_pow_le_ker_pow_finrank`：ker_pow_le_ker_pow_finrank [Finit
eDimensional K V] (f : End K V) (m : Nat) : LinearMap.ker (f ^ m) <= LinearMap.k
er (f ^ finrank K V)
-/
lemma maxUnifEigenspaceIndex_le_finrank [FiniteDimensional K V] (f : End K V) (μ : K) :
    maxUnifEigenspaceIndex f μ ≤ finrank K V := by
  apply Nat.sInf_le
  intro n hn
  apply le_antisymm
  · exact (f.genEigenspace μ).monotone <| WithTop.coeOrderHom.monotone hn
  · change (f.genEigenspace μ) n ≤ (f.genEigenspace μ) (finrank K V)
    rw [genEigenspace_nat, genEigenspace_nat]
    apply ker_pow_le_ker_pow_finrank

/-- Every generalized eigenvector is a generalized eigenvector for exponent `finrank K V`.
(Lemma 8.20 of [axler2024]) -/
/-
**Module.End.genEigenspace_le_genEigenspace_finrank** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.End`。
形式化陈述：genEigenspace_le_genEigenspace_finrank [FiniteDimensional K V] (f : End K 
V) (μ : K) (k : Nat∞) : f.genEigenspace μ k <= f.genEigenspace μ (finrank K V)
参数：f : End K V；μ : K；k : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex`：genEigenspace_to
p_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) : genEigens
pace f μ ⊤ = f.genEigenspace μ (maxUnifEigen…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `Module.End.maxUnifEigenspaceIndex_le_finrank`：maxUnifEigenspaceIndex_le_
finrank [FiniteDimensional K V] (f : End K V) (μ : K) : maxUnifEigenspaceIndex f
 μ <= finrank K V

--- 原说明 ---
Every generalized eigenvector is a generalized eigenvector for exponent `finrank
 K V`.
(Lemma 8.20 of [axler2024])
-/
lemma genEigenspace_le_genEigenspace_finrank [FiniteDimensional K V] (f : End K V)
    (μ : K) (k : ℕ∞) : f.genEigenspace μ k ≤ f.genEigenspace μ (finrank K V) := by
  calc f.genEigenspace μ k
      ≤ f.genEigenspace μ ⊤ := (f.genEigenspace _).monotone le_top
    _ ≤ f.genEigenspace μ (finrank K V) := by
      rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
      exact (f.genEigenspace _).monotone <| by simpa using maxUnifEigenspaceIndex_le_finrank f μ

/-- Generalized eigenspaces for exponents at least `finrank K V` are equal to each other. -/
/-
**Module.End.genEigenspace_eq_genEigenspace_finrank_of_le** 是 Mathlib 中的一个定理，位于命
名空间 `Module.End`。
形式化陈述：genEigenspace_eq_genEigenspace_finrank_of_le [FiniteDimensional K V] (f : 
End K V) (μ : K) {k : Nat} (hk : finrank K V <= k) : f.genEigenspace μ k = f.gen
Eigenspace μ (finrank K V)
参数：f : End K V；μ : K；hk : finrank K V <= k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Module.End.genEigenspace_le_genEigenspace_finrank`：genEigenspace_le_genE
igenspace_finrank [FiniteDimensional K V] (f : End K V) (μ : K) (k : Nat∞) : f.g
enEigenspace μ k <= f.genEigenspace μ (…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
Generalized eigenspaces for exponents at least `finrank K V` are equal to each o
ther.
-/
theorem genEigenspace_eq_genEigenspace_finrank_of_le [FiniteDimensional K V]
    (f : End K V) (μ : K) {k : ℕ} (hk : finrank K V ≤ k) :
    f.genEigenspace μ k = f.genEigenspace μ (finrank K V) :=
  le_antisymm
    (genEigenspace_le_genEigenspace_finrank _ _ _)
    ((f.genEigenspace μ).monotone <| by simpa using hk)
/-
**Module.End.mapsTo_genEigenspace_of_comm** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`
。
形式化陈述：mapsTo_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) (k 
: Nat∞) : MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k)
参数：h : Commute f g；μ : R；k : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Commute.pow_left`：pow_left (h : Commute a b) (n : Nat) : Commute (a ^ n)
 b
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `Module.End.mul_eq_comp`：mul_eq_comp (f g : Module.End R M) : f * g = f.c
omp g
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
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
-/
lemma mapsTo_genEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) (k : ℕ∞) :
    MapsTo g (f.genEigenspace μ k) (f.genEigenspace μ k) := by
  intro x hx
  simp only [SetLike.mem_coe, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  rcases hx with ⟨l, hl, hx⟩
  replace h : Commute ((f - μ • (1 : End R M)) ^ l) g :=
    (h.sub_left <| Algebra.commute_algebraMap_left μ g).pow_left l
  use l, hl
  rw [← LinearMap.comp_apply, ← Module.End.mul_eq_comp, h.eq, Module.End.mul_eq_comp,
    LinearMap.comp_apply, hx, map_zero]

set_option backward.isDefEq.respectTransparency false in
/-- The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nilpotent. -/
/-
**Module.End.isNilpotent_restrict_genEigenspace_nat** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.End`。
形式化陈述：isNilpotent_restrict_genEigenspace_nat (f : End R M) (μ : R) (k : Nat) (h 
: MapsTo (f - μ • (1 : End R M)) (f.genEigenspace μ k) (f.genEigenspace μ k)
参数：f : End R M；μ : R；k : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.zero_apply`：zero_apply (x : M) : (0 : M ->ₛₗ[σ₁₂] M₂) x = 0
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
· 使用定理 `Module.End.pow_apply_mem_of_forall_mem`：∀ {R : Type u_1} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f
' : M →ₗ[R] M} {p : Submodul…
· 使用定理 `Module.End.pow_restrict`：∀ {R : Type u_1} {M : Type u_5} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : M →ₗ[R] M} 
{p : Submodul…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `LinearMap.restrict_apply`：restrict_apply {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) (x : p) : f.restr
ict hf x = ⟨f …
· 使用引理 `Module.End.mem_genEigenspace_nat`：mem_genEigenspace_nat {f : End R M} {μ
 : R} {k : Nat} {x : M} : x in f.genEigenspace μ k ↔ x in LinearMap.ker ((f - μ 
• 1) ^ k)

--- 原说明 ---
The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nil
potent.
-/
lemma isNilpotent_restrict_genEigenspace_nat (f : End R M) (μ : R) (k : ℕ)
    (h : MapsTo (f - μ • (1 : End R M))
      (f.genEigenspace μ k) (f.genEigenspace μ k) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - μ • 1).restrict h) := by
  use k
  ext ⟨x, hx⟩
  rw [mem_genEigenspace_nat] at hx
  rw [LinearMap.zero_apply, ZeroMemClass.coe_zero, ZeroMemClass.coe_eq_zero,
    Module.End.pow_restrict, LinearMap.restrict_apply]
  ext
  simpa

/-- The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent. -/
/-
**Module.End.isNilpotent_restrict_genEigenspace_top** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.End`。
形式化陈述：isNilpotent_restrict_genEigenspace_top [IsNoetherian R M] (f : End R M) (μ
 : R) (h : MapsTo (f - μ • (1 : End R M)) (f.genEigenspace μ ⊤) (f.genEigenspace
 μ ⊤)
参数：f : End R M；μ : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.isNilpotent_restrict_of_le`：isNilpotent_restrict_of_le {f : E
nd R M} {p q : Submodule R M} {hp : MapsTo f p p} {hq : MapsTo f q q} (h : p <= 
q) (hf : IsNilpotent (f.res…
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex`：genEigenspace_to
p_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) : genEigens
pace f μ ⊤ = f.genEigenspace μ (maxUnifEigen…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Module.End.isNilpotent_restrict_genEigenspace_nat`：isNilpotent_restrict_
genEigenspace_nat (f : End R M) (μ : R) (k : Nat) (h : MapsTo (f - μ • (1 : End 
R M)) (f.genEigenspace μ k) (f.genEigen…

--- 原说明 ---
The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent.
-/
lemma isNilpotent_restrict_genEigenspace_top [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - μ • (1 : End R M))
      (f.genEigenspace μ ⊤) (f.genEigenspace μ ⊤) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ _) :
    IsNilpotent ((f - μ • 1).restrict h) := by
  apply isNilpotent_restrict_of_le
  on_goal 2 => apply isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ)
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]

/-- The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of all vectors `x`
such that `f x = μ • x`. (Def 5.52 of [axler2024]). -/
/-
**Module.End.eigenspace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：eigenspace (f : End R M) (μ : R) : Submodule R M
参数：f : End R M；μ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule `eigenspace f μ` for a linear map `f` and a scalar `μ` consists of
 all vectors `x`
such that `f x = μ • x`. (Def 5.52 of [axler2024]).
-/
abbrev eigenspace (f : End R M) (μ : R) : Submodule R M :=
  f.genEigenspace μ 1
/-
**Module.End.eigenspace_def** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：eigenspace_def {f : End R M} {μ : R} : f.eigenspace μ = LinearMap.ker (f -
 μ • 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.eigenspace.eq_1`：∀ {R : Type v} {M : Type w} [inst : CommRing
 R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (f : Module.End R M
) (μ : R), f.eig…
· 使用引理 `Module.End.genEigenspace_one`：genEigenspace_one {f : End R M} {μ : R} : 
f.genEigenspace μ 1 = LinearMap.ker (f - μ • 1)
-/
lemma eigenspace_def {f : End R M} {μ : R} :
    f.eigenspace μ = LinearMap.ker (f - μ • 1) := by
  rw [eigenspace, genEigenspace_one]

@[simp]
/-
**Module.End.eigenspace_zero** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：eigenspace_zero (f : End R M) : f.eigenspace 0 = LinearMap.ker f
参数：f : End R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Module.End.genEigenspace_zero_nat`：genEigenspace_zero_nat (f : End R M) 
(k : Nat) : f.genEigenspace 0 k = LinearMap.ker (f ^ k)
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem eigenspace_zero (f : End R M) : f.eigenspace 0 = LinearMap.ker f := by
  simp only [eigenspace, ← Nat.cast_one (R := ℕ∞), genEigenspace_zero_nat, pow_one]

/-- A nonzero element of an eigenspace is an eigenvector. (Def 5.8 of [axler2024]) -/
/-
**Module.End.HasEigenvector** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：HasEigenvector (f : End R M) (μ : R) (x : M) : Prop
参数：f : End R M；μ : R；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonzero element of an eigenspace is an eigenvector. (Def 5.8 of [axler2024])
-/
abbrev HasEigenvector (f : End R M) (μ : R) (x : M) : Prop :=
  HasUnifEigenvector f μ 1 x
/-
**Module.End.hasEigenvector_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvector_iff {f : End R M} {μ : R} {x : M} : f.HasEigenvector μ x ↔ 
x in f.eigenspace μ ∧ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasEigenvector_iff {f : End R M} {μ : R} {x : M} :
    f.HasEigenvector μ x ↔ x ∈ f.eigenspace μ ∧ x ≠ 0 := Iff.rfl

/-- A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors `x`
such that `f x = μ • x`. (Def 5.5 of [axler2024]). -/
/-
**Module.End.HasEigenvalue** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：HasEigenvalue (f : End R M) (a : R) : Prop
参数：f : End R M；a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scalar `μ` is an eigenvalue for a linear map `f` if there are nonzero vectors 
`x`
such that `f x = μ • x`. (Def 5.5 of [axler2024]).
-/
abbrev HasEigenvalue (f : End R M) (a : R) : Prop :=
  HasUnifEigenvalue f a 1
/-
**Module.End.hasEigenvalue_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvalue_iff {f : End R M} {μ : R} : f.HasEigenvalue μ ↔ f.eigenspace
 μ != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasEigenvalue_iff {f : End R M} {μ : R} :
    f.HasEigenvalue μ ↔ f.eigenspace μ ≠ ⊥ := Iff.rfl

/-- The eigenvalues of the endomorphism `f`, as a subtype of `R`. -/
/-
**Module.End.Eigenvalues** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：Eigenvalues (f : End R M) : Type _
参数：f : End R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The eigenvalues of the endomorphism `f`, as a subtype of `R`.
-/
abbrev Eigenvalues (f : End R M) : Type _ :=
  UnifEigenvalues f 1

@[coe]
/-
**Module.End.Eigenvalues.val** 是 Mathlib 中的一个定义，位于命名空间 `Module.End.Eigenvalues`。
形式化陈述：{R : Type v} →   {M : Type w} →     [inst : CommRing R] →       [inst_1 : 
AddCommGroup M] → [inst_2 : _root_.Module R M] → (f : Module.End R M) → f.Eigenv
alues → R
参数：f : Module.End R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev Eigenvalues.val (f : Module.End R M) : Eigenvalues f → R := UnifEigenvalues.val f 1

@[simp]
/-
**Module.End.Eigenvalues.val_mk** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.Eigenvalue
s`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} (h : f.HasEigenvalue
 μ), ↑f ⟨μ, h⟩ = μ
参数：h : f.HasEigenvalue μ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Eigenvalues.val_mk {f : End R M} {μ : R} (h : f.HasEigenvalue μ) :
    Eigenvalues.val f ⟨μ, h⟩ = μ := rfl

@[simp]
/-
**Module.End.Eigenvalues.mk_val** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.Eigenvalue
s`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} (μ : f.Eigenvalues), ⟨↑f μ, 
⋯⟩ = μ
参数：μ : f.Eigenvalues。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma Eigenvalues.mk_val {f : End R M} (μ : Eigenvalues f) : ⟨μ.val, μ.property⟩ = μ := rfl
/-
**Module.End.hasEigenvalue_of_hasEigenvector** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd`。
形式化陈述：hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEige
nvector f μ x) : HasEigenvalue f μ
参数：h : HasEigenvector f μ x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvector.hasUnifEigenvalue`：∀ {R : Type v} {M : Typ
e w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] 
  {f : Module.End R M} {μ : R} {k : ℕ…
-/
theorem hasEigenvalue_of_hasEigenvector {f : End R M} {μ : R} {x : M} (h : HasEigenvector f μ x) :
    HasEigenvalue f μ :=
  h.hasUnifEigenvalue
/-
**Module.End.mem_eigenspace_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x in eigenspace f μ ↔ f
 x = μ • x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.mem_genEigenspace_one`：mem_genEigenspace_one {f : End R M} {μ
 : R} {x : M} : x in f.genEigenspace μ 1 ↔ f x = μ • x
-/
theorem mem_eigenspace_iff {f : End R M} {μ : R} {x : M} : x ∈ eigenspace f μ ↔ f x = μ • x :=
  mem_genEigenspace_one

nonrec
/-
**Module.End.HasEigenvector.apply_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.
HasEigenvector`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {x : M}, f.HasEigenv
ector μ x → f x = μ • x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvector.apply_eq_smul`：∀ {R : Type v} {M : Type w}
 [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f
 : Module.End R M} {μ : R} {x : M…
-/
theorem HasEigenvector.apply_eq_smul {f : End R M} {μ : R} {x : M} (hx : f.HasEigenvector μ x) :
    f x = μ • x :=
  hx.apply_eq_smul

nonrec
/-
**Module.End.HasEigenvector.pow_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.HasE
igenvector`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R} {v : M}, f.HasEigenv
ector μ v → ∀ (n : ℕ), (f ^ n) v = μ ^ n • v
参数：n : ℕ；f ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvector.pow_apply`：∀ {R : Type v} {M : Type w} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : M
odule.End R M} {μ : R} {v : M…
-/
theorem HasEigenvector.pow_apply {f : End R M} {μ : R} {v : M} (hv : f.HasEigenvector μ v) (n : ℕ) :
    (f ^ n) v = μ ^ n • v :=
  hv.pow_apply n
/-
**Module.End.HasEigenvalue.exists_hasEigenvector** 是 Mathlib 中的一个定理，位于命名空间 `Modu
le.End.HasEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R}, f.HasEigenvalue μ →
 ∃ v, f.HasEigenvector μ v
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_mem_ne_zero_of_ne_bot`：exists_mem_ne_zero_of_ne_bot {p 
: Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0
-/
theorem HasEigenvalue.exists_hasEigenvector {f : End R M} {μ : R} (hμ : f.HasEigenvalue μ) :
    ∃ v, f.HasEigenvector μ v :=
  Submodule.exists_mem_ne_zero_of_ne_bot hμ

nonrec
/-
**Module.End.HasEigenvalue.pow** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.HasEigenval
ue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R}, f.HasEigenvalue μ →
 ∀ (n : ℕ), (f ^ n).HasEigenvalue (μ ^ n)
参数：n : ℕ；f ^ n；μ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.pow`：∀ {R : Type v} {M : Type w} [inst : Co
mmRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.E
nd R M} {μ : R}, f.Has…
-/
lemma HasEigenvalue.pow {f : End R M} {μ : R} (h : f.HasEigenvalue μ) (n : ℕ) :
    (f ^ n).HasEigenvalue (μ ^ n) :=
  h.pow n
/-
**Module.End.genEigenspace_mem_invtSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd`。
形式化陈述：genEigenspace_mem_invtSubmodule (f : End R M) (μ : R) (n : Nat∞) : genEige
nspace f μ n in invtSubmodule f
参数：f : End R M；μ : R；n : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
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
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
-/
theorem genEigenspace_mem_invtSubmodule (f : End R M) (μ : R) (n : ℕ∞) :
    genEigenspace f μ n ∈ invtSubmodule f := by
  intro x hx
  simp only [Submodule.mem_comap, mem_genEigenspace, LinearMap.mem_ker] at hx ⊢
  obtain ⟨k, hk, hx⟩ := hx
  refine ⟨k, hk, ?_⟩
  induction k generalizing x
  case zero => simp_all
  case succ k ih =>
    rw [pow_succ, mul_apply] at hx ⊢
    simpa using ih (le_trans (by simp) hk) hx
/-
**Module.End.eigenspace_mem_invtSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`
。
形式化陈述：eigenspace_mem_invtSubmodule (f : End R M) (μ : R) : eigenspace f μ in inv
tSubmodule f
参数：f : End R M；μ : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.genEigenspace_mem_invtSubmodule`：genEigenspace_mem_invtSubmod
ule (f : End R M) (μ : R) (n : Nat∞) : genEigenspace f μ n in invtSubmodule f
-/
theorem eigenspace_mem_invtSubmodule (f : End R M) (μ : R) :
    eigenspace f μ ∈ invtSubmodule f :=
  genEigenspace_mem_invtSubmodule f μ 1
/-
**Module.End.restrict_eigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：restrict_eigenspace (f : End R M) (μ : R) : f.restrict (f.mem_invtSubmodul
e_iff_forall_mem_of_mem.mp (eigenspace_mem_invtSubmodule f μ)) = μ • LinearMap.i
d
参数：f : End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.End.mem_invtSubmodule_iff_forall_mem_of_mem`：mem_invtSubmodule_if
f_forall_mem_of_mem {p : Submodule R M} : p in f.invtSubmodule ↔ forall x in p, 
f x in p
· 使用定理 `Module.End.eigenspace_mem_invtSubmodule`：eigenspace_mem_invtSubmodule (f
 : End R M) (μ : R) : eigenspace f μ in invtSubmodule f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Module.End.mem_eigenspace_iff`：mem_eigenspace_iff {f : End R M} {μ : R} 
{x : M} : x in eigenspace f μ ↔ f x = μ • x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem restrict_eigenspace (f : End R M) (μ : R) :
    f.restrict (f.mem_invtSubmodule_iff_forall_mem_of_mem.mp
      (eigenspace_mem_invtSubmodule f μ)) = μ • LinearMap.id := by
  ext x
  exact mem_eigenspace_iff.mp x.2

/-- A nilpotent endomorphism has nilpotent eigenvalues.

See also `LinearMap.isNilpotent_trace_of_isNilpotent`. -/
nonrec
/-
**Module.End.HasEigenvalue.isNilpotent_of_isNilpotent** 是 Mathlib 中的一个定理，位于命名空间 
`Module.End.HasEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M] [IsDomain R]   [Module.IsTorsionFree R M] {f : Modu
le.End R M}, IsNilpotent f → ∀ {μ : R}, f.HasEigenvalue μ → IsNilpotent μ
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.isNilpotent_of_isNilpotent`：∀ {R : Type v} 
{M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Modu
le R M] [IsDomain R]   [Module.IsTorsionFree …
-/
lemma HasEigenvalue.isNilpotent_of_isNilpotent [IsDomain R] [IsTorsionFree R M] {f : End R M}
    (hfn : IsNilpotent f) {μ : R} (hf : f.HasEigenvalue μ) :
    IsNilpotent μ :=
  hf.isNilpotent_of_isNilpotent hfn

nonrec
/-
**Module.End.HasEigenvalue.mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `Module.End.Ha
sEigenvalue`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ : R}, f.HasEigenvalue μ →
 μ ∈ spectrum R f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.mem_spectrum`：∀ {R : Type v} {M : Type w} [
inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f :
 Module.End R M} {μ : R}, f.Has…
-/
theorem HasEigenvalue.mem_spectrum {f : End R M} {μ : R} (hμ : HasEigenvalue f μ) :
    μ ∈ spectrum R f :=
  hμ.mem_spectrum
/-
**Module.End.hasEigenvalue_iff_mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `Module.En
d`。
形式化陈述：hasEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : 
K} : f.HasEigenvalue μ ↔ μ in spectrum K f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.hasUnifEigenvalue_iff_mem_spectrum`：hasUnifEigenvalue_iff_mem
_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} : f.HasUnifEigenvalue μ 
1 ↔ μ in spectrum K f
-/
theorem hasEigenvalue_iff_mem_spectrum [FiniteDimensional K V] {f : End K V} {μ : K} :
    f.HasEigenvalue μ ↔ μ ∈ spectrum K f :=
  hasUnifEigenvalue_iff_mem_spectrum

alias ⟨_, HasEigenvalue.of_mem_spectrum⟩ := hasEigenvalue_iff_mem_spectrum
/-
**Module.End.eigenspace_div** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：eigenspace_div (f : End K V) (a b : K) (hb : b != 0) : eigenspace f (a / b
) = LinearMap.ker (b • f - algebraMap K (End K V) a)
参数：f : End K V；a b : K；hb : b != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.genEigenspace_div`：genEigenspace_div (f : End K V) (a b : K) 
(hb : b != 0) : genEigenspace f (a / b) 1 = LinearMap.ker (b • f - a • 1)
-/
theorem eigenspace_div (f : End K V) (a b : K) (hb : b ≠ 0) :
    eigenspace f (a / b) = LinearMap.ker (b • f - algebraMap K (End K V) a) :=
  genEigenspace_div f a b hb

/-- A nonzero element of a generalized eigenspace is a generalized eigenvector.
(Def 8.8 of [axler2024]) -/
/-
**Module.End.HasGenEigenvector** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：HasGenEigenvector (f : End R M) (μ : R) (k : Nat) (x : M) : Prop
参数：f : End R M；μ : R；k : Nat；x : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A nonzero element of a generalized eigenspace is a generalized eigenvector.
(Def 8.8 of [axler2024])
-/
abbrev HasGenEigenvector (f : End R M) (μ : R) (k : ℕ) (x : M) : Prop :=
  HasUnifEigenvector f μ k x
/-
**Module.End.hasGenEigenvector_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasGenEigenvector_iff {f : End R M} {μ : R} {k : Nat} {x : M} : f.HasGenEi
genvector μ k x ↔ x in f.genEigenspace μ k ∧ x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasGenEigenvector_iff {f : End R M} {μ : R} {k : ℕ} {x : M} :
    f.HasGenEigenvector μ k x ↔ x ∈ f.genEigenspace μ k ∧ x ≠ 0 := Iff.rfl

/-- A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k ∈ ℕ` if there
are generalized eigenvectors for `f`, `k`, and `μ`. -/
/-
**Module.End.HasGenEigenvalue** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：HasGenEigenvalue (f : End R M) (μ : R) (k : Nat) : Prop
参数：f : End R M；μ : R；k : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scalar `μ` is a generalized eigenvalue for a linear map `f` and an exponent `k
 ∈ ℕ` if there
are generalized eigenvectors for `f`, `k`, and `μ`.
-/
abbrev HasGenEigenvalue (f : End R M) (μ : R) (k : ℕ) : Prop :=
  HasUnifEigenvalue f μ k
/-
**Module.End.hasGenEigenvalue_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasGenEigenvalue_iff {f : End R M} {μ : R} {k : Nat} : f.HasGenEigenvalue 
μ k ↔ f.genEigenspace μ k != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasGenEigenvalue_iff {f : End R M} {μ : R} {k : ℕ} :
    f.HasGenEigenvalue μ k ↔ f.genEigenspace μ k ≠ ⊥ := Iff.rfl

/-- The exponent of a generalized eigenvalue is never 0. -/
/-
**Module.End.exp_ne_zero_of_hasGenEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd`。
形式化陈述：exp_ne_zero_of_hasGenEigenvalue {f : End R M} {μ : R} {k : Nat} (h : f.Has
GenEigenvalue μ k) : k != 0
参数：h : f.HasGenEigenvalue μ k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.exp_ne_zero`：∀ {R : Type v} {M : Type w} [i
nst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : 
Module.End R M} {μ : R} {k : ℕ…

--- 原说明 ---
The exponent of a generalized eigenvalue is never 0.
-/
theorem exp_ne_zero_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (h : f.HasGenEigenvalue μ k) : k ≠ 0 :=
  HasUnifEigenvalue.exp_ne_zero h

/-- The union of the kernels of `(f - μ • id) ^ k` over all `k`. -/
/-
**Module.End.maxGenEigenspace** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：maxGenEigenspace (f : End R M) (μ : R) : Submodule R M
参数：f : End R M；μ : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The union of the kernels of `(f - μ • id) ^ k` over all `k`.
-/
abbrev maxGenEigenspace (f : End R M) (μ : R) : Submodule R M :=
  genEigenspace f μ ⊤
/-
**Module.End.iSup_genEigenspace_eq** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：iSup_genEigenspace_eq (f : End R M) (μ : R) : ⨆ k : Nat, (f.genEigenspace 
μ) k = f.maxGenEigenspace μ
参数：f : End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_top`：genEigenspace_top (f : End R M) (μ : R) : 
f.genEigenspace μ ⊤ = ⨆ k : Nat, f.genEigenspace μ k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_genEigenspace_eq (f : End R M) (μ : R) :
    ⨆ k : ℕ, (f.genEigenspace μ) k = f.maxGenEigenspace μ := by
  simp_rw [maxGenEigenspace, genEigenspace_top]
/-
**Module.End.genEigenspace_le_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_le_maximal (f : End R M) (μ : R) (k : Nat) : f.genEigenspace
 μ k <= f.maxGenEigenspace μ
参数：f : End R M；μ : R；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem genEigenspace_le_maximal (f : End R M) (μ : R) (k : ℕ) :
    f.genEigenspace μ k ≤ f.maxGenEigenspace μ :=
  (f.genEigenspace μ).monotone le_top

@[simp]
/-
**Module.End.mem_maxGenEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：mem_maxGenEigenspace (f : End R M) (μ : R) (m : M) : m in f.maxGenEigenspa
ce μ ↔ exists k : Nat, ((f - μ • (1 : End R M)) ^ k) m = 0
参数：f : End R M；μ : R；m : M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.mem_genEigenspace_top`：mem_genEigenspace_top {f : End R M} {μ
 : R} {x : M} : x in f.genEigenspace μ ⊤ ↔ exists k : Nat, x in LinearMap.ker ((
f - μ • 1) ^ k)
-/
theorem mem_maxGenEigenspace (f : End R M) (μ : R) (m : M) :
    m ∈ f.maxGenEigenspace μ ↔ ∃ k : ℕ, ((f - μ • (1 : End R M)) ^ k) m = 0 :=
  mem_genEigenspace_top

/-- If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` is the
maximal generalized eigenspace, then this value is the least such `k`. If not, this value is not
meaningful. -/
/-
**Module.End.maxGenEigenspaceIndex** 是 Mathlib 中的一个缩写定义，位于命名空间 `Module.End`。
形式化陈述：maxGenEigenspaceIndex (f : End R M) (μ : R)
参数：f : End R M；μ : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If there exists a natural number `k` such that the kernel of `(f - μ • id) ^ k` 
is the
maximal generalized eigenspace, then this value is the least such `k`. If not, t
his value is not
meaningful.
-/
noncomputable abbrev maxGenEigenspaceIndex (f : End R M) (μ : R) :=
  maxUnifEigenspaceIndex f μ

/-- For an endomorphism of a Noetherian module, the maximal eigenspace is always of the form kernel
`(f - μ • id) ^ k` for some `k`. -/
/-
**Module.End.maxGenEigenspace_eq** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：maxGenEigenspace_eq [IsNoetherian R M] (f : End R M) (μ : R) : maxGenEigen
space f μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ)
参数：f : End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex`：genEigenspace_to
p_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) : genEigens
pace f μ ⊤ = f.genEigenspace μ (maxUnifEigen…

--- 原说明 ---
For an endomorphism of a Noetherian module, the maximal eigenspace is always of 
the form kernel
`(f - μ • id) ^ k` for some `k`.
-/
theorem maxGenEigenspace_eq [IsNoetherian R M] (f : End R M) (μ : R) :
    maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspaceIndex f μ) :=
  genEigenspace_top_eq_maxUnifEigenspaceIndex _ _
/-
**Module.End.maxGenEigenspace_eq_maxGenEigenspace_zero** 是 Mathlib 中的一个定理，位于命名空间
 `Module.End`。
形式化陈述：maxGenEigenspace_eq_maxGenEigenspace_zero (f : End R M) (μ : R) : maxGenEi
genspace f μ = maxGenEigenspace (f - μ • 1) 0
参数：f : End R M；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem maxGenEigenspace_eq_maxGenEigenspace_zero (f : End R M) (μ : R) :
    maxGenEigenspace f μ = maxGenEigenspace (f - μ • 1) 0 := by
  ext; simp

/-- A generalized eigenvalue for some exponent `k` is also
a generalized eigenvalue for exponents larger than `k`. -/
/-
**Module.End.hasGenEigenvalue_of_hasGenEigenvalue_of_le** 是 Mathlib 中的一个定理，位于命名空
间 `Module.End`。
形式化陈述：hasGenEigenvalue_of_hasGenEigenvalue_of_le {f : End R M} {μ : R} {k : Nat}
 {m : Nat} (hm : k <= m) (hk : f.HasGenEigenvalue μ k) : f.HasGenEigenvalue μ m
参数：hm : k <= m；hk : f.HasGenEigenvalue μ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.le`：∀ {R : Type v} {M : Type w} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.En
d R M} {μ : R} {k m :…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
A generalized eigenvalue for some exponent `k` is also
a generalized eigenvalue for exponents larger than `k`.
-/
theorem hasGenEigenvalue_of_hasGenEigenvalue_of_le {f : End R M} {μ : R} {k : ℕ}
    {m : ℕ} (hm : k ≤ m) (hk : f.HasGenEigenvalue μ k) :
    f.HasGenEigenvalue μ m :=
  hk.le <| by simpa using hm

/-- The eigenspace is a subspace of the generalized eigenspace. -/
/-
**Module.End.eigenspace_le_genEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：eigenspace_le_genEigenspace {f : End R M} {μ : R} {k : Nat} (hk : 0 < k) :
 f.eigenspace μ <= f.genEigenspace μ k
参数：hk : 0 < k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m

--- 原说明 ---
The eigenspace is a subspace of the generalized eigenspace.
-/
theorem eigenspace_le_genEigenspace {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.eigenspace μ ≤ f.genEigenspace μ k :=
  (f.genEigenspace _).monotone <| by simpa using Nat.succ_le_of_lt hk
/-
**Module.End.eigenspace_le_maxGenEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module.En
d`。
形式化陈述：eigenspace_le_maxGenEigenspace {f : End R M} {μ : R} : f.eigenspace μ <= f
.maxGenEigenspace μ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `OrderTop.le_top`：∀ {α : Type u} {inst : LE α} [self : OrderTop α] (a : α
), a ≤ ⊤
-/
theorem eigenspace_le_maxGenEigenspace {f : End R M} {μ : R} :
    f.eigenspace μ ≤ f.maxGenEigenspace μ :=
  (f.genEigenspace _).monotone <| OrderTop.le_top _

/-- All eigenvalues are generalized eigenvalues. -/
/-
**Module.End.hasGenEigenvalue_of_hasEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Module
.End`。
形式化陈述：hasGenEigenvalue_of_hasEigenvalue {f : End R M} {μ : R} {k : Nat} (hk : 0 
< k) (hμ : f.HasEigenvalue μ) : f.HasGenEigenvalue μ k
参数：hk : 0 < k；hμ : f.HasEigenvalue μ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.lt`：∀ {R : Type v} {M : Type w} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.En
d R M} {μ : R} {k m :…
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞

--- 原说明 ---
All eigenvalues are generalized eigenvalues.
-/
theorem hasGenEigenvalue_of_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k)
    (hμ : f.HasEigenvalue μ) : f.HasGenEigenvalue μ k :=
  hμ.lt <| by simpa using hk

/-- All generalized eigenvalues are eigenvalues. -/
/-
**Module.End.hasEigenvalue_of_hasGenEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Module
.End`。
形式化陈述：hasEigenvalue_of_hasGenEigenvalue {f : End R M} {μ : R} {k : Nat} (hμ : f.
HasGenEigenvalue μ k) : f.HasEigenvalue μ
参数：hμ : f.HasGenEigenvalue μ k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.HasUnifEigenvalue.lt`：∀ {R : Type v} {M : Type w} [inst : Com
mRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.En
d R M} {μ : R} {k m :…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞

--- 原说明 ---
All generalized eigenvalues are eigenvalues.
-/
theorem hasEigenvalue_of_hasGenEigenvalue {f : End R M} {μ : R} {k : ℕ}
    (hμ : f.HasGenEigenvalue μ k) : f.HasEigenvalue μ :=
  hμ.lt zero_lt_one

/-- Generalized eigenvalues are actually just eigenvalues. -/
/-
**Module.End.hasGenEigenvalue_iff_hasEigenvalue** 是 Mathlib 中的一个定理，位于命名空间 `Modul
e.End`。
形式化陈述：hasGenEigenvalue_iff_hasEigenvalue {f : End R M} {μ : R} {k : Nat} (hk : 0
 < k) : f.HasGenEigenvalue μ k ↔ f.HasEigenvalue μ
参数：hk : 0 < k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instNontrivialENat`：Nontrivial ℕ∞
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `instCanonicallyOrderedAddENat`：CanonicallyOrderedAdd ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Generalized eigenvalues are actually just eigenvalues.
-/
theorem hasGenEigenvalue_iff_hasEigenvalue {f : End R M} {μ : R} {k : ℕ} (hk : 0 < k) :
    f.HasGenEigenvalue μ k ↔ f.HasEigenvalue μ := by
  simp [hk]
/-
**Module.End.maxGenEigenspace_eq_genEigenspace_finrank** 是 Mathlib 中的一个定理，位于命名空间
 `Module.End`。
形式化陈述：maxGenEigenspace_eq_genEigenspace_finrank [FiniteDimensional K V] (f : End
 K V) (μ : K) : f.maxGenEigenspace μ = f.genEigenspace μ (finrank K V)
参数：f : End K V；μ : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_top_eq_maxUnifEigenspaceIndex`：genEigenspace_to
p_eq_maxUnifEigenspaceIndex [IsNoetherian R M] (f : End R M) (μ : R) : genEigens
pace f μ ⊤ = f.genEigenspace μ (maxUnifEigen…
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用引理 `Module.End.genEigenspace_le_genEigenspace_finrank`：genEigenspace_le_genE
igenspace_finrank [FiniteDimensional K V] (f : End K V) (μ : K) (k : Nat∞) : f.g
enEigenspace μ k <= f.genEigenspace μ (…
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem maxGenEigenspace_eq_genEigenspace_finrank
    [FiniteDimensional K V] (f : End K V) (μ : K) :
    f.maxGenEigenspace μ = f.genEigenspace μ (finrank K V) := by
  apply le_antisymm _ <| (f.genEigenspace μ).monotone le_top
  rw [genEigenspace_top_eq_maxUnifEigenspaceIndex]
  apply genEigenspace_le_genEigenspace_finrank f μ
/-
**Module.End.mapsTo_maxGenEigenspace_of_comm** 是 Mathlib 中的一个引理，位于命名空间 `Module.E
nd`。
形式化陈述：mapsTo_maxGenEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) 
: MapsTo g ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ)
参数：h : Commute f g；μ : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
-/
lemma mapsTo_maxGenEigenspace_of_comm {f g : End R M} (h : Commute f g) (μ : R) :
    MapsTo g ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
  mapsTo_genEigenspace_of_comm h μ ⊤

/-- The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nilpotent. -/
/-
**Module.End.isNilpotent_restrict_sub_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `Modu
le.End`。
形式化陈述：isNilpotent_restrict_sub_algebraMap (f : End R M) (μ : R) (k : Nat) (h : M
apsTo (f - algebraMap R (End R M) μ) (f.genEigenspace μ k) (f.genEigenspace μ k)
参数：f : End R M；μ : R；k : Nat。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.isNilpotent_restrict_genEigenspace_nat`：isNilpotent_restrict_
genEigenspace_nat (f : End R M) (μ : R) (k : Nat) (h : MapsTo (f - μ • (1 : End 
R M)) (f.genEigenspace μ k) (f.genEigen…
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x

--- 原说明 ---
The restriction of `f - μ • 1` to the `k`-fold generalized `μ`-eigenspace is nil
potent.
-/
lemma isNilpotent_restrict_sub_algebraMap (f : End R M) (μ : R) (k : ℕ)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      (f.genEigenspace μ k) (f.genEigenspace μ k) :=
      mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ k) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) :=
  isNilpotent_restrict_genEigenspace_nat _ _ _

/-- The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent. -/
/-
**Module.End.isNilpotent_restrict_maxGenEigenspace_sub_algebraMap** 是 Mathlib 中的
一个引理，位于命名空间 `Module.End`。
形式化陈述：isNilpotent_restrict_maxGenEigenspace_sub_algebraMap [IsNoetherian R M] (f
 : End R M) (μ : R) (h : MapsTo (f - algebraMap R (End R M) μ) ↑(f.maxGenEigensp
ace μ) ↑(f.maxGenEigenspace μ)
参数：f : End R M；μ : R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.isNilpotent_restrict_of_le`：isNilpotent_restrict_of_le {f : E
nd R M} {p q : Submodule R M} {hp : MapsTo f p p} {hq : MapsTo f q q} (h : p <= 
q) (hf : IsNilpotent (f.res…
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.maxGenEigenspace_eq`：maxGenEigenspace_eq [IsNoetherian R M] (
f : End R M) (μ : R) : maxGenEigenspace f μ = f.genEigenspace μ (maxGenEigenspac
eIndex f μ)
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `Module.End.isNilpotent_restrict_genEigenspace_nat`：isNilpotent_restrict_
genEigenspace_nat (f : End R M) (μ : R) (k : Nat) (h : MapsTo (f - μ • (1 : End 
R M)) (f.genEigenspace μ k) (f.genEigen…

--- 原说明 ---
The restriction of `f - μ • 1` to the generalized `μ`-eigenspace is nilpotent.
-/
lemma isNilpotent_restrict_maxGenEigenspace_sub_algebraMap [IsNoetherian R M] (f : End R M) (μ : R)
    (h : MapsTo (f - algebraMap R (End R M) μ)
      ↑(f.maxGenEigenspace μ) ↑(f.maxGenEigenspace μ) :=
      mapsTo_maxGenEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ) μ) :
    IsNilpotent ((f - algebraMap R (End R M) μ).restrict h) := by
  apply isNilpotent_restrict_of_le (q := f.genEigenspace μ (maxUnifEigenspaceIndex f μ))
    _ (isNilpotent_restrict_genEigenspace_nat f μ (maxUnifEigenspaceIndex f μ))
  rw [maxGenEigenspace_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.disjoint_genEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：disjoint_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) {μ₁ 
μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disjoint (f.genEigenspace μ₁ k) (f.genEig
enspace μ₂ l)
参数：f : End R M；hμ : μ₁ != μ₂；k l : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_eq_iSup_genEigenspace_nat`：genEigenspace_eq_iSu
p_genEigenspace_nat (f : End R M) (μ : R) (k : Nat∞) : f.genEigenspace μ k = ⨆ l
 : {l : Nat // l <= k}, f.genEigenspace …
· 使用定理 `Directed.disjoint_iSup_left`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Com
pleteLattice α] {f : ι → α} [IsCompactlyGenerated α] {a : α},   Directed (fun x1
 x2 => x1 ≤ x2) f…
· 使用定理 `Submodule.instIsCompactlyGenerated`：∀ {R : Type u_1} {M : Type u_4} [ins
t : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsCom
pactlyGenerated (Submodu…
· 使用引理 `Module.End.genEigenspace_directed`：genEigenspace_directed {f : End R M} 
{μ : R} {k : Nat∞} : Directed (· <= ·) (fun l : {l : Nat // l <= k} => f.genEige
nspace μ l)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Directed.disjoint_iSup_right`：∀ {ι : Sort u_1} {α : Type u_2} [inst : Co
mpleteLattice α] {f : ι → α} [IsCompactlyGenerated α] {a : α},   Directed (fun x
1 x2 => x1 ≤ x2) f…
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.nontrivial_iff_ne_bot`：nontrivial_iff_ne_bot : Nontrivial p ↔ 
p != ⊥
· 使用定理 `Set.MapsTo.inter_inter`：∀ {α : Type u_1} {β : Type u_2} {s₁ s₂ : Set α} 
{t₁ t₂ : Set β} {f : α → β},   Set.MapsTo f s₁ t₁ → Set.MapsTo f s₂ t₂ → Set.Map
sTo f (s₁ ∩ …
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `Algebra.mul_sub_algebraMap_commutes`：mul_sub_algebraMap_commutes [Ring A
] [Algebra R A] (x : A) (r : R) : x * (x - algebraMap R A r) = (x - algebraMap R
 A r) * x
· 使用定理 `Commute.isNilpotent_sub`：isNilpotent_sub (h_comm : Commute x y) (hx : Is
Nilpotent x) (hy : IsNilpotent y) : IsNilpotent (x - y)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_sub_left_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a 
b c : α), a + (b - c) = b + (a - c)
（共 50 条，此处仅展示前 30 条）
-/
lemma disjoint_genEigenspace [IsDomain R] [IsTorsionFree R M]
    (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ ≠ μ₂) (k l : ℕ∞) :
    Disjoint (f.genEigenspace μ₁ k) (f.genEigenspace μ₂ l) := by
  rw [genEigenspace_eq_iSup_genEigenspace_nat, genEigenspace_eq_iSup_genEigenspace_nat]
  simp_rw [genEigenspace_directed.disjoint_iSup_left, genEigenspace_directed.disjoint_iSup_right]
  rintro ⟨k, -⟩ ⟨l, -⟩
  nontriviality M
  rw [disjoint_iff]
  set p := f.genEigenspace μ₁ k ⊓ f.genEigenspace μ₂ l
  by_contra hp
  replace hp : Nontrivial p := Submodule.nontrivial_iff_ne_bot.mpr hp
  let f₁ : End R p := (f - algebraMap R (End R M) μ₁).restrict <| MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₁) μ₂ l)
  let f₂ : End R p := (f - algebraMap R (End R M) μ₂).restrict <| MapsTo.inter_inter
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₁ k)
    (mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f μ₂) μ₂ l)
  have : IsNilpotent (f₂ - f₁) := by
    apply Commute.isNilpotent_sub (x := f₂) (y := f₁) _
      (isNilpotent_restrict_of_le inf_le_right _)
      (isNilpotent_restrict_of_le inf_le_left _)
    · ext; simp [f₁, f₂, smul_sub, sub_sub, smul_comm μ₁, add_sub_left_comm]
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    · apply isNilpotent_restrict_genEigenspace_nat
    · apply mapsTo_genEigenspace_of_comm (Algebra.mul_sub_algebraMap_commutes f _)
    apply isNilpotent_restrict_genEigenspace_nat
  have hf₁₂ : f₂ - f₁ = algebraMap R (End R p) (μ₁ - μ₂) := by ext; simp [f₁, f₂]
  rw [hf₁₂, IsNilpotent.map_iff (FaithfulSMul.algebraMap_injective R (End R p)),
    isNilpotent_iff_eq_zero, sub_eq_zero] at this
  contradiction
/-
**Module.End.injOn_genEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：injOn_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : Na
t∞) : InjOn (f.genEigenspace · k) {μ | f.genEigenspace μ k != ⊥}
参数：f : End R M；k : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.disjoint_genEigenspace`：disjoint_genEigenspace [IsDomain R] [
IsTorsionFree R M] (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disj
oint (f.genEigenspace μ…
-/
lemma injOn_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : ℕ∞) :
    InjOn (f.genEigenspace · k) {μ | f.genEigenspace μ k ≠ ⊥} := by
  rintro μ₁ _ μ₂ hμ₂ hμ₁₂
  by_contra contra
  apply hμ₂
  simpa only [hμ₁₂, disjoint_self] using f.disjoint_genEigenspace contra k k
/-
**Module.End.injOn_maxGenEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：injOn_maxGenEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) : In
jOn (f.maxGenEigenspace ·) {μ | f.maxGenEigenspace μ != ⊥}
参数：f : End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.End.injOn_genEigenspace`：injOn_genEigenspace [IsDomain R] [IsTors
ionFree R M] (f : End R M) (k : Nat∞) : InjOn (f.genEigenspace · k) {μ | f.genEi
genspace μ k != ⊥}
-/
lemma injOn_maxGenEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) :
    InjOn (f.maxGenEigenspace ·) {μ | f.maxGenEigenspace μ ≠ ⊥} :=
  injOn_genEigenspace f ⊤
/-
**Module.End.independent_genEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：independent_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) (
k : Nat∞) : iSupIndep (f.genEigenspace · k)
参数：f : End R M；k : Nat∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sup_empty`：sup_empty : (∅ : Finset β).sup f = ⊥
· 使用定理 `not_or`：∀ {p q : Prop}, ¬(p ∨ q) ↔ ¬p ∧ ¬q
· 使用定理 `Finset.mem_insert`：mem_insert : a in insert b s ↔ a = b ∨ a in s
· 使用定理 `Finset.sup_insert`：sup_insert [DecidableEq β] {b : β} : (insert b s : Fi
nset β).sup f = f b ⊔ s.sup f
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用引理 `Module.End.mapsTo_genEigenspace_of_comm`：mapsTo_genEigenspace_of_comm {f
 g : End R M} (h : Commute f g) (μ : R) (k : Nat∞) : MapsTo g (f.genEigenspace μ
 k) (f.genEigenspace μ k)
· 使用定理 `Algebra.mul_sub_algebraMap_pow_commutes`：mul_sub_algebraMap_pow_commutes
 [Ring A] [Algebra R A] (x : A) (r : R) (n : Nat) : x * (x - algebraMap R A r) ^
 n = (x - algebraMap R A r) ^…
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Finset.sup_eq_iSup`：sup_eq_iSup [CompleteLattice β] (s : Finset α) (f : 
α -> β) : s.sup f = ⨆ a in s, f a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_iSup`：map_iSup {ι : Sort*} (f : M ->ₛₗ[σ₁₂] M₂) (p : ι -> 
Submodule R M) : map f (⨆ i, p i) = ⨆ i, map f (p i)
· 使用定理 `iSup₂_mono`：iSup₂_mono {f g : forall i, κ i -> α} (h : forall i j, f i j
 <= g i j) : ⨆ (i) (j), f i j <= ⨆ (i) (j), g i j
· 使用定理 `Submodule.mem_map_of_mem`：mem_map_of_mem {f : M ->ₛₗ[σ₁₂] M₂} {p : Submo
dule R M} {r} (h : r in p) : f r in map f p
· 使用定理 `Submodule.mem_bot`：mem_bot {x : M} : x in (⊥ : Submodule R M) ↔ x = 0
（共 36 条，此处仅展示前 30 条）
-/
theorem independent_genEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) (k : ℕ∞) :
    iSupIndep (f.genEigenspace · k) := by
  classical
  suffices ∀ μ₁ (s : Finset R), μ₁ ∉ s → Disjoint (f.genEigenspace μ₁ k)
    (s.sup fun μ ↦ f.genEigenspace μ k) by
    simp_rw [iSupIndep_iff_supIndep,
      Finset.supIndep_iff_disjoint_erase]
    exact fun s μ _ ↦ this _ _ (s.notMem_erase μ)
  intro μ₁ s
  induction s using Finset.induction_on with
  | empty => simp
  | insert μ₂ s _ ih =>
  intro hμ₁₂
  obtain ⟨hμ₁₂ : μ₁ ≠ μ₂, hμ₁ : μ₁ ∉ s⟩ := by rwa [Finset.mem_insert, not_or] at hμ₁₂
  specialize ih hμ₁
  rw [Finset.sup_insert, disjoint_iff, Submodule.eq_bot_iff]
  rintro x ⟨hx, hx'⟩
  simp only [SetLike.mem_coe] at hx hx'
  suffices x ∈ genEigenspace f μ₂ k by
    rw [← Submodule.mem_bot (R := R), ← (f.disjoint_genEigenspace hμ₁₂ k k).eq_bot]
    exact ⟨hx, this⟩
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx'; clear hx'
  let g := f - μ₂ • 1
  simp_rw [mem_genEigenspace, ← exists_prop] at hy ⊢
  peel hy with l hlk hl
  simp only [LinearMap.mem_ker] at hl
  have hyz : (g ^ l) (y + z) ∈
      (f.genEigenspace μ₁ k) ⊓ s.sup fun μ ↦ f.genEigenspace μ k := by
    refine ⟨f.mapsTo_genEigenspace_of_comm (g := g ^ l) ?_ μ₁ k hx, ?_⟩
    · exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
    · rw [SetLike.mem_coe, map_add, hl, zero_add]
      suffices (s.sup fun μ ↦ f.genEigenspace μ k).map (g ^ l) ≤
          s.sup fun μ ↦ f.genEigenspace μ k by exact this (Submodule.mem_map_of_mem hz)
      simp_rw [Finset.sup_eq_iSup, Submodule.map_iSup (ι := R), Submodule.map_iSup (ι := _ ∈ s)]
      refine iSup₂_mono fun μ _ ↦ ?_
      rintro - ⟨u, hu, rfl⟩
      refine f.mapsTo_genEigenspace_of_comm ?_ μ k hu
      exact Algebra.mul_sub_algebraMap_pow_commutes f μ₂ l
  rwa [ih.eq_bot, Submodule.mem_bot] at hyz
/-
**Module.End.independent_maxGenEigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`
。
形式化陈述：independent_maxGenEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M
) : iSupIndep f.maxGenEigenspace
参数：f : End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.independent_genEigenspace`：independent_genEigenspace [IsDomai
n R] [IsTorsionFree R M] (f : End R M) (k : Nat∞) : iSupIndep (f.genEigenspace ·
 k)
-/
theorem independent_maxGenEigenspace [IsDomain R] [IsTorsionFree R M] (f : End R M) :
    iSupIndep f.maxGenEigenspace := by
  apply independent_genEigenspace

/-- The eigenspaces of a linear operator form an independent family of subspaces of `M`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspaces. -/
/-
**Module.End.eigenspaces_iSupIndep** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：eigenspaces_iSupIndep [IsDomain R] [IsTorsionFree R M] (f : End R M) : iSu
pIndep f.eigenspace
参数：f : End R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.independent_genEigenspace`：independent_genEigenspace [IsDomai
n R] [IsTorsionFree R M] (f : End R M) (k : Nat∞) : iSupIndep (f.genEigenspace ·
 k)

--- 原说明 ---
The eigenspaces of a linear operator form an independent family of subspaces of 
`M`.  That is,
any eigenspace has trivial intersection with the span of all the other eigenspac
es.
-/
theorem eigenspaces_iSupIndep [IsDomain R] [IsTorsionFree R M] (f : End R M) :
    iSupIndep f.eigenspace :=
  f.independent_genEigenspace 1

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
independent. -/
/-
**Module.End.eigenvectors_linearIndependent'** 是 Mathlib 中的一个定理，位于命名空间 `Module.E
nd`。
形式化陈述：eigenvectors_linearIndependent' {ι : Type*} [IsDomain R] [IsTorsionFree R 
M] (f : End R M) (μ : ι -> R) (hμ : Function.Injective μ) (v : ι -> M) (h_eigenv
ec : forall i, f.HasEigenvector (μ i) (v i)) : LinearIndependent R v
参数：f : End R M；μ : ι -> R；hμ : Function.Injective μ；v : ι -> M；h_eigenvec : fora
ll i, f.HasEigenvector (μ i) (v i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.linearIndependent`：iSupIndep.linearIndependent [IsDomain R] [I
sTorsionFree R N] {ι : Type*} (p : ι -> Submodule R N) (hp : iSupIndep p) {v : ι
 -> N} (hv : fora…
· 使用定理 `iSupIndep.comp`：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι}
 (ht : iSupIndep t) (hf : Injective f) : iSupIndep (t ∘ f)
· 使用定理 `Module.End.eigenspaces_iSupIndep`：eigenspaces_iSupIndep [IsDomain R] [Is
TorsionFree R M] (f : End R M) : iSupIndep f.eigenspace
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Eigenvectors corresponding to distinct eigenvalues of a linear operator are line
arly
independent.
-/
theorem eigenvectors_linearIndependent' {ι : Type*} [IsDomain R] [IsTorsionFree R M]
    (f : End R M) (μ : ι → R) (hμ : Function.Injective μ) (v : ι → M)
    (h_eigenvec : ∀ i, f.HasEigenvector (μ i) (v i)) : LinearIndependent R v :=
  f.eigenspaces_iSupIndep.comp hμ |>.linearIndependent _
    (fun i ↦ h_eigenvec i |>.left) (fun i ↦ h_eigenvec i |>.right)

/-- Eigenvectors corresponding to distinct eigenvalues of a linear operator are linearly
independent. (Lemma 5.11 of [axler2024])

We use the eigenvalues as indexing set to ensure that there is only one eigenvector for each
eigenvalue in the image of `xs`.
See `Module.End.eigenvectors_linearIndependent'` for an indexed variant. -/
/-
**Module.End.eigenvectors_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Module.En
d`。
形式化陈述：eigenvectors_linearIndependent [IsDomain R] [IsTorsionFree R M] (f : End R
 M) (μs : Set R) (xs : μs -> M) (h_eigenvec : forall μ : μs, f.HasEigenvector μ 
(xs μ)) : LinearIndependent R xs
参数：f : End R M；μs : Set R；xs : μs -> M；h_eigenvec : forall μ : μs, f.HasEigenvec
tor μ (xs μ)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.eigenvectors_linearIndependent'`：eigenvectors_linearIndepende
nt' {ι : Type*} [IsDomain R] [IsTorsionFree R M] (f : End R M) (μ : ι -> R) (hμ 
: Function.Injective μ) (v : ι -…
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))

--- 原说明 ---
Eigenvectors corresponding to distinct eigenvalues of a linear operator are line
arly
independent. (Lemma 5.11 of [axler2024])

We use the eigenvalues as indexing set to ensure that there is only one eigenvec
tor for each
eigenvalue in the image of `xs`.
See `Module.End.eigenvectors_linearIndependent'` for an indexed variant.
-/
theorem eigenvectors_linearIndependent [IsDomain R] [IsTorsionFree R M]
    (f : End R M) (μs : Set R) (xs : μs → M)
    (h_eigenvec : ∀ μ : μs, f.HasEigenvector μ (xs μ)) : LinearIndependent R xs :=
  f.eigenvectors_linearIndependent' (fun μ : μs ↦ μ) Subtype.coe_injective _ h_eigenvec

set_option backward.isDefEq.respectTransparency.types false in
/-- If `f` maps a subspace `p` into itself, then the generalized eigenspace of the restriction
of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`. -/
/-
**Module.End.genEigenspace_restrict** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_restrict (f : End R M) (p : Submodule R M) (k : Nat∞) (μ : R
) (hfp : forall x : M, x in p -> f x in p) : genEigenspace (LinearMap.restrict f
 hfp) μ k = Submodule.comap p.subtype (f.genEigenspace μ k)
参数：f : End R M；p : Submodule R M；k : Nat∞；μ : R；hfp : forall x : M, x in p -> f 
x in p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.restrict_smul_one`：restrict_smul_one {R M : Type*} [CommSemiri
ng R] [AddCommMonoid M] [Module R M] {p : Submodule R M} (μ : R) (h : forall x i
n p, (μ • (1 : Mo…
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用引理 `LinearMap.restrict_sub`：restrict_sub {R R₂ M M₂ : Type*} [Ring R] [Ring 
R₂] {σ₁₂ : R ->+* R₂} [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R₂
 M₂] {p : Su…
· 使用定理 `Module.End.pow_apply_mem_of_forall_mem`：∀ {R : Type u_1} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f
' : M →ₗ[R] M} {p : Submodul…
· 使用定理 `Module.End.pow_restrict`：∀ {R : Type u_1} {M : Type u_5} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : M →ₗ[R] M} 
{p : Submodul…
· 使用定理 `LinearMap.ker_comp_of_ker_eq_bot`：ker_comp_of_ker_eq_bot (f : M ->ₛₗ[τ₁₂
] M₂) {g : M₂ ->ₛₗ[τ₂₃] M₃} (hg : ker g = ⊥) : ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) =
 ker f
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `LinearMap.subtype_comp_restrict`：subtype_comp_restrict {f : M ->ₛₗ[σ₁₂] 
M₂} {p : Submodule R M} {q : Submodule R₂ M₂} (hf : forall x in p, f x in q) : q
.subtype.comp (f.rest…
· 使用定理 `LinearMap.domRestrict.eq_1`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u
_5} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddCo
mmMonoid M] [ins…
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Module.End.mem_genEigenspace`：mem_genEigenspace {f : End R M} {μ : R} {k
 : Nat∞} {x : M} : x in f.genEigenspace μ k ↔ exists l : Nat, l <= k ∧ x in Line
arMap.ker ((f - μ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `f` maps a subspace `p` into itself, then the generalized eigenspace of the r
estriction
of `f` to `p` is the part of the generalized eigenspace of `f` that lies in `p`.
-/
theorem genEigenspace_restrict (f : End R M) (p : Submodule R M) (k : ℕ∞) (μ : R)
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    genEigenspace (LinearMap.restrict f hfp) μ k =
      Submodule.comap p.subtype (f.genEigenspace μ k) := by
  ext x
  suffices ∀ l : ℕ, genEigenspace (LinearMap.restrict f hfp) μ l =
      Submodule.comap p.subtype (f.genEigenspace μ l) by
    simp_rw [mem_genEigenspace, ← mem_genEigenspace_nat, this,
      Submodule.mem_comap, mem_genEigenspace (k := k), mem_genEigenspace_nat]
  intro l
  rw [genEigenspace_nat, genEigenspace_nat, ← LinearMap.restrict_smul_one μ,
    LinearMap.restrict_sub hfp, Module.End.pow_restrict _,
    ← LinearMap.ker_comp_of_ker_eq_bot _ (Submodule.ker_subtype p),
    LinearMap.subtype_comp_restrict, LinearMap.domRestrict, ← LinearMap.ker_comp]
/-
**Module.End._root_.Submodule.inf_genEigenspace** 是 Mathlib 中的一个引理，位于命名空间 `Modul
e.End`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Submodule.inf_genEigenspace (f : End R M) (p : Submodule R M) {k : ℕ∞} {μ : R}
    (hfp : ∀ x : M, x ∈ p → f x ∈ p) :
    p ⊓ f.genEigenspace μ k =
      (genEigenspace (LinearMap.restrict f hfp) μ k).map p.subtype := by
  rw [f.genEigenspace_restrict _ _ _ hfp, Submodule.map_comap_eq, Submodule.range_subtype]

set_option backward.isDefEq.respectTransparency false in
/-
**Module.End.mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo** 是 Mathlib 中的一
个引理，位于命名空间 `Module.End`。
形式化陈述：mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo {p : Submodule R M} (f
 g : End R M) (hf : MapsTo f p p) (hg : MapsTo g p p) {μ₁ μ₂ : R} (h : MapsTo f 
(g.maxGenEigenspace μ₁) (g.maxGenEigenspace μ₂)) : MapsTo (f.restrict hf) (maxGe
nEigenspace (g.restrict hg) μ₁) (maxGenEigenspace (g.restrict hg) μ₂)
参数：f g : End R M；hf : MapsTo f p p；hg : MapsTo g p p；h : MapsTo f (g.maxGenEigen
space μ₁) (g.maxGenEigenspace μ₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearMap.restrict_smul_one`：restrict_smul_one {R M : Type*} [CommSemiri
ng R] [AddCommMonoid M] [Module R M] {p : Submodule R M} (μ : R) (h : forall x i
n p, (μ • (1 : Mo…
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用引理 `LinearMap.restrict_sub`：restrict_sub {R R₂ M M₂ : Type*} [Ring R] [Ring 
R₂] {σ₁₂ : R ->+* R₂} [AddCommGroup M] [AddCommGroup M₂] [Module R M] [Module R₂
 M₂] {p : Su…
· 使用定理 `Module.End.pow_apply_mem_of_forall_mem`：∀ {R : Type u_1} {M : Type u_5} 
[inst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f
' : M →ₗ[R] M} {p : Submodul…
· 使用定理 `Module.End.pow_restrict`：∀ {R : Type u_1} {M : Type u_5} [inst : Semirin
g R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {f' : M →ₗ[R] M} 
{p : Submodul…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma mapsTo_restrict_maxGenEigenspace_restrict_of_mapsTo
    {p : Submodule R M} (f g : End R M) (hf : MapsTo f p p) (hg : MapsTo g p p) {μ₁ μ₂ : R}
    (h : MapsTo f (g.maxGenEigenspace μ₁) (g.maxGenEigenspace μ₂)) :
    MapsTo (f.restrict hf)
      (maxGenEigenspace (g.restrict hg) μ₁)
      (maxGenEigenspace (g.restrict hg) μ₂) := by
  intro x hx
  simp_rw [SetLike.mem_coe, mem_maxGenEigenspace, ← LinearMap.restrict_smul_one _,
    LinearMap.restrict_sub _, Module.End.pow_restrict _, LinearMap.restrict_apply,
    Submodule.mk_eq_zero, ← mem_maxGenEigenspace] at hx ⊢
  exact h hx

/-- If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`. -/
/-
**Module.End.eigenspace_restrict_le_eigenspace** 是 Mathlib 中的一个定理，位于命名空间 `Module
.End`。
形式化陈述：eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp :
 forall x in p, f x in p) (μ : R) : (eigenspace (f.restrict hfp) μ).map p.subtyp
e <= f.eigenspace μ
参数：f : End R M；hfp : forall x in p, f x in p；μ : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If `p` is an invariant submodule of an endomorphism `f`, then the `μ`-eigenspace
 of the
restriction of `f` to `p` is a submodule of the `μ`-eigenspace of `f`.
-/
theorem eigenspace_restrict_le_eigenspace (f : End R M) {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    (μ : R) : (eigenspace (f.restrict hfp) μ).map p.subtype ≤ f.eigenspace μ := by
  rintro a ⟨x, hx, rfl⟩
  simp only [SetLike.mem_coe, mem_eigenspace_iff, LinearMap.restrict_apply] at hx ⊢
  exact congr_arg Subtype.val hx

/-- Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are disjoint. -/
/-
**Module.End.generalized_eigenvec_disjoint_range_ker** 是 Mathlib 中的一个定理，位于命名空间 `
Module.End`。
形式化陈述：generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K
 V) (μ : K) : Disjoint (f.genEigenrange μ (finrank K V)) (f.genEigenspace μ (fin
rank K V))
参数：f : End K V；μ : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenspace_nat`：genEigenspace_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenspace μ k = LinearMap.ker ((f - μ • 1) ^ k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_comp`：ker_comp (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) 
: ker (g.comp f : M ->ₛₗ[τ₁₃] M₃) = comap f (ker g)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.End.genEigenspace_eq_genEigenspace_finrank_of_le`：genEigenspace_e
q_genEigenspace_finrank_of_le [FiniteDimensional K V] (f : End K V) (μ : K) {k :
 Nat} (hk : finrank K V <= k) : f.genEigenspa…
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用引理 `Module.End.genEigenrange_nat`：genEigenrange_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k)
· 使用定理 `LinearMap.range_eq_map`：range_eq_map [RingHomSurjective τ₁₂] (f : M ->ₛₗ
[τ₁₂] M₂) : range f = map f ⊤
· 使用定理 `Submodule.map_inf_eq_map_inf_comap`：map_inf_eq_map_inf_comap [RingHomSur
jective σ₁₂] {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {p' : Submodule R₂ M₂} : m
ap f p ⊓ p' = map f (p ⊓…
· 使用定理 `top_inf_eq`：∀ {α : Type u_1} [inst : SemilatticeInf α] [inst_1 : OrderTo
p α] (a : α), ⊤ ⊓ a = a
· 使用定理 `Submodule.map_comap_le`：map_comap_le [RingHomSurjective σ₁₂] (f : M ->ₛₗ
[σ₁₂] M₂) (q : Submodule R₂ M₂) : map f (comap f q) <= q

--- 原说明 ---
Generalized eigenrange and generalized eigenspace for exponent `finrank K V` are
 disjoint.
-/
theorem generalized_eigenvec_disjoint_range_ker [FiniteDimensional K V] (f : End K V) (μ : K) :
    Disjoint (f.genEigenrange μ (finrank K V))
      (f.genEigenspace μ (finrank K V)) := by
  have h :=
    calc
      Submodule.comap ((f - μ • 1) ^ finrank K V)
        (f.genEigenspace μ (finrank K V)) =
          LinearMap.ker ((f - algebraMap _ _ μ) ^ finrank K V *
            (f - algebraMap K (End K V) μ) ^ finrank K V) := by
              rw [genEigenspace_nat, ← LinearMap.ker_comp]; rfl
      _ = f.genEigenspace μ (finrank K V + finrank K V : ℕ) := by
              simp_rw [← pow_add, genEigenspace_nat]; rfl
      _ = f.genEigenspace μ (finrank K V) := by
              rw [genEigenspace_eq_genEigenspace_finrank_of_le]; lia
  rw [disjoint_iff_inf_le, genEigenrange_nat, LinearMap.range_eq_map,
    Submodule.map_inf_eq_map_inf_comap, top_inf_eq, h, genEigenspace_nat]
  apply Submodule.map_comap_le

/-- If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eigenspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace. -/
/-
**Module.End.eigenspace_restrict_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : forall
 x in p, f x in p) {μ : R} (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.r
estrict hfp) μ = ⊥
参数：hfp : forall x in p, f x in p；hμp : Disjoint (f.eigenspace μ) p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Module.End.eigenspace_restrict_le_eigenspace`：eigenspace_restrict_le_eig
enspace (f : End R M) {p : Submodule R M} (hfp : forall x in p, f x in p) (μ : R
) : (eigenspace (f.restrict hfp) μ…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
If an invariant subspace `p` of an endomorphism `f` is disjoint from the `μ`-eig
enspace of `f`,
then the restriction of `f` to `p` has trivial `μ`-eigenspace.
-/
theorem eigenspace_restrict_eq_bot {f : End R M} {p : Submodule R M} (hfp : ∀ x ∈ p, f x ∈ p)
    {μ : R} (hμp : Disjoint (f.eigenspace μ) p) : eigenspace (f.restrict hfp) μ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  simpa using hμp.le_bot ⟨eigenspace_restrict_le_eigenspace f hfp μ ⟨x, hx, rfl⟩, x.prop⟩

/-- The generalized eigenspace of an eigenvalue has positive dimension for positive exponents. -/
/-
**Module.End.pos_finrank_genEigenspace_of_hasEigenvalue** 是 Mathlib 中的一个定理，位于命名空
间 `Module.End`。
形式化陈述：pos_finrank_genEigenspace_of_hasEigenvalue [FiniteDimensional K V] {f : En
d K V} {k : Nat} {μ : K} (hx : f.HasEigenvalue μ) (hk : 0 < k) : 0 < finrank K (
f.genEigenspace μ k)
参数：hx : f.HasEigenvalue μ；hk : 0 < k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Submodule.finrank_lt_finrank_of_lt`：finrank_lt_finrank_of_lt {s t : Subm
odule K V} [FiniteDimensional K t] (hst : s < t) : finrank K s < finrank K t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Submodule.finrank_mono`：Submodule.finrank_mono {s t : Submodule R M} [Mo
dule.Finite R t] (hst : s <= t) : finrank R s <= finrank R t
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `OrderHom.monotone`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] [
inst_1 : Preorder β] (f : α →o β), Monotone ⇑f
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Nat.succ_le_of_lt`：∀ {n m : ℕ}, n < m → n.succ ≤ m

--- 原说明 ---
The generalized eigenspace of an eigenvalue has positive dimension for positive 
exponents.
-/
theorem pos_finrank_genEigenspace_of_hasEigenvalue [FiniteDimensional K V] {f : End K V}
    {k : ℕ} {μ : K} (hx : f.HasEigenvalue μ) (hk : 0 < k) :
    0 < finrank K (f.genEigenspace μ k) :=
  calc
    0 = finrank K (⊥ : Submodule K V) := by rw [finrank_bot]
    _ < finrank K (f.eigenspace μ) := Submodule.finrank_lt_finrank_of_lt (bot_lt_iff_ne_bot.2 hx)
    _ ≤ finrank K (f.genEigenspace μ k) :=
      Submodule.finrank_mono ((f.genEigenspace μ).monotone (by simpa using Nat.succ_le_of_lt hk))

/-- A linear map maps a generalized eigenrange into itself. -/
/-
**Module.End.map_genEigenrange_le** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：map_genEigenrange_le {f : End K V} {μ : K} {n : Nat} : Submodule.map f (f.
genEigenrange μ n) <= f.genEigenrange μ n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.End.genEigenrange_nat`：genEigenrange_nat {f : End R M} {μ : R} {k
 : Nat} : f.genEigenrange μ k = LinearMap.range ((f - μ • 1) ^ k)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `Algebra.mul_sub_algebraMap_pow_commutes`：mul_sub_algebraMap_pow_commutes
 [Ring A] [Algebra R A] (x : A) (r : R) (n : Nat) : x * (x - algebraMap R A r) ^
 n = (x - algebraMap R A r) ^…
· 使用定理 `LinearMap.map_le_range`：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} {p : Submodule R M} : map f p <= range f

--- 原说明 ---
A linear map maps a generalized eigenrange into itself.
-/
theorem map_genEigenrange_le {f : End K V} {μ : K} {n : ℕ} :
    Submodule.map f (f.genEigenrange μ n) ≤ f.genEigenrange μ n :=
  calc
    Submodule.map f (f.genEigenrange μ n) =
      LinearMap.range (f * (f - algebraMap _ _ μ) ^ n) := by
        rw [genEigenrange_nat]; exact (LinearMap.range_comp _ _).symm
    _ = LinearMap.range ((f - algebraMap _ _ μ) ^ n * f) := by
        rw [Algebra.mul_sub_algebraMap_pow_commutes]
    _ = Submodule.map ((f - algebraMap _ _ μ) ^ n) (LinearMap.range f) := LinearMap.range_comp _ _
    _ ≤ f.genEigenrange μ n := by rw [genEigenrange_nat]; apply LinearMap.map_le_range
/-
**Module.End.genEigenspace_le_smul** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_le_smul (f : Module.End R M) (μ t : R) (k : Nat∞) : (f.genEi
genspace μ k) <= (t • f).genEigenspace (t * μ) k
参数：f : Module.End R M；μ t : R；k : Nat∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `smul_pow`：∀ {M : Type u_1} {N : Type u_2} [inst : Monoid M] [inst_1 : Mo
noid N] [inst_2 : MulAction M N] [IsScalarTower M N N]   [SMulCommClass M N N]…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
-/
lemma genEigenspace_le_smul (f : Module.End R M) (μ t : R) (k : ℕ∞) :
    (f.genEigenspace μ k) ≤ (t • f).genEigenspace (t * μ) k := by
  intro m hm
  simp_rw [mem_genEigenspace, ← exists_prop, LinearMap.mem_ker] at hm ⊢
  peel hm with l hlk hl
  rw [mul_smul, ← smul_sub, smul_pow, LinearMap.smul_apply, hl, smul_zero]
/-
**Module.End.genEigenspace_inf_le_add** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：genEigenspace_inf_le_add (f₁ f₂ : End R M) (μ₁ μ₂ : R) (k₁ k₂ : Nat∞) (h :
 Commute f₁ f₂) : (f₁.genEigenspace μ₁ k₁) ⊓ (f₂.genEigenspace μ₂ k₂) <= (f₁ + f
₂).genEigenspace (μ₁ + μ₂) (k₁ + k₂)
参数：f₁ f₂ : End R M；μ₁ μ₂ : R；k₁ k₂ : Nat∞；h : Commute f₁ f₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `add_sub_add_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b
 c d : α), a + b - (c + d) = a - c + (b - d)
· 使用定理 `Commute.sub_left`：sub_left : Commute a c -> Commute b c -> Commute (a - 
b) c
· 使用定理 `Commute.sub_right`：sub_right : Commute a b -> Commute a c -> Commute a (
b - c)
· 使用引理 `Algebra.commute_algebraMap_right`：commute_algebraMap_right (r : R) (x : 
A) : Commute x (algebraMap R A r)
· 使用引理 `Algebra.commute_algebraMap_left`：commute_algebraMap_left (r : R) (x : A)
 : Commute (algebraMap R A r) x
· 使用定理 `Commute.add_pow'`：add_pow' (h : Commute x y) (n : Nat) : (x + y) ^ n = ∑
 m in antidiagonal n, n.choose m.1 • (x ^ m.1 * y ^ m.2)
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `instIsOrderedRingENat`：IsOrderedRing ℕ∞
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `Commute.eq`：∀ {S : Type u_3} [inst : Mul S] {a b : S}, Commute a b → a *
 b = b * a
· 使用定理 `Commute.pow_pow`：pow_pow (h : Commute a b) (m n : Nat) : Commute (a ^ m)
 (b ^ n)
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `Module.End.pow_map_zero_of_le`：pow_map_zero_of_le {f : End R M} {m : M} 
{k l : Nat} (hk : k <= l) (hm : (f ^ k) m = 0) : (f ^ l) m = 0
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
（共 32 条，此处仅展示前 30 条）
-/
lemma genEigenspace_inf_le_add
    (f₁ f₂ : End R M) (μ₁ μ₂ : R) (k₁ k₂ : ℕ∞) (h : Commute f₁ f₂) :
    (f₁.genEigenspace μ₁ k₁) ⊓ (f₂.genEigenspace μ₂ k₂) ≤
    (f₁ + f₂).genEigenspace (μ₁ + μ₂) (k₁ + k₂) := by
  intro m hm
  simp only [Submodule.mem_inf, mem_genEigenspace, LinearMap.mem_ker] at hm ⊢
  obtain ⟨⟨l₁, hlk₁, hl₁⟩, ⟨l₂, hlk₂, hl₂⟩⟩ := hm
  use l₁ + l₂
  have : f₁ + f₂ - (μ₁ + μ₂) • 1 = (f₁ - μ₁ • 1) + (f₂ - μ₂ • 1) := by
    rw [add_smul]; exact add_sub_add_comm f₁ f₂ (μ₁ • 1) (μ₂ • 1)
  replace h : Commute (f₁ - μ₁ • 1) (f₂ - μ₂ • 1) :=
    (h.sub_right <| Algebra.commute_algebraMap_right μ₂ f₁).sub_left
      (Algebra.commute_algebraMap_left μ₁ _)
  rw [this, h.add_pow', LinearMap.coe_sum, Finset.sum_apply]
  constructor
  · simpa only [Nat.cast_add] using add_le_add hlk₁ hlk₂
  refine Finset.sum_eq_zero fun ⟨i, j⟩ hij ↦ ?_
  suffices (((f₁ - μ₁ • 1) ^ i) * ((f₂ - μ₂ • 1) ^ j)) m = 0 by
    rw [LinearMap.smul_apply, this, smul_zero]
  rw [Finset.mem_antidiagonal] at hij
  obtain hi | hj : l₁ ≤ i ∨ l₂ ≤ j := by lia
  · rw [(h.pow_pow i j).eq, Module.End.mul_apply, Module.End.pow_map_zero_of_le hi hl₁, map_zero]
  · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le hj hl₂, map_zero]
/-
**Module.End.map_smul_of_iInf_genEigenspace_ne_bot** 是 Mathlib 中的一个引理，位于命名空间 `Mo
dule.End`。
形式化陈述：map_smul_of_iInf_genEigenspace_ne_bot [IsDomain R] [IsTorsionFree R M] {L 
F : Type*} [SMul R L] [FunLike F L (End R M)] [MulActionHomClass F R L (End R M)
] (f : F) (μ : L -> R) (k : Nat∞) (h_ne : ⨅ x, (f x).genEigenspace (μ x) k != ⊥)
 (t : R) (x : L) : μ (t • x) = t • μ x
参数：End R M；End R M；f : F；μ : L -> R；k : Nat∞；h_ne : ⨅ x, (f x).genEigenspace (μ 
x) k != ⊥；t : R；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用引理 `Module.End.genEigenspace_le_smul`：genEigenspace_le_smul (f : Module.End 
R M) (μ t : R) (k : Nat∞) : (f.genEigenspace μ k) <= (t • f).genEigenspace (t * 
μ) k
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用引理 `Module.End.disjoint_genEigenspace`：disjoint_genEigenspace [IsDomain R] [
IsTorsionFree R M] (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disj
oint (f.genEigenspace μ…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma map_smul_of_iInf_genEigenspace_ne_bot [IsDomain R] [IsTorsionFree R M]
    {L F : Type*} [SMul R L] [FunLike F L (End R M)] [MulActionHomClass F R L (End R M)] (f : F)
    (μ : L → R) (k : ℕ∞) (h_ne : ⨅ x, (f x).genEigenspace (μ x) k ≠ ⊥)
    (t : R) (x : L) :
    μ (t • x) = t • μ x := by
  by_contra contra
  let g : L → Submodule R M := fun x ↦ (f x).genEigenspace (μ x) k
  have : ⨅ x, g x ≤ g x ⊓ g (t • x) := le_inf_iff.mpr ⟨iInf_le g x, iInf_le g (t • x)⟩
  refine h_ne <| eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_le_smul (f x) (μ x) t k)
  simp only [g, map_smul]
  exact disjoint_genEigenspace (t • f x) (Ne.symm contra) k k
/-
**Module.End.map_add_of_iInf_genEigenspace_ne_bot_of_commute** 是 Mathlib 中的一个引理，
位于命名空间 `Module.End`。
形式化陈述：map_add_of_iInf_genEigenspace_ne_bot_of_commute [IsDomain R] [IsTorsionFre
e R M] {L F : Type*} [Add L] [FunLike F L (End R M)] [AddHomClass F L (End R M)]
 (f : F) (μ : L -> R) (k : Nat∞) (h_ne : ⨅ x, (f x).genEigenspace (μ x) k != ⊥) 
(h : forall x y, Commute (f x) (f y)) (x y : L) : μ (x + y) = μ x + μ y
参数：End R M；End R M；f : F；μ : L -> R；k : Nat∞；h_ne : ⨅ x, (f x).genEigenspace (μ 
x) k != ⊥；h : forall x y, Commute (f x) (f y)；x y : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用引理 `Module.End.genEigenspace_inf_le_add`：genEigenspace_inf_le_add (f₁ f₂ : E
nd R M) (μ₁ μ₂ : R) (k₁ k₂ : Nat∞) (h : Commute f₁ f₂) : (f₁.genEigenspace μ₁ k₁
) ⊓ (f₂.genEigenspace μ₂ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用引理 `Module.End.disjoint_genEigenspace`：disjoint_genEigenspace [IsDomain R] [
IsTorsionFree R M] (f : End R M) {μ₁ μ₂ : R} (hμ : μ₁ != μ₂) (k l : Nat∞) : Disj
oint (f.genEigenspace μ…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma map_add_of_iInf_genEigenspace_ne_bot_of_commute [IsDomain R] [IsTorsionFree R M]
    {L F : Type*} [Add L] [FunLike F L (End R M)] [AddHomClass F L (End R M)] (f : F)
    (μ : L → R) (k : ℕ∞) (h_ne : ⨅ x, (f x).genEigenspace (μ x) k ≠ ⊥)
    (h : ∀ x y, Commute (f x) (f y)) (x y : L) :
    μ (x + y) = μ x + μ y := by
  by_contra contra
  let g : L → Submodule R M := fun x ↦ (f x).genEigenspace (μ x) k
  have : ⨅ x, g x ≤ (g x ⊓ g y) ⊓ g (x + y) :=
    le_inf_iff.mpr ⟨le_inf_iff.mpr ⟨iInf_le g x, iInf_le g y⟩, iInf_le g (x + y)⟩
  refine h_ne <| eq_bot_iff.mpr (le_trans this (disjoint_iff_inf_le.mp ?_))
  apply Disjoint.mono_left (genEigenspace_inf_le_add (f x) (f y) (μ x) (μ y) k k (h x y))
  simp only [g, map_add]
  exact disjoint_genEigenspace (f x + f y) (Ne.symm contra) _ k

section Arithmetic

variable {f : End R M} {μ ρ : R}

/-
**Module.End.hasEigenvalue_neg_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvalue_neg_iff : HasEigenvalue (-f) μ ↔ HasEigenvalue f (-μ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Module.End.eigenspace_def`：eigenspace_def {f : End R M} {μ : R} : f.eige
nspace μ = LinearMap.ker (f - μ • 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ker_neg`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_5} {M₂ :
 Type u_7} [inst : Ring R] [inst_1 : Ring R₂]   [inst_2 : AddCommGroup M] [inst_
3 : Add…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma hasEigenvalue_neg_iff :
    HasEigenvalue (-f) μ ↔ HasEigenvalue f (-μ) := by
  simp only [hasEigenvalue_iff, eigenspace_def]
  rw [← LinearMap.ker_neg]
  simp [add_comm]
/-
**Module.End.hasEigenvalue_add_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvalue_add_iff : HasEigenvalue (f + ρ • .id) μ ↔ HasEigenvalue f (μ
 - ρ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 53 条，此处仅展示前 30 条）
-/
lemma hasEigenvalue_add_iff :
    HasEigenvalue (f + ρ • .id) μ ↔ HasEigenvalue f (μ - ρ) := by
  have aux : f + ρ • .id - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]
/-
**Module.End.hasEigenvalue_add'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ ρ : R}, (ρ • LinearMap.id
 + f).HasEigenvalue μ ↔ f.HasEigenvalue (μ - ρ)
参数：ρ • LinearMap.id + f；μ - ρ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₃`：sub_eq_eval₃ [Ring R] [AddCommGro
up M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::ᵣ l₁)
.eval - l₂.eval = l.eval) :…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 53 条，此处仅展示前 30 条）
-/
lemma hasEigenvalue_add'_iff :
    HasEigenvalue (ρ • .id + f) μ ↔ HasEigenvalue f (μ - ρ) := by
  have aux : ρ • .id + f - μ • 1 = f - (μ - ρ) • 1 := by module
  simp only [hasEigenvalue_iff, eigenspace_def, aux]
/-
**Module.End.hasEigenvalue_sub_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.End`。
形式化陈述：hasEigenvalue_sub_iff : HasEigenvalue (f - ρ • .id) μ ↔ HasEigenvalue f (μ
 + ρ)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `Module.End.hasEigenvalue_add_iff`：hasEigenvalue_add_iff : HasEigenvalue 
(f + ρ • .id) μ ↔ HasEigenvalue f (μ - ρ)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasEigenvalue_sub_iff :
    HasEigenvalue (f - ρ • .id) μ ↔ HasEigenvalue f (μ + ρ) := by
  rw [sub_eq_add_neg, ← neg_smul, hasEigenvalue_add_iff, sub_neg_eq_add]
/-
**Module.End.hasEigenvalue_sub'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type v} {M : Type w} [inst : CommRing R] [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   {f : Module.End R M} {μ ρ : R}, (ρ • LinearMap.id
 - f).HasEigenvalue μ ↔ f.HasEigenvalue (ρ - μ)
参数：ρ • LinearMap.id - f；ρ - μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Module.End.hasEigenvalue_add'_iff`：∀ {R : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   {f : Module.
End R M} {μ ρ : R}, (ρ …
· 使用引理 `Module.End.hasEigenvalue_neg_iff`：hasEigenvalue_neg_iff : HasEigenvalue 
(-f) μ ↔ HasEigenvalue f (-μ)
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma hasEigenvalue_sub'_iff :
    HasEigenvalue (ρ • .id - f) μ ↔ HasEigenvalue f (ρ - μ) := by
  rw [sub_eq_add_neg, hasEigenvalue_add'_iff, hasEigenvalue_neg_iff, neg_sub]

end Arithmetic

end End

end Module

