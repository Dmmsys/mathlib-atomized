/-
Copyright (c) 2026 Daniel Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Morrison
-/
module

public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Basis for `ExteriorAlgebra`
-/

@[expose] public section

namespace ExteriorAlgebra

open Module Set Set.powersetCard exteriorPower

variable {R M : Type*} {m n : ℕ} {I : Type*} [LinearOrder I] [CommRing R]
  [AddCommGroup M] [Module R M] (b : Module.Basis I R M)

/-- The direct sum decomposition of the exterior algebra from the graded algebra structure. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The direct sum decomposition of the exterior algebra from the graded algebra str
ucture.
-/
instance : DirectSum.Decomposition (fun n ↦ ⋀[R]^n M) :=
  GradedRing.toDecomposition (self := ExteriorAlgebra.gradedAlgebra R M)

/-- If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the exterior
algebra of `M` formed by the `n`-fold exterior products of elements of `b` for each `n`. -/
/-
**ExteriorAlgebra._root_.Module.Basis.ExteriorAlgebra** 是 Mathlib 中的一个定义，位于命名空间 
`ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `b` is a basis of `M` (indexed by a linearly ordered type), the basis of the 
exterior
algebra of `M` formed by the `n`-fold exterior products of elements of `b` for e
ach `n`.
-/
noncomputable def _root_.Module.Basis.ExteriorAlgebra : Basis (Finset I) R (ExteriorAlgebra R M) :=
  .reindex
    ((DirectSum.Decomposition.isInternal (fun n => ⋀[R]^n M)).collectedBasis b.exteriorPower)
    Set.powersetCard.prodEquiv
/-
**ExteriorAlgebra.basis_apply** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：basis_apply (s : Finset I) : b.ExteriorAlgebra s = ιMulti_family R s.card 
b (prodEquiv.symm s).2
参数：s : Finset I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_reindex`：coe_reindex : (b.reindex e : ι' -> M) = b ∘ e.
symm
· 使用定理 `DirectSum.IsInternal.collectedBasis_coe`：∀ {R : Type u} [inst : Semiring
 R] {ι : Type v} [dec_ι : DecidableEq ι] {M : Type u_1} [inst_1 : AddCommMonoid 
M]   [inst_2 : _root_.Module …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `exteriorPower.coe_basis`：coe_basis {I : Type*} [LinearOrder I] (b : Basi
s I R M) : DFunLike.coe (b.exteriorPower n) = ιMulti_family R n b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basis_apply (s : Finset I) :
    b.ExteriorAlgebra s = ιMulti_family R s.card b (prodEquiv.symm s).2 := by
  simp [Basis.ExteriorAlgebra]
/-
**ExteriorAlgebra.basis_apply_ofCard** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`
。
形式化陈述：basis_apply_ofCard {s : Finset I} (s_card : s.card = n) : b.ExteriorAlgebr
a s = ιMulti_family R n b (ofCard s_card)
参数：s_card : s.card = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExteriorAlgebra.basis_apply`：basis_apply (s : Finset I) : b.ExteriorAlge
bra s = ιMulti_family R s.card b (prodEquiv.symm s).2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basis_apply_ofCard {s : Finset I} (s_card : s.card = n) :
    b.ExteriorAlgebra s = ιMulti_family R n b (ofCard s_card) := by
  subst s_card
  simp [basis_apply]

variable (s : powersetCard I m) (t : powersetCard I n)
/-
**ExteriorAlgebra.basis_apply_powersetCard** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAl
gebra`。
形式化陈述：basis_apply_powersetCard : b.ExteriorAlgebra s = ιMulti_family R m b s
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExteriorAlgebra.basis_apply_ofCard`：basis_apply_ofCard {s : Finset I} (s
_card : s.card = n) : b.ExteriorAlgebra s = ιMulti_family R n b (ofCard s_card)
· 使用定理 `Set.powersetCard.card_eq`：card_eq (s : Set.powersetCard α n) : (s : Fins
et α).card = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma basis_apply_powersetCard :
    b.ExteriorAlgebra s = ιMulti_family R m b s := by
  simp [basis_apply_ofCard]
/-
**ExteriorAlgebra.basis_eq_coe_basis** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`
。
形式化陈述：basis_eq_coe_basis : b.ExteriorAlgebra s = (b.exteriorPower m s : Exterior
Algebra R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExteriorAlgebra.basis_apply_powersetCard`：basis_apply_powersetCard : b.E
xteriorAlgebra s = ιMulti_family R m b s
· 使用引理 `exteriorPower.basis_apply`：basis_apply {I : Type*} [LinearOrder I] (b : 
Basis I R M) (s : powersetCard I n) : b.exteriorPower n s = ιMulti_family R n b 
s
· 使用定理 `exteriorPower.ιMulti_family_apply_coe`：∀ (R : Type u) [inst : CommRing R
] (n : ℕ) {M : Type u_1} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] 
  {I : Type u_4} [inst_3 : …
-/
lemma basis_eq_coe_basis :
    b.ExteriorAlgebra s = (b.exteriorPower m s : ExteriorAlgebra R M) := by
  rw [basis_apply_powersetCard, exteriorPower.basis_apply, ιMulti_family_apply_coe]
/-
**ExteriorAlgebra.basis_mul_of_not_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorA
lgebra`。
形式化陈述：basis_mul_of_not_disjoint (h : ¬Disjoint s.val t.val) : b.ExteriorAlgebra 
s * b.ExteriorAlgebra t = 0
参数：h : ¬Disjoint s.val t.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `ExteriorAlgebra.basis_apply_powersetCard`：basis_apply_powersetCard : b.E
xteriorAlgebra s = ιMulti_family R m b s
· 使用引理 `ExteriorAlgebra.ιMulti_family_mul_of_not_disjoint`：ιMulti_family_mul_of_
not_disjoint {m n : Nat} {I : Type*} [LinearOrder I] (v : I -> M) (s : powersetC
ard I m) (t : powersetCard I n) (h : ¬D…
-/
lemma basis_mul_of_not_disjoint (h : ¬Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t = 0 := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_not_disjoint R b s t h
/-
**ExteriorAlgebra.basis_mul_of_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgeb
ra`。
形式化陈述：basis_mul_of_disjoint (h : Disjoint s.val t.val) : b.ExteriorAlgebra s * b
.ExteriorAlgebra t = (permOfDisjoint h).sign • b.ExteriorAlgebra (disjUnion h)
参数：h : Disjoint s.val t.val。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ExteriorAlgebra.basis_apply_powersetCard`：basis_apply_powersetCard : b.E
xteriorAlgebra s = ιMulti_family R m b s
· 使用引理 `ExteriorAlgebra.ιMulti_family_mul_of_disjoint`：ιMulti_family_mul_of_disj
oint {m n : Nat} {I : Type*} [LinearOrder I] (v : I -> M) (s : powersetCard I m)
 (t : powersetCard I n) (h : Disjoi…
-/
lemma basis_mul_of_disjoint (h : Disjoint s.val t.val) :
    b.ExteriorAlgebra s * b.ExteriorAlgebra t =
      (permOfDisjoint h).sign • b.ExteriorAlgebra (disjUnion h) := by
  simpa only [basis_apply_powersetCard] using ιMulti_family_mul_of_disjoint R b s t h

end ExteriorAlgebra

