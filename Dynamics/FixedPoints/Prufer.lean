/-
Copyright (c) 2022 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Dynamics.FixedPoints.Basic

/-!
# Results about pointwise operations on sets with iteration.
-/

public section


open scoped Pointwise

open Set Function

/-- Let `n : ℤ` and `s` a subset of a commutative group `G` that is invariant under preimage for
the map `x ↦ x^n`. Then `s` is invariant under the pointwise action of the subgroup of elements
`g : G` such that `g^(n^j) = 1` for some `j : ℕ`. (This subgroup is called the Prüfer subgroup when
`G` is the `Circle` and `n` is prime.) -/
@[to_additive
      /-- Let `n : ℤ` and `s` a subset of an additive commutative group `G` that is invariant
      under preimage for the map `x ↦ n • x`. Then `s` is invariant under the pointwise action of
      the additive subgroup of elements `g : G` such that `(n^j) • g = 0` for some `j : ℕ`.
      (This additive subgroup is called the Prüfer subgroup when `G` is the `AddCircle` and `n` is
      prime.) -/]
/-
**smul_eq_self_of_preimage_zpow_eq_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_eq_self_of_preimage_zpow_eq_self {G : Type*} [CommGroup G] {n : Int} 
{s : Set G} (hs : (fun x => x ^ n) ⁻¹' s = s) {g : G} {j : Nat} (hg : g ^ n ^ j 
= 1) : g • s = s
参数：hs : (fun x => x ^ n) ⁻¹' s = s；hg : g ^ n ^ j = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.IsFixedPt.preimage_iterate`：preimage_iterate {s : Set α} (h : I
sFixedPt (Set.preimage f) s) (n : Nat) : IsFixedPt (Set.preimage f^[n]) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `zpow_iterate`：∀ {G : Type u_3} [inst : Group G] (k : ℤ) (n : ℕ), (fun x 
=> x ^ k)^[n] = fun x => x ^ k ^ n
· 使用引理 `iterate_map_mul`：iterate_map_mul {M F : Type*} [Mul M] [FunLike F M M] [
MulHomClass F M M] (f : F) (n : Nat) (x y : M) : f^[n] (x * y) = f^[n] x * f^[n]
 y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `inv_zpow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℤ), a⁻
¹ ^ n = (a ^ n)⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem smul_eq_self_of_preimage_zpow_eq_self {G : Type*} [CommGroup G] {n : ℤ} {s : Set G}
    (hs : (fun x => x ^ n) ⁻¹' s = s) {g : G} {j : ℕ} (hg : g ^ n ^ j = 1) : g • s = s := by
  suffices ∀ {g' : G} (_ : g' ^ n ^ j = 1), g' • s ⊆ s by
    refine le_antisymm (this hg) ?_
    conv_lhs => rw [← smul_inv_smul g s]
    replace hg : g⁻¹ ^ n ^ j = 1 := by rw [inv_zpow, hg, inv_one]
    simp only [smul_set_subset_smul_set_iff, this hg]
  rw [(IsFixedPt.preimage_iterate hs j : (zpowGroupHom n)^[j] ⁻¹' s = s).symm]
  rintro g' hg' - ⟨y, hy, rfl⟩
  change (zpowGroupHom n)^[j] (g' * y) ∈ s
  replace hg' : (zpowGroupHom n)^[j] g' = 1 := by simpa [zpowGroupHom]
  rwa [iterate_map_mul, hg', one_mul]
