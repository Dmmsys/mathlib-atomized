/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Saturated subgroups

## Tags
subgroup, subgroups

-/

@[expose] public section


namespace Submonoid

variable {G : Type*} [Monoid G]

/-- A submonoid `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with `g^n ∈ H` we have
`n = 0` or `g ∈ H`. We use the name `PowSaturated` to distinguish from `Submonoid.MulSaturated`. -/
@[to_additive
/-- An additive submonoid `H` of `G` is *saturated* if for all `n : ℕ` and `g : G` with
`n•g ∈ H` we have `n = 0` or `g ∈ H`. We use the name `NSMulSaturated` to distinguish from
`Submonoid.MulSaturated`. -/]
/--
Definition of `PowSaturated` / `PowSaturated` 的定义

English:
definition PowSaturated
  signature: (H : Submonoid G)
  body: forall ⦃n g⦄, g ^ n in H -> n = 0 ∨ g in H

@[to_additive]

中文:
定义 PowSaturated
  签名: (H : 子幺半群 G)
  定义体: forall ⦃n g⦄, g ^ n in H -> n = 0 ∨ g in H

@[to_additive]
-/
def PowSaturated (H : Submonoid G) : Prop :=
  forall ⦃n g⦄, g ^ n in H -> n = 0 ∨ g in H

@[to_additive]
/--
theorem `powSaturated_iff_npow` / 定理 `powSaturated_iff_npow`

English:
theorem powSaturated_iff_npow
  given: {H : Submonoid G}
  proof: Iff.rfl

中文:
定理 powSaturated_iff_npow
  条件: {H : 子幺半群 G}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem powSaturated_iff_npow {H : Submonoid G} :
    PowSaturated H ↔ forall (n : Nat) (g : G), g ^ n in H -> n = 0 ∨ g in H :=
  Iff.rfl

end Submonoid

@[deprecated (since := "2026-03-03")] alias Subgroup.Saturated := Submonoid.PowSaturated
@[deprecated (since := "2026-03-03")] alias AddSubgroup.Saturated := AddSubmonoid.NSMulSaturated
@[deprecated (since := "2026-03-03")]
alias Subgroup.saturated_iff_npow := Submonoid.powSaturated_iff_npow
@[deprecated (since := "2026-03-03")]
alias AddSubgroup.saturated_iff_nsmul := AddSubmonoid.nsmulSaturated_iff_nsmul

namespace Subgroup

variable {G : Type*} [Group G]

@[to_additive]
/--
theorem `saturated_iff_zpow` / 定理 `saturated_iff_zpow`

English:
theorem saturated_iff_zpow
  given: {H : Subgroup G}
  proof: by
  refine ⟨fun h n g hgn => ?_, fun h n g hgn => by simpa using h n g (by simpa using hgn)⟩
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using h (by simpa using hgn)

中文:
定理 saturated_iff_zpow
  条件: {H : 子群 G}
  证明: by
  refine ⟨fun h n g hgn => ?_, fun h n g hgn => by simpa using h n g (by simpa using hgn)⟩
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using h (by simpa using hgn)

Depends on / 依赖: eq_nat_or_neg, n.eq_nat_or_neg
-/
theorem saturated_iff_zpow {H : Subgroup G} :
    H.PowSaturated ↔ forall (n : Int) (g : G), g ^ n in H -> n = 0 ∨ g in H := by
  refine ⟨fun h n g hgn => ?_, fun h n g hgn => by simpa using h n g (by simpa using hgn)⟩
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg <;> simpa using h (by simpa using hgn)

end Subgroup

namespace AddSubmonoid

/--
theorem `ker_saturated` / 定理 `ker_saturated`

English:
theorem ker_saturated
  statement: {A₁ A₂ : Type*} [AddGroup A₁] [AddMonoid A₂] [IsAddTorsionFree A₂]
  proof: by simp [NSMulSaturated, or_comm]

中文:
定理 ker_saturated
  结论: {A₁ A₂ : 类型} [加法群 A₁] [加法幺半群 A₂] [是加法无挠 A₂]
  证明: by simp [NSMulSaturated, or_comm]

Depends on / 依赖: NSMulSaturated, or_comm
-/
theorem ker_saturated {A₁ A₂ : Type*} [AddGroup A₁] [AddMonoid A₂] [IsAddTorsionFree A₂]
    (f : A₁ ->+ A₂) : f.ker.NSMulSaturated := by simp [NSMulSaturated, or_comm]

end AddSubmonoid

@[deprecated (since := "2026-03-03")] alias AddSubgroup.ker_saturated := AddSubmonoid.ker_saturated
