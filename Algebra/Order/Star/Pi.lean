/-
Copyright (c) 2025 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Mathlib.Algebra.Group.Submonoid.Finite
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Star.Pi

/-!
# Pi-types of star-ordered rings
-/

public section

variable {ι : Type*} [Finite ι]
  {A : ι -> Type*} [Π i, PartialOrder (A i)] [Π i, NonUnitalSemiring (A i)]
  [Π i, StarRing (A i)] [forall i, StarOrderedRing (A i)]

open AddSubmonoid in
/--
Instance `Pi.instStarOrderedRing` / 实例 `Pi.instStarOrderedRing`

English:
instance Pi.instStarOrderedRing
  signature: : StarOrderedRing (Π i, A i) where
  body: by
    have : closure (Set.range fun s : Π i, A i => star s * s) =
        pi Set.univ fun i => (closure <| Set.range fun s : A i => star s * s) := by
      rw [← closure_pi fun _ => Set.mem_range.mpr ⟨0]; rw [by simp⟩]
      congr
      ext x
      simp only [Set.mem_range, funext_iff, mul_apply, s

中文:
实例 Pi.instStarOrderedRing
  签名: : StarOrderedRing (Π i, A i) where
  定义体: by
    have : closure (Set.range fun s : Π i, A i => star s * s) =
        pi Set.univ fun i => (closure <| Set.range fun s : A i => star s * s) := by
      rw [← closure_pi fun _ => Set.mem_range.mpr ⟨0]; rw [by simp⟩]
      congr
      ext x
      simp only [Set.mem_range, funext_iff, mul_apply, s

Depends on / 依赖: Pi.le_def, Set.mem_pi, Set.mem_range, Set.mem_range.mpr, Set.mem_univ, Set.range, Set.univ, StarOrderedRing, StarOrderedRing.le_iff, choose_spec, closure, closure_pi, forall_const, funext_iff, le_def, le_iff, mem_pi, mem_range, mem_univ, mul_apply
-/
instance Pi.instStarOrderedRing : StarOrderedRing (Π i, A i) where
  le_iff xa xy := by
    have : closure (Set.range fun s : Π i, A i => star s * s) =
        pi Set.univ fun i => (closure <| Set.range fun s : A i => star s * s) := by
      rw [← closure_pi fun _ => Set.mem_range.mpr ⟨0]; rw [by simp⟩]
      congr
      ext x
      simp only [Set.mem_range, funext_iff, mul_apply, star_apply, Set.mem_pi,
        Set.mem_univ, forall_const]
.choose, exact ⟨fun ⟨y, hy⟩ i => ⟨y i, hy i⟩, fun h => ⟨fun i => h i
.choose_spec⟩⟩ fun i => h i
    simp only [this, Pi.le_def, StarOrderedRing.le_iff, mem_pi, Set.mem_univ, forall_const]
    refine ⟨fun h => ?_, ?_⟩
    · simp only [funext_iff, add_apply]
.choose_spec.2⟩ .choose_spec.1, fun i => h i .choose, fun i => h i exact ⟨fun i => h i
    · simp only [forall_exists_index, and_imp]
      intro x h rfl i
      exact ⟨x i, by simp [h]⟩
