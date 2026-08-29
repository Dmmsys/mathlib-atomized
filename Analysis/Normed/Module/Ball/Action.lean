/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth
-/
module

public import Mathlib.Analysis.Normed.Field.UnitBall
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# Multiplicative actions of/on balls and spheres

Let `E` be a normed vector space over a normed field `𝕜`. In this file we define the following
multiplicative actions.

- The closed unit ball in `𝕜` acts on open balls and closed balls centered at `0` in `E`.
- The unit sphere in `𝕜` acts on open balls, closed balls, and spheres centered at `0` in `E`.
-/

public section


open Metric Set

variable {𝕜 𝕜' E : Type*} [NormedField 𝕜] [NormedField 𝕜'] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜' E] {r : Real}

section ClosedBall

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r)
  body: ⟨(c : 𝕜) • ↑x,
mem_ball_zero_iff.2 by
        simpa only [norm_smul, one_mul] using
          mul_lt_mul' (mem_closedBall_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _)
            one_pos⟩

中文:
实例 :
  签名: SMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r)
  定义体: ⟨(c : 𝕜) • ↑x,
mem_ball_zero_iff.2 by
        simpa only [norm_smul, one_mul] using
          mul_lt_mul' (mem_closedBall_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _)
            one_pos⟩

Depends on / 依赖: mem_ball_zero_iff, mem_closedBall_zero_iff, mul_lt_mul, norm_nonneg, norm_smul, one_mul, one_pos
-/
instance : SMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
mem_ball_zero_iff.2 by
        simpa only [norm_smul, one_mul] using
          mul_lt_mul' (mem_closedBall_zero_iff.1 c.2) (mem_ball_zero_iff.1 x.2) (norm_nonneg _)
            one_pos⟩

/--
Instance `mulActionClosedBallBall` / 实例 `mulActionClosedBallBall`

English:
instance mulActionClosedBallBall
  signature: : MulAction (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  body: Subtype.ext one_smul 𝕜 _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

中文:
实例 mulActionClosedBallBall
  签名: : MulAction (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
  定义体: Subtype.ext one_smul 𝕜 _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance mulActionClosedBallBall : MulAction (closedBall (0 : 𝕜) 1) (ball (0 : E) r) where
one_smul _c₂ := Subtype.ext one_smul 𝕜 _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

/--
Instance `continuousSMul_closedBall_ball` / 实例 `continuousSMul_closedBall_ball`

English:
instance continuousSMul_closedBall_ball
  signature: : ContinuousSMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r)
  body: ⟨Continuous.subtype_mk (by fun_prop) _⟩

中文:
实例 continuousSMul_closedBall_ball
  签名: : ContinuousSMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r)
  定义体: ⟨Continuous.subtype_mk (by fun_prop) _⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance continuousSMul_closedBall_ball : ContinuousSMul (closedBall (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r)
  body: ⟨(c : 𝕜) • ↑x,
mem_closedBall_zero_iff.2 by
        simpa only [norm_smul, one_mul] using
          mul_le_mul (mem_closedBall_zero_iff.1 c.2) (mem_closedBall_zero_iff.1 x.2) (norm_nonneg _)
            zero_le_one⟩

中文:
实例 :
  签名: SMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r)
  定义体: ⟨(c : 𝕜) • ↑x,
mem_closedBall_zero_iff.2 by
        simpa only [norm_smul, one_mul] using
          mul_le_mul (mem_closedBall_zero_iff.1 c.2) (mem_closedBall_zero_iff.1 x.2) (norm_nonneg _)
            zero_le_one⟩

Depends on / 依赖: mem_closedBall_zero_iff, mul_le_mul, norm_nonneg, norm_smul, one_mul, zero_le_one
-/
instance : SMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
mem_closedBall_zero_iff.2 by
        simpa only [norm_smul, one_mul] using
          mul_le_mul (mem_closedBall_zero_iff.1 c.2) (mem_closedBall_zero_iff.1 x.2) (norm_nonneg _)
            zero_le_one⟩

/--
Instance `mulActionClosedBallClosedBall` / 实例 `mulActionClosedBallClosedBall`

English:
instance mulActionClosedBallClosedBall
  signature: :
  body: Subtype.ext one_smul 𝕜 _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

中文:
实例 mulActionClosedBallClosedBall
  签名: :
  定义体: Subtype.ext one_smul 𝕜 _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance mulActionClosedBallClosedBall :
    MulAction (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) where
one_smul _ := Subtype.ext one_smul 𝕜 _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

/--
Instance `continuousSMul_closedBall_closedBall` / 实例 `continuousSMul_closedBall_closedBall`

English:
instance continuousSMul_closedBall_closedBall
  signature: :
  body: ⟨Continuous.subtype_mk (by fun_prop) _⟩

中文:
实例 continuousSMul_closedBall_closedBall
  签名: :
  定义体: ⟨Continuous.subtype_mk (by fun_prop) _⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance continuousSMul_closedBall_closedBall :
    ContinuousSMul (closedBall (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end ClosedBall

section Sphere

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (sphere (0 : 𝕜) 1) (ball (0 : E) r)
  body: inclusion sphere_subset_closedBall c • x

中文:
实例 :
  签名: SMul (sphere (0 : 𝕜) 1) (ball (0 : E) r)
  定义体: inclusion sphere_subset_closedBall c • x

Depends on / 依赖: inclusion, sphere_subset_closedBall
-/
instance : SMul (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  smul c x := inclusion sphere_subset_closedBall c • x

/--
Instance `mulActionSphereBall` / 实例 `mulActionSphereBall`

English:
instance mulActionSphereBall
  signature: : MulAction (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  body: Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

中文:
实例 mulActionSphereBall
  签名: : MulAction (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
  定义体: Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance mulActionSphereBall : MulAction (sphere (0 : 𝕜) 1) (ball (0 : E) r) where
one_smul _ := Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

/--
Instance `continuousSMul_sphere_ball` / 实例 `continuousSMul_sphere_ball`

English:
instance continuousSMul_sphere_ball
  signature: : ContinuousSMul (sphere (0 : 𝕜) 1) (ball (0 : E) r)
  body: ⟨Continuous.subtype_mk (by fun_prop) _⟩

中文:
实例 continuousSMul_sphere_ball
  签名: : ContinuousSMul (sphere (0 : 𝕜) 1) (ball (0 : E) r)
  定义体: ⟨Continuous.subtype_mk (by fun_prop) _⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance continuousSMul_sphere_ball : ContinuousSMul (sphere (0 : 𝕜) 1) (ball (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r)
  body: inclusion sphere_subset_closedBall c • x

中文:
实例 :
  签名: SMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r)
  定义体: inclusion sphere_subset_closedBall c • x

Depends on / 依赖: inclusion, sphere_subset_closedBall
-/
instance : SMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  smul c x := inclusion sphere_subset_closedBall c • x

/--
Instance `mulActionSphereClosedBall` / 实例 `mulActionSphereClosedBall`

English:
instance mulActionSphereClosedBall
  signature: : MulAction (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  body: Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

中文:
实例 mulActionSphereClosedBall
  签名: : MulAction (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
  定义体: Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance mulActionSphereClosedBall : MulAction (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) where
one_smul _ := Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

/--
Instance `continuousSMul_sphere_closedBall` / 实例 `continuousSMul_sphere_closedBall`

English:
instance continuousSMul_sphere_closedBall
  signature: :
  body: ⟨Continuous.subtype_mk (by fun_prop) _⟩

中文:
实例 continuousSMul_sphere_closedBall
  签名: :
  定义体: ⟨Continuous.subtype_mk (by fun_prop) _⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance continuousSMul_sphere_closedBall :
    ContinuousSMul (sphere (0 : 𝕜) 1) (closedBall (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r)
  body: ⟨(c : 𝕜) • ↑x,
mem_sphere_zero_iff_norm.2 by
        rw [norm_smul]; rw [mem_sphere_zero_iff_norm.1 c.coe_prop]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [one_mul]⟩

中文:
实例 :
  签名: SMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r)
  定义体: ⟨(c : 𝕜) • ↑x,
mem_sphere_zero_iff_norm.2 by
        rw [norm_smul]; rw [mem_sphere_zero_iff_norm.1 c.coe_prop]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [one_mul]⟩

Depends on / 依赖: c.coe_prop, coe_prop, mem_sphere_zero_iff_norm, norm_smul, one_mul, x.coe_prop
-/
instance : SMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  smul c x :=
    ⟨(c : 𝕜) • ↑x,
mem_sphere_zero_iff_norm.2 by
        rw [norm_smul]; rw [mem_sphere_zero_iff_norm.1 c.coe_prop]; rw [mem_sphere_zero_iff_norm.1 x.coe_prop]; rw [one_mul]⟩

/--
Instance `mulActionSphereSphere` / 实例 `mulActionSphereSphere`

English:
instance mulActionSphereSphere
  signature: : MulAction (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  body: Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

中文:
实例 mulActionSphereSphere
  签名: : MulAction (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
  定义体: Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

Depends on / 依赖: Subtype, Subtype.ext, one_smul
-/
instance mulActionSphereSphere : MulAction (sphere (0 : 𝕜) 1) (sphere (0 : E) r) where
one_smul _ := Subtype.ext one_smul _ _
mul_smul _ _ _ := Subtype.ext mul_smul _ _ _

/--
Instance `continuousSMul_sphere_sphere` / 实例 `continuousSMul_sphere_sphere`

English:
instance continuousSMul_sphere_sphere
  signature: : ContinuousSMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r)
  body: ⟨Continuous.subtype_mk (by fun_prop) _⟩

中文:
实例 continuousSMul_sphere_sphere
  签名: : ContinuousSMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r)
  定义体: ⟨Continuous.subtype_mk (by fun_prop) _⟩

Depends on / 依赖: Continuous, Continuous.subtype_mk, fun_prop, subtype_mk
-/
instance continuousSMul_sphere_sphere : ContinuousSMul (sphere (0 : 𝕜) 1) (sphere (0 : E) r) :=
  ⟨Continuous.subtype_mk (by fun_prop) _⟩

end Sphere

section IsScalarTower

variable [NormedAlgebra 𝕜 𝕜'] [IsScalarTower 𝕜 𝕜' E]

/--
Instance `isScalarTower_closedBall_closedBall_closedBall` / 实例 `isScalarTower_closedBall_closedBall_closedBall`

English:
instance isScalarTower_closedBall_closedBall_closedBall
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_closedBall_closedBall_closedBall
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_closedBall_closedBall_closedBall :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_closedBall_closedBall_ball` / 实例 `isScalarTower_closedBall_closedBall_ball`

English:
instance isScalarTower_closedBall_closedBall_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_closedBall_closedBall_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_closedBall_closedBall_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_sphere_closedBall_closedBall` / 实例 `isScalarTower_sphere_closedBall_closedBall`

English:
instance isScalarTower_sphere_closedBall_closedBall
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_sphere_closedBall_closedBall
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_sphere_closedBall_closedBall :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_sphere_closedBall_ball` / 实例 `isScalarTower_sphere_closedBall_ball`

English:
instance isScalarTower_sphere_closedBall_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_sphere_closedBall_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_sphere_closedBall_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_sphere_sphere_closedBall` / 实例 `isScalarTower_sphere_sphere_closedBall`

English:
instance isScalarTower_sphere_sphere_closedBall
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_sphere_sphere_closedBall
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_sphere_sphere_closedBall :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_sphere_sphere_ball` / 实例 `isScalarTower_sphere_sphere_ball`

English:
instance isScalarTower_sphere_sphere_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_sphere_sphere_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_sphere_sphere_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_sphere_sphere_sphere` / 实例 `isScalarTower_sphere_sphere_sphere`

English:
instance isScalarTower_sphere_sphere_sphere
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 isScalarTower_sphere_sphere_sphere
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_sphere_sphere_sphere :
    IsScalarTower (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `isScalarTower_sphere_ball_ball` / 实例 `isScalarTower_sphere_ball_ball`

English:
instance isScalarTower_sphere_ball_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

中文:
实例 isScalarTower_sphere_ball_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_sphere_ball_ball :
    IsScalarTower (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

/--
Instance `isScalarTower_closedBall_ball_ball` / 实例 `isScalarTower_closedBall_ball_ball`

English:
instance isScalarTower_closedBall_ball_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

中文:
实例 isScalarTower_closedBall_ball_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_assoc
-/
instance isScalarTower_closedBall_ball_ball :
    IsScalarTower (closedBall (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
⟨fun a b c => Subtype.ext smul_assoc (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

end IsScalarTower

section SMulCommClass

variable [SMulCommClass 𝕜 𝕜' E]

/--
Instance `instSMulCommClass_closedBall_closedBall_closedBall` / 实例 `instSMulCommClass_closedBall_closedBall_closedBall`

English:
instance instSMulCommClass_closedBall_closedBall_closedBall
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_closedBall_closedBall_closedBall
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_closedBall_closedBall_closedBall :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `instSMulCommClass_closedBall_closedBall_ball` / 实例 `instSMulCommClass_closedBall_closedBall_ball`

English:
instance instSMulCommClass_closedBall_closedBall_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_closedBall_closedBall_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_closedBall_closedBall_ball :
    SMulCommClass (closedBall (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `instSMulCommClass_sphere_closedBall_closedBall` / 实例 `instSMulCommClass_sphere_closedBall_closedBall`

English:
instance instSMulCommClass_sphere_closedBall_closedBall
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_sphere_closedBall_closedBall
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_sphere_closedBall_closedBall :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (closedBall (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `instSMulCommClass_sphere_closedBall_ball` / 实例 `instSMulCommClass_sphere_closedBall_ball`

English:
instance instSMulCommClass_sphere_closedBall_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_sphere_closedBall_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_sphere_closedBall_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (closedBall (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `instSMulCommClass_sphere_ball_ball` / 实例 `instSMulCommClass_sphere_ball_ball`

English:
instance instSMulCommClass_sphere_ball_ball
  signature: [NormedAlgebra 𝕜 𝕜']
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

中文:
实例 instSMulCommClass_sphere_ball_ball
  签名: [NormedAlgebra 𝕜 𝕜']
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_sphere_ball_ball [NormedAlgebra 𝕜 𝕜'] :
    SMulCommClass (sphere (0 : 𝕜) 1) (ball (0 : 𝕜') 1) (ball (0 : 𝕜') 1) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : 𝕜')⟩

/--
Instance `instSMulCommClass_sphere_sphere_closedBall` / 实例 `instSMulCommClass_sphere_sphere_closedBall`

English:
instance instSMulCommClass_sphere_sphere_closedBall
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_sphere_sphere_closedBall
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_sphere_sphere_closedBall :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (closedBall (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `instSMulCommClass_sphere_sphere_ball` / 实例 `instSMulCommClass_sphere_sphere_ball`

English:
instance instSMulCommClass_sphere_sphere_ball
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_sphere_sphere_ball
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_sphere_sphere_ball :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (ball (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

/--
Instance `instSMulCommClass_sphere_sphere_sphere` / 实例 `instSMulCommClass_sphere_sphere_sphere`

English:
instance instSMulCommClass_sphere_sphere_sphere
  signature: :
  body: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

中文:
实例 instSMulCommClass_sphere_sphere_sphere
  签名: :
  定义体: ⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

Depends on / 依赖: Subtype, Subtype.ext, smul_comm
-/
instance instSMulCommClass_sphere_sphere_sphere :
    SMulCommClass (sphere (0 : 𝕜) 1) (sphere (0 : 𝕜') 1) (sphere (0 : E) r) :=
⟨fun a b c => Subtype.ext smul_comm (a : 𝕜) (b : 𝕜') (c : E)⟩

end SMulCommClass

variable (𝕜)
variable [CharZero 𝕜]

include 𝕜 in
/--
theorem `ne_neg_of_mem_sphere` / 定理 `ne_neg_of_mem_sphere`

English:
theorem ne_neg_of_mem_sphere
  given: {r : Real} (hr : r != 0) (x : sphere (0 : E) r)
  statement: x != -x
  proof: have : IsAddTorsionFree E := .of_isTorsionFree 𝕜 E
  fun h => ne_zero_of_mem_sphere hr x (self_eq_neg.mp (by (conv_lhs => rw [h]); rfl))

include 𝕜 in

中文:
定理 ne_neg_of_mem_sphere
  条件: {r : 实数} (hr : r != 0) (x : sphere (0 : E) r)
  结论: x != -x
  证明: have : IsAddTorsionFree E := .of_isTorsionFree 𝕜 E
  fun h => ne_zero_of_mem_sphere hr x (self_eq_neg.mp (by (conv_lhs => rw [h]); rfl))

include 𝕜 in

Depends on / 依赖: IsAddTorsionFree, conv_lhs, ne_zero_of_mem_sphere, of_isTorsionFree, self_eq_neg, self_eq_neg.mp
-/
theorem ne_neg_of_mem_sphere {r : Real} (hr : r != 0) (x : sphere (0 : E) r) : x != -x :=
  have : IsAddTorsionFree E := .of_isTorsionFree 𝕜 E
  fun h => ne_zero_of_mem_sphere hr x (self_eq_neg.mp (by (conv_lhs => rw [h]); rfl))

include 𝕜 in
/--
theorem `ne_neg_of_mem_unit_sphere` / 定理 `ne_neg_of_mem_unit_sphere`

English:
theorem ne_neg_of_mem_unit_sphere
  given: (x : sphere (0 : E) 1)
  statement: x != -x
  proof: ne_neg_of_mem_sphere 𝕜 one_ne_zero x

中文:
定理 ne_neg_of_mem_unit_sphere
  条件: (x : sphere (0 : E) 1)
  结论: x != -x
  证明: ne_neg_of_mem_sphere 𝕜 one_ne_zero x

Depends on / 依赖: ne_neg_of_mem_sphere, one_ne_zero
-/
theorem ne_neg_of_mem_unit_sphere (x : sphere (0 : E) 1) : x != -x :=
  ne_neg_of_mem_sphere 𝕜 one_ne_zero x
