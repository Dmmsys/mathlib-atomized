/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Equiv.Defs
public import Mathlib.Algebra.GroupWithZero.Hom

/-! # Isomorphisms of monoids with zero -/

@[expose] public section

assert_not_exists Ring

namespace MulEquivClass
variable {F α β : Type*} [EquivLike F α β]

-- See note [lower instance priority]
instance (priority := 100) toZeroHomClass [MulZeroClass α] [MulZeroClass β] [MulEquivClass F α β] :
    ZeroHomClass F α β where
  map_zero f :=
    calc
      f 0 = f 0 * f (EquivLike.inv f 0) := by rw [← map_mul, zero_mul]
        _ = 0 := by simp

-- See note [lower instance priority]
instance (priority := 100) toMonoidWithZeroHomClass
    [MulZeroOneClass α] [MulZeroOneClass β] [MulEquivClass F α β] :
    MonoidWithZeroHomClass F α β :=
  { MulEquivClass.instMonoidHomClass F, MulEquivClass.toZeroHomClass with }

end MulEquivClass

namespace MulEquiv

variable {G H : Type*} [MulZeroOneClass G] [MulZeroOneClass H]

/--
Definition of `toMonoidWithZeroHom` / `toMonoidWithZeroHom` 的定义

English:
definition toMonoidWithZeroHom
  signature: (f : G ≃* H)
  body: .ofClass f

中文:
定义 toMonoidWithZeroHom
  签名: (f : G ≃* H)
  定义体: .ofClass f

Depends on / 依赖: ofClass
-/
def toMonoidWithZeroHom (f : G ≃* H) : G ->*₀ H := .ofClass f

/--
lemma `toMonoidWithZeroHom_apply` / 引理 `toMonoidWithZeroHom_apply`

English:
lemma toMonoidWithZeroHom_apply
  given: (f : G ≃* H) (x : G)
  statement: f.toMonoidWithZeroHom x = f x
  proof: rfl

中文:
引理 toMonoidWithZeroHom_apply
  条件: (f : G ≃* H) (x : G)
  结论: f.toMonoidWithZeroHom x = f x
  证明: rfl
-/
@[simp] lemma toMonoidWithZeroHom_apply (f : G ≃* H) (x : G) : f.toMonoidWithZeroHom x = f x := rfl

/--
lemma `toMonoidWithZeroHom_injective` / 引理 `toMonoidWithZeroHom_injective`

English:
lemma toMonoidWithZeroHom_injective
  given: (f : G ≃* H)
  proof: f.injective

中文:
引理 toMonoidWithZeroHom_injective
  条件: (f : G ≃* H)
  证明: f.injective

Depends on / 依赖: f.injective, injective
-/
lemma toMonoidWithZeroHom_injective (f : G ≃* H) :
    Function.Injective f.toMonoidWithZeroHom :=
  f.injective

/--
lemma `toMonoidWithZeroHom_surjective` / 引理 `toMonoidWithZeroHom_surjective`

English:
lemma toMonoidWithZeroHom_surjective
  given: (f : G ≃* H)
  proof: f.surjective

中文:
引理 toMonoidWithZeroHom_surjective
  条件: (f : G ≃* H)
  证明: f.surjective

Depends on / 依赖: f.surjective, surjective
-/
lemma toMonoidWithZeroHom_surjective (f : G ≃* H) :
    Function.Surjective f.toMonoidWithZeroHom :=
  f.surjective

/--
lemma `toMonoidWithZeroHom_bijective` / 引理 `toMonoidWithZeroHom_bijective`

English:
lemma toMonoidWithZeroHom_bijective
  given: (f : G ≃* H)
  proof: f.bijective

中文:
引理 toMonoidWithZeroHom_bijective
  条件: (f : G ≃* H)
  证明: f.bijective

Depends on / 依赖: bijective, f.bijective
-/
lemma toMonoidWithZeroHom_bijective (f : G ≃* H) :
    Function.Bijective f.toMonoidWithZeroHom :=
  f.bijective

/--
lemma `toMonoidWithZeroHom_inj` / 引理 `toMonoidWithZeroHom_inj`

English:
lemma toMonoidWithZeroHom_inj
  given: {f g : G ≃* H}
  proof: by
  simp [MonoidWithZeroHom.ext_iff, MulEquiv.ext_iff]

中文:
引理 toMonoidWithZeroHom_inj
  条件: {f g : G ≃* H}
  证明: by
  simp [MonoidWithZeroHom.ext_iff, MulEquiv.ext_iff]
-/
@[simp] lemma toMonoidWithZeroHom_inj {f g : G ≃* H} :
    f.toMonoidWithZeroHom = g.toMonoidWithZeroHom ↔ f = g := by
  simp [MonoidWithZeroHom.ext_iff, MulEquiv.ext_iff]

end MulEquiv
