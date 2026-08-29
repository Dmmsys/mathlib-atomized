/-
Copyright (c) 2025 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.GroupTheory.Congruence.Basic

/-!
# Congruence relations respecting scalar multiplication
-/

@[expose] public section

variable (R S M N : Type*)

/--
Definition of `VAddCon` / `VAddCon` 的定义

English:
structure VAddCon
  parameters: [VAdd S M]
  extends: Setoid M
  axioms and operations (1):
    - vadd((s : S) {x y}) : r x y -> r (s +ᵥ x) (s +ᵥ y)

中文:
结构 VAddCon
  参数: [VAdd S M]
  继承: Setoid M
  公理与运算 (1 个):
    - vadd((s : S) {x y}) : r x y -> r (s +ᵥ x) (s +ᵥ y)
-/
structure VAddCon [VAdd S M] extends Setoid M where
  /-- A `VAddCon` is closed under additive action. -/
  vadd (s : S) {x y} : r x y -> r (s +ᵥ x) (s +ᵥ y)

/--
Definition of `SMulCon` / `SMulCon` 的定义

English:
structure SMulCon
  parameters: [SMul S M]
  extends: Setoid M
  axioms and operations (1):
    - smul((s : S) {x y}) : r x y -> r (s • x) (s • y)

中文:
结构 SMulCon
  参数: [SMul S M]
  继承: Setoid M
  公理与运算 (1 个):
    - smul((s : S) {x y}) : r x y -> r (s • x) (s • y)
-/
@[to_additive] structure SMulCon [SMul S M] extends Setoid M where
  /-- A `SMulCon` is closed under scalar multiplication. -/
  smul (s : S) {x y} : r x y -> r (s • x) (s • y)

/--
Definition of `ModuleCon` / `ModuleCon` 的定义

English:
structure ModuleCon
  parameters: [Add M] [SMul S M]
  extends: AddCon M, SMulCon S M
  (no additional axioms)

中文:
结构 ModuleCon
  参数: [Add M] [SMul S M]
  继承: AddCon M, SMulCon S M
  (无附加公理)
-/
structure ModuleCon [Add M] [SMul S M] extends AddCon M, SMulCon S M

/-- The `SMulCon` underlying an `ModuleCon`. -/
add_decl_doc ModuleCon.toSMulCon

variable {S}

namespace SMulCon

/-- The quotient by a congruence relation preserving scalar multiplication. -/
@[to_additive /-- The quotient by a congruence relation preserving additive action. -/]
/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  signature: [SMul S M] (c : SMulCon S M)
  body: Quotient c.toSetoid

中文:
定义 Quotient
  签名: [SMul S M] (c : SMulCon S M)
  定义体: Quotient c.toSetoid
-/
protected def Quotient [SMul S M] (c : SMulCon S M) : Type _ := Quotient c.toSetoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] (c
  body: Quotient.map (s • ·) (@c.smul s)

中文:
实例 [SMul
  签名: S M] (c
  定义体: Quotient.map (s • ·) (@c.smul s)
-/
@[to_additive] instance [SMul S M] (c : SMulCon S M) : SMul S c.Quotient where
  smul s := Quotient.map (s • ·) (@c.smul s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [Zero M] (c
  body: ⟦0⟧

中文:
实例 [SMul
  签名: S M] [Zero M] (c
  定义体: ⟦0⟧
-/
instance [SMul S M] [Zero M] (c : SMulCon S M) : Zero c.Quotient where
  zero := ⟦0⟧

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M] [SMulZeroClass S M] (c
  body: congr_arg _ (smul_zero s)

中文:
实例 [Zero
  签名: M] [SMulZeroClass S M] (c
  定义体: congr_arg _ (smul_zero s)

Depends on / 依赖: congr_arg, smul_zero
-/
instance [Zero M] [SMulZeroClass S M] (c : SMulCon S M) : SMulZeroClass S c.Quotient where
  smul_zero s := congr_arg _ (smul_zero s)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: S] [Zero M] [SMulWithZero S M] (c
  body: fast_instance% Quotient.mk''_surjective.smulWithZero ⟨_, rfl⟩ fun _ _ => rfl

中文:
实例 [Zero
  签名: S] [Zero M] [SMulWithZero S M] (c
  定义体: fast_instance% Quotient.mk''_surjective.smulWithZero ⟨_, rfl⟩ fun _ _ => rfl

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.smulWithZero, fast_instance, smulWithZero
-/
instance [Zero S] [Zero M] [SMulWithZero S M] (c : SMulCon S M) : SMulWithZero S c.Quotient :=
  fast_instance% Quotient.mk''_surjective.smulWithZero ⟨_, rfl⟩ fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [MulAction S M] (c
  body: fast_instance% Quotient.mk''_surjective.mulAction (⟦·⟧) fun _ _ => rfl

中文:
实例 [Monoid
  签名: S] [MulAction S M] (c
  定义体: fast_instance% Quotient.mk''_surjective.mulAction (⟦·⟧) fun _ _ => rfl
-/
@[to_additive] instance [Monoid S] [MulAction S M] (c : SMulCon S M) : MulAction S c.Quotient :=
  fast_instance% Quotient.mk''_surjective.mulAction (⟦·⟧) fun _ _ => rfl

section addConGen

variable {M} [AddZeroClass M] [DistribSMul S M]

/--
Definition of `addConGen'` / `addConGen'` 的定义

English:
definition addConGen'
  signature: (r : M -> M -> Prop) (hr : forall (s : S) {m m'}, r m m' -> r (s • m) (s • m'))
  body: addConGen r
  smul s _ _ h := ((addConGen r).comap (DistribSMul.toAddMonoidHom M s) <| by simp).addConGen_le.2
    (fun _ _ h => .of _ _ (hr s h)) h

中文:
定义 addConGen'
  签名: (r : M -> M -> 命题) (hr : 对任意 (s : S) {m m'}, r m m' -> r (s • m) (s • m'))
  定义体: addConGen r
  smul s _ _ h := ((addConGen r).comap (DistribSMul.toAddMonoidHom M s) <| by simp).addConGen_le.2
    (fun _ _ h => .of _ _ (hr s h)) h

Depends on / 依赖: addConGen
-/
def addConGen' (r : M -> M -> Prop) (hr : forall (s : S) {m m'}, r m m' -> r (s • m) (s • m')) :
    ModuleCon S M where
  toAddCon := addConGen r
  smul s _ _ h := ((addConGen r).comap (DistribSMul.toAddMonoidHom M s) <| by simp).addConGen_le.2
    (fun _ _ h => .of _ _ (hr s h)) h

/--
Definition of `addConGen` / `addConGen` 的定义

English:
abbreviation addConGen
  signature: (c : SMulCon S M)
  body: addConGen' c.r c.smul

中文:
缩写 addConGen
  签名: (c : SMulCon S M)
  定义体: addConGen' c.r c.smul
-/
protected abbrev addConGen (c : SMulCon S M) : ModuleCon S M := addConGen' c.r c.smul

end addConGen

end SMulCon

namespace ModuleCon

/--
Definition of `Quotient` / `Quotient` 的定义

English:
definition Quotient
  signature: [Add M] [SMul S M] (c : ModuleCon S M)
  body: Quotient c.toSetoid

中文:
定义 Quotient
  签名: [Add M] [SMul S M] (c : ModuleCon S M)
  定义体: Quotient c.toSetoid
-/
protected def Quotient [Add M] [SMul S M] (c : ModuleCon S M) : Type _ := Quotient c.toSetoid

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [Add M] (c
  body: inferInstanceAs (SMul S c.toSMulCon.Quotient)

中文:
实例 [SMul
  签名: S M] [Add M] (c
  定义体: inferInstanceAs (SMul S c.toSMulCon.Quotient)

Depends on / 依赖: Quotient, c.toSMulCon.Quotient, toSMulCon
-/
instance [SMul S M] [Add M] (c : ModuleCon S M) : SMul S c.Quotient :=
  inferInstanceAs (SMul S c.toSMulCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [Zero M] [Add M] (c
  body: ⟦0⟧

中文:
实例 [SMul
  签名: S M] [Zero M] [Add M] (c
  定义体: ⟦0⟧
-/
instance [SMul S M] [Zero M] [Add M] (c : ModuleCon S M) : Zero c.Quotient where
  zero := ⟦0⟧

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [Add M] (c
  body: inferInstanceAs (Add c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [Add M] (c
  定义体: inferInstanceAs (Add c.toAddCon.Quotient)

Depends on / 依赖: Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [Add M] (c : ModuleCon S M) : Add c.Quotient :=
  inferInstanceAs (Add c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddZeroClass M] (c
  body: inferInstanceAs (AddZeroClass c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddZeroClass M] (c
  定义体: inferInstanceAs (AddZeroClass c.toAddCon.Quotient)

Depends on / 依赖: AddZeroClass, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddZeroClass M] (c : ModuleCon S M) : AddZeroClass c.Quotient :=
  inferInstanceAs (AddZeroClass c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddCommMagma M] (c
  body: inferInstanceAs (AddCommMagma c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddCommMagma M] (c
  定义体: inferInstanceAs (AddCommMagma c.toAddCon.Quotient)

Depends on / 依赖: AddCommMagma, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddCommMagma M] (c : ModuleCon S M) : AddCommMagma c.Quotient :=
  inferInstanceAs (AddCommMagma c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddSemigroup M] (c
  body: inferInstanceAs (AddSemigroup c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddSemigroup M] (c
  定义体: inferInstanceAs (AddSemigroup c.toAddCon.Quotient)

Depends on / 依赖: AddSemigroup, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddSemigroup M] (c : ModuleCon S M) : AddSemigroup c.Quotient :=
  inferInstanceAs (AddSemigroup c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddCommSemigroup M] (c
  body: inferInstanceAs (AddCommSemigroup c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddCommSemigroup M] (c
  定义体: inferInstanceAs (AddCommSemigroup c.toAddCon.Quotient)

Depends on / 依赖: AddCommSemigroup, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddCommSemigroup M] (c : ModuleCon S M) : AddCommSemigroup c.Quotient :=
  inferInstanceAs (AddCommSemigroup c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddMonoid M] (c
  body: inferInstanceAs (AddMonoid c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddMonoid M] (c
  定义体: inferInstanceAs (AddMonoid c.toAddCon.Quotient)

Depends on / 依赖: AddMonoid, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddMonoid M] (c : ModuleCon S M) : AddMonoid c.Quotient :=
  inferInstanceAs (AddMonoid c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddCommMonoid M] (c
  body: inferInstanceAs (AddCommMonoid c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddCommMonoid M] (c
  定义体: inferInstanceAs (AddCommMonoid c.toAddCon.Quotient)

Depends on / 依赖: AddCommMonoid, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddCommMonoid M] (c : ModuleCon S M) : AddCommMonoid c.Quotient :=
  inferInstanceAs (AddCommMonoid c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddGroup M] (c
  body: inferInstanceAs (AddGroup c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddGroup M] (c
  定义体: inferInstanceAs (AddGroup c.toAddCon.Quotient)

Depends on / 依赖: AddGroup, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddGroup M] (c : ModuleCon S M) : AddGroup c.Quotient :=
  inferInstanceAs (AddGroup c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [SMul
  signature: S M] [AddCommGroup M] (c
  body: inferInstanceAs (AddCommGroup c.toAddCon.Quotient)

中文:
实例 [SMul
  签名: S M] [AddCommGroup M] (c
  定义体: inferInstanceAs (AddCommGroup c.toAddCon.Quotient)

Depends on / 依赖: AddCommGroup, Quotient, c.toAddCon.Quotient, toAddCon
-/
instance [SMul S M] [AddCommGroup M] (c : ModuleCon S M) : AddCommGroup c.Quotient :=
  inferInstanceAs (AddCommGroup c.toAddCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: M] [Add M] [SMulZeroClass S M] (c
  body: inferInstanceAs (SMulZeroClass S c.toSMulCon.Quotient)

中文:
实例 [Zero
  签名: M] [Add M] [SMulZeroClass S M] (c
  定义体: inferInstanceAs (SMulZeroClass S c.toSMulCon.Quotient)

Depends on / 依赖: Quotient, SMulZeroClass, c.toSMulCon.Quotient, toSMulCon
-/
instance [Zero M] [Add M] [SMulZeroClass S M] (c : ModuleCon S M) : SMulZeroClass S c.Quotient :=
  inferInstanceAs (SMulZeroClass S c.toSMulCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Zero
  signature: S] [Zero M] [Add M] [SMulWithZero S M] (c
  body: inferInstanceAs (SMulWithZero S c.toSMulCon.Quotient)

中文:
实例 [Zero
  签名: S] [Zero M] [Add M] [SMulWithZero S M] (c
  定义体: inferInstanceAs (SMulWithZero S c.toSMulCon.Quotient)

Depends on / 依赖: Quotient, SMulWithZero, c.toSMulCon.Quotient, toSMulCon
-/
instance [Zero S] [Zero M] [Add M] [SMulWithZero S M] (c : ModuleCon S M) :
    SMulWithZero S c.Quotient :=
  inferInstanceAs (SMulWithZero S c.toSMulCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [Add M] [MulAction S M] (c
  body: inferInstanceAs (MulAction S c.toSMulCon.Quotient)

中文:
实例 [Monoid
  签名: S] [Add M] [MulAction S M] (c
  定义体: inferInstanceAs (MulAction S c.toSMulCon.Quotient)

Depends on / 依赖: MulAction, Quotient, c.toSMulCon.Quotient, toSMulCon
-/
instance [Monoid S] [Add M] [MulAction S M] (c : ModuleCon S M) : MulAction S c.Quotient :=
  inferInstanceAs (MulAction S c.toSMulCon.Quotient)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [AddZeroClass
  signature: M] [DistribSMul S M] (c
  body: fast_instance% Quotient.mk''_surjective.distribSMul c.mk' fun _ _ => rfl

中文:
实例 [AddZeroClass
  签名: M] [DistribSMul S M] (c
  定义体: fast_instance% Quotient.mk''_surjective.distribSMul c.mk' fun _ _ => rfl

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.distribSMul, c.mk, distribSMul, fast_instance
-/
instance [AddZeroClass M] [DistribSMul S M] (c : ModuleCon S M) : DistribSMul S c.Quotient :=
  fast_instance% Quotient.mk''_surjective.distribSMul c.mk' fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Monoid
  signature: S] [AddMonoid M] [DistribMulAction S M] (c
  body: fast_instance%
  Quotient.mk''_surjective.distribMulAction c.mk' fun _ _ => rfl

中文:
实例 [Monoid
  签名: S] [AddMonoid M] [DistribMulAction S M] (c
  定义体: fast_instance%
  Quotient.mk''_surjective.distribMulAction c.mk' fun _ _ => rfl

Depends on / 依赖: fast_instance
-/
instance [Monoid S] [AddMonoid M] [DistribMulAction S M] (c : ModuleCon S M) :
    DistribMulAction S c.Quotient := fast_instance%
  Quotient.mk''_surjective.distribMulAction c.mk' fun _ _ => rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Semiring
  signature: S] [AddCommMonoid M] [Module S M] (c
  body: fast_instance% Quotient.mk''_surjective.module _ c.mk' fun _ _ => rfl

中文:
实例 [Semiring
  签名: S] [AddCommMonoid M] [Module S M] (c
  定义体: fast_instance% Quotient.mk''_surjective.module _ c.mk' fun _ _ => rfl

Depends on / 依赖: Quotient, Quotient.mk, _surjective, _surjective.module, c.mk, fast_instance, module
-/
instance [Semiring S] [AddCommMonoid M] [Module S M] (c : ModuleCon S M) : Module S c.Quotient :=
  fast_instance% Quotient.mk''_surjective.module _ c.mk' fun _ _ => rfl

end ModuleCon

section ker

variable {R M N}

/-- The kernel of a `MulActionHom` as a congruence relation. -/
@[to_additive /-- The kernel of an `AddActionHom` as a congruence relation. -/]
/--
Definition of `SMulCon.ker` / `SMulCon.ker` 的定义

English:
definition SMulCon.ker
  signature: [SMul R M] [SMul S N] {φ : R -> S} (f : M ->ₑ[φ] N)
  body: Setoid.ker f
  smul r _ _ h := by rw [Setoid.ker_def] at h ⊢; simp_rw [map_smulₛₗ, h]

中文:
定义 SMulCon.ker
  签名: [SMul R M] [SMul S N] {φ : R -> S} (f : M ->ₑ[φ] N)
  定义体: Setoid.ker f
  smul r _ _ h := by rw [Setoid.ker_def] at h ⊢; simp_rw [map_smulₛₗ, h]

Depends on / 依赖: Setoid, Setoid.ker
-/
def SMulCon.ker [SMul R M] [SMul S N] {φ : R -> S} (f : M ->ₑ[φ] N) : SMulCon R M where
  __ := Setoid.ker f
  smul r _ _ h := by rw [Setoid.ker_def] at h ⊢; simp_rw [map_smulₛₗ, h]

/--
Definition of `ModuleCon.ker` / `ModuleCon.ker` 的定义

English:
definition ModuleCon.ker
  signature: [Monoid R] [Monoid S] [AddMonoid M] [AddMonoid N] [DistribMulAction R M]
  body: SMulCon.ker f.toMulActionHom
  __ := AddCon.ker f

中文:
定义 ModuleCon.ker
  签名: [Monoid R] [Monoid S] [AddMonoid M] [AddMonoid N] [DistribMulAction R M]
  定义体: SMulCon.ker f.toMulActionHom
  __ := AddCon.ker f

Depends on / 依赖: SMulCon, SMulCon.ker, f.toMulActionHom, toMulActionHom
-/
def ModuleCon.ker [Monoid R] [Monoid S] [AddMonoid M] [AddMonoid N] [DistribMulAction R M]
    [DistribMulAction S N] {φ : R ->* S} (f : M ->ₑ+[φ] N) : ModuleCon R M where
  __ := SMulCon.ker f.toMulActionHom
  __ := AddCon.ker f

/--
Definition of `ModuleCon.quotientKerEquivOfSurjective` / `ModuleCon.quotientKerEquivOfSurjective` 的定义

English:
definition ModuleCon.quotientKerEquivOfSurjective
  signature: [Semiring S] [AddCommMonoid M]
  body: AddCon.quotientKerEquivOfSurjective f.toAddMonoidHom hf
  map_smul' s := by rintro ⟨⟩; apply map_smul f

中文:
定义 ModuleCon.quotientKerEquivOfSurjective
  签名: [Semiring S] [AddCommMonoid M]
  定义体: AddCon.quotientKerEquivOfSurjective f.toAddMonoidHom hf
  map_smul' s := by rintro ⟨⟩; apply map_smul f

Depends on / 依赖: AddCon, AddCon.quotientKerEquivOfSurjective, f.toAddMonoidHom, quotientKerEquivOfSurjective, toAddMonoidHom
-/
noncomputable def ModuleCon.quotientKerEquivOfSurjective [Semiring S] [AddCommMonoid M]
    [AddCommMonoid N] [Module S M] [Module S N] (f : M ->ₗ[S] N) (hf : Function.Surjective f) :
    (ker f.toDistribMulActionHom).Quotient ≃ₗ[S] N where
  __ := AddCon.quotientKerEquivOfSurjective f.toAddMonoidHom hf
  map_smul' s := by rintro ⟨⟩; apply map_smul f

end ker
