/-
Copyright (c) 2022 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.GradedMulAction
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Module.BigOperators

/-!
# Graded Module

Given an `R`-algebra `A` graded by `𝓐`, a graded `A`-module `M` is expressed as
`DirectSum.Decomposition 𝓜` and `SetLike.GradedSMul 𝓐 𝓜`.
Then `⨁ i, 𝓜 i` is an `A`-module and is isomorphic to `M`.

## Tags

graded module
-/

@[expose] public section


section

open DirectSum

variable {ιA ιB : Type*} (A : ιA → Type*) (M : ιB → Type*)

namespace DirectSum

open GradedMonoid

/-- A graded version of `DistribMulAction`. -/
/-
**DirectSum.GdistribMulAction** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ιA : Type u_1} →   {ιB : Type u_2} →     (A : ιA → Type u_3) →       (M :
 ιB → Type u_4) →         [inst : AddMonoid ιA] →           [VAdd ιA ιB] →      
       [GradedMonoid.GMonoid A] → [(i : ιB) → AddMonoid (M i)] → Type (max (max 
(max u_1 u_2) u_3) u_4)
参数：A : ιA → Type u_3；M : ιB → Type u_4；i : ιB；M i；max (max (max u_1 u_2) u_3) u_
4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `DistribMulAction`.
-/
class GdistribMulAction [AddMonoid ιA] [VAdd ιA ιB] [GMonoid A] [∀ i, AddMonoid (M i)]
    extends GMulAction A M where
  smul_add {i j} (a : A i) (b c : M j) : smul a (b + c) = smul a b + smul a c
  smul_zero {i j} (a : A i) : smul a (0 : M j) = 0

/-- A graded version of `Module`. -/
/-
**DirectSum.Gmodule** 是 Mathlib 中的一个归纳类型，位于命名空间 `DirectSum`。
形式化陈述：{ιA : Type u_1} →   {ιB : Type u_2} →     (A : ιA → Type u_3) →       (M :
 ιB → Type u_4) →         [inst : AddMonoid ιA] →           [VAdd ιA ιB] →      
       [(i : ιA) → AddMonoid (A i)] →               [(i : ιB) → AddMonoid (M i)]
 → [GradedMonoid.GMonoid A] → Type (max (max (max u_1 u_2) u_3) u_4)
参数：A : ιA → Type u_3；M : ιB → Type u_4；i : ιA；A i；i : ιB；M i；max (max (max u_1 u
_2) u_3) u_4。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Module`.
-/
class Gmodule [AddMonoid ιA] [VAdd ιA ιB] [∀ i, AddMonoid (A i)] [∀ i, AddMonoid (M i)] [GMonoid A]
    extends GdistribMulAction A M where
  add_smul {i j} (a a' : A i) (b : M j) : smul (a + a') b = smul a b + smul a' b
  zero_smul {i j} (b : M j) : smul (0 : A i) b = 0

/-- A graded version of `Semiring.toModule`. -/
/-
**DirectSum.GSemiring.toGmodule** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.GSemiring`。
形式化陈述：{ιA : Type u_1} →   (A : ιA → Type u_3) →     [inst : AddMonoid ιA] →     
  [inst_1 : (i : ιA) → AddCommMonoid (A i)] → [h : DirectSum.GSemiring A] → Dire
ctSum.Gmodule A A
参数：A : ιA → Type u_3；i : ιA；A i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A graded version of `Semiring.toModule`.
-/
instance GSemiring.toGmodule [AddMonoid ιA] [∀ i : ιA, AddCommMonoid (A i)]
    [h : GSemiring A] : Gmodule A A :=
  { GMonoid.toGMulAction A with
    smul_add := fun _ _ _ => h.mul_add _ _ _
    smul_zero := fun _ => h.mul_zero _
    add_smul := fun _ _ => h.add_mul _ _
    zero_smul := fun _ => h.zero_mul _ }

variable [AddMonoid ιA] [VAdd ιA ιB] [∀ i : ιA, AddCommMonoid (A i)] [∀ i, AddCommMonoid (M i)]

/-- The piecewise multiplication from the `Mul` instance, as a bundled homomorphism. -/
@[simps]
/-
**DirectSum.gsmulHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：gsmulHom [GMonoid A] [Gmodule A M] {i j} : A i ->+ M j ->+ M (i +ᵥ j) wher
e toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The piecewise multiplication from the `Mul` instance, as a bundled homomorphism.
-/
def gsmulHom [GMonoid A] [Gmodule A M] {i j} : A i →+ M j →+ M (i +ᵥ j) where
  toFun a :=
    { toFun := fun b => GSMul.smul a b
      map_zero' := GdistribMulAction.smul_zero _
      map_add' := GdistribMulAction.smul_add _ }
  map_zero' := AddMonoidHom.ext fun a => Gmodule.zero_smul a
  map_add' _a₁ _a₂ := AddMonoidHom.ext fun _b => Gmodule.add_smul _ _ _

namespace Gmodule

/-- For graded monoid `A` and a graded module `M` over `A`. `Gmodule.smulAddMonoidHom` is the
`⨁ᵢ Aᵢ`-scalar multiplication on `⨁ᵢ Mᵢ` induced by `gsmul_hom`. -/
/-
**DirectSum.Gmodule.smulAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.Gmodul
e`。
形式化陈述：smulAddMonoidHom [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A 
M] : (⨁ i, A i) ->+ (⨁ i, M i) ->+ ⨁ i, M i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For graded monoid `A` and a graded module `M` over `A`. `Gmodule.smulAddMonoidHo
m` is the
`⨁ᵢ Aᵢ`-scalar multiplication on `⨁ᵢ Mᵢ` induced by `gsmul_hom`.
-/
def smulAddMonoidHom [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] :
    (⨁ i, A i) →+ (⨁ i, M i) →+ ⨁ i, M i :=
  toAddMonoid fun _i =>
    AddMonoidHom.flip <|
      toAddMonoid fun _j => AddMonoidHom.flip <| (of M _).compHom.comp <| gsmulHom A M

section

open GradedMonoid DirectSum Gmodule

/-
**DirectSum.Gmodule.** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum.Gmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] :
    SMul (⨁ i, A i) (⨁ i, M i) where
  smul x y := smulAddMonoidHom A M x y

@[simp]
/-
**DirectSum.Gmodule.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Gmodule`。
形式化陈述：smul_def [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] (x : 
⨁ i, A i) (y : ⨁ i, M i) : x • y = smulAddMonoidHom _ _ x y
参数：x : ⨁ i, A i；y : ⨁ i, M i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_def [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    (x : ⨁ i, A i) (y : ⨁ i, M i) :
    x • y = smulAddMonoidHom _ _ x y := rfl

@[simp]
/-
**DirectSum.Gmodule.smulAddMonoidHom_apply_of_of** 是 Mathlib 中的一个定理，位于命名空间 `Dire
ctSum.Gmodule`。
形式化陈述：smulAddMonoidHom_apply_of_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A]
 [Gmodule A M] {i j} (x : A i) (y : M j) : smulAddMonoidHom A M (DirectSum.of A 
i x) (of M j y) = of M (i +ᵥ j) (GSMul.smul x y)
参数：x : A i；y : M j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.toAddMonoid_of`：toAddMonoid_of (i) (x : β i) : toAddMonoid φ (
of β i x) = φ i x
· 使用定理 `AddMonoidHom.compHom_apply_apply`：∀ {M : Type uM} {N : Type uN} {P : Typ
e uP} [inst : AddZeroClass M] [inst_1 : AddCommMonoid N]   [inst_2 : AddCommMono
id P] (g : N →+ P) (hm…
· 使用定理 `DirectSum.gsmulHom_apply_apply`：∀ {ιA : Type u_1} {ιB : Type u_2} (A : ι
A → Type u_3) (M : ιB → Type u_4) [inst : AddMonoid ιA] [inst_1 : VAdd ιA ιB]   
[inst_2 : (i : ιA) →…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem smulAddMonoidHom_apply_of_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    {i j} (x : A i) (y : M j) :
    smulAddMonoidHom A M (DirectSum.of A i x) (of M j y) = of M (i +ᵥ j) (GSMul.smul x y) := by
  simp [smulAddMonoidHom]
/-
**DirectSum.Gmodule.of_smul_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Gmodule`。
形式化陈述：of_smul_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] {i 
j} (x : A i) (y : M j) : DirectSum.of A i x • of M j y = of M (i +ᵥ j) (GSMul.sm
ul x y)
参数：x : A i；y : M j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.Gmodule.smulAddMonoidHom_apply_of_of`：smulAddMonoidHom_apply_o
f_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M] {i j} (x : A i)
 (y : M j) : smulAddMonoidHom A M (D…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_smul_of [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    {i j} (x : A i) (y : M j) :
    DirectSum.of A i x • of M j y = of M (i +ᵥ j) (GSMul.smul x y) := by simp

open AddMonoidHom

-- Almost identical to the proof of `direct_sum.one_mul`
/-
**DirectSum.Gmodule.one_smul'** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Gmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem one_smul' [DecidableEq ιA] [DecidableEq ιB] [GMonoid A] [Gmodule A M]
    (x : ⨁ i, M i) :
    (1 : ⨁ i, A i) • x = x := by
  suffices smulAddMonoidHom A M 1 = AddMonoidHom.id (⨁ i, M i) from DFunLike.congr_fun this x
  apply DirectSum.addHom_ext; intro i xi
  rw [show (1 : DirectSum ιA fun i => A i) = (of A 0) GOne.one by rfl]
  rw [smulAddMonoidHom_apply_of_of]
  exact DirectSum.of_eq_of_gradedMonoid_eq (one_smul (GradedMonoid A) <| GradedMonoid.mk i xi)

set_option backward.defeqAttrib.useBackward true in
-- Almost identical to the proof of `direct_sum.mul_assoc`
/-
**DirectSum.Gmodule.mul_smul'** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum.Gmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem mul_smul' [DecidableEq ιA] [DecidableEq ιB] [GSemiring A] [Gmodule A M]
    (a b : ⨁ i, A i)
    (c : ⨁ i, M i) : (a * b) • c = a • b • c := by
  suffices
    (-- `fun a b c ↦ (a * b) • c` as a bundled hom
              smulAddMonoidHom
              A M).compHom.comp
        (DirectSum.mulHom A) =
      (AddMonoidHom.compHom AddMonoidHom.flipHom <|
          (smulAddMonoidHom A M).flip.compHom.comp <| smulAddMonoidHom A M).flip
    from -- `fun a b c ↦ a • (b • c)` as a bundled hom
      DFunLike.congr_fun (DFunLike.congr_fun (DFunLike.congr_fun this a) b) c
  ext ai ax bi bx ci cx : 6
  dsimp only [coe_comp, Function.comp_apply, compHom_apply_apply, flip_apply, flipHom_apply]
  rw [smulAddMonoidHom_apply_of_of, smulAddMonoidHom_apply_of_of, DirectSum.mulHom_of_of,
    smulAddMonoidHom_apply_of_of]
  exact
    DirectSum.of_eq_of_gradedMonoid_eq
      (mul_smul (GradedMonoid.mk ai ax) (GradedMonoid.mk bi bx) (GradedMonoid.mk ci cx))

/-- The `Module` derived from `gmodule A M`. -/
/-
**DirectSum.Gmodule.module** 是 Mathlib 中的一个实例，位于命名空间 `DirectSum.Gmodule`。
形式化陈述：module [DecidableEq ιA] [DecidableEq ιB] [GSemiring A] [Gmodule A M] : Mod
ule (⨁ i, A i) (⨁ i, M i) where one_smul
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `Module` derived from `gmodule A M`.
-/
instance module [DecidableEq ιA] [DecidableEq ιB] [GSemiring A] [Gmodule A M] :
    Module (⨁ i, A i) (⨁ i, M i) where
  one_smul := by exact one_smul' _ _
  mul_smul := by exact mul_smul' _ _
  smul_add r := (smulAddMonoidHom A M r).map_add
  smul_zero r := (smulAddMonoidHom A M r).map_zero
  add_smul r s x := by simp only [smul_def, map_add, AddMonoidHom.add_apply]
  zero_smul x := by simp only [smul_def, map_zero, AddMonoidHom.zero_apply]

end

end Gmodule

end DirectSum

end

open DirectSum

variable {ιA ιM R A M σ σ' : Type*}
variable [AddMonoid ιA] [AddAction ιA ιM] [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝓐 : ιA → σ') [SetLike σ' A]
variable (𝓜 : ιM → σ)

namespace SetLike

/-
**SetLike.gmulAction** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：gmulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M] [SetLike.Gra
dedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜] : GradedMonoid.GMulAction (fun i => 𝓐 i) f
un i => 𝓜 i
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance gmulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M] [SetLike.GradedMonoid 𝓐]
    [SetLike.GradedSMul 𝓐 𝓜] : GradedMonoid.GMulAction (fun i => 𝓐 i) fun i => 𝓜 i :=
  { SetLike.toGSMul 𝓐 𝓜 with
    one_smul := fun ⟨_i, _m⟩ => Sigma.subtype_ext (zero_vadd _ _) (one_smul _ _)
    mul_smul := fun ⟨_i, _a⟩ ⟨_j, _a'⟩ ⟨_k, _b⟩ =>
      Sigma.subtype_ext (add_vadd _ _ _) (mul_smul _ _ _) }
/-
**SetLike.gdistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：gdistribMulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M] [AddS
ubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜] : DirectSum
.GdistribMulAction (fun i => 𝓐 i) fun i => 𝓜 i
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance gdistribMulAction [AddMonoid M] [DistribMulAction A M] [SetLike σ M]
    [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜] :
    DirectSum.GdistribMulAction (fun i => 𝓐 i) fun i => 𝓜 i :=
  { SetLike.gmulAction 𝓐 𝓜 with
    smul_add := fun _a _b _c => Subtype.ext <| smul_add _ _ _
    smul_zero := fun _a => Subtype.ext <| smul_zero _ }

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]

/-- `[SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]` is the internal version of graded
  module, the internal version can be translated into the external version `gmodule`. -/
/-
**SetLike.gmodule** 是 Mathlib 中的一个实例，位于命名空间 `SetLike`。
形式化陈述：gmodule : DirectSum.Gmodule (fun i => 𝓐 i) fun i => 𝓜 i
该定义给出了一等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`[SetLike.GradedMonoid 𝓐] [SetLike.GradedSMul 𝓐 𝓜]` is the internal version of g
raded
  module, the internal version can be translated into the external version `gmod
ule`.
-/
instance gmodule : DirectSum.Gmodule (fun i => 𝓐 i) fun i => 𝓜 i :=
  { SetLike.gdistribMulAction 𝓐 𝓜 with
    smul := fun x y => ⟨(x : A) • (y : M), SetLike.GradedSMul.smul_mem x.2 y.2⟩
    add_smul := fun _a _a' _b => Subtype.ext <| add_smul _ _ _
    zero_smul := fun _b => Subtype.ext <| zero_smul _ _ }

end SetLike

namespace GradedModule

variable [AddCommMonoid M] [Module A M] [SetLike σ M] [AddSubmonoidClass σ' A]
  [AddSubmonoidClass σ M] [SetLike.GradedSMul 𝓐 𝓜]
  [DecidableEq ιA] [DecidableEq ιM] [GradedRing 𝓐]

/-- The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁ i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
@[instance_reducible]
/-
**GradedModule.isModule** 是 Mathlib 中的一个定义，位于命名空间 `GradedModule`。
形式化陈述：isModule : Module A (⨁ i, 𝓜 i)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …

--- 原说明 ---
The smul multiplication of `A` on `⨁ i, 𝓜 i` from `(⨁ i, 𝓐 i) →+ (⨁ i, 𝓜 i) →+ ⨁
 i, 𝓜 i`
turns `⨁ i, 𝓜 i` into an `A`-module
-/
def isModule : Module A (⨁ i, 𝓜 i) :=
  { Module.compHom _ (DirectSum.decomposeRingEquiv 𝓐 : A ≃+* ⨁ i, 𝓐 i).toRingHom with
    smul := fun a b => DirectSum.decompose 𝓐 a • b }

/-- `⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
"The internal version" and "the external version" are isomorphism as `A`-modules.
-/
/-
**GradedModule.linearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `GradedModule`。
形式化陈述：linearEquiv [DirectSum.Decomposition 𝓜] : @LinearEquiv A A _ _ (RingHom.id
 A) (RingHom.id A) _ _ M (⨁ i, 𝓜 i) _ _ _ (by letI
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`⨁ i, 𝓜 i` and `M` are isomorphic as `A`-modules.
"The internal version" and "the external version" are isomorphism as `A`-modules
.
-/
def linearEquiv [DirectSum.Decomposition 𝓜] :
    @LinearEquiv A A _ _ (RingHom.id A) (RingHom.id A) _ _ M (⨁ i, 𝓜 i) _
    _ _ (by letI := isModule 𝓐 𝓜; infer_instance) := by
  letI h := isModule 𝓐 𝓜
  refine ⟨⟨(DirectSum.decomposeAddEquiv 𝓜).toAddHom, ?_⟩,
    (DirectSum.decomposeAddEquiv 𝓜).symm.toFun, (DirectSum.decomposeAddEquiv 𝓜).left_inv,
    (DirectSum.decomposeAddEquiv 𝓜).right_inv⟩
  intro x y
  classical
  rw [AddHom.toFun_eq_coe, ← DirectSum.sum_support_decompose 𝓐 x, map_sum, Finset.sum_smul,
    AddEquiv.coe_toAddHom, map_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl (fun i _hi => ?_)
  rw [RingHom.id_apply, ← DirectSum.sum_support_decompose 𝓜 y, map_sum, Finset.smul_sum, map_sum,
    Finset.smul_sum]
  refine Finset.sum_congr rfl (fun j _hj => ?_)
  rw [show (decompose 𝓐 x i : A) • (decomposeAddEquiv 𝓜 ↑(decompose 𝓜 y j) : (⨁ i, 𝓜 i)) =
    DirectSum.Gmodule.smulAddMonoidHom _ _ (decompose 𝓐 ↑(decompose 𝓐 x i))
    (decomposeAddEquiv 𝓜 ↑(decompose 𝓜 y j)) from DirectSum.Gmodule.smul_def _ _ _ _]
  simp only [decomposeAddEquiv_apply, decompose_coe, Gmodule.smulAddMonoidHom_apply_of_of]
  convert! DirectSum.decompose_coe 𝓜 _
  rfl

end GradedModule

