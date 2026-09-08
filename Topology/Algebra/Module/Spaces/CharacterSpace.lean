/-
Copyright (c) 2022 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Algebra.Algebra.Spectrum.Basic
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Data.Set.Lattice

/-!
# Character space of a topological algebra

The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. This space is used in the Gelfand transform, which gives an
isomorphism between a commutative C⋆-algebra and continuous functions on the character space
of the algebra. This, in turn, is used to construct the continuous functional calculus on
C⋆-algebras.


## Implementation notes

We define `WeakDual.characterSpace 𝕜 A` as a subset of the weak dual, which automatically puts the
correct topology on the space. We then define `WeakDual.CharacterSpace.toAlgHom` which provides the
algebra homomorphism corresponding to any element. We also provide `WeakDual.CharacterSpace.toCLM`
which provides the element as a continuous linear map. (Even though `WeakDual 𝕜 A` is a type copy of
`A →L[𝕜] 𝕜`, this is often more convenient.)

## Tags

character space, Gelfand transform, functional calculus

-/

@[expose] public section


namespace WeakDual

/-- The character space of a topological algebra is the subset of elements of the weak dual that
are also algebra homomorphisms. -/
/-
**WeakDual.characterSpace** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual`。
形式化陈述：characterSpace (𝕜 : Type*) (A : Type*) [CommSemiring 𝕜] [TopologicalSpace 
𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [To
pologicalSpace A] [Module 𝕜 A]
参数：𝕜 : Type*；A : Type*。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The character space of a topological algebra is the subset of elements of the we
ak dual that
are also algebra homomorphisms.
-/
def characterSpace (𝕜 : Type*) (A : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A] :=
  {φ : WeakDual 𝕜 A | φ ≠ 0 ∧ ∀ x y : A, φ (x * y) = φ x * φ y}

variable {𝕜 : Type*} {A : Type*}

-- Even though the capitalization of the namespace differs, it doesn't matter
-- because there is no dot notation since `characterSpace` is only a type via `CoeSort`.
namespace CharacterSpace

section NonUnitalNonAssocSemiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A]

/-
**WeakDual.CharacterSpace.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual.Charac
terSpace`。
形式化陈述：instFunLike : FunLike (characterSpace 𝕜 A) A 𝕜 where coe φ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance instFunLike : FunLike (characterSpace 𝕜 A) A 𝕜 where
  coe φ := ((φ : WeakDual 𝕜 A) : A → 𝕜)
  coe_injective φ ψ h := by ext1; apply DFunLike.ext; exact congr_fun h

/-- Elements of the character space are continuous linear maps. -/
/-
**WeakDual.CharacterSpace.instContinuousLinearMapClass** 是 Mathlib 中的一个实例，位于命名空间
 `WeakDual.CharacterSpace`。
形式化陈述：instContinuousLinearMapClass : ContinuousLinearMapClass (characterSpace 𝕜 
A) 𝕜 A 𝕜 where map_smulₛₗ φ
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousLinearMap.map_add`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : S
emiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_2 :
 TopologicalSpace…
· 使用定理 `ContinuousLinearMap.map_smul`：∀ {R₁ : Type u_1} [inst : Semiring R₁] {M₁
 : Type u_4} [inst_1 : TopologicalSpace M₁] [inst_2 : AddCommMonoid M₁]   {M₂ : 
Type u_6} [inst_3 …
· 使用定理 `ContinuousLinearMap.cont`：∀ {R : Type u_1} {S : Type u_2} [inst : Semiri
ng R] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_3}   [inst_2 : Topological
Space M] [inst…

--- 原说明 ---
Elements of the character space are continuous linear maps.
-/
instance instContinuousLinearMapClass : ContinuousLinearMapClass (characterSpace 𝕜 A) 𝕜 A 𝕜 where
  map_smulₛₗ φ := (φ : WeakDual 𝕜 A).map_smul
  map_add φ := (φ : WeakDual 𝕜 A).map_add
  map_continuous φ := (φ : WeakDual 𝕜 A).cont

/-- This has to come after `WeakDual.CharacterSpace.instFunLike`, otherwise the right-hand side
gets coerced via `Subtype.val` instead of directly via `DFunLike`. -/
@[simp, norm_cast]
/-
**WeakDual.CharacterSpace.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.CharacterS
pace`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : CommSemiring 𝕜] [inst_1 : Topologi
calSpace 𝕜] [inst_2 : ContinuousAdd 𝕜]   [inst_3 : ContinuousConstSMul 𝕜 𝕜] [ins
t_4 : NonUnitalNonAssocSemiring A] [inst_5 : TopologicalSpace A]   [inst_6 : _ro
ot_.Module 𝕜 A] (φ : ↑(WeakDual.characterSpace 𝕜 A)), ⇑↑φ = ⇑φ
参数：φ : ↑(WeakDual.characterSpace 𝕜 A)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This has to come after `WeakDual.CharacterSpace.instFunLike`, otherwise the righ
t-hand side
gets coerced via `Subtype.val` instead of directly via `DFunLike`.
-/
protected theorem coe_coe (φ : characterSpace 𝕜 A) : ⇑(φ : WeakDual 𝕜 A) = (φ : A → 𝕜) :=
  rfl

@[ext]
/-
**WeakDual.CharacterSpace.ext** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.CharacterSpace
`。
形式化陈述：ext {φ ψ : characterSpace 𝕜 A} (h : forall x, φ x = ψ x) : φ = ψ
参数：h : forall x, φ x = ψ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {φ ψ : characterSpace 𝕜 A} (h : ∀ x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext _ _ h

/-- An element of the character space, as a continuous linear map. -/
/-
**WeakDual.CharacterSpace.toCLM** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.CharacterSpa
ce`。
形式化陈述：toCLM (φ : characterSpace 𝕜 A) : A ->L[𝕜] 𝕜
参数：φ : characterSpace 𝕜 A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the character space, as a continuous linear map.
-/
def toCLM (φ : characterSpace 𝕜 A) : A →L[𝕜] 𝕜 :=
  (φ : WeakDual 𝕜 A)

@[simp]
/-
**WeakDual.CharacterSpace.coe_toCLM** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.Characte
rSpace`。
形式化陈述：coe_toCLM (φ : characterSpace 𝕜 A) : ⇑(toCLM φ) = φ
参数：φ : characterSpace 𝕜 A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toCLM (φ : characterSpace 𝕜 A) : ⇑(toCLM φ) = φ :=
  rfl

/-- Elements of the character space are non-unital algebra homomorphisms. -/
/-
**WeakDual.CharacterSpace.instNonUnitalAlgHomClass** 是 Mathlib 中的一个实例，位于命名空间 `We
akDual.CharacterSpace`。
形式化陈述：instNonUnitalAlgHomClass : NonUnitalAlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
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
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
Elements of the character space are non-unital algebra homomorphisms.
-/
instance instNonUnitalAlgHomClass : NonUnitalAlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜 :=
  { CharacterSpace.instContinuousLinearMapClass with
    map_smulₛₗ := fun φ => map_smul φ
    map_zero := fun φ => map_zero φ
    map_mul := fun φ => φ.prop.2 }

/-- An element of the character space, as a non-unital algebra homomorphism. -/
/-
**WeakDual.CharacterSpace.toNonUnitalAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.
CharacterSpace`。
形式化陈述：toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : A ->ₙₐ[𝕜] 𝕜 where toFun
参数：φ : characterSpace 𝕜 A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the character space, as a non-unital algebra homomorphism.
-/
noncomputable def toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : A →ₙₐ[𝕜] 𝕜 where
  toFun := (φ : A → 𝕜)
  map_mul' := map_mul φ
  map_smul' := map_smul φ
  map_zero' := map_zero φ
  map_add' := map_add φ

@[simp]
/-
**WeakDual.CharacterSpace.coe_toNonUnitalAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `WeakD
ual.CharacterSpace`。
形式化陈述：coe_toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : ⇑(toNonUnitalAlgHom φ) = 
φ
参数：φ : characterSpace 𝕜 A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : ⇑(toNonUnitalAlgHom φ) = φ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**WeakDual.CharacterSpace.instIsEmpty** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual.Charac
terSpace`。
形式化陈述：instIsEmpty [Subsingleton A] : IsEmpty (characterSpace 𝕜 A)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
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
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
instance instIsEmpty [Subsingleton A] : IsEmpty (characterSpace 𝕜 A) :=
  ⟨fun φ => φ.prop.1 <|
    ContinuousLinearMap.ext fun x => by
      rw [show x = 0 from Subsingleton.elim x 0, map_zero, map_zero] ⟩

variable (𝕜 A)
/-
**WeakDual.CharacterSpace.union_zero** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.Charact
erSpace`。
形式化陈述：union_zero : characterSpace 𝕜 A union {0} = {φ : WeakDual 𝕜 A | forall x y
 : A, φ (x * y) = φ x * φ y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
theorem union_zero :
    characterSpace 𝕜 A ∪ {0} = {φ : WeakDual 𝕜 A | ∀ x y : A, φ (x * y) = φ x * φ y} :=
  le_antisymm (by
      rintro φ (hφ | rfl)
      · exact hφ.2
      · exact fun _ _ => by exact (zero_mul (0 : 𝕜)).symm)
    fun φ hφ => Or.elim (em <| φ = 0) Or.inr fun h₀ => Or.inl ⟨h₀, hφ⟩

/-- The `characterSpace 𝕜 A` along with `0` is always a closed set in `WeakDual 𝕜 A`. -/
/-
**WeakDual.CharacterSpace.union_zero_isClosed** 是 Mathlib 中的一个定理，位于命名空间 `WeakDua
l.CharacterSpace`。
形式化陈述：union_zero_isClosed [T2Space 𝕜] [ContinuousMul 𝕜] : IsClosed (characterSpa
ce 𝕜 A union {0})
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `WeakDual.CharacterSpace.union_zero`：union_zero : characterSpace 𝕜 A unio
n {0} = {φ : WeakDual 𝕜 A | forall x y : A, φ (x * y) = φ x * φ y}
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `isClosed_iInter`：isClosed_iInter {f : ι -> Set X} (h : forall i, IsClose
d (f i)) : IsClosed (⋂ i, f i)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `WeakDual.eval_continuous`：eval_continuous (y : E) : Continuous fun x : W
eakDual 𝕜 E => x y
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)

--- 原说明 ---
The `characterSpace 𝕜 A` along with `0` is always a closed set in `WeakDual 𝕜 A`
.
-/
theorem union_zero_isClosed [T2Space 𝕜] [ContinuousMul 𝕜] :
    IsClosed (characterSpace 𝕜 A ∪ {0}) := by
  simp only [union_zero, Set.ofPred_forall]
  exact
    isClosed_iInter fun x =>
      isClosed_iInter fun y =>
        isClosed_eq (eval_continuous _) <| (eval_continuous _).mul (eval_continuous _)

end NonUnitalNonAssocSemiring

section Unital

variable [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [TopologicalSpace A] [Semiring A] [Algebra 𝕜 A]

/-- In a unital algebra, elements of the character space are algebra homomorphisms. -/
/-
**WeakDual.CharacterSpace.instAlgHomClass** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual.Ch
aracterSpace`。
形式化陈述：instAlgHomClass : AlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_eq_zero`：mul_eq_zero : a * b = 0 ↔ a = 0 ∨ b = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `ContinuousLinearMap.ext`：ext {f g : M₁ ->SL[σ₁₂] M₂} (h : forall x, f x 
= g x) : f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `Algebra.algebraMap_eq_smul_one`：algebraMap_eq_smul_one (r : R) : algebra
Map R A r = r • (1 : A)
· 使用定理 `Algebra.algebraMap_self`：∀ {R : Type u} [inst : CommSemiring R], algebra
Map R R = RingHom.id R
· 使用定理 `RingHom.id_apply`：id_apply (x : α) : RingHom.id α x = x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b

--- 原说明 ---
In a unital algebra, elements of the character space are algebra homomorphisms.
-/
instance instAlgHomClass : AlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜 :=
  haveI map_one' : ∀ φ : characterSpace 𝕜 A, φ 1 = 1 := fun φ => by
    have h₁ : φ 1 * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ← map_mul φ, one_mul]
    rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
    · have : ∀ a, φ (a * 1) = 0 := fun a => by simp only [map_mul φ, h₂, mul_zero]
      exact False.elim (φ.prop.1 <| ContinuousLinearMap.ext <| by simpa only [mul_one] using! this)
    · exact (sub_eq_zero.mp h₂).symm
  { CharacterSpace.instNonUnitalAlgHomClass with
    map_one := map_one'
    commutes := fun φ r => by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_self, RingHom.id_apply]
      rw [map_smul, smul_eq_mul, map_one' φ, mul_one] }

/-- An element of the character space of a unital algebra, as an algebra homomorphism. -/
@[simps]
/-
**WeakDual.CharacterSpace.toAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual.Character
Space`。
形式化陈述：toAlgHom (φ : characterSpace 𝕜 A) : A ->ₐ[𝕜] 𝕜
参数：φ : characterSpace 𝕜 A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element of the character space of a unital algebra, as an algebra homomorphis
m.
-/
noncomputable def toAlgHom (φ : characterSpace 𝕜 A) : A →ₐ[𝕜] 𝕜 :=
  { toNonUnitalAlgHom φ with
    map_one' := map_one φ
    commutes' := AlgHomClass.commutes φ }
/-
**WeakDual.CharacterSpace.eq_set_map_one_map_mul** 是 Mathlib 中的一个定理，位于命名空间 `Weak
Dual.CharacterSpace`。
形式化陈述：eq_set_map_one_map_mul [Nontrivial 𝕜] : characterSpace 𝕜 A = {φ : WeakDual
 𝕜 A | φ 1 = 1 ∧ forall x y : A, φ (x * y) = φ x * φ y}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem eq_set_map_one_map_mul [Nontrivial 𝕜] :
    characterSpace 𝕜 A = {φ : WeakDual 𝕜 A | φ 1 = 1 ∧ ∀ x y : A, φ (x * y) = φ x * φ y} := by
  ext φ
  refine ⟨?_, ?_⟩
  · rintro hφ
    lift φ to characterSpace 𝕜 A using hφ
    exact ⟨map_one φ, map_mul φ⟩
  · rintro ⟨hφ₁, hφ₂⟩
    refine ⟨?_, hφ₂⟩
    rintro rfl
    exact zero_ne_one hφ₁

/-- under suitable mild assumptions on `𝕜`, the character space is a closed set in
`WeakDual 𝕜 A`. -/
/-
**WeakDual.CharacterSpace.isClosed** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.Character
Space`。
形式化陈述：∀ {𝕜 : Type u_1} {A : Type u_2} [inst : CommRing 𝕜] [NoZeroDivisors 𝕜] [in
st_2 : TopologicalSpace 𝕜]   [inst_3 : ContinuousAdd 𝕜] [inst_4 : ContinuousCons
tSMul 𝕜 𝕜] [inst_5 : TopologicalSpace A] [inst_6 : Semiring A]   [inst_7 : Algeb
ra 𝕜 A] [Nontrivial 𝕜] [T2Space 𝕜] [ContinuousMul 𝕜], IsClosed (WeakDual.charact
erSpace 𝕜 A)
参数：WeakDual.characterSpace 𝕜 A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeakDual.CharacterSpace.eq_set_map_one_map_mul`：eq_set_map_one_map_mul [
Nontrivial 𝕜] : characterSpace 𝕜 A = {φ : WeakDual 𝕜 A | φ 1 = 1 ∧ forall x y : 
A, φ (x * y) = φ x * φ y}
· 使用定理 `Set.ofPred_and`：ofPred_and {p q : α -> Prop} : { a | p a ∧ q a } = { a |
 p a } inter { a | q a }
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `WeakDual.eval_continuous`：eval_continuous (y : E) : Continuous fun x : W
eakDual 𝕜 E => x y
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WeakDual.CharacterSpace.union_zero`：union_zero : characterSpace 𝕜 A unio
n {0} = {φ : WeakDual 𝕜 A | forall x y : A, φ (x * y) = φ x * φ y}
· 使用定理 `WeakDual.CharacterSpace.union_zero_isClosed`：union_zero_isClosed [T2Spac
e 𝕜] [ContinuousMul 𝕜] : IsClosed (characterSpace 𝕜 A union {0})

--- 原说明 ---
under suitable mild assumptions on `𝕜`, the character space is a closed set in
`WeakDual 𝕜 A`.
-/
protected theorem isClosed [Nontrivial 𝕜] [T2Space 𝕜] [ContinuousMul 𝕜] :
    IsClosed (characterSpace 𝕜 A) := by
  rw [eq_set_map_one_map_mul, Set.ofPred_and]
  refine IsClosed.inter (isClosed_eq (eval_continuous _) continuous_const) ?_
  simpa only [(union_zero 𝕜 A).symm] using union_zero_isClosed _ _

end Unital

section Ring

variable [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [TopologicalSpace A] [Ring A] [Algebra 𝕜 A]

/-
**WeakDual.CharacterSpace.apply_mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual
.CharacterSpace`。
形式化陈述：apply_mem_spectrum [Nontrivial 𝕜] (φ : characterSpace 𝕜 A) (a : A) : φ a i
n spectrum 𝕜 a
参数：φ : characterSpace 𝕜 A；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.apply_mem_spectrum`：apply_mem_spectrum [Nontrivial R] (φ : F) (a 
: A) : φ a in σ a
-/
theorem apply_mem_spectrum [Nontrivial 𝕜] (φ : characterSpace 𝕜 A) (a : A) : φ a ∈ spectrum 𝕜 a :=
  AlgHom.apply_mem_spectrum φ a
/-
**WeakDual.CharacterSpace.ext_ker** 是 Mathlib 中的一个定理，位于命名空间 `WeakDual.CharacterS
pace`。
形式化陈述：ext_ker {φ ψ : characterSpace 𝕜 A} (h : RingHom.ker φ = RingHom.ker ψ) : φ
 = ψ
参数：h : RingHom.ker φ = RingHom.ker ψ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `WeakDual.CharacterSpace.ext`：ext {φ ψ : characterSpace 𝕜 A} (h : forall 
x, φ x = ψ x) : φ = ψ
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
-/
theorem ext_ker {φ ψ : characterSpace 𝕜 A} (h : RingHom.ker φ = RingHom.ker ψ) : φ = ψ := by
  ext x
  have : x - algebraMap 𝕜 A (ψ x) ∈ RingHom.ker φ := by
    simpa only [h, RingHom.mem_ker, map_sub, AlgHomClass.commutes] using! sub_self (ψ x)
  rwa [RingHom.mem_ker, map_sub, AlgHomClass.commutes, sub_eq_zero] at this

end Ring

end CharacterSpace

section Kernel

variable [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [Ring A] [TopologicalSpace A] [Algebra 𝕜 A]

/-- The `RingHom.ker` of `φ : characterSpace 𝕜 A` is maximal. -/
/-
**WeakDual.ker_isMaximal** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
形式化陈述：ker_isMaximal (φ : characterSpace 𝕜 A) : (RingHom.ker φ).IsMaximal
参数：φ : characterSpace 𝕜 A。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ker_isMaximal_of_surjective`：ker_isMaximal_of_surjective {R K F 
: Type*} [Ring R] [DivisionRing K] [FunLike F R K] [RingHomClass F R K] (f : F) 
(hf : Function.Surjective…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHomClass.commutes`：∀ {F : Type u_1} {R : outParam (Type u_2)} {A : ou
tParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {inst_1 :
 Semiring …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The `RingHom.ker` of `φ : characterSpace 𝕜 A` is maximal.
-/
instance ker_isMaximal (φ : characterSpace 𝕜 A) : (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ fun z ↦ ⟨algebraMap 𝕜 A z, by simp [AlgHomClass.commutes]⟩

end Kernel

section GelfandTransform

open ContinuousMap

variable (𝕜 A) [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [TopologicalSpace A] [Semiring A] [Algebra 𝕜 A]

/-- The **Gelfand transform** is an algebra homomorphism (over `𝕜`) from a topological `𝕜`-algebra
`A` into the `𝕜`-algebra of continuous `𝕜`-valued functions on the `characterSpace 𝕜 A`.
The character space itself consists of all algebra homomorphisms from `A` to `𝕜`. -/
@[simps]
/-
**WeakDual.gelfandTransform** 是 Mathlib 中的一个定义，位于命名空间 `WeakDual`。
形式化陈述：gelfandTransform : A ->ₐ[𝕜] C(characterSpace 𝕜 A, 𝕜) where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **Gelfand transform** is an algebra homomorphism (over `𝕜`) from a topologic
al `𝕜`-algebra
`A` into the `𝕜`-algebra of continuous `𝕜`-valued functions on the `characterSpa
ce 𝕜 A`.
The character space itself consists of all algebra homomorphisms from `A` to `𝕜`
.
-/
noncomputable def gelfandTransform : A →ₐ[𝕜] C(characterSpace 𝕜 A, 𝕜) where
  toFun a :=
    { toFun := fun φ => φ a
      continuous_toFun := (eval_continuous a).comp continuous_induced_dom }
  map_one' := by ext a; simp only [coe_mk, coe_one, Pi.one_apply, map_one a]
  map_mul' a b := by ext; simp only [map_mul, coe_mk, coe_mul, Pi.mul_apply]
  map_zero' := by ext; simp only [map_zero, coe_mk, coe_zero, Pi.zero_apply]
  map_add' a b := by ext; simp only [map_add, coe_mk, coe_add, Pi.add_apply]
  commutes' k := by ext; simp [AlgHomClass.commutes]

end GelfandTransform

end WeakDual

