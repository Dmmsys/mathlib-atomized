/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu, Jiedong Jiang
-/
module

public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Relative Algebraic Closure

In this file we construct the relative algebraic closure of a field extension.

## Main Definitions

- `algebraicClosure F E` is the relative algebraic closure (i.e. the maximal algebraic subextension)
  of the field extension `E / F`, which is defined to be the integral closure of `F` in `E`.

-/

@[expose] public section
noncomputable section

open Polynomial FiniteDimensional IntermediateField Field

variable (F E : Type*) [Field F] [Field E] [Algebra F E]
variable {K : Type*} [Field K] [Algebra F K]

/--
The *relative algebraic closure* of a field `F` in a field extension `E`,
also called the *maximal algebraic subextension* of `E / F`,
is defined to be the subalgebra `integralClosure F E`
upgraded to an intermediate field (since `F` and `E` are both fields).
This is exactly the intermediate field of `E / F` consisting of all integral/algebraic elements.
-/
@[stacks 09GI]
/-
**algebraicClosure** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：algebraicClosure : IntermediateField F E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The *relative algebraic closure* of a field `F` in a field extension `E`,
also called the *maximal algebraic subextension* of `E / F`,
is defined to be the subalgebra `integralClosure F E`
upgraded to an intermediate field (since `F` and `E` are both fields).
This is exactly the intermediate field of `E / F` consisting of all integral/alg
ebraic elements.
-/
def algebraicClosure : IntermediateField F E :=
  Algebra.IsAlgebraic.toIntermediateField (integralClosure F E)

variable {F E}
/-
**algebraicClosure_toSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：algebraicClosure_toSubalgebra : (algebraicClosure F E).toSubalgebra = inte
gralClosure F E
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraicClosure_toSubalgebra : (algebraicClosure F E).toSubalgebra = integralClosure F E :=
  rfl

/-- An element is contained in the algebraic closure of `F` in `E` if and only if
it is an integral element. -/
/-
**mem_algebraicClosure_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_algebraicClosure_iff' {x : E} : x in algebraicClosure F E ↔ IsIntegral
 F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An element is contained in the algebraic closure of `F` in `E` if and only if
it is an integral element.
-/
theorem mem_algebraicClosure_iff' {x : E} :
    x ∈ algebraicClosure F E ↔ IsIntegral F x := Iff.rfl

/-- An element is contained in the algebraic closure of `F` in `E` if and only if
it is an algebraic element. -/
/-
**mem_algebraicClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_algebraicClosure_iff {x : E} : x in algebraicClosure F E ↔ IsAlgebraic
 F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `isAlgebraic_iff_isIntegral`：isAlgebraic_iff_isIntegral {x : A} : IsAlgeb
raic K x ↔ IsIntegral K x

--- 原说明 ---
An element is contained in the algebraic closure of `F` in `E` if and only if
it is an algebraic element.
-/
theorem mem_algebraicClosure_iff {x : E} :
    x ∈ algebraicClosure F E ↔ IsAlgebraic F x := isAlgebraic_iff_isIntegral.symm

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained in
`algebraicClosure F K` if and only if `x` is contained in `algebraicClosure F E`. -/
/-
**map_mem_algebraicClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：map_mem_algebraicClosure_iff (i : E ->ₐ[F] K) {x : E} : i x in algebraicCl
osure F K ↔ x in algebraicClosure F E
参数：i : E ->ₐ[F] K。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then `i x` is contained i
n
`algebraicClosure F K` if and only if `x` is contained in `algebraicClosure F E`
.
-/
theorem map_mem_algebraicClosure_iff (i : E →ₐ[F] K) {x : E} :
    i x ∈ algebraicClosure F K ↔ x ∈ algebraicClosure F E := by
  simp_rw [mem_algebraicClosure_iff', ← minpoly.ne_zero_iff, minpoly.algHom_eq i i.injective]

namespace algebraicClosure

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of
`algebraicClosure F K` under the map `i` is equal to `algebraicClosure F E`. -/
/-
**algebraicClosure.comap_eq_of_algHom** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClosur
e`。
形式化陈述：comap_eq_of_algHom (i : E ->ₐ[F] K) : (algebraicClosure F K).comap i = alg
ebraicClosure F E
参数：i : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.ext`：ext {S T : IntermediateField K L} (h : forall x, 
x in S ↔ x in T) : S = T
· 使用定理 `map_mem_algebraicClosure_iff`：map_mem_algebraicClosure_iff (i : E ->ₐ[F]
 K) {x : E} : i x in algebraicClosure F K ↔ x in algebraicClosure F E

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then the preimage of
`algebraicClosure F K` under the map `i` is equal to `algebraicClosure F E`.
-/
theorem comap_eq_of_algHom (i : E →ₐ[F] K) :
    (algebraicClosure F K).comap i = algebraicClosure F E := by
  ext x
  exact map_mem_algebraicClosure_iff i

/-- If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `algebraicClosure F E`
under the map `i` is contained in `algebraicClosure F K`. -/
/-
**algebraicClosure.map_le_of_algHom** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClosure`
。
形式化陈述：map_le_of_algHom (i : E ->ₐ[F] K) : (algebraicClosure F E).map i <= algebr
aicClosure F K
参数：i : E ->ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.map_le_iff_le_comap`：map_le_iff_le_comap {f : L ->ₐ[K]
 L'} {s : IntermediateField K L} {t : IntermediateField K L'} : s.map f <= t ↔ s
 <= t.comap f
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `algebraicClosure.comap_eq_of_algHom`：comap_eq_of_algHom (i : E ->ₐ[F] K)
 : (algebraicClosure F K).comap i = algebraicClosure F E

--- 原说明 ---
If `i` is an `F`-algebra homomorphism from `E` to `K`, then the image of `algebr
aicClosure F E`
under the map `i` is contained in `algebraicClosure F K`.
-/
theorem map_le_of_algHom (i : E →ₐ[F] K) :
    (algebraicClosure F E).map i ≤ algebraicClosure F K :=
  map_le_iff_le_comap.2 (comap_eq_of_algHom i).ge

variable (F) in
/-- If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial algebraic
subextensions (this means that it is purely transcendental),
then the image of `algebraicClosure F E` in `K` is equal to `algebraicClosure F K`. -/
/-
**algebraicClosure.map_eq_of_algebraicClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `
algebraicClosure`。
形式化陈述：map_eq_of_algebraicClosure_eq_bot [Algebra E K] [IsScalarTower F E K] (h :
 algebraicClosure E K = ⊥) : (algebraicClosure F E).map (IsScalarTower.toAlgHom 
F E K) = algebraicClosure F K
参数：h : algebraicClosure E K = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `algebraicClosure.map_le_of_algHom`：map_le_of_algHom (i : E ->ₐ[F] K) : (
algebraicClosure F E).map i <= algebraicClosure F K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_algebraicClosure_iff'`：mem_algebraicClosure_iff' {x : E} : x in alge
braicClosure F E ↔ IsIntegral F x
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `map_mem_algebraicClosure_iff`：map_mem_algebraicClosure_iff (i : E ->ₐ[F]
 K) {x : E} : i x in algebraicClosure F K ↔ x in algebraicClosure F E

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `K / E` has no non-trivial 
algebraic
subextensions (this means that it is purely transcendental),
then the image of `algebraicClosure F E` in `K` is equal to `algebraicClosure F 
K`.
-/
theorem map_eq_of_algebraicClosure_eq_bot [Algebra E K] [IsScalarTower F E K]
    (h : algebraicClosure E K = ⊥) :
    (algebraicClosure F E).map (IsScalarTower.toAlgHom F E K) = algebraicClosure F K := by
  refine le_antisymm (map_le_of_algHom _) (fun x hx ↦ ?_)
  obtain ⟨y, rfl⟩ := mem_bot.1 <| h ▸ mem_algebraicClosure_iff'.2
    (IsIntegral.tower_top <| mem_algebraicClosure_iff'.1 hx)
  exact ⟨y, (map_mem_algebraicClosure_iff <| IsScalarTower.toAlgHom F E K).mp hx, rfl⟩

/-- If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `algebraicClosure F E`
under the map `i` is equal to `algebraicClosure F K`. -/
/-
**algebraicClosure.map_eq_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClosur
e`。
形式化陈述：map_eq_of_algEquiv (i : E ≃ₐ[F] K) : (algebraicClosure F E).map i = algebr
aicClosure F K
参数：i : E ≃ₐ[F] K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `algebraicClosure.map_le_of_algHom`：map_le_of_algHom (i : E ->ₐ[F] K) : (
algebraicClosure F E).map i <= algebraicClosure F K
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_mem_algebraicClosure_iff`：map_mem_algebraicClosure_iff (i : E ->ₐ[F]
 K) {x : E} : i x in algebraicClosure F K ↔ x in algebraicClosure F E
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `i` is an `F`-algebra isomorphism of `E` and `K`, then the image of `algebrai
cClosure F E`
under the map `i` is equal to `algebraicClosure F K`.
-/
theorem map_eq_of_algEquiv (i : E ≃ₐ[F] K) :
    (algebraicClosure F E).map i = algebraicClosure F K :=
  (map_le_of_algHom i.toAlgHom).antisymm
    (fun x h ↦ ⟨_, (map_mem_algebraicClosure_iff i.symm).2 h, by simp⟩)

/-- If `E` and `K` are isomorphic as `F`-algebras, then `algebraicClosure F E` and
`algebraicClosure F K` are also isomorphic as `F`-algebras. -/
/-
**algebraicClosure.algEquivOfAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `algebraicClosur
e`。
形式化陈述：algEquivOfAlgEquiv (i : E ≃ₐ[F] K) : algebraicClosure F E ≃ₐ[F] algebraicC
losure F K
参数：i : E ≃ₐ[F] K。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `algebraicClosure.map_eq_of_algEquiv`：map_eq_of_algEquiv (i : E ≃ₐ[F] K) 
: (algebraicClosure F E).map i = algebraicClosure F K

--- 原说明 ---
If `E` and `K` are isomorphic as `F`-algebras, then `algebraicClosure F E` and
`algebraicClosure F K` are also isomorphic as `F`-algebras.
-/
def algEquivOfAlgEquiv (i : E ≃ₐ[F] K) :
    algebraicClosure F E ≃ₐ[F] algebraicClosure F K :=
  (intermediateFieldMap i _).trans (equivOfEq (map_eq_of_algEquiv i))

alias _root_.AlgEquiv.algebraicClosure := algEquivOfAlgEquiv

variable (F E K)

/-- The algebraic closure of `F` in `E` is algebraic over `F`. -/
/-
**algebraicClosure.isAlgebraic** 是 Mathlib 中的一个实例，位于命名空间 `algebraicClosure`。
形式化陈述：isAlgebraic : Algebra.IsAlgebraic F (algebraicClosure F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.isAlgebraic_iff`：isAlgebraic_iff {x : S} : IsAlgebraic
 K x ↔ IsAlgebraic K (x : L)
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The algebraic closure of `F` in `E` is algebraic over `F`.
-/
instance isAlgebraic : Algebra.IsAlgebraic F (algebraicClosure F E) :=
  ⟨fun x ↦ isAlgebraic_iff.mpr x.2.isAlgebraic⟩

/-- The algebraic closure of `F` in `E` is the integral closure of `F` in `E`. -/
/-
**algebraicClosure.isIntegralClosure** 是 Mathlib 中的一个实例，位于命名空间 `algebraicClosure
`。
形式化陈述：isIntegralClosure : IsIntegralClosure (algebraicClosure F E) F E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The algebraic closure of `F` in `E` is the integral closure of `F` in `E`.
-/
instance isIntegralClosure : IsIntegralClosure (algebraicClosure F E) F E :=
  inferInstanceAs (IsIntegralClosure (integralClosure F E) F E)

end algebraicClosure

/-
**Transcendental.algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 `Transcendental`。
形式化陈述：∀ {F : Type u_1} {E : Type u_2} [inst : Field F] [inst_1 : Field E] [inst_
2 : Algebra F E] {a : E},   Transcendental F a → Transcendental (↥(algebraicClos
ure F E)) a
参数：↥(algebraicClosure F E)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Transcendental.extendScalars`：extendScalars [Algebra.IsAlgebraic R S] : 
Transcendental S a
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
-/
protected theorem Transcendental.algebraicClosure {a : E} (ha : Transcendental F a) :
    Transcendental (algebraicClosure F E) a :=
  ha.extendScalars _

variable (F E K)

/-- An intermediate field of `E / F` is contained in the algebraic closure of `F` in `E`
if all of its elements are algebraic over `F`. -/
/-
**le_algebraicClosure'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_algebraicClosure' {L : IntermediateField F E} (hs : forall x : L, IsAlg
ebraic F x) : L <= algebraicClosure F E
参数：hs : forall x : L, IsAlgebraic F x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algebraMap_eq_zero_iff`：aeval_algebraMap_eq_zero_iff [I
sDomain A] [IsTorsionFree A B] [Nontrivial B] (x : A) (p : R[X]) : aeval (algebr
aMap A B x) p = 0 ↔ aeval x p…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L

--- 原说明 ---
An intermediate field of `E / F` is contained in the algebraic closure of `F` in
 `E`
if all of its elements are algebraic over `F`.
-/
theorem le_algebraicClosure' {L : IntermediateField F E} (hs : ∀ x : L, IsAlgebraic F x) :
    L ≤ algebraicClosure F E := fun x h ↦ by
  simpa only [mem_algebraicClosure_iff, IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    Algebra.algebraMap_self, RingHom.id_apply, IntermediateField.algebraMap_apply] using hs ⟨x, h⟩

/-- An intermediate field of `E / F` is contained in the algebraic closure of `F` in `E`
if it is algebraic over `F`. -/
/-
**le_algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_algebraicClosure (L : IntermediateField F E) [Algebra.IsAlgebraic F L] 
: L <= algebraicClosure F E
参数：L : IntermediateField F E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_algebraicClosure'`：le_algebraicClosure' {L : IntermediateField F E} (
hs : forall x : L, IsAlgebraic F x) : L <= algebraicClosure F E
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…

--- 原说明 ---
An intermediate field of `E / F` is contained in the algebraic closure of `F` in
 `E`
if it is algebraic over `F`.
-/
theorem le_algebraicClosure (L : IntermediateField F E) [Algebra.IsAlgebraic F L] :
    L ≤ algebraicClosure F E := le_algebraicClosure' F E (Algebra.IsAlgebraic.isAlgebraic)

/-- An intermediate field of `E / F` is contained in the algebraic closure of `F` in `E`
if and only if it is algebraic over `F`. -/
/-
**le_algebraicClosure_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_algebraicClosure_iff (L : IntermediateField F E) : L <= algebraicClosur
e F E ↔ Algebra.IsAlgebraic F L
参数：L : IntermediateField F E。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `SubfieldClass.toSubringClass`：∀ {S : Type u_1} {K : Type u_2} {inst : Di
visionRing K} {inst_1 : SetLike S K} [self : SubfieldClass S K],   SubringClass 
S K
· 使用定理 `IntermediateField.instSubfieldClass`：∀ {K : Type u_1} {L : Type u_2} [in
st : Field K] [inst_1 : Field L] [inst_2 : Algebra K L],   SubfieldClass (Interm
ediateField K L) L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.aeval_algebraMap_eq_zero_iff`：aeval_algebraMap_eq_zero_iff [I
sDomain A] [IsTorsionFree A B] [Nontrivial B] (x : A) (p : R[X]) : aeval (algebr
aMap A B x) p = 0 ↔ aeval x p…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHomCompTriple.comp_apply`：comp_apply [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
 {x : R₁} : σ₂₃ (σ₁₂ x) = σ₁₃ x
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_algebraicClosure`：le_algebraicClosure (L : IntermediateField F E) [Al
gebra.IsAlgebraic F L] : L <= algebraicClosure F E

--- 原说明 ---
An intermediate field of `E / F` is contained in the algebraic closure of `F` in
 `E`
if and only if it is algebraic over `F`.
-/
theorem le_algebraicClosure_iff (L : IntermediateField F E) :
    L ≤ algebraicClosure F E ↔ Algebra.IsAlgebraic F L :=
  ⟨fun h ↦ ⟨fun x ↦ by simpa only [IsAlgebraic, ne_eq, ← aeval_algebraMap_eq_zero_iff E,
    IntermediateField.algebraMap_apply,
    Algebra.algebraMap_self, RingHomCompTriple.comp_apply, mem_algebraicClosure_iff] using h x.2⟩,
    fun _ ↦ le_algebraicClosure _ _ _⟩

namespace algebraicClosure

/-- The algebraic closure in `E` of the algebraic closure of `F` in `E` is equal to itself. -/
/-
**algebraicClosure.algebraicClosure_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `algebraicC
losure`。
形式化陈述：algebraicClosure_eq_bot : algebraicClosure (algebraicClosure F E) E = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.mem_bot`：mem_bot {x : E} : x in (⊥ : IntermediateField
 F E) ↔ x in Set.range (algebraMap F E)
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_algebraicClosure_iff'`：mem_algebraicClosure_iff' {x : E} : x in alge
braicClosure F E ↔ IsIntegral F x

--- 原说明 ---
The algebraic closure in `E` of the algebraic closure of `F` in `E` is equal to 
itself.
-/
theorem algebraicClosure_eq_bot :
    algebraicClosure (algebraicClosure F E) E = ⊥ :=
  bot_unique fun x hx ↦ mem_bot.2
    ⟨⟨x, isIntegral_trans x (mem_algebraicClosure_iff'.1 hx)⟩, rfl⟩

/-- The normal closure in `E/F` of the algebraic closure of `F` in `E` is equal to itself. -/
/-
**algebraicClosure.normalClosure_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClo
sure`。
形式化陈述：normalClosure_eq_self : normalClosure F (algebraicClosure F E) E = algebra
icClosure F E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `normalClosure_le_iff`：normalClosure_le_iff {K' : IntermediateField F L} 
: normalClosure F K L <= K' ↔ forall f : K ->ₐ[F] L, f.fieldRange <= K'
· 使用定理 `le_algebraicClosure`：le_algebraicClosure (L : IntermediateField F E) [Al
gebra.IsAlgebraic F L] : L <= algebraicClosure F E
· 使用定理 `AlgEquiv.isAlgebraic`：AlgEquiv.isAlgebraic (e : A ≃ₐ[R] B) [Algebra.IsAl
gebraic R A] : Algebra.IsAlgebraic R B
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L

--- 原说明 ---
The normal closure in `E/F` of the algebraic closure of `F` in `E` is equal to i
tself.
-/
theorem normalClosure_eq_self :
    normalClosure F (algebraicClosure F E) E = algebraicClosure F E :=
  le_antisymm (normalClosure_le_iff.2 fun i ↦
    haveI : Algebra.IsAlgebraic F i.fieldRange := (AlgEquiv.ofInjectiveField i).isAlgebraic
    le_algebraicClosure F E _) (le_normalClosure _)

end algebraicClosure

/-- If `E / F` is a field extension and `E` is algebraically closed, then the algebraic closure
of `F` in `E` is equal to `F` if and only if `F` is algebraically closed. -/
/-
**IsAlgClosed.algebraicClosure_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsAlgClosed.algebraicClosure_eq_bot_iff [IsAlgClosed E] : algebraicClosure
 F E = ⊥ ↔ IsAlgClosed F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsAlgClosed.of_exists_root`：of_exists_root (H : forall p : k[X], p.Monic
 -> Irreducible p -> exists x, p.eval x = 0) : IsAlgClosed k
· 使用定理 `IsAlgClosed.exists_aeval_eq_zero`：exists_aeval_eq_zero {R : Type*} [Comm
Semiring R] [IsAlgClosed k] [Algebra R k] [FaithfulSMul R k] (p : R[X]) (hp : p.
degree != 0) : exists …
· 使用定理 `Module.Free.instFaithfulSMulOfNontrivial`：∀ (R : Type u) (M : Type v) [i
nst : Semiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Mod
ule.Free R M] [Nontrivial M], …
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Polynomial.degree_pos_of_irreducible`：degree_pos_of_irreducible (hp : Ir
reducible p) : 0 < p.degree
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_algebraicClosure_iff'`：mem_algebraicClosure_iff' {x : E} : x in alge
braicClosure F E ↔ IsIntegral F x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `minpoly.ne_zero_iff`：ne_zero_iff [Nontrivial A] : minpoly A x != 0 ↔ IsI
ntegral A x
· 使用定理 `ne_zero_of_dvd_ne_zero`：ne_zero_of_dvd_ne_zero {p q : α} (h₁ : q != 0) (
h₂ : p ∣ q) : p != 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `minpoly.dvd`：dvd {p : A[X]} (hp : Polynomial.aeval x p = 0) : minpoly A 
x ∣ p
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic`：IntermediateFiel
d.eq_bot_of_isAlgClosed_of_isAlgebraic {k K : Type*} [Field k] [Field K] [IsAlgC
losed k] [Algebra k K] (L : IntermediateFiel…

--- 原说明 ---
If `E / F` is a field extension and `E` is algebraically closed, then the algebr
aic closure
of `F` in `E` is equal to `F` if and only if `F` is algebraically closed.
-/
theorem IsAlgClosed.algebraicClosure_eq_bot_iff [IsAlgClosed E] :
    algebraicClosure F E = ⊥ ↔ IsAlgClosed F := by
  refine ⟨fun h ↦ IsAlgClosed.of_exists_root _ fun p hmon hirr ↦ ?_,
    fun _ ↦ IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic _⟩
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_aeval_eq_zero E p (degree_pos_of_irreducible hirr).ne'
  obtain ⟨x, rfl⟩ := h ▸ mem_algebraicClosure_iff'.2 (minpoly.ne_zero_iff.1 <|
    ne_zero_of_dvd_ne_zero hmon.ne_zero (minpoly.dvd _ x hx))
  exact ⟨x, by simpa [Algebra.ofId_apply] using hx⟩

/-- `F(S) / F` is an algebraic extension if and only if all elements of `S` are
algebraic elements. -/
/-
**IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic {S : Set E} : Algebra
.IsAlgebraic F (adjoin F S) ↔ forall x in S, IsAlgebraic F x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `le_algebraicClosure_iff`：le_algebraicClosure_iff (L : IntermediateField 
F E) : L <= algebraicClosure F E ↔ Algebra.IsAlgebraic F L
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Iff.imp`：∀ {a b c d : Prop}, (a ↔ c) → (b ↔ d) → (a → b ↔ c → d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `mem_algebraicClosure_iff`：mem_algebraicClosure_iff {x : E} : x in algebr
aicClosure F E ↔ IsAlgebraic F x

--- 原说明 ---
`F(S) / F` is an algebraic extension if and only if all elements of `S` are
algebraic elements.
-/
theorem IntermediateField.isAlgebraic_adjoin_iff_isAlgebraic {S : Set E} :
    Algebra.IsAlgebraic F (adjoin F S) ↔ ∀ x ∈ S, IsAlgebraic F x :=
  ((le_algebraicClosure_iff F E _).symm.trans (adjoin_le_iff.trans <| forall_congr' <|
    fun _ => Iff.imp Iff.rfl mem_algebraicClosure_iff))

namespace algebraicClosure

/-- If `E` is algebraically closed, then the algebraic closure of `F` in `E` is an absolute
algebraic closure of `F`. -/
/-
**algebraicClosure.isAlgClosure** 是 Mathlib 中的一个实例，位于命名空间 `algebraicClosure`。
形式化陈述：isAlgClosure [IsAlgClosed E] : IsAlgClosure F (algebraicClosure F E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsAlgClosed.algebraicClosure_eq_bot_iff`：IsAlgClosed.algebraicClosure_eq
_bot_iff [IsAlgClosed E] : algebraicClosure F E = ⊥ ↔ IsAlgClosed F
· 使用定理 `algebraicClosure.algebraicClosure_eq_bot`：algebraicClosure_eq_bot : alge
braicClosure (algebraicClosure F E) E = ⊥

--- 原说明 ---
If `E` is algebraically closed, then the algebraic closure of `F` in `E` is an a
bsolute
algebraic closure of `F`.
-/
instance isAlgClosure [IsAlgClosed E] : IsAlgClosure F (algebraicClosure F E) :=
  ⟨(IsAlgClosed.algebraicClosure_eq_bot_iff _ E).mp (algebraicClosure_eq_bot F E),
    isAlgebraic F E⟩

/-- The algebraic closure of `F` in `E` is equal to `E` if and only if `E / F` is
algebraic. -/
/-
**algebraicClosure.eq_top_iff** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClosure`。
形式化陈述：eq_top_iff : algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_algebraicClosure_iff`：mem_algebraicClosure_iff {x : E} : x in algebr
aicClosure F E ↔ IsAlgebraic F x
· 使用定理 `IntermediateField.mem_top`：mem_top {x : E} : x in (⊤ : IntermediateField
 F E)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `top_unique`：top_unique (h : ⊤ <= a) : a = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.IsAlgebraic.isAlgebraic`：∀ {R : Type u} {A : Type v} {inst : Com
mRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsAlgebraic 
R A] (x : A), IsAlgeb…

--- 原说明 ---
The algebraic closure of `F` in `E` is equal to `E` if and only if `E / F` is
algebraic.
-/
theorem eq_top_iff : algebraicClosure F E = ⊤ ↔ Algebra.IsAlgebraic F E :=
  ⟨fun h ↦ ⟨fun _ ↦ mem_algebraicClosure_iff.1 (h ▸ mem_top)⟩,
    fun _ ↦ top_unique fun x _ ↦ mem_algebraicClosure_iff.2 (Algebra.IsAlgebraic.isAlgebraic x)⟩

/-- If `K / E / F` is a field extension tower, then `algebraicClosure F K` is contained in
`algebraicClosure E K`. -/
/-
**algebraicClosure.le_restrictScalars** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClosur
e`。
形式化陈述：le_restrictScalars [Algebra E K] [IsScalarTower F E K] : algebraicClosure 
F K <= (algebraicClosure E K).restrictScalars F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_algebraicClosure_iff`：mem_algebraicClosure_iff {x : E} : x in algebr
aicClosure F E ↔ IsAlgebraic F x
· 使用定理 `IsAlgebraic.tower_top`：IsAlgebraic.tower_top {x : A} (A_alg : IsAlgebrai
c K x) : IsAlgebraic L x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b

--- 原说明 ---
If `K / E / F` is a field extension tower, then `algebraicClosure F K` is contai
ned in
`algebraicClosure E K`.
-/
theorem le_restrictScalars [Algebra E K] [IsScalarTower F E K] :
    algebraicClosure F K ≤ (algebraicClosure E K).restrictScalars F :=
  fun _ h ↦ mem_algebraicClosure_iff.2 <| IsAlgebraic.tower_top E (mem_algebraicClosure_iff.1 h)

/-- If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`algebraicClosure F K` is equal to `algebraicClosure E K`. -/
/-
**algebraicClosure.eq_restrictScalars_of_isAlgebraic** 是 Mathlib 中的一个定理，位于命名空间 `
algebraicClosure`。
形式化陈述：eq_restrictScalars_of_isAlgebraic [Algebra E K] [IsScalarTower F E K] [Alg
ebra.IsAlgebraic F E] : algebraicClosure F K = (algebraicClosure E K).restrictSc
alars F
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `algebraicClosure.le_restrictScalars`：le_restrictScalars [Algebra E K] [I
sScalarTower F E K] : algebraicClosure F K <= (algebraicClosure E K).restrictSca
lars F
· 使用定理 `isIntegral_trans`：isIntegral_trans [Algebra.IsIntegral R A] (x : B) (hx 
: IsIntegral A x) : IsIntegral R x
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A

--- 原说明 ---
If `K / E / F` is a field extension tower, such that `E / F` is algebraic, then
`algebraicClosure F K` is equal to `algebraicClosure E K`.
-/
theorem eq_restrictScalars_of_isAlgebraic [Algebra E K] [IsScalarTower F E K]
    [Algebra.IsAlgebraic F E] : algebraicClosure F K = (algebraicClosure E K).restrictScalars F :=
  (algebraicClosure.le_restrictScalars F E K).antisymm fun _ h ↦
    isIntegral_trans _ h

/-- If `K / E / F` is a field extension tower, then `E` adjoin `algebraicClosure F K` is contained
in `algebraicClosure E K`. -/
/-
**algebraicClosure.adjoin_le** 是 Mathlib 中的一个定理，位于命名空间 `algebraicClosure`。
形式化陈述：adjoin_le [Algebra E K] [IsScalarTower F E K] : adjoin E (algebraicClosure
 F K) <= algebraicClosure E K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IntermediateField.adjoin_le_iff`：adjoin_le_iff {S : Set E} {T : Intermed
iateField F E} : adjoin F S <= T ↔ S subseteq T
· 使用定理 `algebraicClosure.le_restrictScalars`：le_restrictScalars [Algebra E K] [I
sScalarTower F E K] : algebraicClosure F K <= (algebraicClosure E K).restrictSca
lars F

--- 原说明 ---
If `K / E / F` is a field extension tower, then `E` adjoin `algebraicClosure F K
` is contained
in `algebraicClosure E K`.
-/
theorem adjoin_le [Algebra E K] [IsScalarTower F E K] :
    adjoin E (algebraicClosure F K) ≤ algebraicClosure E K :=
  adjoin_le_iff.2 <| le_restrictScalars F E K

end algebraicClosure

variable {F}
/--
Let `E / F` be a field extension. If a polynomial `p`
splits in `E`, then it splits in the relative algebraic closure of `F` in `E` already.
-/
/-
**Splits.algebraicClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Splits.algebraicClosure {p : F[X]} (h : (p.map (algebraMap F E)).Splits) :
 (p.map (algebraMap F (algebraicClosure F E))).Splits
参数：h : (p.map (algebraMap F E)).Splits。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.splits_of_splits`：IntermediateField.splits_of_splits (
h : (p.map (algebraMap K L)).Splits) (hF : forall x in p.rootSet L, x in F) : (p
.map (algebraMap K F)).S…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Field K] [in
st_1 : Ring A] [inst_2 : Algebra K A] {x : A},   IsAlgebraic K x → IsIntegral K 
x
· 使用定理 `isAlgebraic_of_mem_rootSet`：isAlgebraic_of_mem_rootSet {R : Type u} {A :
 Type v} [CommRing R] [Field A] [Algebra R A] {p : R[X]} {x : A} (hx : x in p.ro
otSet A) : IsAlg…

--- 原说明 ---
Let `E / F` be a field extension. If a polynomial `p`
splits in `E`, then it splits in the relative algebraic closure of `F` in `E` al
ready.
-/
theorem Splits.algebraicClosure {p : F[X]} (h : (p.map (algebraMap F E)).Splits) :
    (p.map (algebraMap F (algebraicClosure F E))).Splits :=
  splits_of_splits h fun _ hx ↦ (isAlgebraic_of_mem_rootSet hx).isIntegral
