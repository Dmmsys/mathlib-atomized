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

/--
Definition of `characterSpace` / `characterSpace` 的定义

English:
definition characterSpace
  signature: (𝕜 : Type*) (A : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  body: {φ : WeakDual 𝕜 A | φ != 0 ∧ forall x y : A, φ (x * y) = φ x * φ y}

中文:
定义 characterSpace
  签名: (𝕜 : 类型) (A : 类型) [交换半环 𝕜] [拓扑空间 𝕜] [连续加法 𝕜]
  定义体: {φ : WeakDual 𝕜 A | φ != 0 ∧ forall x y : A, φ (x * y) = φ x * φ y}

Depends on / 依赖: WeakDual
-/
def characterSpace (𝕜 : Type*) (A : Type*) [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
    [ContinuousConstSMul 𝕜 𝕜] [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A] :=
  {φ : WeakDual 𝕜 A | φ != 0 ∧ forall x y : A, φ (x * y) = φ x * φ y}

variable {𝕜 : Type*} {A : Type*}

-- Even though the capitalization of the namespace differs, it doesn't matter
-- because there is no dot notation since `characterSpace` is only a type via `CoeSort`.
namespace CharacterSpace

section NonUnitalNonAssocSemiring

variable [CommSemiring 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
  [NonUnitalNonAssocSemiring A] [TopologicalSpace A] [Module 𝕜 A]

/--
Instance `instFunLike` / 实例 `instFunLike`

English:
instance instFunLike
  signature: : FunLike (characterSpace 𝕜 A) A 𝕜 where
  body: ((φ : WeakDual 𝕜 A) : A -> 𝕜)
  coe_injective φ ψ h := by ext1; apply DFunLike.ext; exact congr_fun h

中文:
实例 instFunLike
  签名: : 函数状 (characterSpace 𝕜 A) A 𝕜 where
  定义体: ((φ : WeakDual 𝕜 A) : A -> 𝕜)
  coe_injective φ ψ h := by ext1; apply DFunLike.ext; exact congr_fun h

Depends on / 依赖: WeakDual
-/
noncomputable instance instFunLike : FunLike (characterSpace 𝕜 A) A 𝕜 where
  coe φ := ((φ : WeakDual 𝕜 A) : A -> 𝕜)
  coe_injective φ ψ h := by ext1; apply DFunLike.ext; exact congr_fun h

/--
Instance `instContinuousLinearMapClass` / 实例 `instContinuousLinearMapClass`

English:
instance instContinuousLinearMapClass
  signature: : ContinuousLinearMapClass (characterSpace 𝕜 A) 𝕜 A 𝕜 where
  body: (φ : WeakDual 𝕜 A).map_smul
  map_add φ := (φ : WeakDual 𝕜 A).map_add
  map_continuous φ := (φ : WeakDual 𝕜 A).cont

中文:
实例 instContinuousLinearMapClass
  签名: : ContinuousLinearMapClass (characterSpace 𝕜 A) 𝕜 A 𝕜 where
  定义体: (φ : WeakDual 𝕜 A).map_smul
  map_add φ := (φ : WeakDual 𝕜 A).map_add
  map_continuous φ := (φ : WeakDual 𝕜 A).cont

Depends on / 依赖: WeakDual, map_smul
-/
instance instContinuousLinearMapClass : ContinuousLinearMapClass (characterSpace 𝕜 A) 𝕜 A 𝕜 where
  map_smulₛₗ φ := (φ : WeakDual 𝕜 A).map_smul
  map_add φ := (φ : WeakDual 𝕜 A).map_add
  map_continuous φ := (φ : WeakDual 𝕜 A).cont

/-- This has to come after `WeakDual.CharacterSpace.instFunLike`, otherwise the right-hand side
gets coerced via `Subtype.val` instead of directly via `DFunLike`. -/
@[simp, norm_cast]
/--
theorem `coe_coe` / 定理 `coe_coe`

English:
theorem coe_coe
  given: (φ : characterSpace 𝕜 A)
  statement: ⇑(φ : WeakDual 𝕜 A) = (φ : A -> 𝕜)
  proof: rfl

@[ext]

中文:
定理 coe_coe
  条件: (φ : characterSpace 𝕜 A)
  结论: ⇑(φ : WeakDual 𝕜 A) = (φ : A -> 𝕜)
  证明: rfl

@[ext]
-/
protected theorem coe_coe (φ : characterSpace 𝕜 A) : ⇑(φ : WeakDual 𝕜 A) = (φ : A -> 𝕜) :=
  rfl

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {φ ψ : characterSpace 𝕜 A} (h : forall x, φ x = ψ x)
  statement: φ = ψ
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: {φ ψ : characterSpace 𝕜 A} (h : 对任意 x, φ x = ψ x)
  结论: φ = ψ
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext {φ ψ : characterSpace 𝕜 A} (h : forall x, φ x = ψ x) : φ = ψ :=
  DFunLike.ext _ _ h

/--
Definition of `toCLM` / `toCLM` 的定义

English:
definition toCLM
  signature: (φ : characterSpace 𝕜 A)
  body: (φ : WeakDual 𝕜 A)

@[simp]

中文:
定义 toCLM
  签名: (φ : characterSpace 𝕜 A)
  定义体: (φ : WeakDual 𝕜 A)

@[simp]

Depends on / 依赖: WeakDual
-/
def toCLM (φ : characterSpace 𝕜 A) : A ->L[𝕜] 𝕜 :=
  (φ : WeakDual 𝕜 A)

@[simp]
/--
theorem `coe_toCLM` / 定理 `coe_toCLM`

English:
theorem coe_toCLM
  given: (φ : characterSpace 𝕜 A)
  statement: ⇑(toCLM φ) = φ
  proof: rfl

中文:
定理 coe_toCLM
  条件: (φ : characterSpace 𝕜 A)
  结论: ⇑(toCLM φ) = φ
  证明: rfl
-/
theorem coe_toCLM (φ : characterSpace 𝕜 A) : ⇑(toCLM φ) = φ :=
  rfl

/--
Instance `instNonUnitalAlgHomClass` / 实例 `instNonUnitalAlgHomClass`

English:
instance instNonUnitalAlgHomClass
  signature: : NonUnitalAlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜
  body: { CharacterSpace.instContinuousLinearMapClass with
    map_smulₛₗ := fun φ => map_smul φ
    map_zero := fun φ => map_zero φ
    map_mul := fun φ => φ.prop.2 }

中文:
实例 instNonUnitalAlgHomClass
  签名: : NonUnitalAlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜
  定义体: { CharacterSpace.instContinuousLinearMapClass with
    map_smulₛₗ := fun φ => map_smul φ
    map_zero := fun φ => map_zero φ
    map_mul := fun φ => φ.prop.2 }

Depends on / 依赖: CharacterSpace, CharacterSpace.instContinuousLinearMapClass, instContinuousLinearMapClass, map_mul, map_smul, map_zero
-/
instance instNonUnitalAlgHomClass : NonUnitalAlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜 :=
  { CharacterSpace.instContinuousLinearMapClass with
    map_smulₛₗ := fun φ => map_smul φ
    map_zero := fun φ => map_zero φ
    map_mul := fun φ => φ.prop.2 }

/--
Definition of `toNonUnitalAlgHom` / `toNonUnitalAlgHom` 的定义

English:
definition toNonUnitalAlgHom
  signature: (φ : characterSpace 𝕜 A)
  body: (φ : A -> 𝕜)
  map_mul' := map_mul φ
  map_smul' := map_smul φ
  map_zero' := map_zero φ
  map_add' := map_add φ

@[simp]

中文:
定义 toNonUnitalAlgHom
  签名: (φ : characterSpace 𝕜 A)
  定义体: (φ : A -> 𝕜)
  map_mul' := map_mul φ
  map_smul' := map_smul φ
  map_zero' := map_zero φ
  map_add' := map_add φ

@[simp]
-/
noncomputable def toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : A ->ₙₐ[𝕜] 𝕜 where
  toFun := (φ : A -> 𝕜)
  map_mul' := map_mul φ
  map_smul' := map_smul φ
  map_zero' := map_zero φ
  map_add' := map_add φ

@[simp]
/--
theorem `coe_toNonUnitalAlgHom` / 定理 `coe_toNonUnitalAlgHom`

English:
theorem coe_toNonUnitalAlgHom
  given: (φ : characterSpace 𝕜 A)
  statement: ⇑(toNonUnitalAlgHom φ) = φ
  proof: rfl

中文:
定理 coe_toNonUnitalAlgHom
  条件: (φ : characterSpace 𝕜 A)
  结论: ⇑(toNonUnitalAlgHom φ) = φ
  证明: rfl
-/
theorem coe_toNonUnitalAlgHom (φ : characterSpace 𝕜 A) : ⇑(toNonUnitalAlgHom φ) = φ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
Instance `instIsEmpty` / 实例 `instIsEmpty`

English:
instance instIsEmpty
  signature: [Subsingleton A]
  body: ⟨fun φ => φ.prop.1
    ContinuousLinearMap.ext fun x => by
      rw [show x = 0 from Subsingleton.elim x 0]; rw [map_zero]; rw [map_zero] ⟩

中文:
实例 instIsEmpty
  签名: [子单例 A]
  定义体: ⟨fun φ => φ.prop.1
    ContinuousLinearMap.ext fun x => by
      rw [show x = 0 from Subsingleton.elim x 0]; rw [map_zero]; rw [map_zero] ⟩

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.ext, Subsingleton, Subsingleton.elim, map_zero
-/
instance instIsEmpty [Subsingleton A] : IsEmpty (characterSpace 𝕜 A) :=
⟨fun φ => φ.prop.1
    ContinuousLinearMap.ext fun x => by
      rw [show x = 0 from Subsingleton.elim x 0]; rw [map_zero]; rw [map_zero] ⟩

variable (𝕜 A)

/--
theorem `union_zero` / 定理 `union_zero`

English:
theorem union_zero
  proof: le_antisymm (by
      rintro φ (hφ | rfl)
      · exact hφ.2
      · exact fun _ _ => by exact (zero_mul (0 : 𝕜)).symm)
    fun φ hφ => Or.elim (em <| φ = 0) Or.inr fun h₀ => Or.inl ⟨h₀, hφ⟩

中文:
定理 union_zero
  证明: le_antisymm (by
      rintro φ (hφ | rfl)
      · exact hφ.2
      · exact fun _ _ => by exact (zero_mul (0 : 𝕜)).symm)
    fun φ hφ => Or.elim (em <| φ = 0) Or.inr fun h₀ => Or.inl ⟨h₀, hφ⟩

Depends on / 依赖: Or.elim, Or.inl, Or.inr, le_antisymm, zero_mul
-/
theorem union_zero :
    characterSpace 𝕜 A union {0} = {φ : WeakDual 𝕜 A | forall x y : A, φ (x * y) = φ x * φ y} :=
  le_antisymm (by
      rintro φ (hφ | rfl)
      · exact hφ.2
      · exact fun _ _ => by exact (zero_mul (0 : 𝕜)).symm)
    fun φ hφ => Or.elim (em <| φ = 0) Or.inr fun h₀ => Or.inl ⟨h₀, hφ⟩

/--
theorem `union_zero_isClosed` / 定理 `union_zero_isClosed`

English:
theorem union_zero_isClosed
  given: [T2Space 𝕜] [ContinuousMul 𝕜]
  proof: by
  simp only [union_zero, Set.ofPred_forall]
  exact
    isClosed_iInter fun x =>
      isClosed_iInter fun y =>
isClosed_eq (eval_continuous _) (eval_continuous _).mul (eval_continuous _)

中文:
定理 union_zero_isClosed
  条件: [T2空间 𝕜] [连续乘法 𝕜]
  证明: by
  simp only [union_zero, Set.ofPred_forall]
  exact
    isClosed_iInter fun x =>
      isClosed_iInter fun y =>
isClosed_eq (eval_continuous _) (eval_continuous _).mul (eval_continuous _)

Depends on / 依赖: Set.ofPred_forall, eval_continuous, isClosed_eq, isClosed_iInter, ofPred_forall, union_zero
-/
theorem union_zero_isClosed [T2Space 𝕜] [ContinuousMul 𝕜] :
    IsClosed (characterSpace 𝕜 A union {0}) := by
  simp only [union_zero, Set.ofPred_forall]
  exact
    isClosed_iInter fun x =>
      isClosed_iInter fun y =>
isClosed_eq (eval_continuous _) (eval_continuous _).mul (eval_continuous _)

end NonUnitalNonAssocSemiring

section Unital

variable [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [TopologicalSpace A] [Semiring A] [Algebra 𝕜 A]

/--
Instance `instAlgHomClass` / 实例 `instAlgHomClass`

English:
instance instAlgHomClass
  signature: : AlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜
  body: haveI map_one' : forall φ : characterSpace 𝕜 A, φ 1 = 1 := fun φ => by
    have h₁ : φ 1 * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ← map_mul φ, one_mul]
    rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
    · have : forall a, φ (a * 1) = 0 := fun a => by simp only [map_mul φ, h₂, mul_zero]


中文:
实例 instAlgHomClass
  签名: : 代数态射类 (characterSpace 𝕜 A) 𝕜 A 𝕜
  定义体: haveI map_one' : forall φ : characterSpace 𝕜 A, φ 1 = 1 := fun φ => by
    have h₁ : φ 1 * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ← map_mul φ, one_mul]
    rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
    · have : forall a, φ (a * 1) = 0 := fun a => by simp only [map_mul φ, h₂, mul_zero]


Depends on / 依赖: CharacterSpace, CharacterSpace.instNonUnitalAlgHomClass, ContinuousLinearMap, ContinuousLinearMap.ext, False.elim, characterSpace, commutes, instNonUnitalAlgHomClass, map_mul, map_one, mul_eq_zero, mul_eq_zero.mp, mul_one, mul_sub, mul_zero, one_mul, sub_eq_zero, sub_eq_zero.mp
-/
instance instAlgHomClass : AlgHomClass (characterSpace 𝕜 A) 𝕜 A 𝕜 :=
  haveI map_one' : forall φ : characterSpace 𝕜 A, φ 1 = 1 := fun φ => by
    have h₁ : φ 1 * (1 - φ 1) = 0 := by rw [mul_sub, sub_eq_zero, mul_one, ← map_mul φ, one_mul]
    rcases mul_eq_zero.mp h₁ with (h₂ | h₂)
    · have : forall a, φ (a * 1) = 0 := fun a => by simp only [map_mul φ, h₂, mul_zero]
      exact False.elim (φ.prop.1 <| ContinuousLinearMap.ext <| by simpa only [mul_one] using! this)
    · exact (sub_eq_zero.mp h₂).symm
  { CharacterSpace.instNonUnitalAlgHomClass with
    map_one := map_one'
    commutes := fun φ r => by
      rw [Algebra.algebraMap_eq_smul_one]; rw [Algebra.algebraMap_self]; rw [RingHom.id_apply]
      rw [map_smul]; rw [smul_eq_mul]; rw [map_one' φ]; rw [mul_one] }

/-- An element of the character space of a unital algebra, as an algebra homomorphism. -/
@[simps]
/--
Definition of `toAlgHom` / `toAlgHom` 的定义

English:
definition toAlgHom
  signature: (φ : characterSpace 𝕜 A)
  body: { toNonUnitalAlgHom φ with
    map_one' := map_one φ
    commutes' := AlgHomClass.commutes φ }

中文:
定义 toAlgHom
  签名: (φ : characterSpace 𝕜 A)
  定义体: { toNonUnitalAlgHom φ with
    map_one' := map_one φ
    commutes' := AlgHomClass.commutes φ }

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, commutes, map_one, toNonUnitalAlgHom
-/
noncomputable def toAlgHom (φ : characterSpace 𝕜 A) : A ->ₐ[𝕜] 𝕜 :=
  { toNonUnitalAlgHom φ with
    map_one' := map_one φ
    commutes' := AlgHomClass.commutes φ }

/--
theorem `eq_set_map_one_map_mul` / 定理 `eq_set_map_one_map_mul`

English:
theorem eq_set_map_one_map_mul
  given: [Nontrivial 𝕜]
  proof: by
  ext φ
  refine ⟨?_, ?_⟩
  · rintro hφ
    lift φ to characterSpace 𝕜 A using hφ
    exact ⟨map_one φ, map_mul φ⟩
  · rintro ⟨hφ₁, hφ₂⟩
    refine ⟨?_, hφ₂⟩
    rintro rfl
    exact zero_ne_one hφ₁

中文:
定理 eq_set_map_one_map_mul
  条件: [非平凡 𝕜]
  证明: by
  ext φ
  refine ⟨?_, ?_⟩
  · rintro hφ
    lift φ to characterSpace 𝕜 A using hφ
    exact ⟨map_one φ, map_mul φ⟩
  · rintro ⟨hφ₁, hφ₂⟩
    refine ⟨?_, hφ₂⟩
    rintro rfl
    exact zero_ne_one hφ₁

Depends on / 依赖: characterSpace, map_mul, map_one, zero_ne_one
-/
theorem eq_set_map_one_map_mul [Nontrivial 𝕜] :
    characterSpace 𝕜 A = {φ : WeakDual 𝕜 A | φ 1 = 1 ∧ forall x y : A, φ (x * y) = φ x * φ y} := by
  ext φ
  refine ⟨?_, ?_⟩
  · rintro hφ
    lift φ to characterSpace 𝕜 A using hφ
    exact ⟨map_one φ, map_mul φ⟩
  · rintro ⟨hφ₁, hφ₂⟩
    refine ⟨?_, hφ₂⟩
    rintro rfl
    exact zero_ne_one hφ₁

/--
theorem `isClosed` / 定理 `isClosed`

English:
theorem isClosed
  given: [Nontrivial 𝕜] [T2Space 𝕜] [ContinuousMul 𝕜]
  proof: by
  rw [eq_set_map_one_map_mul]; rw [Set.ofPred_and]
  refine IsClosed.inter (isClosed_eq (eval_continuous _) continuous_const) ?_
  simpa only [(union_zero 𝕜 A).symm] using union_zero_isClosed _ _

中文:
定理 isClosed
  条件: [非平凡 𝕜] [T2空间 𝕜] [连续乘法 𝕜]
  证明: by
  rw [eq_set_map_one_map_mul]; rw [Set.ofPred_and]
  refine IsClosed.inter (isClosed_eq (eval_continuous _) continuous_const) ?_
  simpa only [(union_zero 𝕜 A).symm] using union_zero_isClosed _ _
-/
protected theorem isClosed [Nontrivial 𝕜] [T2Space 𝕜] [ContinuousMul 𝕜] :
    IsClosed (characterSpace 𝕜 A) := by
  rw [eq_set_map_one_map_mul]; rw [Set.ofPred_and]
  refine IsClosed.inter (isClosed_eq (eval_continuous _) continuous_const) ?_
  simpa only [(union_zero 𝕜 A).symm] using union_zero_isClosed _ _

end Unital

section Ring

variable [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜]
  [ContinuousConstSMul 𝕜 𝕜] [TopologicalSpace A] [Ring A] [Algebra 𝕜 A]

/--
theorem `apply_mem_spectrum` / 定理 `apply_mem_spectrum`

English:
theorem apply_mem_spectrum
  given: [Nontrivial 𝕜] (φ : characterSpace 𝕜 A) (a : A)
  statement: φ a in spectrum 𝕜 a
  proof: AlgHom.apply_mem_spectrum φ a

中文:
定理 apply_mem_spectrum
  条件: [非平凡 𝕜] (φ : characterSpace 𝕜 A) (a : A)
  结论: φ a in spectrum 𝕜 a
  证明: AlgHom.apply_mem_spectrum φ a

Depends on / 依赖: AlgHom, AlgHom.apply_mem_spectrum, apply_mem_spectrum
-/
theorem apply_mem_spectrum [Nontrivial 𝕜] (φ : characterSpace 𝕜 A) (a : A) : φ a in spectrum 𝕜 a :=
  AlgHom.apply_mem_spectrum φ a

/--
theorem `ext_ker` / 定理 `ext_ker`

English:
theorem ext_ker
  given: {φ ψ : characterSpace 𝕜 A} (h : RingHom.ker φ = RingHom.ker ψ)
  statement: φ = ψ
  proof: by
  ext x
  have : x - algebraMap 𝕜 A (ψ x) in RingHom.ker φ := by
    simpa only [h, RingHom.mem_ker, map_sub, AlgHomClass.commutes] using! sub_self (ψ x)
  rwa [RingHom.mem_ker, map_sub, AlgHomClass.commutes, sub_eq_zero] at this

中文:
定理 ext_ker
  条件: {φ ψ : characterSpace 𝕜 A} (h : 环态射.ker φ = 环态射.ker ψ)
  结论: φ = ψ
  证明: by
  ext x
  have : x - algebraMap 𝕜 A (ψ x) in RingHom.ker φ := by
    simpa only [h, RingHom.mem_ker, map_sub, AlgHomClass.commutes] using! sub_self (ψ x)
  rwa [RingHom.mem_ker, map_sub, AlgHomClass.commutes, sub_eq_zero] at this

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, RingHom, RingHom.ker, RingHom.mem_ker, algebraMap, commutes, map_sub, mem_ker, sub_eq_zero, sub_self
-/
theorem ext_ker {φ ψ : characterSpace 𝕜 A} (h : RingHom.ker φ = RingHom.ker ψ) : φ = ψ := by
  ext x
  have : x - algebraMap 𝕜 A (ψ x) in RingHom.ker φ := by
    simpa only [h, RingHom.mem_ker, map_sub, AlgHomClass.commutes] using! sub_self (ψ x)
  rwa [RingHom.mem_ker, map_sub, AlgHomClass.commutes, sub_eq_zero] at this

end Ring

end CharacterSpace

section Kernel

variable [Field 𝕜] [TopologicalSpace 𝕜] [ContinuousAdd 𝕜] [ContinuousConstSMul 𝕜 𝕜]
variable [Ring A] [TopologicalSpace A] [Algebra 𝕜 A]

/--
Instance `ker_isMaximal` / 实例 `ker_isMaximal`

English:
instance ker_isMaximal
  signature: (φ : characterSpace 𝕜 A)
  body: RingHom.ker_isMaximal_of_surjective φ fun z => ⟨algebraMap 𝕜 A z, by simp [AlgHomClass.commutes]⟩

中文:
实例 ker_isMaximal
  签名: (φ : characterSpace 𝕜 A)
  定义体: RingHom.ker_isMaximal_of_surjective φ fun z => ⟨algebraMap 𝕜 A z, by simp [AlgHomClass.commutes]⟩

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, RingHom, RingHom.ker_isMaximal_of_surjective, algebraMap, commutes, ker_isMaximal_of_surjective
-/
instance ker_isMaximal (φ : characterSpace 𝕜 A) : (RingHom.ker φ).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective φ fun z => ⟨algebraMap 𝕜 A z, by simp [AlgHomClass.commutes]⟩

end Kernel

section GelfandTransform

open ContinuousMap

variable (𝕜 A) [CommRing 𝕜] [NoZeroDivisors 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]
  [TopologicalSpace A] [Semiring A] [Algebra 𝕜 A]

/-- The **Gelfand transform** is an algebra homomorphism (over `𝕜`) from a topological `𝕜`-algebra
`A` into the `𝕜`-algebra of continuous `𝕜`-valued functions on the `characterSpace 𝕜 A`.
The character space itself consists of all algebra homomorphisms from `A` to `𝕜`. -/
@[simps]
/--
Definition of `gelfandTransform` / `gelfandTransform` 的定义

English:
definition gelfandTransform
  signature: : A ->ₐ[𝕜] C(characterSpace 𝕜 A, 𝕜) where
  body: { toFun := fun φ => φ a
      continuous_toFun := (eval_continuous a).comp continuous_induced_dom }
  map_one' := by ext a; simp only [coe_mk, coe_one, Pi.one_apply, map_one a]
  map_mul' a b := by ext; simp only [map_mul, coe_mk, coe_mul, Pi.mul_apply]
  map_zero' := by ext; simp only [map_zero, co

中文:
定义 gelfandTransform
  签名: : A ->ₐ[𝕜] C(characterSpace 𝕜 A, 𝕜) where
  定义体: { toFun := fun φ => φ a
      continuous_toFun := (eval_continuous a).comp continuous_induced_dom }
  map_one' := by ext a; simp only [coe_mk, coe_one, Pi.one_apply, map_one a]
  map_mul' a b := by ext; simp only [map_mul, coe_mk, coe_mul, Pi.mul_apply]
  map_zero' := by ext; simp only [map_zero, co

Depends on / 依赖: AlgHomClass, AlgHomClass.commutes, Pi.add_apply, Pi.mul_apply, Pi.one_apply, Pi.zero_apply, add_apply, coe_add, coe_mk, coe_mul, coe_one, coe_zero, commutes, continuous_induced_dom, continuous_toFun, eval_continuous, map_add, map_mul, map_one, map_zero
-/
noncomputable def gelfandTransform : A ->ₐ[𝕜] C(characterSpace 𝕜 A, 𝕜) where
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
