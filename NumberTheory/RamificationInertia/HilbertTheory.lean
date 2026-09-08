/-
Copyright (c) 2026 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-!

# Decomposition and Inertia fields

In this file, we develop Hilbert Theory on the splitting of prime ideals in a Galois extension.

Let `L/K` be a Galois extension of fields. Let `A` and `B` be subrings of `K` `L` respectively with
`K` fraction field of `A`, `L` fraction field of `B` and `B` the integral closure of `A` in `L`.

For `P` a prime ideal of `B` lying over the prime ideal `p` of `A`, the decomposition field `D` of
`P` in `L/K` is the subfield of elements of `L` fixed by the stabilizer of `P` in `Gal(L/K)`, and
the inertia field `E` of `P` in `L/K` is the subfield of elements of `L` fixed by the inertia
group of `P` in `Gal(L/K)`.

Let `e` and `f` the ramification index and inertia degree of `P` over `p` and let `g`
be the number of prime ideals above `p` in `L`. Denote by `𝓟D`, resp. `𝓟E`, the prime ideal of `D`,
resp. `E`, below `P`. Then we have the following properties
```
degree            ramif. index   inertia deg.
        L      P
  e     |      |      e               1
        E      𝓟E
  f     |      |      1               f
        D      𝓟D
  g     |      |      1               1
        K      p
```

-/

@[expose] public section

variable (A K L : Type*) {B : Type*} [Field K] [Field L] [Algebra K L] [CommRing A] [CommRing B]
  [Algebra A B] {p : Ideal A} (P : Ideal B) [P.LiesOver p]

open MulAction Pointwise Ideal

section basic

variable (D : Type*) [Field D] [Algebra D L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield fixed by the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
@[mk_iff]
/-
**IsDecompositionField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_2) →   (L : Type u_3) →     {B : Type u_4} →       [inst : Fie
ld K] →         [inst_1 : Field L] →           [inst_2 : Algebra K L] →         
    [inst_3 : CommRing B] →               Ideal B → (D : Type u_5) → [inst_4 : F
ield D] → [Algebra D L] → [MulSemiringAction Gal(L/K) B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. T
he predicate that
says that `D` is the decomposition field of `P` in `L/K`, that is the subfield f
ixed by the
decomposition subgroup of `P`, that is the stabilizer of `P` in `Gal(L/K)`.
-/
class IsDecompositionField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (stabilizer Gal(L/K) P) D L
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (stabilizer Gal(L/K) P) D L] :
    IsDecompositionField K L P D := { toIsGaloisGroup := h }

variable (E : Type*) [Field E] [Algebra E L]

/--
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. The predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed by the inertia
subgroup of `P` in `Gal(L/K)`.
-/
@[mk_iff]
/-
**IsInertiaField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_2) →   (L : Type u_3) →     {B : Type u_4} →       [inst : Fie
ld K] →         [inst_1 : Field L] →           [inst_2 : Algebra K L] →         
    [inst_3 : CommRing B] →               Ideal B → (E : Type u_6) → [inst_4 : F
ield E] → [Algebra E L] → [MulSemiringAction Gal(L/K) B] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Let `L/K` be a Galois extension of fields and let `P` be a prime ideal of `B`. T
he predicate that
says that `E` is the inertia field of `P` in `L/K`, that is the subfield fixed b
y the inertia
subgroup of `P` in `Gal(L/K)`.
-/
class IsInertiaField [MulSemiringAction Gal(L/K) B] extends
    IsGaloisGroup (inertia Gal(L/K) P) E L
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [MulSemiringAction Gal(L/K) B] [h : IsGaloisGroup (inertia Gal(L/K) P) E L] :
    IsInertiaField K L P E := { toIsGaloisGroup := h }

variable [MulSemiringAction Gal(L/K) B]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsGalois K L] : IsDecompositionField K L P
    (FixedPoints.intermediateField (stabilizer Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (stabilizer Gal(L/K) P)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsGalois K L] : IsInertiaField K L P
    (FixedPoints.intermediateField (inertia Gal(L/K) P) : IntermediateField K L) where
  toIsGaloisGroup := IsGaloisGroup.subgroup Gal(L/K) K L (inertia Gal(L/K) P)

variable (G : Type*) [Group G] [Finite G] [MulSemiringAction G L] [IsGaloisGroup G K L]
  [MulSemiringAction G B]

section of_isGaloisGroup

variable [Algebra B L] [IsFractionRing B L] [SMulDistribClass Gal(L/K) B L] [SMulDistribClass G B L]

/--
If `G` is a Galois group for `L/K` and the stabilizer of `P` in `G` is a Galois group for
`L/D`, then `D` is a decomposition field for `P`.
-/
/-
**IsDecompositionField.of_isGaloisGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) 
D L] : IsDecompositionField K L P D
参数：stabilizer G P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isDecompositionField_iff`：∀ (K : Type u_2) (L : Type u_3) {B : Type u_4}
 [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : CommRing
 B] (P : Ideal…
· 使用定理 `IsGaloisGroup.of_mulEquiv`：of_mulEquiv [hG : IsGaloisGroup G A B] {H : T
ype*} [Group H] [MulSemiringAction H B] (e : H ≃* G) (he : forall h (x : B), (e 
h) • x = h • x)…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap.smul'`：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] 
[SMulDistribClass A B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
· 使用定理 `IsGaloisGroup.mulEquivAlgEquiv_apply_apply`：∀ (G : Type u_1) [inst : Gro
up G] (A : Type u_2) (B : Type u_3) [inst_1 : CommRing A] [inst_2 : CommRing B] 
  [inst_3 : IsDomain B] [inst_4 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `smul_div₀'`：smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • 
y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.stabilizerEquiv_symm_apply_smul`：stabilizerEquiv_symm_apply_smul (
I : Ideal R) (e : M ≃* N) (he : forall (m : M) (x : R), (e m) • x = m • x) (n : 
MulAction.stabilizer N I) (…

--- 原说明 ---
If `G` is a Galois group for `L/K` and the stabilizer of `P` in `G` is a Galois 
group for
`L/D`, then `D` is a decomposition field for `P`.
-/
theorem IsDecompositionField.of_isGaloisGroup [h : IsGaloisGroup (stabilizer G P) D L] :
    IsDecompositionField K L P D := by
  refine (isDecompositionField_iff K L P D).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (stabilizerEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      stabilizerEquiv_symm_apply_smul]

/--
If `G` is a Galois group for `L/K` and the inertia group of `P` in `G` is a Galois group for
`L/E`, then `E` is an inertia field for `P`.
-/
/-
**IsInertiaField.of_isGaloisGroup** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) E L] : Is
InertiaField K L P E
参数：inertia G P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isInertiaField_iff`：∀ (K : Type u_2) (L : Type u_3) {B : Type u_4} [inst
 : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : CommRing B] (P
 : Ideal…
· 使用定理 `IsGaloisGroup.of_mulEquiv`：of_mulEquiv [hG : IsGaloisGroup G A B] {H : T
ype*} [Group H] [MulSemiringAction H B] (e : H ≃* G) (he : forall h (x : B), (e 
h) • x = h • x)…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `IsFractionRing.instFaithfulSMul`：∀ (R : Type u_1) [inst : CommRing R] (K
 : Type u_5) [inst_1 : CommRing K] [inst_2 : Algebra R K] [IsFractionRing R K], 
  FaithfulSMul R K
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `algebraMap.smul'`：algebraMap.smul' [Monoid A] [MulDistribMulAction A C] 
[SMulDistribClass A B C] : algebraMap B C (a • b) = a • (algebraMap B C b)
· 使用定理 `IsGaloisGroup.mulEquivAlgEquiv_apply_apply`：∀ (G : Type u_1) [inst : Gro
up G] (A : Type u_2) (B : Type u_3) [inst_1 : CommRing A] [inst_2 : CommRing B] 
  [inst_3 : IsDomain B] [inst_4 …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `IsFractionRing.div_surjective`：div_surjective (z : K) : exists x y : A, 
y in nonZeroDivisors A ∧ algebraMap _ _ x / algebraMap _ _ y = z
· 使用定理 `smul_div₀'`：smul_div₀' (g : α) (x y : β) : g • (x / y) = (g • x) / (g • 
y)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Ideal.inertiaEquiv_symm_apply_smul`：inertiaEquiv_symm_apply_smul {R : Ty
pe*} [Ring R] [MulSemiringAction M R] [MulSemiringAction N R] (I : Ideal R) (e :
 M ≃* N) (he : forall (m…

--- 原说明 ---
If `G` is a Galois group for `L/K` and the inertia group of `P` in `G` is a Galo
is group for
`L/E`, then `E` is an inertia field for `P`.
-/
theorem IsInertiaField.of_isGaloisGroup [h : IsGaloisGroup (inertia G P) E L] :
    IsInertiaField K L P E := by
  refine (isInertiaField_iff K L P E).mpr <| .of_mulEquiv (hG := h) ?_ fun _ x ↦ ?_
  · refine (inertiaEquiv _ (IsGaloisGroup.mulEquivAlgEquiv G K L) fun _ _ ↦ ?_).symm
    apply FaithfulSMul.algebraMap_injective B L
    simp [algebraMap.smul']
  · obtain ⟨y, z, _, rfl⟩ := IsFractionRing.div_surjective B x
    simp_rw [smul_div₀', subgroup_smul_def, ← algebraMap.smul', ← subgroup_smul_def,
      inertiaEquiv_symm_apply_smul]

end of_isGaloisGroup

variable (D' : Type*) [Field D'] [Algebra D' L] (E' : Type*) [Field E'] [Algebra E' L]

/-- Two decomposition fields are isomorphic. -/
/-
**IsDecompositionField.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsDecompositionField.ringEquiv [IsDecompositionField K L P D] [IsDecomposi
tionField K L P D'] : D ≃+* D'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsDecompositionField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B
 : Type u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_
3 : CommRing B} {P : Ideal…

--- 原说明 ---
Two decomposition fields are isomorphic.
-/
noncomputable def IsDecompositionField.ringEquiv [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] :
    D ≃+* D' :=
  IsGaloisGroup.ringEquiv (stabilizer Gal(L/K) P) D D' L

@[simp]
/-
**IsDecompositionField.algebraMap_ringEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L 
P D] [IsDecompositionField K L P D'] (x : D) : algebraMap D' L (IsDecompositionF
ield.ringEquiv K L P D D' x) = algebraMap D L x
参数：x : D。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDecompositionField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B
 : Type u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_
3 : CommRing B} {P : Ideal…
· 使用定理 `IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply`：algebraMap_rin
gEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) : algebraMap A B 
((ringEquivFixedPoints G A B).symm x) = x
· 使用定理 `IsGaloisGroup.ringEquivFixedPoints_apply_coe`：∀ (G : Type u_1) (A : Type
 u_2) (B : Type u_4) [inst : Group G] [inst_1 : CommSemiring A] [inst_2 : Semiri
ng B]   [inst_3 : Algebra A B] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsDecompositionField.algebraMap_ringEquiv_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D) :
    algebraMap D' L (IsDecompositionField.ringEquiv K L P D D' x) = algebraMap D L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
/-
**IsDecompositionField.algebraMap_ringEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField
 K L P D] [IsDecompositionField K L P D'] (x : D') : algebraMap D L ((IsDecompos
itionField.ringEquiv K L P D D').symm x) = algebraMap D' L x
参数：x : D'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsDecompositionField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B
 : Type u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_
3 : CommRing B} {P : Ideal…
· 使用定理 `IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply`：algebraMap_rin
gEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) : algebraMap A B 
((ringEquivFixedPoints G A B).symm x) = x
· 使用定理 `IsGaloisGroup.ringEquivFixedPoints_apply_coe`：∀ (G : Type u_1) (A : Type
 u_2) (B : Type u_4) [inst : Group G] [inst_1 : CommSemiring A] [inst_2 : Semiri
ng B]   [inst_3 : Algebra A B] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsDecompositionField.algebraMap_ringEquiv_symm_apply [IsDecompositionField K L P D]
    [IsDecompositionField K L P D'] (x : D') :
    algebraMap D L ((IsDecompositionField.ringEquiv K L P D D').symm x) = algebraMap D' L x := by
  simp [IsDecompositionField.ringEquiv, IsGaloisGroup.ringEquiv]

/-- Two inertia fields are isomorphic. -/
/-
**IsInertiaField.ringEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'
] : E ≃+* E'
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsInertiaField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B : Typ
e u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_3 : Co
mmRing B} {P : Ideal…

--- 原说明 ---
Two inertia fields are isomorphic.
-/
noncomputable def IsInertiaField.ringEquiv [IsInertiaField K L P E] [IsInertiaField K L P E'] :
    E ≃+* E' :=
  IsGaloisGroup.ringEquiv (inertia Gal(L/K) P) E E' L

@[simp]
/-
**IsInertiaField.algebraMap_ringEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E] [IsIner
tiaField K L P E'] (x : E) : algebraMap E' L (IsInertiaField.ringEquiv K L P E E
' x) = algebraMap E L x
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsInertiaField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B : Typ
e u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_3 : Co
mmRing B} {P : Ideal…
· 使用定理 `IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply`：algebraMap_rin
gEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) : algebraMap A B 
((ringEquivFixedPoints G A B).symm x) = x
· 使用定理 `IsGaloisGroup.ringEquivFixedPoints_apply_coe`：∀ (G : Type u_1) (A : Type
 u_2) (B : Type u_4) [inst : Group G] [inst_1 : CommSemiring A] [inst_2 : Semiri
ng B]   [inst_3 : Algebra A B] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsInertiaField.algebraMap_ringEquiv_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E) :
    algebraMap E' L (IsInertiaField.ringEquiv K L P E E' x) = algebraMap E L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

@[simp]
/-
**IsInertiaField.algebraMap_ringEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInertiaField.algebraMap_ringEquiv_symm_apply [IsInertiaField K L P E] [I
sInertiaField K L P E'] (x : E') : algebraMap E L ((IsInertiaField.ringEquiv K L
 P E E').symm x) = algebraMap E' L x
参数：x : E'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsInertiaField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B : Typ
e u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_3 : Co
mmRing B} {P : Ideal…
· 使用定理 `IsGaloisGroup.algebraMap_ringEquivFixedPoints_symm_apply`：algebraMap_rin
gEquivFixedPoints_symm_apply (x : FixedPoints.subsemiring B G) : algebraMap A B 
((ringEquivFixedPoints G A B).symm x) = x
· 使用定理 `IsGaloisGroup.ringEquivFixedPoints_apply_coe`：∀ (G : Type u_1) (A : Type
 u_2) (B : Type u_4) [inst : Group G] [inst_1 : CommSemiring A] [inst_2 : Semiri
ng B]   [inst_3 : Algebra A B] [in…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsInertiaField.algebraMap_ringEquiv_symm_apply [IsInertiaField K L P E]
    [IsInertiaField K L P E'] (x : E') :
    algebraMap E L ((IsInertiaField.ringEquiv K L P E E').symm x) = algebraMap E' L x := by
  simp [IsInertiaField.ringEquiv, IsGaloisGroup.ringEquiv]

end basic

section rank

attribute [local instance] Ideal.Quotient.field

variable [FiniteDimensional K L] [MulSemiringAction Gal(L/K) B]
  [IsGaloisGroup Gal(L/K) A B] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Ring.HasFiniteQuotients A] [P.IsMaximal]

variable (D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D]

include K P

/--
The degree `[L : D]` of `L` over the decomposition field `D` equals the product of the
ramification index and the inertia degree of `p` in `B`.
-/
/-
**IsDecompositionField.rank_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDecompositionField.rank_left (hp : p != ⊥) : Module.finrank D L = p.rami
ficationIdxIn B * p.inertiaDegIn B
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
· 使用定理 `IsDecompositionField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B
 : Type u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_
3 : CommRing B} {P : Ideal…
· 使用引理 `Ideal.card_stabilizer_eq`：card_stabilizer_eq [IsDomain R] [IsDomain S] [
Module.Finite R S] [Flat R S] (p : Ideal R) (P : Ideal S) [P.LiesOver p] [p.IsPr
ime] [P.IsPrim…
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instFiniteResidueFieldOfQuotientIdeal`：∀ {R : Type u_1} [inst : CommRing
 R] (I : Ideal R) [inst_1 : I.IsPrime] [Finite (R ⧸ I)], Finite I.ResidueField

--- 原说明 ---
The degree `[L : D]` of `L` over the decomposition field `D` equals the product 
of the
ramification index and the inertia degree of `p` in `B`.
-/
theorem IsDecompositionField.rank_left (hp : p ≠ ⊥) :
    Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L, card_stabilizer_eq p]

/--
The degree `[D : K]` of the decomposition field `D` over `K` equals the number of prime ideals
of `B` lying over `p`.
-/
/-
**IsDecompositionField.rank_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTowe
r K D L] (hp : p != ⊥) : Module.finrank K D = (p.primesOver B).ncard
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `FiniteDimensional.right`：∀ (F : Type u) (K : Type v) (A : Type w) [inst 
: Semiring F] [inst_1 : Semiring K] [inst_2 : _root_.Module F K]   [inst_3 : Add
CommMonoid A]…
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `IsDecompositionField.rank_left`：IsDecompositionField.rank_left (hp : p !
= ⊥) : Module.finrank D L = p.ramificationIdxIn B * p.inertiaDegIn B
· 使用定理 `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`：ncard_pri
mesOver_mul_ramificationIdxIn_mul_inertiaDegIn : (primesOver p B).ncard * (ramif
icationIdxIn p B * inertiaDegIn p B) = Nat.card G
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L

--- 原说明 ---
The degree `[D : K]` of the decomposition field `D` over `K` equals the number o
f prime ideals
of `B` lying over `p`.
-/
theorem IsDecompositionField.rank_right [IsGalois K L] [Algebra K D] [IsScalarTower K D L]
    (hp : p ≠ ⊥) :
    Module.finrank K D = (p.primesOver B).ncard := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional D L := FiniteDimensional.right K D L
  refine mul_left_injective₀ (b := Module.finrank D L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P D hp,
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

variable (E : Type*) [Field E] [Algebra E L] [IsInertiaField K L P E]

/--
The degree `[L : E]` of `L` over the inertia field `E` equals the ramification index of `p` in `B`.
-/
/-
**IsInertiaField.rank_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInertiaField.rank_left (hp : p != ⊥) : Module.finrank E L = p.ramificati
onIdxIn B
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Ring.HasFiniteQuotients.finiteQuotient`：∀ {R : Type u_1} {inst : CommRin
g R} [self : Ring.HasFiniteQuotients R] {I : Ideal R}, I ≠ ⊥ → Finite (R ⧸ I)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsGaloisGroup.card_eq_finrank`：card_eq_finrank [IsGaloisGroup G K L] : N
at.card G = Module.finrank K L
· 使用定理 `IsInertiaField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B : Typ
e u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_3 : Co
mmRing B} {P : Ideal…
· 使用引理 `Ideal.card_inertia_eq_ramificationIdxIn`：card_inertia_eq_ramificationIdx
In [IsDomain R] [IsDomain S] [Module.Finite R S] [Flat R S] (p : Ideal R) (P : I
deal S) [P.LiesOver p] [p.IsP…
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `instFiniteResidueFieldOfQuotientIdeal`：∀ {R : Type u_1} [inst : CommRing
 R] (I : Ideal R) [inst_1 : I.IsPrime] [Finite (R ⧸ I)], Finite I.ResidueField

--- 原说明 ---
The degree `[L : E]` of `L` over the inertia field `E` equals the ramification i
ndex of `p` in `B`.
-/
theorem IsInertiaField.rank_left (hp : p ≠ ⊥) :
    Module.finrank E L = p.ramificationIdxIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : Finite (A ⧸ p) := Ring.HasFiniteQuotients.finiteQuotient hp
  rw [← IsGaloisGroup.card_eq_finrank (inertia Gal(L/K) P) E L, card_inertia_eq_ramificationIdxIn p]

/--
The degree `[E : K]` of the inertia field `E` over `K` equals the product of the number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`.
-/
/-
**IsInertiaField.rank_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E 
L] (hp : p != ⊥) : Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn 
B
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `FiniteDimensional.right`：∀ (F : Type u) (K : Type v) (A : Type w) [inst 
: Semiring F] [inst_1 : Semiring K] [inst_2 : _root_.Module F K]   [inst_3 : Add
CommMonoid A]…
· 使用定理 `mul_left_injective₀`：mul_left_injective₀ (hb : b != 0) : Function.Inject
ive fun a => a * b
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Module.finrank_pos`：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] 
[h : Nontrivial M] : 0 < finrank R M
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Module.FaithfullyFlat.toFlat`：∀ {R : Type u} {M : Type v} {inst : CommRi
ng R} {inst_1 : AddCommGroup M} {inst_2 : _root_.Module R M}   [self : Module.Fa
ithfullyFlat R M],…
· 使用定理 `Module.FaithfullyFlat.instOfNontrivialOfFree`：∀ (R : Type u) (M : Type v
) [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] [No
ntrivial M]   [Module.Free R M], M…
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `IsInertiaField.rank_left`：IsInertiaField.rank_left (hp : p != ⊥) : Modul
e.finrank E L = p.ramificationIdxIn B
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`：ncard_pri
mesOver_mul_ramificationIdxIn_mul_inertiaDegIn : (primesOver p B).ncard * (ramif
icationIdxIn p B * inertiaDegIn p B) = Nat.card G
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The degree `[E : K]` of the inertia field `E` over `K` equals the product of the
 number of
prime ideals of `B` lying over `p` and the inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_right [IsGalois K L] [Algebra K E] [IsScalarTower K E L] (hp : p ≠ ⊥) :
    Module.finrank K E = (p.primesOver B).ncard * p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have : FiniteDimensional E L := FiniteDimensional.right K E L
  refine mul_left_injective₀ (b := Module.finrank E L) Module.finrank_pos.ne' ?_
  dsimp only
  rw [Module.finrank_mul_finrank, rank_left A K L P E hp, mul_assoc, mul_comm (p.inertiaDegIn B),
    ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn p B Gal(L/K),
    IsGaloisGroup.card_eq_finrank Gal(L/K) K L]

/--
The degree `[E : D]` of the inertia field `E` over the decomposition field `D` equals the
inertia degree of `p` in `B`.
-/
/-
**IsInertiaField.rank_decompositionField** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algeb
ra K E] [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower
 K D L] (hp : p != ⊥) : Module.finrank D E = p.inertiaDegIn B
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.under`：∀ (A : Type u_1) [inst : CommRing A] {B : Type u_
2} [inst_1 : CommRing B] [inst_2 : Algebra A B]   [Algebra.IsIntegral A B] (P : 
Ideal B) [P…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.over_def`：over_def [P.LiesOver p] : p = P.under A
· 使用定理 `Module.finrank_mul_finrank`：Module.finrank_mul_finrank : finrank F K * f
inrank K A = finrank F A
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `mul_right_inj'`：mul_right_inj' (ha : a != 0) : a * b = a * c ↔ b = c
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `IsDedekindDomain.primesOver_ncard_ne_zero`：primesOver_ncard_ne_zero : (p
rimesOver p B).ncard != 0
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDecompositionField.rank_right`：IsDecompositionField.rank_right [IsGalo
is K L] [Algebra K D] [IsScalarTower K D L] (hp : p != ⊥) : Module.finrank K D =
 (p.primesOver B).nca…
· 使用定理 `IsInertiaField.rank_right`：IsInertiaField.rank_right [IsGalois K L] [Alg
ebra K E] [IsScalarTower K E L] (hp : p != ⊥) : Module.finrank K E = (p.primesOv
er B).ncard * p…

--- 原说明 ---
The degree `[E : D]` of the inertia field `E` over the decomposition field `D` e
quals the
inertia degree of `p` in `B`.
-/
theorem IsInertiaField.rank_decompositionField [IsGalois K L] [Algebra K D] [Algebra K E]
    [Algebra D E] [IsScalarTower K D E] [IsScalarTower K E L] [IsScalarTower K D L] (hp : p ≠ ⊥) :
    Module.finrank D E = p.inertiaDegIn B := by
  have : p.IsMaximal := over_def P p ▸ Ideal.IsMaximal.under A P
  have := Module.finrank_mul_finrank K D E
  rwa [IsInertiaField.rank_right A K L P E hp, IsDecompositionField.rank_right A K L P D hp,
    mul_right_inj'] at this
  exact IsDedekindDomain.primesOver_ncard_ne_zero p B

end rank

section splitting

variable [Algebra A K] [IsFractionRing A K] [Algebra A L] [IsScalarTower A K L] [Algebra B L]
  [IsScalarTower A B L] [IsFractionRing B L] [MulSemiringAction Gal(L/K) B]
  [SMulDistribClass Gal(L/K) B L]

namespace IsDecompositionField

variable (D 𝓞D : Type*) [Field D] [Algebra D L] [IsDecompositionField K L P D] [CommRing 𝓞D]
  [Algebra 𝓞D D] [IsFractionRing 𝓞D D] [Algebra 𝓞D B] [Algebra 𝓞D L] [IsScalarTower 𝓞D D L]
  [IsScalarTower 𝓞D B L] (𝓟D : Ideal 𝓞D) [hD : P.LiesOver 𝓟D]

include K L D in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `P` is the only prime of `L` above `𝓟D`.
-/
/-
**IsDecompositionField.primesOver_eq_singleton** 是 Mathlib 中的一个定理，位于命名空间 `IsDeco
mpositionField`。
形式化陈述：primesOver_eq_singleton [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)] 
[IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] : primesOver 𝓟D B = {P}
参数：stabilizer Gal(L/K) P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGaloisGroup.of_isFractionRing`：IsGaloisGroup.of_isFractionRing [hGKL :
 IsGaloisGroup G K L] [IsIntegrallyClosed A] [Algebra.IsIntegral A B] : IsGalois
Group G A B
· 使用定理 `IsDecompositionField.toIsGaloisGroup`：∀ {K : Type u_2} {L : Type u_3} {B
 : Type u_4} {inst : Field K} {inst_1 : Field L} {inst_2 : Algebra K L}   {inst_
3 : CommRing B} {P : Ideal…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.eq_singleton_iff_unique_mem`：eq_singleton_iff_unique_mem : s = {a} ↔
 a in s ∧ forall x in s, x = a
· 使用定理 `Ideal.exists_smul_eq_of_isGaloisGroup`：exists_smul_eq_of_isGaloisGroup :
 exists σ : G, σ • P = Q
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of
 `D` below `P`,
then `P` is the only prime of `L` above `𝓟D`.
-/
theorem primesOver_eq_singleton [hP : P.IsPrime] [Finite (stabilizer Gal(L/K) P)]
    [IsIntegrallyClosed 𝓞D] [Algebra.IsIntegral 𝓞D B] :
    primesOver 𝓟D B = {P} := by
  have := IsGaloisGroup.of_isFractionRing (stabilizer Gal(L/K) P) 𝓞D B D L
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨hP, hD⟩, ?_⟩
  rintro Q ⟨_, _⟩
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup 𝓟D P Q (stabilizer Gal(L/K) P)
  exact σ.prop

variable [IsGalois K L] [IsDedekindDomain A] [IsDedekindDomain B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra A 𝓞D] [Module.Finite A 𝓞D] [IsScalarTower A 𝓞D B]
  [IsDedekindDomain 𝓞D] [𝓟D.LiesOver p]

omit [P.LiesOver p] hD in
include K L D P in
/-
**IsDecompositionField.instances** 是 Mathlib 中的一个引理，位于命名空间 `IsDecompositionField
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma instances (hp : p ≠ ⊥) :
    Module.Finite 𝓞D B ∧ Module.IsTorsionFree 𝓞D B ∧ Module.IsTorsionFree A 𝓞D ∧
      IsGaloisGroup Gal(L/K) A B ∧ IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B ∧ 𝓟D ≠ ⊥ := by
  have inst₁ : Module.Finite 𝓞D B := Module.Finite.right A 𝓞D B
  have inst₂ : Module.IsTorsionFree 𝓞D B := by
    rw [Module.isTorsionFree_iff_faithfulSMul]
    apply Algebra.IsAlgebraic.faithfulSMul_tower_top A
  have inst₃ : Module.IsTorsionFree A 𝓞D := Module.IsTorsionFree.of_faithfulSMul _ _ B
  have inst₄ : IsGaloisGroup Gal(L/K) A B := .of_isFractionRing _ _ _ K L
  have inst₅ : IsGaloisGroup (stabilizer Gal(L/K) P) 𝓞D B := .of_isFractionRing _ _ _ D L
  exact ⟨inst₁, inst₂, inst₃, inst₄, inst₅, Ideal.ne_bot_of_liesOver_of_ne_bot hp 𝓟D⟩

variable [FiniteDimensional K L] [Ring.HasFiniteQuotients A] [𝓟D.IsMaximal] [P.IsMaximal]

include K L D P in
/-
**IsDecompositionField.ramificationIdxIn_eq_and_inertiaDegIn_eq** 是 Mathlib 中的一个
引理，位于命名空间 `IsDecompositionField`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma ramificationIdxIn_eq_and_inertiaDegIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B ∧ inertiaDegIn 𝓟D B = p.inertiaDegIn B := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  refine eq_and_eq_of_pos_of_le_of_mul_le_mul ?_ ?_ ?_ ?_ ?_
  · exact Nat.pos_of_ne_zero <| ramificationIdxIn_ne_zero (stabilizer Gal(L/K) P)
  · exact Nat.pos_of_ne_zero <| inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)
  · rw [ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
      ramificationIdxIn_eq_ramificationIdx _ P (stabilizer Gal(L/K) P)]
    exact 𝓟D.ramificationIdx_above_le P
  · rw [inertiaDegIn_eq_inertiaDeg p P Gal(L/K),
      inertiaDegIn_eq_inertiaDeg _ P (stabilizer Gal(L/K) P)]
    exact inertiaDeg_above_le 𝓟D P
  · have := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝓟D B (stabilizer Gal(L/K) P)
    rw [primesOver_eq_singleton K L P D 𝓞D, Set.ncard_singleton, one_mul] at this
    rw [this, IsGaloisGroup.card_eq_finrank (stabilizer Gal(L/K) P) D L,
      IsDecompositionField.rank_left A K L P D hp]

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the ramification index of `𝓟D` in `L` is equal to the ramification index of `p` in `L`.
-/
/-
**IsDecompositionField.ramificationIdxIn_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsDecompo
sitionField`。
形式化陈述：ramificationIdxIn_eq (hp : p != ⊥) : ramificationIdxIn 𝓟D B = p.ramificati
onIdxIn B
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `_private.Mathlib.NumberTheory.RamificationInertia.HilbertTheory.0.IsDeco
mpositionField.ramificationIdxIn_eq_and_inertiaDegIn_eq`：∀ (A : Type u_1) (K : T
ype u_2) (L : Type u_3) {B : Type u_4} [inst : Field K] [inst_1 : Field L] [inst
_2 : Algebra K L]   [inst_3 : CommRin…

--- 原说明 ---
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of
 `D` below `P`,
then the ramification index of `𝓟D` in `L` is equal to the ramification index of
 `p` in `L`.
-/
theorem ramificationIdxIn_eq (hp : p ≠ ⊥) :
    ramificationIdxIn 𝓟D B = p.ramificationIdxIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).1

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` in `L` is equal to the inertia degree of `p` in `L`.
-/
/-
**IsDecompositionField.inertiaDegIn_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsDecompositio
nField`。
形式化陈述：inertiaDegIn_eq (hp : p != ⊥) : inertiaDegIn 𝓟D B = p.inertiaDegIn B
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `_private.Mathlib.NumberTheory.RamificationInertia.HilbertTheory.0.IsDeco
mpositionField.ramificationIdxIn_eq_and_inertiaDegIn_eq`：∀ (A : Type u_1) (K : T
ype u_2) (L : Type u_3) {B : Type u_4} [inst : Field K] [inst_1 : Field L] [inst
_2 : Algebra K L]   [inst_3 : CommRin…

--- 原说明 ---
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of
 `D` below `P`,
then the inertia degree of `𝓟D` in `L` is equal to the inertia degree of `p` in 
`L`.
-/
theorem inertiaDegIn_eq (hp : p ≠ ⊥) :
    inertiaDegIn 𝓟D B = p.inertiaDegIn B :=
  (ramificationIdxIn_eq_and_inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp).2

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then `𝓟D` is unramified over `K`.
-/
/-
**IsDecompositionField.ramificationIdx_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsDecomposi
tionField`。
形式化陈述：ramificationIdx_eq (hp : p != ⊥) : 𝓟D.ramificationIdx A = 1
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.RamificationInertia.HilbertTheory.0.IsDeco
mpositionField.instances`：∀ (A : Type u_1) (K : Type u_2) (L : Type u_3) {B : Ty
pe u_4} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : C
ommRin…
· 使用定理 `Ideal.ramificationIdx_tower`：ramificationIdx_tower [r.LiesOver q] [Modul
e.Flat S T] : r.ramificationIdx R = q.ramificationIdx R * r.ramificationIdx S
· 使用定理 `Module.Flat.instOfIsDedekindDomainOfIsTorsionFree`：∀ {R : Type u_1} {M :
 Type u_2} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module
 R M]   [IsDedekindDomain R] [Module.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_eq_mul₀`：right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b != 0) : b
 = a * b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Ideal.ramificationIdx_pos`：ramificationIdx_pos [q.IsPrime] [Module.Finit
e R S] : 0 < q.ramificationIdx R
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Ideal.ramificationIdxIn_eq_ramificationIdx`：ramificationIdxIn_eq_ramific
ationIdx : ramificationIdxIn p B = P.ramificationIdx A
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `IsDecompositionField.ramificationIdxIn_eq`：ramificationIdxIn_eq (hp : p 
!= ⊥) : ramificationIdxIn 𝓟D B = p.ramificationIdxIn B
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K

--- 原说明 ---
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of
 `D` below `P`,
then `𝓟D` is unramified over `K`.
-/
theorem ramificationIdx_eq (hp : p ≠ ⊥) :
    𝓟D.ramificationIdx A = 1 := by
  obtain ⟨_, _, _, _, _, h𝓟⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := ramificationIdx_tower (R := A) 𝓟D P
  rwa [← ramificationIdxIn_eq_ramificationIdx 𝓟D P (stabilizer Gal(L/K) P),
    ramificationIdxIn_eq A K L P D 𝓞D 𝓟D hp, ramificationIdxIn_eq_ramificationIdx p P Gal(L/K),
    right_eq_mul₀ <| (ramificationIdx_pos P A).ne'] at this

include K L D P in
/--
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of `D` below `P`,
then the inertia degree of `𝓟D` over `K` is equal to `1`.
-/
/-
**IsDecompositionField.inertiaDeg_eq** 是 Mathlib 中的一个定理，位于命名空间 `IsDecompositionF
ield`。
形式化陈述：inertiaDeg_eq (hp : p != ⊥) : 𝓟D.inertiaDeg A = 1
参数：hp : p != ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.RamificationInertia.HilbertTheory.0.IsDeco
mpositionField.instances`：∀ (A : Type u_1) (K : Type u_2) (L : Type u_3) {B : Ty
pe u_4} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L]   [inst_3 : C
ommRin…
· 使用定理 `Ideal.inertiaDeg_tower`：inertiaDeg_tower [r.LiesOver q] : r.inertiaDeg R
 = q.inertiaDeg R * r.inertiaDeg S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `right_eq_mul₀`：right_eq_mul₀ [IsRightCancelMulZero M₀] (hb : b != 0) : b
 = a * b ↔ a = 1
· 使用定理 `IsCancelMulZero.toIsRightCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} 
{inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsRightCancelMulZero M₀
· 使用定理 `Ideal.inertiaDegIn_ne_zero`：inertiaDegIn_ne_zero [Module.Finite A B] [Fa
ithfulSMul A B] {p : Ideal A} [p.IsPrime] : inertiaDegIn p B != 0
· 使用定理 `Subgroup.instFiniteSubtypeMem`：∀ {G : Type u_1} [inst : Group G] (K : Su
bgroup G) [Finite G], Finite ↥K
· 使用定理 `Finite.algEquiv`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [inst :
 CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Algeb
ra R …
· 使用定理 `instFiniteAlgHomOfFinite`：∀ (R : Type u_1) [inst : CommSemiring R] (K : 
Type u_2) [inst_1 : Field K] [inst_2 : Algebra R K] (S : Type u_3)   [inst_3 : S
emiring S] [in…
· 使用定理 `Module.IsTorsionFree.to_faithfulSMul`：∀ {R : Type u_1} {A : Type u_2} [i
nst : CommRing R] [inst_1 : Ring A] [inst_2 : Algebra R A] [IsCancelMulZero R]  
 [Nontrivial A] [Module.Is…
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `IsDedekindDomain.toIsDomain`：∀ {A : Type u_2} {inst : CommRing A} [self 
: IsDedekindDomain A], IsDomain A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Ideal.IsMaximal.isPrime'`：∀ {α : Type u} [inst : CommSemiring α] (I : Id
eal α) [_H : I.IsMaximal], I.IsPrime
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.inertiaDegIn_eq_inertiaDeg`：inertiaDegIn_eq_inertiaDeg : inertiaDe
gIn p B = P.inertiaDeg A
· 使用定理 `IsDecompositionField.inertiaDegIn_eq`：inertiaDegIn_eq (hp : p != ⊥) : in
ertiaDegIn 𝓟D B = p.inertiaDegIn B

--- 原说明 ---
Let `D` be the decomposition field of `P` in `L/K`. Let `𝓟D` be a prime ideal of
 `D` below `P`,
then the inertia degree of `𝓟D` over `K` is equal to `1`.
-/
theorem inertiaDeg_eq (hp : p ≠ ⊥) :
    𝓟D.inertiaDeg A = 1 := by
  obtain ⟨_, _, _, _, _, _⟩ := instances A K L P D 𝓞D 𝓟D hp
  have := inertiaDeg_tower (R := A) 𝓟D P
  rwa [← inertiaDegIn_eq_inertiaDeg p P Gal(L/K), ← inertiaDegIn_eq A K L P D 𝓞D 𝓟D hp,
    ← inertiaDegIn_eq_inertiaDeg 𝓟D P (stabilizer Gal(L/K) P),
    right_eq_mul₀ <| inertiaDegIn_ne_zero (stabilizer Gal(L/K) P)] at this

end IsDecompositionField

end splitting

