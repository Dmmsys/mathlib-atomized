/-
Copyright (c) 2024 Jon Bannon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Bannon, Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Topology.ContinuousMap.Units

/-!
# Continuous Functional Calculus for Hermitian Matrices

This file defines an instance of the continuous functional calculus for Hermitian matrices over an
`RCLike` field `𝕜`.

## Main Results

- `Matrix.IsHermitian.cfc` : Realization of the functional calculus for a Hermitian matrix
  as the triple product `U * diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues) * star U` with
  `U = eigenvectorUnitary hA`.

- `cfc_eq` : Proof that the above agrees with the continuous functional calculus.

- `Matrix.IsHermitian.instContinuousFunctionalCalculus` : Instance of the continuous functional
  calculus for a Hermitian matrix `A` over `𝕜`.

## Tags

spectral theorem, diagonalization theorem, continuous functional calculus
-/

@[expose] public section

open Topology Unitary

namespace Matrix

variable {n 𝕜 : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

namespace IsHermitian

variable (hA : IsHermitian A)

/-- The star algebra homomorphism underlying the instance of the continuous functional
calculus of a Hermitian matrix. This is an auxiliary definition and is not intended
for use outside of this file. -/
@[simps]
/-
**Matrix.IsHermitian.cfcAux** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：cfcAux : C(spectrum Real A, Real) ->⋆ₐ[Real] (Matrix n n 𝕜) where toFun g
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Matrix.IsHermitian.eigenvalues_mem_spectrum_real`：eigenvalues_mem_spectr
um_real (i : n) : hA.eigenvalues i in spectrum Real A

--- 原说明 ---
The star algebra homomorphism underlying the instance of the continuous function
al
calculus of a Hermitian matrix. This is an auxiliary definition and is not inten
ded
for use outside of this file.
-/
noncomputable def cfcAux : C(spectrum ℝ A, ℝ) →⋆ₐ[ℝ] (Matrix n n 𝕜) where
  toFun g := conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary <|
    diagonal (RCLike.ofReal ∘ g ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
  map_zero' := by simp [Pi.zero_def, Function.comp_def]
  map_one' := by simp [Pi.one_def, Function.comp_def]
  map_mul' f g := by
    simp only [ContinuousMap.coe_mul, ← map_mul, diagonal_mul_diagonal, Function.comp_apply]
    rfl
  map_add' f g := by
    simp only [ContinuousMap.coe_add, ← map_add, diagonal_add, Function.comp_apply]
    rfl
  commutes' r := by
    simp only [Function.comp_def, algebraMap_apply, smul_eq_mul, mul_one]
    rw [← mul_one (algebraMap _ _ _), ← coe_mul_star_self hA.eigenvectorUnitary,
      ← Algebra.left_comm, coe_star, ← mul_assoc, conjStarAlgAut_apply]
    rfl
  map_star' f := by
    simp only [star_trivial, ← map_star, star_eq_conjTranspose, diagonal_conjTranspose, Pi.star_def,
      Function.comp_apply, RCLike.star_def, RCLike.conj_ofReal]
    rfl
/-
**Matrix.IsHermitian.isClosedEmbedding_cfcAux** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.
IsHermitian`。
形式化陈述：isClosedEmbedding_cfcAux : IsClosedEmbedding hA.cfcAux
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `FiniteDimensional.of_injective`：of_injective (f : V ->ₗ[K] V₂) (w : Func
tion.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
· 使用定理 `Matrix.instFiniteElemRealSpectrum`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n
 : Type u_2} [inst_1 : Fintype n] {A : Matrix n n 𝕜} [inst_2 : DecidableEq n],  
 Finite ↑(spectrum ℝ A)
· 使用定理 `LinearMap.isClosedEmbedding_of_injective`：LinearMap.isClosedEmbedding_of
_injective [T2Space E] [FiniteDimensional 𝕜 E] [T2Space F] {f : E ->ₗ[𝕜] F} (hf 
: LinearMap.ker f = ⊥) : IsClo…
· 使用定理 `ContinuousMap.instIsTopologicalAddGroup`：∀ {α : Type u_1} {β : Type u_2}
 [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [inst_2 : AddCommGrou
p β]   [inst_3 : IsTopologica…
· 使用定理 `ContinuousMap.instContinuousSMul`：∀ {α : Type u_1} [inst : TopologicalSp
ace α] {R : Type u_3} {M : Type u_5} [inst_1 : TopologicalSpace M]   [inst_2 : T
opologicalSpace R] [in…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalAddGroupMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Ty
pe u_8} [inst : TopologicalSpace R] [inst_1 : AddGroup R]   [IsTopologicalAddGro
up R], IsTopologicalA…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `instContinuousSMulMatrix`：∀ {α : Type u_2} {m : Type u_4} {n : Type u_5}
 {R : Type u_8} [inst : TopologicalSpace R] [inst_1 : TopologicalSpace α]   [ins
t_2 : SMul α R…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousMap.instT2Space`：∀ {X : Type u_2} {Y : Type u_3} [inst : Topol
ogicalSpace X] [inst_1 : TopologicalSpace Y] [T2Space Y], T2Space C(X, Y)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
· 使用定理 `Matrix.IsHermitian.eigenvalues_mem_spectrum_real`：eigenvalues_mem_spectr
um_real (i : n) : hA.eigenvalues i in spectrum Real A
（共 49 条，此处仅展示前 30 条）
-/
lemma isClosedEmbedding_cfcAux : IsClosedEmbedding hA.cfcAux := by
  have h0 : FiniteDimensional ℝ C(spectrum ℝ A, ℝ) :=
    FiniteDimensional.of_injective (ContinuousMap.coeFnLinearMap ℝ (M := ℝ)) DFunLike.coe_injective
  refine LinearMap.isClosedEmbedding_of_injective (𝕜 := ℝ) (E := C(spectrum ℝ A, ℝ))
    (F := Matrix n n 𝕜) (f := hA.cfcAux) <| LinearMap.ker_eq_bot'.mpr fun f hf ↦ ?_
  have h2 :
      diagonal (RCLike.ofReal ∘ f ∘ fun i ↦ ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i⟩)
        = (0 : Matrix n n 𝕜) := by
    simp only [LinearMap.coe_coe, cfcAux_apply, conjStarAlgAut_apply] at hf
    replace hf := congr($hf * (hA.eigenvectorUnitary : Matrix n n 𝕜))
    simp only [mul_assoc, SetLike.coe_mem, Unitary.star_mul_self_of_mem, mul_one, zero_mul] at hf
    simpa [← mul_assoc] using congr((star hA.eigenvectorUnitary : Matrix n n 𝕜) * $hf)
  ext x
  simp only [ContinuousMap.zero_apply]
  obtain ⟨x, hx⟩ := x
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  rw [← diagonal_zero] at h2
  have := diagonal_eq_diagonal_iff.mp h2
  exact RCLike.ofReal_eq_zero.mp (this i)
/-
**Matrix.IsHermitian.cfcAux_id** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：cfcAux_id : hA.cfcAux (.restrict (spectrum Real A) (.id Real)) = A
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.IsHermitian.spectral_theorem`：spectral_theorem : A = conjStarAlgA
ut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ hA.eigenvalues))
-/
lemma cfcAux_id : hA.cfcAux (.restrict (spectrum ℝ A) (.id ℝ)) = A := by
  conv_rhs => rw [hA.spectral_theorem]
  rfl

/-- Instance of the continuous functional calculus for a Hermitian matrix over `𝕜` with
`RCLike 𝕜`. -/
/-
**Matrix.IsHermitian.instContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名空间 
`Matrix.IsHermitian`。
形式化陈述：instContinuousFunctionalCalculus : ContinuousFunctionalCalculus Real (Matr
ix n n 𝕜) IsSelfAdjoint where exists_cfc_of_predicate a ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsSelfAdjoint.zero`：∀ (R : Type u_1) [inst : AddMonoid R] [inst_1 : Star
AddMonoid R], IsSelfAdjoint 0
· 使用定理 `TopologicalSpace.NoetherianSpace.compactSpace`：∀ (α : Type u_1) [inst : 
TopologicalSpace α] [h : TopologicalSpace.NoetherianSpace α], CompactSpace α
· 使用定理 `TopologicalSpace.Finite.to_noetherianSpace`：∀ {α : Type u_1} [inst : Top
ologicalSpace α] [Finite α], TopologicalSpace.NoetherianSpace α
· 使用定理 `Matrix.instFiniteElemRealSpectrum`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n
 : Type u_2} [inst_1 : Fintype n] {A : Matrix n n 𝕜} [inst_2 : DecidableEq n],  
 Finite ↑(spectrum ℝ A)
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Set.range_nonempty`：range_nonempty [h : Nonempty ι] (f : ι -> α) : (rang
e f).Nonempty
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`：spectrum_real_eq_
range_eigenvalues : spectrum Real A = Set.range hA.eigenvalues
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用引理 `Matrix.IsHermitian.isClosedEmbedding_cfcAux`：isClosedEmbedding_cfcAux : 
IsClosedEmbedding hA.cfcAux
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `Topology.IsClosedEmbedding.toIsEmbedding`：∀ {X : Type u_1} {Y : Type u_2
} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.Is
ClosedEmbedding f → Topology.I…
· 使用引理 `Matrix.IsHermitian.cfcAux_id`：cfcAux_id : hA.cfcAux (.restrict (spectrum
 Real A) (.id Real)) = A
· 使用定理 `Set.eq_of_subset_of_subset`：eq_of_subset_of_subset {a b : Set α} : a sub
seteq b -> b subseteq a -> a = b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.spectrum_eq_range`：spectrum_eq_range [CompleteSpace 𝕜] (f 
: C(X, 𝕜)) : spectrum 𝕜 f = Set.range f
· 使用定理 `AlgHom.spectrum_apply_subset`：spectrum_apply_subset (φ : F) (a : A) : σ 
((φ : A -> B) a) subseteq σ a
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Instance of the continuous functional calculus for a Hermitian matrix over `𝕜` w
ith
`RCLike 𝕜`.
-/
instance instContinuousFunctionalCalculus :
    ContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  exists_cfc_of_predicate a ha := by
    replace ha : IsHermitian a := ha
    refine ⟨ha.cfcAux, ha.isClosedEmbedding_cfcAux.continuous,
      ha.isClosedEmbedding_cfcAux.injective, ha.cfcAux_id, fun f ↦ ?map_spec,
      fun f ↦ ?hermitian⟩
    case map_spec =>
      apply Set.eq_of_subset_of_subset
      · rw [← ContinuousMap.spectrum_eq_range f]
        apply AlgHom.spectrum_apply_subset
      · rw [cfcAux_apply, conjStarAlgAut_apply, Unitary.spectrum_star_right_conjugate]
        rintro - ⟨x, rfl⟩
        apply spectrum.of_algebraMap_mem 𝕜
        simp only [Function.comp_apply, Set.mem_range, spectrum_diagonal]
        obtain ⟨x, hx⟩ := x
        obtain ⟨i, rfl⟩ := ha.spectrum_real_eq_range_eigenvalues ▸ hx
        exact ⟨i, rfl⟩
    case hermitian =>
      simp only [isSelfAdjoint_iff, cfcAux_apply, ← map_star]
      rw [star_eq_conjTranspose, diagonal_conjTranspose]
      congr!
      simp [Pi.star_def, Function.comp_def]
  spectrum_nonempty a ha := by
    obtain (h | h) := isEmpty_or_nonempty n
    · obtain ⟨x, y, hxy⟩ := exists_pair_ne (Matrix n n 𝕜)
      exact False.elim <| Matrix.of.symm.injective.ne hxy <| Subsingleton.elim _ _
    · exact spectrum_real_eq_range_eigenvalues ha ▸ Set.range_nonempty _
  predicate_zero := .zero _

/-- The continuous functional calculus of a Hermitian matrix as a triple product using the
spectral theorem. Note that this actually operates on bare functions since every function is
continuous on the spectrum of a matrix, since the spectrum is finite. This is shown to be equal to
the generic continuous functional calculus API in `Matrix.IsHermitian.cfc_eq`. In general, users
should prefer the generic API, especially because it will make rewriting easier. -/
/-
**Matrix.IsHermitian.cfc** 是 Mathlib 中的一个定义，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：{n : Type u_1} →   {𝕜 : Type u_2} →     [inst : RCLike 𝕜] → [Fintype n] → 
[DecidableEq n] → {A : Matrix n n 𝕜} → A.IsHermitian → (ℝ → ℝ) → Matrix n n 𝕜
参数：ℝ → ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The continuous functional calculus of a Hermitian matrix as a triple product usi
ng the
spectral theorem. Note that this actually operates on bare functions since every
 function is
continuous on the spectrum of a matrix, since the spectrum is finite. This is sh
own to be equal to
the generic continuous functional calculus API in `Matrix.IsHermitian.cfc_eq`. I
n general, users
should prefer the generic API, especially because it will make rewriting easier.
-/
protected noncomputable def cfc (f : ℝ → ℝ) : Matrix n n 𝕜 :=
  conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary (diagonal (RCLike.ofReal ∘ f ∘ hA.eigenvalues))
/-
**Matrix.IsHermitian.cfcHom_eq_cfcAux** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.IsHermit
ian`。
形式化陈述：cfcHom_eq_cfcAux : cfcHom hA.isSelfAdjoint = hA.cfcAux
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `cfcHom_eq_of_continuous_of_map_id`：cfcHom_eq_of_continuous_of_map_id [Un
iqueHom R A] (φ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.
restrict (spectrum R a)…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用引理 `Matrix.IsHermitian.isClosedEmbedding_cfcAux`：isClosedEmbedding_cfcAux : 
IsClosedEmbedding hA.cfcAux
· 使用引理 `Matrix.IsHermitian.cfcAux_id`：cfcAux_id : hA.cfcAux (.restrict (spectrum
 Real A) (.id Real)) = A
-/
lemma cfcHom_eq_cfcAux : cfcHom hA.isSelfAdjoint = hA.cfcAux :=
  cfcHom_eq_of_continuous_of_map_id hA hA.cfcAux
    hA.isClosedEmbedding_cfcAux.continuous hA.cfcAux_id
/-
**Matrix.IsHermitian.instContinuousFunctionalCalculusIsClosedEmbedding** 是 Mathl
ib 中的一个实例，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：instContinuousFunctionalCalculusIsClosedEmbedding : ClosedEmbeddingContinu
ousFunctionalCalculus Real (Matrix n n 𝕜) IsSelfAdjoint where isClosedEmbedding 
_ hA
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `Matrix.IsHermitian.isClosedEmbedding_cfcAux`：isClosedEmbedding_cfcAux : 
IsClosedEmbedding hA.cfcAux
· 使用定理 `IsSelfAdjoint.isHermitian`：∀ {α : Type u_1} {n : Type u_4} [inst : Star 
α] {A : Matrix n n α}, IsSelfAdjoint A → A.IsHermitian
· 使用定理 `Matrix.IsHermitian.isSelfAdjoint`：∀ {α : Type u_1} {n : Type u_4} [inst 
: Star α] {A : Matrix n n α}, A.IsHermitian → IsSelfAdjoint A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Matrix.IsHermitian.cfcHom_eq_cfcAux`：cfcHom_eq_cfcAux : cfcHom hA.isSelf
Adjoint = hA.cfcAux
-/
instance instContinuousFunctionalCalculusIsClosedEmbedding :
    ClosedEmbeddingContinuousFunctionalCalculus ℝ (Matrix n n 𝕜) IsSelfAdjoint where
  isClosedEmbedding _ hA := cfcHom_eq_cfcAux hA ▸ hA.isHermitian.isClosedEmbedding_cfcAux
/-
**Matrix.IsHermitian.cfc_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.IsHermitian`。
形式化陈述：cfc_eq (f : Real -> Real) : cfc f A = hA.cfc f
参数：f : Real -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用引理 `cfcHom_eq_of_continuous_of_map_id`：cfcHom_eq_of_continuous_of_map_id [Un
iqueHom R A] (φ : C(spectrum R a, R) ->⋆ₐ[R] A) (hφ₁ : Continuous φ) (hφ₂ : φ (.
restrict (spectrum R a)…
· 使用定理 `instT2SpaceMatrix`：∀ {m : Type u_4} {n : Type u_5} {R : Type u_8} [inst 
: TopologicalSpace R] [T2Space R], T2Space (Matrix m n R)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用引理 `Matrix.IsHermitian.isClosedEmbedding_cfcAux`：isClosedEmbedding_cfcAux : 
IsClosedEmbedding hA.cfcAux
· 使用引理 `Matrix.IsHermitian.cfcAux_id`：cfcAux_id : hA.cfcAux (.restrict (spectrum
 Real A) (.id Real)) = A
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuousOn_iff_continuous_domRestrict`：continuousOn_iff_continuous_dom
Restrict : ContinuousOn f s ↔ Continuous (s.domRestrict f)
· 使用定理 `continuous_of_discreteTopology`：continuous_of_discreteTopology [Topologi
calSpace β] {f : α -> β} : Continuous f
· 使用定理 `DiscreteUniformity.instDiscreteTopology`：∀ (X : Type u_1) [u : UniformSp
ace X] [DiscreteUniformity X], DiscreteTopology X
· 使用定理 `DiscreteUniformity.instOfFiniteOfDiscreteTopology`：∀ {Y : Type u_2} [Fin
ite Y] [inst : UniformSpace Y] [DiscreteTopology Y], DiscreteUniformity Y
· 使用定理 `Matrix.instFiniteElemRealSpectrum`：∀ {𝕜 : Type u_1} [inst : RCLike 𝕜] {n
 : Type u_2} [inst_1 : Fintype n] {A : Matrix n n 𝕜} [inst_2 : DecidableEq n],  
 Finite ↑(spectrum ℝ A)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.IsHermitian.cfcAux_apply`：∀ {n : Type u_1} {𝕜 : Type u_2} [inst :
 RCLike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n n 𝕜}   (h
A : A.IsHermitian) (g…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma cfc_eq (f : ℝ → ℝ) : cfc f A = hA.cfc f := by
  have hA' : IsSelfAdjoint A := hA
  have := cfcHom_eq_of_continuous_of_map_id hA' hA.cfcAux hA.isClosedEmbedding_cfcAux.continuous
    hA.cfcAux_id
  rw [cfc_apply f A hA' (by rw [continuousOn_iff_continuous_domRestrict]; fun_prop), this]
  simp only [cfcAux_apply, ContinuousMap.coe_mk, Function.comp_def, Set.domRestrict_apply,
    IsHermitian.cfc]

open Polynomial in
/-
**Matrix.IsHermitian.charpoly_cfc_eq** 是 Mathlib 中的一个引理，位于命名空间 `Matrix.IsHermiti
an`。
形式化陈述：charpoly_cfc_eq (f : Real -> Real) : (cfc f A).charpoly = ∏ i, (X - C (f (
hA.eigenvalues i) : 𝕜))
参数：f : Real -> Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Matrix.IsHermitian.cfc_eq`：cfc_eq (f : Real -> Real) : cfc f A = hA.cfc 
f
· 使用定理 `Matrix.IsHermitian.cfc.eq_1`：∀ {n : Type u_1} {𝕜 : Type u_2} [inst : RCL
ike 𝕜] [inst_1 : Fintype n] [inst_2 : DecidableEq n] {A : Matrix n n 𝕜}   (hA : 
A.IsHermitian) (f…
· 使用定理 `Unitary.conjStarAlgAut_apply`：∀ {S : Type u_1} {R : Type u_2} [inst : Se
miring R] [inst_1 : StarMul R] [inst_2 : SMul S R]   [inst_3 : IsScalarTower S R
 R] [inst_4 : SMul…
· 使用定理 `Matrix.charpoly_mul_comm`：charpoly_mul_comm (A B : Matrix n n R) : (A * 
B).charpoly = (B * A).charpoly
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.charpoly.congr_simp`：∀ {R : Type u_1} [inst : CommRing R] {n : Ty
pe u_4} {inst_1 : DecidableEq n} [inst_2 : DecidableEq n]   [inst_3 : Fintype n]
 (M M_1 : Matrix…
· 使用定理 `Unitary.star_mul_self_of_mem`：star_mul_self_of_mem {U : R} (hU : U in un
itary R) : star U * U = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Matrix.charpoly_diagonal`：charpoly_diagonal (d : n -> R) : charpoly (dia
gonal d) = ∏ i, (X - C (d i))
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma charpoly_cfc_eq (f : ℝ → ℝ) :
    (cfc f A).charpoly = ∏ i, (X - C (f (hA.eigenvalues i) : 𝕜)) := by
  rw [cfc_eq hA f, IsHermitian.cfc, conjStarAlgAut_apply, charpoly_mul_comm, ← mul_assoc]
  simp [charpoly_diagonal]

end IsHermitian
end Matrix

