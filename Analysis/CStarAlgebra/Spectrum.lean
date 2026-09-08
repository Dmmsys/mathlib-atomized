/-
Copyright (c) 2022 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.Unitization
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Algebra.Star.StarAlgHom

/-! # Spectral properties in C⋆-algebras

In this file, we establish various properties related to the spectrum of elements in C⋆-algebras.
In particular, we show that the spectrum of a unitary element is contained in the unit circle in
`ℂ`, the spectrum of a selfadjoint element is real, the spectral radius of a selfadjoint element
or normal element is its norm, among others.

An essential feature of C⋆-algebras is **spectral permanence**. This is the property that the
spectrum of an element in a closed subalgebra is the same as the spectrum of the element in the
whole algebra. For Banach algebras more generally, and even for Banach ⋆-algebras, this fails.

A consequence of spectral permanence is that one may always enlarge the C⋆-algebra (via a unital
embedding) while preserving the spectrum of any element. In addition, it allows us to make sense of
the spectrum of elements in non-unital C⋆-algebras by considering them as elements in the
`Unitization` of the C⋆-algebra, or indeed *any* unital C⋆-algebra. Of course, one may do this
(that is, consider the spectrum of an element in a non-unital by embedding it in a unital algebra)
for any Banach algebra, but the downside in that setting is that embedding in different unital
algebras results in varying spectra.

In Mathlib, we don't *define* the spectrum of an element in a non-unital C⋆-algebra, and instead
simply consider the `quasispectrum` so as to avoid depending on a choice of unital algebra. However,
we can still establish a form of spectral permanence.

## Main statements

+ `Unitary.spectrum_subset_circle`: The spectrum of a unitary element is contained in the unit
  sphere in `ℂ`.
+ `IsSelfAdjoint.spectralRadius_eq_nnnorm`: The spectral radius of a selfadjoint element is equal
  to its norm.
+ `IsStarNormal.spectralRadius_eq_nnnorm`: The spectral radius of a normal element is equal to
  its norm.
+ `spectralRadius_toReal_star_self_mul_self_eq_normSq`: The spectral radius of `a⋆ * a` is equal to
  the square of the norm of `a`.
+ `IsSelfAdjoint.mem_spectrum_eq_re`: Any element of the spectrum of a selfadjoint element is real.
* `StarSubalgebra.coe_isUnit`: for `x : S` in a C⋆-Subalgebra `S` of `A`, then `↑x : A` is a Unit
  if and only if `x` is a unit.
* `StarSubalgebra.spectrum_eq`: **spectral permanence** for `x : S`, where `S` is a C⋆-Subalgebra
  of `A`, `spectrum ℂ x = spectrum ℂ (x : A)`.

## TODO

+ prove a variation of spectral permanence using `StarAlgHom` instead of `StarSubalgebra`.
+ prove a variation of spectral permanence for `quasispectrum`.

-/

public section


local notation "σ" => spectrum
local postfix:max "⋆" => star

section

open scoped Topology ENNReal

open Filter ENNReal spectrum CStarRing NormedSpace

section UnitarySpectrum

variable {𝕜 : Type*} [NormedField 𝕜] {E : Type*} [NormedRing E] [StarRing E] [CStarRing E]
  [NormedAlgebra 𝕜 E] [CompleteSpace E]

/-
**Unitary.spectrum_subset_circle** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Unitary.spectrum_subset_circle (u : unitary E) : spectrum 𝕜 (u : E) subset
eq Metric.sphere 0 1
参数：u : unitary E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mem_sphere_zero_iff_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E]
 {a : E} {r : ℝ}, a ∈ Metric.sphere 0 r ↔ ‖a‖ = r
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CStarRing.norm_coe_unitary`：norm_coe_unitary [Nontrivial E] (U : unitary
 E) : ‖(U : E)‖ = 1
· 使用定理 `spectrum.norm_le_norm_of_mem`：norm_le_norm_of_mem [NormOneClass A] {a : 
A} {k : 𝕜} (hk : k in σ a) : ‖k‖ <= ‖a‖
· 使用定理 `CStarRing.instNormOneClassOfNontrivial`：∀ {E : Type u_2} [inst : NormedR
ing E] [inst_1 : StarRing E] [CStarRing E] [Nontrivial E], NormOneClass E
· 使用定理 `spectrum.ne_zero_of_mem_of_unit`：ne_zero_of_mem_of_unit {a : Aˣ} {r : R}
 (hr : r in σ (a : A)) : r != 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Unitary.val_toUnits_apply`：∀ {R : Type u_1} [inst : Monoid R] [inst_1 : 
StarMul R] (x : ↥(unitary R)), ↑(Unitary.toUnits x) = ↑x
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Set.mem_inv`：mem_inv : a in s⁻¹ ↔ a⁻¹ in s
· 使用定理 `spectrum.map_inv`：∀ {𝕜 : Type u} {A : Type v} [inst : Field 𝕜] [inst_1 :
 Ring A] [inst_2 : Algebra 𝕜 A] (a : Aˣ),   (spectrum 𝕜 ↑a)⁻¹ = spectrum 𝕜 ↑a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Unitary.val_inv_toUnits_apply`：∀ {R : Type u_1} [inst : Monoid R] [inst_
1 : StarMul R] (x : ↥(unitary R)), ↑(Unitary.toUnits x)⁻¹ = ↑x⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用引理 `inv_le_of_inv_le₀`：inv_le_of_inv_le₀ (ha : 0 < a) (h : a⁻¹ <= b) : b⁻¹ <
= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem Unitary.spectrum_subset_circle (u : unitary E) :
    spectrum 𝕜 (u : E) ⊆ Metric.sphere 0 1 := by
  nontriviality E
  refine fun k hk => mem_sphere_zero_iff_norm.mpr (le_antisymm ?_ ?_)
  · simpa only [CStarRing.norm_coe_unitary u] using norm_le_norm_of_mem hk
  · rw [← Unitary.val_toUnits_apply u] at hk
    have hnk := ne_zero_of_mem_of_unit hk
    rw [← inv_inv (Unitary.toUnits u), ← spectrum.map_inv, Set.mem_inv] at hk
    have : ‖k‖⁻¹ ≤ ‖(↑(Unitary.toUnits u)⁻¹ : E)‖ := by
      simpa only [norm_inv] using norm_le_norm_of_mem hk
    simpa using inv_le_of_inv_le₀ (norm_pos_iff.mpr hnk) this
/-
**spectrum.subset_circle_of_unitary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectrum.subset_circle_of_unitary {u : E} (h : u in unitary E) : spectrum 
𝕜 u subseteq Metric.sphere 0 1
参数：h : u in unitary E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unitary.spectrum_subset_circle`：Unitary.spectrum_subset_circle (u : unit
ary E) : spectrum 𝕜 (u : E) subseteq Metric.sphere 0 1
-/
theorem spectrum.subset_circle_of_unitary {u : E} (h : u ∈ unitary E) :
    spectrum 𝕜 u ⊆ Metric.sphere 0 1 :=
  Unitary.spectrum_subset_circle ⟨u, h⟩
/-
**spectrum.norm_eq_one_of_unitary** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：spectrum.norm_eq_one_of_unitary {u : E} (hu : u in unitary E) ⦃z : 𝕜⦄ (hz 
: z in spectrum 𝕜 u) : ‖z‖ = 1
参数：hu : u in unitary E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `spectrum.subset_circle_of_unitary`：spectrum.subset_circle_of_unitary {u 
: E} (h : u in unitary E) : spectrum 𝕜 u subseteq Metric.sphere 0 1
-/
theorem spectrum.norm_eq_one_of_unitary {u : E} (hu : u ∈ unitary E)
    ⦃z : 𝕜⦄ (hz : z ∈ spectrum 𝕜 u) : ‖z‖ = 1 := by
  simpa using spectrum.subset_circle_of_unitary hu hz

end UnitarySpectrum

section Quasispectrum

open scoped NNReal in
/-
**CStarAlgebra.le_nnnorm_of_mem_quasispectrum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CStarAlgebra.le_nnnorm_of_mem_quasispectrum {A : Type*} [NonUnitalCStarAlg
ebra A] {a : A} {x : Real>=0} (hx : x in quasispectrum Real>=0 a) : x <= ‖a‖₊
参数：hx : x in quasispectrum Real>=0 a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Unitization.nnnorm_inr`：nnnorm_inr (a : A) : ‖(a : Unitization 𝕜 A)‖₊ = 
‖a‖₊
· 使用定理 `spectrum.le_nnnorm_of_mem`：le_nnnorm_of_mem {a : A} {r : Real>=0} (hr : 
r in spectrum Real>=0 a) : r <= ‖a‖₊
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `NonUnitalCStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], CompleteSpace A
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用引理 `Unitization.quasispectrum_eq_spectrum_inr'`：quasispectrum_eq_spectrum_in
r' (R S : Type*) {A : Type*} [Semifield R] [Field S] [NonUnitalRing A] [Algebra 
R S] [Module S A] [IsScalarTower…
-/
lemma CStarAlgebra.le_nnnorm_of_mem_quasispectrum {A : Type*} [NonUnitalCStarAlgebra A]
    {a : A} {x : ℝ≥0} (hx : x ∈ quasispectrum ℝ≥0 a) : x ≤ ‖a‖₊ := by
  rw [Unitization.quasispectrum_eq_spectrum_inr' ℝ≥0 ℂ] at hx
  simpa [Unitization.nnnorm_inr] using spectrum.le_nnnorm_of_mem hx

end Quasispectrum

section ComplexScalars

open Complex

variable {A : Type*} [CStarAlgebra A]

local notation "↑ₐ" => algebraMap ℂ A

/-
**IsSelfAdjoint.spectralRadius_eq_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) : sp
ectralRadius Complex a = ‖a‖₊
参数：ha : IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `IsSelfAdjoint.nnnorm_pow_two_pow`：IsSelfAdjoint.nnnorm_pow_two_pow {x : 
E} (hx : IsSelfAdjoint x) (n : Nat) : ‖x ^ 2 ^ n‖₊ = ‖x‖₊ ^ 2 ^ n
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `ENNReal.coe_pow`：∀ (x : NNReal) (n : ℕ), ↑(x ^ n) = ↑x ^ n
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
（共 43 条，此处仅展示前 30 条）
-/
theorem IsSelfAdjoint.spectralRadius_eq_nnnorm {a : A} (ha : IsSelfAdjoint a) :
    spectralRadius ℂ a = ‖a‖₊ := by
  have hconst : Tendsto (fun _n : ℕ => (‖a‖₊ : ℝ≥0∞)) atTop _ := tendsto_const_nhds
  refine tendsto_nhds_unique ?_ hconst
  convert!
    (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a : A)).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two) using 1
  refine funext fun n => ?_
  rw [Function.comp_apply, ha.nnnorm_pow_two_pow, ENNReal.coe_pow, ← rpow_natCast, ← rpow_mul]
  simp

/-- In a C⋆-algebra, the spectral radius of a self-adjoint element is equal to its norm.
See `IsSelfAdjoint.toReal_spectralRadius_eq_norm` for a version involving
`spectralRadius ℝ a`. -/
/-
**IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm {a : A} (ha : IsSelfAd
joint a) : (spectralRadius Complex a).toReal = ‖a‖
参数：ha : IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a C⋆-algebra, the spectral radius of a self-adjoint element is equal to its n
orm.
See `IsSelfAdjoint.toReal_spectralRadius_eq_norm` for a version involving
`spectralRadius ℝ a`.
-/
lemma IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm {a : A} (ha : IsSelfAdjoint a) :
    (spectralRadius ℂ a).toReal = ‖a‖ := by
  simp [ha.spectralRadius_eq_nnnorm]
/-
**IsStarNormal.spectralRadius_eq_nnnorm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsStarNormal.spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] : spectralR
adius Complex a = ‖a‖₊
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `ENNReal.pow_right_strictMono`：∀ {n : ℕ}, n ≠ 0 → StrictMono fun a => a ^
 n
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.rpow_natCast`：rpow_natCast (x : Real>=0∞) (n : Nat) : x ^ (n : R
eal) = x ^ n
· 使用定理 `ENNReal.rpow_mul`：rpow_mul (x : Real>=0∞) (y z : Real) : x ^ (y * z) = (
x ^ y) ^ z
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `ENNReal.coe_pow`：∀ (x : NNReal) (n : ℕ), ↑(x ^ n) = ↑x ^ n
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `CStarRing.nnnorm_star_mul_self`：nnnorm_star_mul_self {x : E} : ‖x⋆ * x‖₊
 = ‖x‖₊ * ‖x‖₊
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `star_comm_self'`：star_comm_self' [Mul R] [Star R] (x : R) [IsStarNormal 
x] : star x * x = x * star x
· 使用定理 `star_pow`：star_pow [Monoid R] [StarMul R] (x : R) (n : Nat) : star (x ^ 
n) = star x ^ n
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ENNReal.continuous_pow`：∀ (n : ℕ), Continuous fun a => a ^ n
· 使用定理 `spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`：pow_nnnorm_
pow_one_div_tendsto_nhds_spectralRadius (a : A) : Tendsto (fun n : Nat => (‖a ^ 
n‖₊ : Real>=0∞) ^ (1 / n : Real)) atTop (𝓝 (spect…
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `ENNReal.coe_mul`：∀ (x y : NNReal), ↑(x * y) = ↑x * ↑y
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `ENNReal.instT2Space`：T2Space ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
（共 33 条，此处仅展示前 30 条）
-/
theorem IsStarNormal.spectralRadius_eq_nnnorm (a : A) [IsStarNormal a] :
    spectralRadius ℂ a = ‖a‖₊ := by
  refine (ENNReal.pow_right_strictMono two_ne_zero).injective ?_
  have heq :
    (fun n : ℕ => (‖(a⋆ * a) ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ)) =
      (fun x => x ^ 2) ∘ fun n : ℕ => (‖a ^ n‖₊ : ℝ≥0∞) ^ (1 / n : ℝ) := by
    funext n
    rw [Function.comp_apply, ← rpow_natCast, ← rpow_mul, mul_comm, rpow_mul, rpow_natCast, ←
      coe_pow, sq, ← nnnorm_star_mul_self, Commute.mul_pow (star_comm_self' a), star_pow]
  have h₂ :=
    ((ENNReal.continuous_pow 2).tendsto (spectralRadius ℂ a)).comp
      (spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius a)
  rw [← heq] at h₂
  convert! tendsto_nhds_unique h₂ (pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius (a⋆ * a))
  rw [(IsSelfAdjoint.star_mul_self a).spectralRadius_eq_nnnorm, sq, nnnorm_star_mul_self, coe_mul]

namespace CStarAlgebra

/-
**CStarAlgebra.toReal_spectralRadius_star_mul_self_eq_norm_sq** 是 Mathlib 中的一个定理
，位于命名空间 `CStarAlgebra`。
形式化陈述：toReal_spectralRadius_star_mul_self_eq_norm_sq (a : A) : (spectralRadius C
omplex (a⋆ * a)).toReal = ‖a‖ ^ 2
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsSelfAdjoint.toReal_spectralRadius_complex_eq_norm`：IsSelfAdjoint.toRea
l_spectralRadius_complex_eq_norm {a : A} (ha : IsSelfAdjoint a) : (spectralRadiu
s Complex a).toReal = ‖a‖
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `CStarRing.norm_star_mul_self`：norm_star_mul_self {x : E} : ‖x⋆ * x‖ = ‖x
‖ * ‖x‖
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
-/
theorem toReal_spectralRadius_star_mul_self_eq_norm_sq (a : A) :
    (spectralRadius ℂ (a⋆ * a)).toReal = ‖a‖ ^ 2 := by
  rw [(IsSelfAdjoint.star_mul_self a).toReal_spectralRadius_complex_eq_norm,
    CStarRing.norm_star_mul_self, ← pow_two]
/-
**CStarAlgebra.toReal_spectralRadius_self_mul_star_eq_norm_sq** 是 Mathlib 中的一个定理
，位于命名空间 `CStarAlgebra`。
形式化陈述：toReal_spectralRadius_self_mul_star_eq_norm_sq (a : A) : (spectralRadius C
omplex (a * a⋆)).toReal = ‖a‖ ^ 2
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `norm_star`：norm_star (x : E) : ‖x⋆‖ = ‖x‖
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `CStarAlgebra.toReal_spectralRadius_star_mul_self_eq_norm_sq`：toReal_spec
tralRadius_star_mul_self_eq_norm_sq (a : A) : (spectralRadius Complex (a⋆ * a)).
toReal = ‖a‖ ^ 2
· 使用定理 `star_star`：star_star [InvolutiveStar R] (r : R) : star (star r) = r
-/
theorem toReal_spectralRadius_self_mul_star_eq_norm_sq (a : A) :
    (spectralRadius ℂ (a * a⋆)).toReal = ‖a‖ ^ 2 := by
  rw [← norm_star a, ← toReal_spectralRadius_star_mul_self_eq_norm_sq, star_star]
/-
**CStarAlgebra.sqrt_toReal_spectralRadius_star_mul_self_eq_norm** 是 Mathlib 中的一个
定理，位于命名空间 `CStarAlgebra`。
形式化陈述：sqrt_toReal_spectralRadius_star_mul_self_eq_norm (a : A) : (spectralRadius
 Complex (a⋆ * a)).toReal.sqrt = ‖a‖
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarAlgebra.toReal_spectralRadius_star_mul_self_eq_norm_sq`：toReal_spec
tralRadius_star_mul_self_eq_norm_sq (a : A) : (spectralRadius Complex (a⋆ * a)).
toReal = ‖a‖ ^ 2
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_toReal_spectralRadius_star_mul_self_eq_norm (a : A) :
    (spectralRadius ℂ (a⋆ * a)).toReal.sqrt = ‖a‖ := by
  simp [toReal_spectralRadius_star_mul_self_eq_norm_sq]
/-
**CStarAlgebra.sqrt_toReal_spectralRadius_self_mul_star_eq_norm** 是 Mathlib 中的一个
定理，位于命名空间 `CStarAlgebra`。
形式化陈述：sqrt_toReal_spectralRadius_self_mul_star_eq_norm (a : A) : (spectralRadius
 Complex (a * a⋆)).toReal.sqrt = ‖a‖
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CStarAlgebra.toReal_spectralRadius_self_mul_star_eq_norm_sq`：toReal_spec
tralRadius_self_mul_star_eq_norm_sq (a : A) : (spectralRadius Complex (a * a⋆)).
toReal = ‖a‖ ^ 2
· 使用定理 `Real.sqrt_sq`：sqrt_sq (h : 0 <= x) : √(x ^ 2) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sqrt_toReal_spectralRadius_self_mul_star_eq_norm (a : A) :
    (spectralRadius ℂ (a * a⋆)).toReal.sqrt = ‖a‖ := by
  simp [toReal_spectralRadius_self_mul_star_eq_norm_sq]

end CStarAlgebra

/-- Any element of the spectrum of a selfadjoint is real. -/
/-
**IsSelfAdjoint.mem_spectrum_eq_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.mem_spectrum_eq_re {a : A} (ha : IsSelfAdjoint a) {z : Compl
ex} (hz : z in spectrum Complex a) : z = z.re
参数：ha : IsSelfAdjoint a；hz : z in spectrum Complex a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `NormedSpace.exp_mem_unitary_of_mem_skewAdjoint`：exp_mem_unitary_of_mem_s
kewAdjoint [StarRing 𝔸] [ContinuousStar 𝔸] {x : 𝔸} (h : x in skewAdjoint 𝔸) : ex
p x in unitary 𝔸
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `NormedStarGroup.to_continuousStar`：∀ {E : Type u_2} [inst : SeminormedAd
dCommGroup E] [inst_1 : StarAddMonoid E] [NormedStarGroup E], ContinuousStar E
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `IsSelfAdjoint.smul_mem_skewAdjoint`：IsSelfAdjoint.smul_mem_skewAdjoint [
Ring R] [AddCommGroup A] [Module R A] [StarAddMonoid R] [StarAddMonoid A] [StarM
odule R A] {r : R} (hr :…
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Complex.conj_I`：conj_I : conj I = -I
· 使用定理 `Complex.I_ne_zero`：Complex.I ≠ 0
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `spectrum.exp_mem_exp`：exp_mem_exp [RCLike 𝕜] [NormedRing A] [NormedAlgeb
ra 𝕜 A] [CompleteSpace A] (a : A) {z : 𝕜} (hz : z in spectrum 𝕜 a) : exp z in sp
ectrum 𝕜 (…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `spectrum.smul_mem_smul_iff`：smul_mem_smul_iff {a : A} {s : R} {r : Rˣ} :
 r • s in σ (r • a) ↔ s in σ a
· 使用定理 `Complex.ext`：∀ {z w : ℂ}, z.re = w.re → z.im = w.im → z = w
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.exp.congr_simp`：∀ {𝔸 : Type u_3} [inst : Ring 𝔸] [inst_1 : T
opologicalSpace 𝔸] [inst_2 : IsTopologicalRing 𝔸] (x x_1 : 𝔸),   x = x_1 → Norme
dSpace.exp x = N…
· 使用定理 `Complex.I_mul`：I_mul (z : Complex) : I * z = ⟨-z.im, z.re⟩
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `spectrum.subset_circle_of_unitary`：spectrum.subset_circle_of_unitary {u 
: E} (h : u in unitary E) : spectrum 𝕜 u subseteq Metric.sphere 0 1

--- 原说明 ---
Any element of the spectrum of a selfadjoint is real.
-/
theorem IsSelfAdjoint.mem_spectrum_eq_re {a : A} (ha : IsSelfAdjoint a) {z : ℂ}
    (hz : z ∈ spectrum ℂ a) : z = z.re := by
  let +nondep : NormedAlgebra ℚ A := .restrictScalars ℚ ℂ A
  have hu := exp_mem_unitary_of_mem_skewAdjoint (ha.smul_mem_skewAdjoint conj_I)
  let Iu := Units.mk0 I I_ne_zero
  have : NormedSpace.exp (I • z) ∈ spectrum ℂ (NormedSpace.exp (I • a)) := by
    simpa only [Units.smul_def, Units.val_mk0] using!
      spectrum.exp_mem_exp (Iu • a) (smul_mem_smul_iff.mpr hz)
  exact Complex.ext (ofReal_re _) <| by
    simpa only [← Complex.exp_eq_exp_ℂ, mem_sphere_zero_iff_norm, norm_exp, Real.exp_eq_one_iff,
      smul_eq_mul, I_mul, neg_eq_zero] using!
      spectrum.subset_circle_of_unitary hu this

/-- Any element of the spectrum of a selfadjoint is real. -/
/-
**selfAdjoint.mem_spectrum_eq_re** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：selfAdjoint.mem_spectrum_eq_re (a : selfAdjoint A) {z : Complex} (hz : z i
n spectrum Complex (a : A)) : z = z.re
参数：a : selfAdjoint A；hz : z in spectrum Complex (a : A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.mem_spectrum_eq_re`：IsSelfAdjoint.mem_spectrum_eq_re {a : 
A} (ha : IsSelfAdjoint a) {z : Complex} (hz : z in spectrum Complex a) : z = z.r
e
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
Any element of the spectrum of a selfadjoint is real.
-/
theorem selfAdjoint.mem_spectrum_eq_re (a : selfAdjoint A) {z : ℂ}
    (hz : z ∈ spectrum ℂ (a : A)) : z = z.re :=
  a.prop.mem_spectrum_eq_re hz

/-- Any element of the spectrum of a selfadjoint is real. -/
/-
**IsSelfAdjoint.im_eq_zero_of_mem_spectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.im_eq_zero_of_mem_spectrum {a : A} (ha : IsSelfAdjoint a) {z
 : Complex} (hz : z in spectrum Complex a) : z.im = 0
参数：ha : IsSelfAdjoint a；hz : z in spectrum Complex a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsSelfAdjoint.mem_spectrum_eq_re`：IsSelfAdjoint.mem_spectrum_eq_re {a : 
A} (ha : IsSelfAdjoint a) {z : Complex} (hz : z in spectrum Complex a) : z = z.r
e
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0

--- 原说明 ---
Any element of the spectrum of a selfadjoint is real.
-/
theorem IsSelfAdjoint.im_eq_zero_of_mem_spectrum {a : A} (ha : IsSelfAdjoint a)
    {z : ℂ} (hz : z ∈ spectrum ℂ a) : z.im = 0 := by
  rw [ha.mem_spectrum_eq_re hz, ofReal_im]

/-- The spectrum of a selfadjoint is real -/
/-
**IsSelfAdjoint.val_re_map_spectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.val_re_map_spectrum {a : A} (ha : IsSelfAdjoint a) : spectru
m Complex a = ((↑) ∘ re '' spectrum Complex a : Set Complex)
参数：ha : IsSelfAdjoint a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.mem_spectrum_eq_re`：IsSelfAdjoint.mem_spectrum_eq_re {a : 
A} (ha : IsSelfAdjoint a) {z : Complex} (hz : z in spectrum Complex a) : z = z.r
e
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
The spectrum of a selfadjoint is real
-/
theorem IsSelfAdjoint.val_re_map_spectrum {a : A} (ha : IsSelfAdjoint a) :
    spectrum ℂ a = ((↑) ∘ re '' spectrum ℂ a : Set ℂ) :=
  le_antisymm (fun z hz => ⟨z, hz, (ha.mem_spectrum_eq_re hz).symm⟩) fun z => by
    rintro ⟨z, hz, rfl⟩
    simpa only [(ha.mem_spectrum_eq_re hz).symm, Function.comp_apply] using hz

/-- The spectrum of a selfadjoint is real -/
/-
**selfAdjoint.val_re_map_spectrum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：selfAdjoint.val_re_map_spectrum (a : selfAdjoint A) : spectrum Complex (a 
: A) = ((↑) ∘ re '' spectrum Complex (a : A) : Set Complex)
参数：a : selfAdjoint A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSelfAdjoint.val_re_map_spectrum`：IsSelfAdjoint.val_re_map_spectrum {a 
: A} (ha : IsSelfAdjoint a) : spectrum Complex a = ((↑) ∘ re '' spectrum Complex
 a : Set Complex)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
The spectrum of a selfadjoint is real
-/
theorem selfAdjoint.val_re_map_spectrum (a : selfAdjoint A) :
    spectrum ℂ (a : A) = ((↑) ∘ re '' spectrum ℂ (a : A) : Set ℂ) :=
  a.property.val_re_map_spectrum

/-- The complement of the spectrum of a selfadjoint element in a C⋆-algebra is connected. -/
/-
**IsSelfAdjoint.isConnected_spectrum_compl** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsSelfAdjoint.isConnected_spectrum_compl {a : A} (ha : IsSelfAdjoint a) : 
IsConnected (σ Complex a)ᶜ
参数：ha : IsSelfAdjoint a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConnected.union`：IsConnected.union {s t : Set α} (H : (s inter t).None
mpty) (Hs : IsConnected s) (Ht : IsConnected t) : IsConnected (s union t)
· 使用定理 `Filter.NeBot.nonempty_of_mem`：∀ {α : Type u} {f : Filter α}, f.NeBot → ∀
 {s : Set α}, s ∈ f → s.Nonempty
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `AntilipschitzWith.tendsto_cobounded`：tendsto_cobounded (hf : Antilipschi
tzWith K f) : Tendsto f (cobounded α) (cobounded β)
· 使用定理 `Isometry.antilipschitz`：antilipschitz (h : Isometry f) : AntilipschitzWi
th 1 f
· 使用定理 `Complex.isometry_ofReal`：Isometry Complex.ofReal
· 使用定理 `Bornology.IsBounded.compl`：∀ {α : Type u_2} {x : Bornology α} {s : Set α
}, Bornology.IsBounded s → Bornology.IsCobounded sᶜ
· 使用定理 `spectrum.isBounded`：isBounded (a : A) : Bornology.IsBounded (σ a)
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `Set.Nonempty.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Nonempty → t.
Nonempty
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用引理 `Complex.isConnected_of_upperHalfPlane`：isConnected_of_upperHalfPlane {r}
 {s : Set Complex} (hs₁ : {z | r < z.im} subseteq s) (hs₂ : s subseteq {z | r <=
 z.im}) : IsConnected s
· 使用定理 `Set.subset_inter`：subset_inter {s t r : Set α} (rs : r subseteq s) (rt :
 r subseteq t) : r subseteq s inter t
· 使用定理 `IsSelfAdjoint.im_eq_zero_of_mem_spectrum`：IsSelfAdjoint.im_eq_zero_of_me
m_spectrum {a : A} (ha : IsSelfAdjoint a) {z : Complex} (hz : z in spectrum Comp
lex a) : z.im = 0
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Complex.isConnected_of_lowerHalfPlane`：isConnected_of_lowerHalfPlane {r}
 {s : Set Complex} (hs₁ : {z | z.im < r} subseteq s) (hs₂ : s subseteq {z | z.im
 <= r}) : IsConnected s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.inter_univ`：inter_univ (a : Set α) : a inter univ = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The complement of the spectrum of a selfadjoint element in a C⋆-algebra is conne
cted.
-/
lemma IsSelfAdjoint.isConnected_spectrum_compl {a : A} (ha : IsSelfAdjoint a) :
    IsConnected (σ ℂ a)ᶜ := by
  suffices IsConnected (((σ ℂ a)ᶜ ∩ {z | 0 ≤ z.im}) ∪ (σ ℂ a)ᶜ ∩ {z | z.im ≤ 0}) by
    rw [← Set.inter_union_distrib_left, ← Set.ofPred_or] at this
    rw [← Set.inter_univ (σ ℂ a)ᶜ]
    convert this
    exact Eq.symm <| Set.eq_univ_of_forall (fun z ↦ le_total 0 z.im)
  refine IsConnected.union ?nonempty ?upper ?lower
  case nonempty =>
    have := Filter.NeBot.nonempty_of_mem inferInstance <| Filter.mem_map.mp <|
      Complex.isometry_ofReal.antilipschitz.tendsto_cobounded (spectrum.isBounded a |>.compl)
    exact this.image Complex.ofReal |>.mono <| by simp
  case' upper => apply Complex.isConnected_of_upperHalfPlane ?_ <| Set.inter_subset_right
  case' lower => apply Complex.isConnected_of_lowerHalfPlane ?_ <| Set.inter_subset_right
  all_goals
    refine Set.subset_inter (fun z hz hz' ↦ ?_) (fun _ ↦ by simpa using le_of_lt)
    rw [Set.mem_ofPred_eq, ha.im_eq_zero_of_mem_spectrum hz'] at hz
    simp_all

namespace StarSubalgebra

variable (S : StarSubalgebra ℂ A) [hS : IsClosed (S : Set A)]

/-- For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in `A`, then
`x` is invertible in `S`. -/
/-
**StarSubalgebra.coe_isUnit** 是 Mathlib 中的一个引理，位于命名空间 `StarSubalgebra`。
形式化陈述：coe_isUnit {a : S} : IsUnit (a : A) ↔ IsUnit a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `IsUnit.mul`：∀ {M : Type u_1} [inst : Monoid M] {a b : M}, IsUnit a → IsU
nit b → IsUnit (a * b)
· 使用定理 `IsUnit.star`：∀ {R : Type u} [inst : Monoid R] [inst_1 : StarMul R] {a : 
R}, IsUnit a → IsUnit (star a)
· 使用引理 `Subalgebra.spectrum_eq_of_isPreconnected_compl`：Subalgebra.spectrum_eq_o
f_isPreconnected_compl (h : IsPreconnected (σ 𝕜 (x : A))ᶜ) : σ 𝕜 x = σ 𝕜 (x : A)
· 使用定理 `CStarAlgebra.toCompleteSpace`：∀ {A : Type u_1} [self : CStarAlgebra A], 
CompleteSpace A
· 使用定理 `IsConnected.isPreconnected`：IsConnected.isPreconnected {s : Set α} (h : 
IsConnected s) : IsPreconnected s
· 使用引理 `IsSelfAdjoint.isConnected_spectrum_compl`：IsSelfAdjoint.isConnected_spec
trum_compl {a : A} (ha : IsSelfAdjoint a) : IsConnected (σ Complex a)ᶜ
· 使用定理 `IsSelfAdjoint.map`：map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
 [StarHomClass F R S] {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f 
x)
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `SubmonoidClass.toMulMemClass`：∀ {S : Type u_3} {M : outParam (Type u_4)}
 {inst : MulOneClass M} {inst_1 : SetLike S M} [self : SubmonoidClass S M],   Mu
lMemClass S M
· 使用定理 `SubsemiringClass.toSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Type 
u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringClas
s S R], SubmonoidClass …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.zero_notMem_iff`：zero_notMem_iff {a : A} : (0 : R) ∉ σ a ↔ IsUn
it a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `MulMemClass.coe_mul`：coe_mul (x y : S') : (↑(x * y) : M) = ↑x * ↑y
· 使用定理 `StarMemClass.coe_star`：∀ {R : Type u} {S : Type w} [inst : Star R] [inst
_1 : SetLike S R] [hS : StarMemClass S R] (s : S) (x : ↥s),   ↑(star x) = star ↑
x
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `IsUnit.val_inv_mul`：val_inv_mul (h : IsUnit a) : ↑h.unit⁻¹ * a = 1
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `IsSelfAdjoint.mul_star_self`：mul_star_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (x * star x)
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `left_inv_eq_right_inv`：∀ {M : Type u_2} [inst : Monoid M] {a b c : M}, b
 * a = 1 → a * c = 1 → b = c
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…

--- 原说明 ---
For a unital C⋆-subalgebra `S` of `A` and `x : S`, if `↑x : A` is invertible in 
`A`, then
`x` is invertible in `S`.
-/
lemma coe_isUnit {a : S} : IsUnit (a : A) ↔ IsUnit a := by
  refine ⟨fun ha ↦ ?_, IsUnit.map S.subtype⟩
  have ha₁ := ha.star.mul ha
  have ha₂ := ha.mul ha.star
  have spec_eq {x : S} (hx : IsSelfAdjoint x) : spectrum ℂ x = spectrum ℂ (x : A) :=
    Subalgebra.spectrum_eq_of_isPreconnected_compl S _ <|
      (hx.map S.subtype).isConnected_spectrum_compl.isPreconnected
  rw [← StarMemClass.coe_star, ← MulMemClass.coe_mul, ← spectrum.zero_notMem_iff ℂ, ← spec_eq,
    spectrum.zero_notMem_iff] at ha₁ ha₂
  · have h₁ : ha₁.unit⁻¹ * star a * a = 1 := mul_assoc _ _ a ▸ ha₁.val_inv_mul
    have h₂ : a * (star a * ha₂.unit⁻¹) = 1 := (mul_assoc a _ _).symm ▸ ha₂.mul_val_inv
    exact ⟨⟨a, ha₁.unit⁻¹ * star a, left_inv_eq_right_inv h₁ h₂ ▸ h₂, h₁⟩, rfl⟩
  · exact IsSelfAdjoint.mul_star_self a
  · exact IsSelfAdjoint.star_mul_self a
/-
**StarSubalgebra.mem_spectrum_iff** 是 Mathlib 中的一个引理，位于命名空间 `StarSubalgebra`。
形式化陈述：mem_spectrum_iff {a : S} {z : Complex} : z in spectrum Complex a ↔ z in sp
ectrum Complex (a : A)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `StarSubalgebra.coe_isUnit`：coe_isUnit {a : S} : IsUnit (a : A) ↔ IsUnit 
a
-/
lemma mem_spectrum_iff {a : S} {z : ℂ} : z ∈ spectrum ℂ a ↔ z ∈ spectrum ℂ (a : A) :=
  not_iff_not.mpr S.coe_isUnit.symm

/-- **Spectral permanence.** The spectrum of an element is invariant of the (closed)
`StarSubalgebra` in which it is contained. -/
/-
**StarSubalgebra.spectrum_eq** 是 Mathlib 中的一个引理，位于命名空间 `StarSubalgebra`。
形式化陈述：spectrum_eq {a : S} : spectrum Complex a = spectrum Complex (a : A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用引理 `StarSubalgebra.mem_spectrum_iff`：mem_spectrum_iff {a : S} {z : Complex} 
: z in spectrum Complex a ↔ z in spectrum Complex (a : A)

--- 原说明 ---
**Spectral permanence.** The spectrum of an element is invariant of the (closed)
`StarSubalgebra` in which it is contained.
-/
lemma spectrum_eq {a : S} : spectrum ℂ a = spectrum ℂ (a : A) :=
  Set.ext fun _ ↦ S.mem_spectrum_iff

end StarSubalgebra

end ComplexScalars

namespace NonUnitalStarAlgHom

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
variable [FunLike F A B] [NonUnitalAlgHomClass F ℂ A B] [StarHomClass F A B]

open Unitization

set_option backward.isDefEq.respectTransparency.types false in
/-- A non-unital star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
/-
**NonUnitalStarAlgHom.nnnorm_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAl
gHom`。
形式化陈述：nnnorm_apply_le (φ : F) (a : A) : ‖φ a‖₊ <= ‖a‖₊
参数：φ : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalCStarAlgebra.toIsScalarTower`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], IsScalarTower ℂ A A
· 使用定理 `NonUnitalCStarAlgebra.toSMulCommClass`：∀ {A : Type u_1} [self : NonUnita
lCStarAlgebra A], SMulCommClass ℂ A A
· 使用定理 `iSup_le_iSup_of_subset`：iSup_le_iSup_of_subset {f : β -> α} {s t : Set β
} : s subseteq t -> ⨆ x in s, f x <= ⨆ x in t, f x
· 使用定理 `AlgHom.spectrum_apply_subset`：spectrum_apply_subset (φ : F) (a : A) : σ 
((φ : A -> B) a) subseteq σ a
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.coe_le_coe`：∀ {r q : NNReal}, ↑r ≤ ↑q ↔ r ≤ q
· 使用定理 `IsSelfAdjoint.spectralRadius_eq_nnnorm`：IsSelfAdjoint.spectralRadius_eq_
nnnorm {a : A} (ha : IsSelfAdjoint a) : spectralRadius Complex a = ‖a‖₊
· 使用定理 `IsSelfAdjoint.map`：map {F R S : Type*} [Star R] [Star S] [FunLike F R S]
 [StarHomClass F R S] {x : R} (hx : IsSelfAdjoint x) (f : F) : IsSelfAdjoint (f 
x)
· 使用定理 `StarAlgHom.instStarHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u
_4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst
_3 : Star A] [ins…
· 使用定理 `nonneg_le_nonneg_of_sq_le_sq`：nonneg_le_nonneg_of_sq_le_sq [PosMulStrict
Mono R] [MulPosMono R] {a b : R} (hb : 0 <= b) (h : a * a <= b * b) : a <= b
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `NonUnitalCStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : NonUnitalCS
tarAlgebra A], StarModule ℂ A
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `NonUnitalCStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : NonUnitalCSt
arAlgebra A], CStarRing A
· 使用定理 `CStarAlgebra.toCStarRing`：∀ {A : Type u_1} [self : CStarAlgebra A], CSta
rRing A
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `IsSelfAdjoint.star_mul_self`：star_mul_self [Mul R] [StarMul R] (x : R) :
 IsSelfAdjoint (star x * x)
· 使用定理 `CStarAlgebra.toStarModule`：∀ {A : Type u_1} [self : CStarAlgebra A], Sta
rModule ℂ A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Unitization.starLift_apply`：∀ {R : Type u_1} {A : Type u_2} {C : Type u_
3} [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : NonUnitalSemiring A
] [inst_3 : Star…
· 使用定理 `NonUnitalAlgHom.toAlgHom_apply`：∀ {R : Type u_2} {A : Type u_3} [inst : 
CommSemiring R] [inst_1 : NonUnitalSemiring A] [inst_2 : _root_.Module R A]   [i
nst_3 : SMulCommClas…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A non-unital star algebra homomorphism of complex C⋆-algebras is norm contractiv
e.
-/
lemma nnnorm_apply_le (φ : F) (a : A) : ‖φ a‖₊ ≤ ‖a‖₊ := by
  have h (ψ : Unitization ℂ A →⋆ₐ[ℂ] Unitization ℂ B) (x : Unitization ℂ A) :
      ‖ψ x‖₊ ≤ ‖x‖₊ := by
    suffices ∀ {s}, IsSelfAdjoint s → ‖ψ s‖₊ ≤ ‖s‖₊ by
      refine nonneg_le_nonneg_of_sq_le_sq zero_le ?_
      simp_rw [← nnnorm_star_mul_self, ← map_star, ← map_mul]
      exact this <| .star_mul_self x
    intro s hs
    suffices this : spectralRadius ℂ (ψ s) ≤ spectralRadius ℂ s by
      rwa [(hs.map ψ).spectralRadius_eq_nnnorm, hs.spectralRadius_eq_nnnorm, coe_le_coe]
        at this
    exact iSup_le_iSup_of_subset (AlgHom.spectrum_apply_subset ψ s)
  simpa [nnnorm_inr] using h (starLift (inrNonUnitalStarAlgHom ℂ B |>.comp (φ : A →⋆ₙₐ[ℂ] B))) a

/-- A non-unital star algebra homomorphism of complex C⋆-algebras is norm contractive. -/
/-
**NonUnitalStarAlgHom.norm_apply_le** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalStarAlgH
om`。
形式化陈述：norm_apply_le (φ : F) (a : A) : ‖φ a‖ <= ‖a‖
参数：φ : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `NonUnitalStarAlgHom.nnnorm_apply_le`：nnnorm_apply_le (φ : F) (a : A) : ‖
φ a‖₊ <= ‖a‖₊

--- 原说明 ---
A non-unital star algebra homomorphism of complex C⋆-algebras is norm contractiv
e.
-/
lemma norm_apply_le (φ : F) (a : A) : ‖φ a‖ ≤ ‖a‖ := by
  exact_mod_cast nnnorm_apply_le φ a

/-- Non-unital star algebra homomorphisms between C⋆-algebras are continuous linear maps.
See note [lower instance priority] -/
/-
**NonUnitalStarAlgHom.instContinuousLinearMapClassComplex** 是 Mathlib 中的一个引理，位于命
名空间 `NonUnitalStarAlgHom`。
形式化陈述：instContinuousLinearMapClassComplex : ContinuousLinearMapClass F Complex A
 B
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AddMonoidHomClass.continuous_of_bound`：∀ {𝓕 : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [i
nst_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `NonUnitalStarAlgHom.nnnorm_apply_le`：nnnorm_apply_le (φ : F) (a : A) : ‖
φ a‖₊ <= ‖a‖₊

--- 原说明 ---
Non-unital star algebra homomorphisms between C⋆-algebras are continuous linear 
maps.
See note [lower instance priority]
-/
lemma instContinuousLinearMapClassComplex : ContinuousLinearMapClass F ℂ A B :=
  { NonUnitalAlgHomClass.instLinearMapClass with
    map_continuous := fun φ =>
      AddMonoidHomClass.continuous_of_bound φ 1 (by simpa only [one_mul] using! nnnorm_apply_le φ) }

scoped[CStarAlgebra] attribute [instance] NonUnitalStarAlgHom.instContinuousLinearMapClassComplex

end NonUnitalStarAlgHom

namespace StarAlgEquiv

variable {F A B : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B] [EquivLike F A B]
variable [NonUnitalAlgEquivClass F ℂ A B] [StarHomClass F A B]

/-
**StarAlgEquiv.nnnorm_map** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：nnnorm_map (φ : F) (a : A) : ‖φ a‖₊ = ‖a‖₊
参数：φ : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `NonUnitalStarAlgHom.nnnorm_apply_le`：nnnorm_apply_le (φ : F) (a : A) : ‖
φ a‖₊ <= ‖a‖₊
· 使用定理 `instNonUnitalAlgHomClassOfNonUnitalAlgEquivClass`：∀ {F : Type u_1} {R : 
Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [inst_1 : NonUnitalNon
AssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `StarAlgEquiv.symm_apply_apply`：symm_apply_apply (e : A ≃⋆ₐ[R] B) : foral
l x, e.symm (e x) = x
· 使用定理 `StarAlgEquiv.instNonUnitalAlgEquivClass`：∀ {R : Type u_2} {A : Type u_3}
 {B : Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B
]   [inst_4 : SMul R A] [inst…
· 使用定理 `NonUnitalStarRingHomClass.toStarHomClass`：∀ {F : Type u_1} {A : outParam
 (Type u_2)} {B : outParam (Type u_3)} {inst : NonUnitalNonAssocSemiring A}   {i
nst_1 : Star A} {inst_2 : NonU…
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalStarAlgHomClass.instNonUnitalStarRingHomClassOfStarHomClass`：∀ 
{F : Type u_1} {R : Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [i
nst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : DistribMu…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `StarRingEquivClass.toRingEquivClass`：∀ {F : Type u_1} {A : outParam (Typ
e u_2)} {B : outParam (Type u_3)} {inst : Add A} {inst_1 : Mul A} {inst_2 : Star
 A}   {inst_3 : Add B} {i…
· 使用定理 `StarAlgEquiv.instStarRingEquivClass`：∀ {R : Type u_2} {A : Type u_3} {B 
: Type u_4} [inst : Add A] [inst_1 : Add B] [inst_2 : Mul A] [inst_3 : Mul B]   
[inst_4 : SMul R A] [inst…
· 使用定理 `StarRingEquivClass.instNonUnitalStarRingHomClass`：∀ {F : Type u_1} {A : 
Type u_2} {B : Type u_3} [inst : NonUnitalNonAssocSemiring A] [inst_1 : Star A] 
  [inst_2 : NonUnitalNonAssocSemiring …
-/
lemma nnnorm_map (φ : F) (a : A) : ‖φ a‖₊ = ‖a‖₊ :=
  le_antisymm (NonUnitalStarAlgHom.nnnorm_apply_le φ a) <| by
    simpa using! NonUnitalStarAlgHom.nnnorm_apply_le (symm (φ : A ≃⋆ₐ[ℂ] B)) ((φ : A ≃⋆ₐ[ℂ] B) a)
/-
**StarAlgEquiv.norm_map** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：norm_map (φ : F) (a : A) : ‖φ a‖ = ‖a‖
参数：φ : F；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `StarAlgEquiv.nnnorm_map`：nnnorm_map (φ : F) (a : A) : ‖φ a‖₊ = ‖a‖₊
-/
lemma norm_map (φ : F) (a : A) : ‖φ a‖ = ‖a‖ :=
  congr_arg NNReal.toReal (nnnorm_map φ a)
/-
**StarAlgEquiv.isometry** 是 Mathlib 中的一个引理，位于命名空间 `StarAlgEquiv`。
形式化陈述：isometry (φ : F) : Isometry φ
参数：φ : F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `instNonUnitalAlgHomClassOfNonUnitalAlgEquivClass`：∀ {F : Type u_1} {R : 
Type u_2} {A : Type u_3} {B : Type u_4} [inst : Monoid R] [inst_1 : NonUnitalNon
AssocSemiring A]   [inst_2 : DistribMu…
· 使用引理 `StarAlgEquiv.norm_map`：norm_map (φ : F) (a : A) : ‖φ a‖ = ‖a‖
-/
lemma isometry (φ : F) : Isometry φ :=
  AddMonoidHomClass.isometry_of_norm φ (norm_map φ)

end StarAlgEquiv

end

namespace WeakDual

open ContinuousMap Complex

open scoped ComplexStarModule

variable {F A : Type*} [CStarAlgebra A] [FunLike F A ℂ] [hF : AlgHomClass F ℂ A ℂ]

/-- This instance is provided instead of `StarHomClass` to avoid type class inference loops.
See note [lower instance priority] -/
/-
**WeakDual.** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is provided instead of `StarHomClass` to avoid type class inferenc
e loops.
See note [lower instance priority]
-/
noncomputable instance (priority := 100) Complex.instStarHomClass : StarHomClass F A ℂ where
  map_star φ a := by
    suffices hsa : ∀ s : selfAdjoint A, (φ s)⋆ = φ s by
      rw [← realPart_add_I_smul_imaginaryPart a]
      simp only [map_add, map_smul, star_add, star_smul, hsa, selfAdjoint.star_val_eq]
    intro s
    rw [selfAdjoint.mem_spectrum_eq_re s (AlgHom.apply_mem_spectrum φ (s : A))]
    simp

/-- This is not an instance to avoid type class inference loops. See
`WeakDual.Complex.instStarHomClass`. -/
/-
**WeakDual._root_.AlgHomClass.instStarHomClass** 是 Mathlib 中的一个引理，位于命名空间 `WeakDu
al`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is not an instance to avoid type class inference loops. See
`WeakDual.Complex.instStarHomClass`.
-/
lemma _root_.AlgHomClass.instStarHomClass : StarHomClass F A ℂ :=
  { WeakDual.Complex.instStarHomClass, hF with }

namespace CharacterSpace

/-
**WeakDual.CharacterSpace.instStarHomClass** 是 Mathlib 中的一个实例，位于命名空间 `WeakDual.C
haracterSpace`。
形式化陈述：instStarHomClass : StarHomClass (characterSpace Complex A) A Complex
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `AlgHomClass.instStarHomClass`：∀ {F : Type u_1} {A : Type u_2} [inst : CS
tarAlgebra A] [inst_1 : FunLike F A ℂ] [hF : AlgHomClass F ℂ A ℂ],   StarHomClas
s F A ℂ
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
noncomputable instance instStarHomClass : StarHomClass (characterSpace ℂ A) A ℂ :=
  { AlgHomClass.instStarHomClass with }

end CharacterSpace

end WeakDual

