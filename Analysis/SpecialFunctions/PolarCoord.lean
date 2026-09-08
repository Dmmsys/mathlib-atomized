/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Polar coordinates

We define polar coordinates, as an open partial homeomorphism in `ℝ^2` between `ℝ^2 - (-∞, 0]` and
`(0, +∞) × (-π, π)`. Its inverse is given by `(r, θ) ↦ (r cos θ, r sin θ)`.

It satisfies the following change of variables formula (see `integral_comp_polarCoord_symm`):
`∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) = ∫ p, f p`

-/

@[expose] public section

noncomputable section Real

open Real Set MeasureTheory

open scoped ENNReal Real Topology

/-- The polar coordinates are an open partial homeomorphism in `ℝ^2`, mapping `(r cos θ, r sin θ)`
to `(r, θ)`. It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π)`. -/
@[simps]
/-
**polarCoord** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：polarCoord : OpenPartialHomeomorph (Real × Real) (Real × Real) where toFun
 q
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The polar coordinates are an open partial homeomorphism in `ℝ^2`, mapping `(r co
s θ, r sin θ)`
to `(r, θ)`. It is a homeomorphism between `ℝ^2 - (-∞, 0]` and `(0, +∞) × (-π, π
)`.
-/
def polarCoord : OpenPartialHomeomorph (ℝ × ℝ) (ℝ × ℝ) where
  toFun q := (√(q.1 ^ 2 + q.2 ^ 2), Complex.arg (Complex.equivRealProd.symm q))
  invFun p := (p.1 * cos p.2, p.1 * sin p.2)
  source := {q | 0 < q.1} ∪ {q | q.2 ≠ 0}
  target := Ioi (0 : ℝ) ×ˢ Ioo (-π) π
  map_target' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    dsimp at hr hθ
    rcases eq_or_ne θ 0 with (rfl | h'θ)
    · simpa using! hr
    · right
      simp at hr
      simpa only [ne_of_gt hr, Ne, mem_ofPred_eq, mul_eq_zero, false_or,
        sin_eq_zero_iff_of_lt_of_lt hθ.1 hθ.2] using! h'θ
  map_source' := by
    rintro ⟨x, y⟩ hxy
    simp only [prodMk_mem_set_prod_eq, mem_Ioi, sqrt_pos, mem_Ioo, Complex.neg_pi_lt_arg,
      true_and, Complex.arg_lt_pi_iff]
    constructor
    · rcases hxy with hxy | hxy
      · dsimp at hxy; linarith [sq_pos_of_ne_zero hxy.ne', sq_nonneg y]
      · linarith [sq_nonneg x, sq_pos_of_ne_zero hxy]
    · rcases hxy with hxy | hxy
      · exact Or.inl (le_of_lt hxy)
      · exact Or.inr hxy
  right_inv' := by
    rintro ⟨r, θ⟩ ⟨hr, hθ⟩
    ext <;> dsimp at hr hθ ⊢
    · conv_rhs => rw [← sqrt_sq (le_of_lt hr), ← one_mul (r ^ 2), ← sin_sq_add_cos_sq θ]
      congr 1
      ring
    · convert! Complex.arg_mul_cos_add_sin_mul_I hr ⟨hθ.1, hθ.2.le⟩
      simp only [Complex.equivRealProd_symm_apply, Complex.ofReal_mul, Complex.ofReal_cos,
        Complex.ofReal_sin]
      ring
  left_inv' := by
    rintro ⟨x, y⟩ _
    have A : √(x ^ 2 + y ^ 2) = ‖x + y * Complex.I‖ := by
      rw [Complex.norm_def, Complex.normSq_add_mul_I]
    simp [A]
  open_target := isOpen_Ioi.prod isOpen_Ioo
  open_source :=
    (isOpen_lt continuous_const continuous_fst).union
      (isOpen_ne_fun continuous_snd continuous_const)
  continuousOn_invFun := by fun_prop
  continuousOn_toFun := by
    refine .prodMk (by fun_prop) ?_
    have A : MapsTo Complex.equivRealProd.symm ({q : ℝ × ℝ | 0 < q.1} ∪ {q : ℝ × ℝ | q.2 ≠ 0})
        Complex.slitPlane := by
      rintro ⟨x, y⟩ hxy; simpa only using! hxy
    refine ContinuousOn.comp (f := Complex.equivRealProd.symm)
      (g := Complex.arg) (fun z hz => ?_) ?_ A
    · exact (Complex.continuousAt_arg hz).continuousWithinAt
    · exact Complex.equivRealProdCLM.symm.continuous.continuousOn

@[fun_prop]
/-
**continuous_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_polarCoord_symm : Continuous polarCoord.symm
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_mul`：continuous_mul : Continuous fun p : M × M => p.1 * p.2
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Continuous.fst`：Continuous.fst {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).1
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `Real.continuous_cos`：continuous_cos : Continuous cos
· 使用定理 `Continuous.snd`：Continuous.snd {f : X -> Y × Z} (hf : Continuous f) : Co
ntinuous fun x : X => (f x).2
· 使用定理 `Real.continuous_sin`：continuous_sin : Continuous sin
-/
theorem continuous_polarCoord_symm :
    Continuous polarCoord.symm :=
  .prodMk (by fun_prop) (by fun_prop)

/-- The derivative of `polarCoord.symm`, see `hasFDerivAt_polarCoord_symm`. -/
/-
**fderivPolarCoordSymm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fderivPolarCoordSymm (p : Real × Real) : Real × Real ->L[Real] Real × Real
参数：p : Real × Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of `polarCoord.symm`, see `hasFDerivAt_polarCoord_symm`.
-/
def fderivPolarCoordSymm (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℝ × ℝ :=
  (Matrix.toLin (.finTwoProd ℝ) (.finTwoProd ℝ)
    !![cos p.2, -p.1 * sin p.2; sin p.2, p.1 * cos p.2]).toContinuousLinearMap
/-
**hasFDerivAt_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_polarCoord_symm (p : Real × Real) : HasFDerivAt polarCoord.sym
m (fderivPolarCoordSymm p) p
参数：p : Real × Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `Prod.instIsTopologicalAddGroup`：∀ {G : Type w} {H : Type x} [inst : Topo
logicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [inst_3 : Topo
logicalSpace H] [ins…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousSMul.continuousConstSMul`：∀ {M : Type u_1} {X : Type u_2} [ins
t : TopologicalSpace M] [inst_1 : TopologicalSpace X] [inst_2 : SMul M X]   [Con
tinuousSMul M X], Contin…
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.toLin_finTwoProd_toContinuousLinearMap`：∀ {𝕜 : Type u} [hnorm : N
ontriviallyNormedField 𝕜] [inst : CompleteSpace 𝕜] (a b c d : 𝕜),   LinearMap.to
ContinuousLinearMap       ((Matrix.…
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
（共 45 条，此处仅展示前 30 条）
-/
theorem hasFDerivAt_polarCoord_symm (p : ℝ × ℝ) :
    HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p := by
  unfold fderivPolarCoordSymm
  rw [Matrix.toLin_finTwoProd_toContinuousLinearMap]
  convert!
    HasFDerivAt.prodMk (𝕜 := ℝ)
      (hasFDerivAt_fst.mul ((hasDerivAt_cos p.2).comp_hasFDerivAt p hasFDerivAt_snd))
      (hasFDerivAt_fst.mul ((hasDerivAt_sin p.2).comp_hasFDerivAt p hasFDerivAt_snd)) using
    2 <;>
  simp [smul_smul, add_comm, neg_mul, smul_neg, neg_smul _ (ContinuousLinearMap.snd ℝ ℝ ℝ)]
/-
**det_fderivPolarCoordSymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_fderivPolarCoordSymm (p : Real × Real) : (fderivPolarCoordSymm p).det 
= p.1
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Real.cos_sq_add_sin_sq`：cos_sq_add_sin_sq : cos x ^ 2 + sin x ^ 2 = 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearMap.det_toLin`：det_toLin (b : Basis ι R M) (f : Matrix ι ι R) : Li
nearMap.det (Matrix.toLin b b f) = f.det
· 使用定理 `Matrix.det_fin_two_of`：det_fin_two_of (a b c d : R) : Matrix.det !![a, b
; c, d] = a * d - b * c
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pp_pf_overlap`：∀ {R : Type u_1} [inst : C
ommSemiring R] {a₂ b₂ c : R} {ea eb e : ℕ} (x : R),   ea + eb = e → a₂ * b₂ = c 
→ x ^ ea * a₂ * (x ^ eb * b₂) = x …
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
（共 37 条，此处仅展示前 30 条）
-/
theorem det_fderivPolarCoordSymm (p : ℝ × ℝ) :
    (fderivPolarCoordSymm p).det = p.1 := by
  conv_rhs => rw [← one_mul p.1, ← cos_sq_add_sin_sq p.2]
  unfold fderivPolarCoordSymm
  simp only [neg_mul, LinearMap.det_toContinuousLinearMap, LinearMap.det_toLin,
    Matrix.det_fin_two_of, sub_neg_eq_add]
  ring

/-- This instance is required to see through the defeq `volume = volume.prod volume`. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This instance is required to see through the defeq `volume = volume.prod volume`
.
-/
instance : Measure.IsAddHaarMeasure volume (G := ℝ × ℝ) :=
  Measure.prod.instIsAddHaarMeasure _ _
/-
**polarCoord_source_ae_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：polarCoord_source_ae_eq_univ : polarCoord.source =ᵐ[volume] univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `polarCoord_source`：polarCoord.source = {q | 0 < q.1} ∪ {q | q.2 ≠ 0}
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MeasureTheory.Measure.addHaar_submodule`：addHaar_submodule {E : Type*} [
NormedAddCommGroup E] [NormedSpace Real E] [MeasurableSpace E] [BorelSpace E] [F
initeDimensional Real E] (μ :…
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsAddHaarMeasureProdRealVolume`：MeasureTheory.volume.IsAddHaarMeasur
e
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem polarCoord_source_ae_eq_univ : polarCoord.source =ᵐ[volume] univ := by
  have A : polarCoord.sourceᶜ ⊆ LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) := by
    intro x hx
    simp only [polarCoord_source, compl_union, mem_inter_iff, mem_compl_iff, mem_ofPred_eq, not_lt,
      Classical.not_not] at hx
    exact hx.2
  have B : volume (LinearMap.ker (LinearMap.snd ℝ ℝ ℝ) : Set (ℝ × ℝ)) = 0 := by
    apply Measure.addHaar_submodule
    rw [Ne, LinearMap.ker_eq_top]
    intro h
    have : (LinearMap.snd ℝ ℝ ℝ) (0, 1) = (0 : ℝ × ℝ →ₗ[ℝ] ℝ) (0, 1) := by rw [h]
    simp at this
  simp only [ae_eq_univ]
  exact le_antisymm ((measure_mono A).trans (le_of_eq B)) bot_le
/-
**integral_comp_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSp
ace Real E] (f : Real × Real -> E) : (∫ p in polarCoord.target, p.1 • f (polarCo
ord.symm p)) = ∫ p, f p
参数：f : Real × Real -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `polarCoord_source_ae_eq_univ`：polarCoord_source_ae_eq_univ : polarCoord.
source =ᵐ[volume] univ
· 使用定理 `OpenPartialHomeomorph.symm_target`：symm_target : e.symm.target = e.sourc
e
· 使用定理 `MeasureTheory.integral_target_eq_integral_abs_det_fderiv_smul`：integral_
target_eq_integral_abs_det_fderiv_smul {f : OpenPartialHomeomorph E E} (hf' : fo
rall x in f.source, HasFDerivAt f (f' x) x) (g : E …
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureProdRealVolume`：MeasureTheory.volume.IsAddHaarMeasur
e
· 使用定理 `hasFDerivAt_polarCoord_symm`：hasFDerivAt_polarCoord_symm (p : Real × Rea
l) : HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p
· 使用定理 `OpenPartialHomeomorph.symm_source`：symm_source : e.symm.source = e.targe
t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `det_fderivPolarCoordSymm`：det_fderivPolarCoordSymm (p : Real × Real) : (
fderivPolarCoordSymm p).det = p.1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ × ℝ → E) :
    (∫ p in polarCoord.target, p.1 • f (polarCoord.symm p)) = ∫ p, f p := by
  symm
  calc
    ∫ p, f p = ∫ p in polarCoord.source, f p := by
      rw [← setIntegral_univ]
      apply setIntegral_congr_set
      exact polarCoord_source_ae_eq_univ.symm
    _ = ∫ p in polarCoord.target, |p.1| • f (polarCoord.symm p) := by
      rw [← OpenPartialHomeomorph.symm_target,
      integral_target_eq_integral_abs_det_fderiv_smul volume
      (fun p _ ↦ hasFDerivAt_polarCoord_symm p), OpenPartialHomeomorph.symm_source]
      simp_rw [det_fderivPolarCoordSymm]
    _ = ∫ p in polarCoord.target, p.1 • f (polarCoord.symm p) := by
      apply setIntegral_congr_fun polarCoord.open_target.measurableSet fun x hx => ?_
      rw [abs_of_pos hx.1]
/-
**lintegral_comp_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lintegral_comp_polarCoord_symm (f : Real × Real -> Real>=0∞) : ∫⁻ (p : Rea
l × Real) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) = ∫⁻ 
(p : Real × Real), f p
参数：f : Real × Real -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.setLIntegral_congr`：setLIntegral_congr {f : α -> Real>=0∞}
 {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `polarCoord_source_ae_eq_univ`：polarCoord_source_ae_eq_univ : polarCoord.
source =ᵐ[volume] univ
· 使用定理 `OpenPartialHomeomorph.symm_image_target_eq_source`：symm_image_target_eq_
source : e.symm '' e.target = e.source
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`：lintegral
_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s) (hf' : forall x in
 s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instIsAddHaarMeasureProdRealVolume`：MeasureTheory.volume.IsAddHaarMeasur
e
· 使用定理 `MeasurableSet.prod`：∀ {α : Type u_1} {β : Type u_2} {m : MeasurableSpace
 α} {mβ : MeasurableSpace β} {s : Set α} {t : Set β},   MeasurableSet s → Measur
ableSet …
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `measurableSet_Ioo`：measurableSet_Ioo [OrderClosedTopology α] : Measurabl
eSet (Ioo a b)
· 使用定理 `HasFDerivAt.hasFDerivWithinAt`：HasFDerivAt.hasFDerivWithinAt (h : HasFDe
rivAt f f' x) : HasFDerivWithinAt f f' s x
· 使用定理 `hasFDerivAt_polarCoord_symm`：hasFDerivAt_polarCoord_symm (p : Real × Rea
l) : HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `det_fderivPolarCoordSymm`：det_fderivPolarCoordSymm (p : Real × Real) : (
fderivPolarCoordSymm p).det = p.1
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
（共 34 条，此处仅展示前 30 条）
-/
theorem lintegral_comp_polarCoord_symm (f : ℝ × ℝ → ℝ≥0∞) :
    ∫⁻ (p : ℝ × ℝ) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) =
      ∫⁻ (p : ℝ × ℝ), f p := by
  symm
  calc
    _ = ∫⁻ p in polarCoord.symm '' polarCoord.target, f p := by
      rw [← setLIntegral_univ, setLIntegral_congr polarCoord_source_ae_eq_univ.symm,
        polarCoord.symm_image_target_eq_source]
    _ = ∫⁻ (p : ℝ × ℝ) in polarCoord.target, ENNReal.ofReal |p.1| • f (polarCoord.symm p) := by
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume _
        (fun p _ ↦ (hasFDerivAt_polarCoord_symm p).hasFDerivWithinAt)]
      · simp_rw [det_fderivPolarCoordSymm]; rfl
      exacts [polarCoord.symm.injOn, measurableSet_Ioi.prod measurableSet_Ioo]
    _ = ∫⁻ (p : ℝ × ℝ) in polarCoord.target, ENNReal.ofReal p.1 • f (polarCoord.symm p) := by
      refine setLIntegral_congr_fun polarCoord.open_target.measurableSet (fun x hx ↦ ?_)
      rw [abs_of_pos hx.1]

end Real

noncomputable section Complex

namespace Complex

open scoped Real ENNReal

/-- The polar coordinates open partial homeomorphism in `ℂ`, mapping `r (cos θ + I * sin θ)` to
`(r, θ)`. It is a homeomorphism between `ℂ - ℝ≤0` and `(0, +∞) × (-π, π)`. -/
/-
**Complex.polarCoord** 是 Mathlib 中的一个定义，位于命名空间 `Complex`。
形式化陈述：OpenPartialHomeomorph ℂ (ℝ × ℝ)
参数：ℝ × ℝ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The polar coordinates open partial homeomorphism in `ℂ`, mapping `r (cos θ + I *
 sin θ)` to
`(r, θ)`. It is a homeomorphism between `ℂ - ℝ≤0` and `(0, +∞) × (-π, π)`.
-/
protected noncomputable def polarCoord : OpenPartialHomeomorph ℂ (ℝ × ℝ) :=
  equivRealProdCLM.toHomeomorph.transOpenPartialHomeomorph polarCoord
/-
**Complex.polarCoord_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (a : ℂ), ↑Complex.polarCoord a = (‖a‖, a.arg)
参数：a : ℂ；‖a‖, a.arg。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.norm_def`：norm_def (z : Complex) : ‖z‖ = √(normSq z)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
protected theorem polarCoord_apply (a : ℂ) :
    Complex.polarCoord a = (‖a‖, Complex.arg a) := by
  simp_rw [Complex.norm_def, Complex.normSq_apply, ← pow_two]
  rfl
/-
**Complex.polarCoord_source** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.polarCoord.source = Complex.slitPlane
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem polarCoord_source : Complex.polarCoord.source = slitPlane := rfl
/-
**Complex.polarCoord_target** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：Complex.polarCoord.target = Set.Ioi 0 ×ˢ Set.Ioo (-Real.pi) Real.pi
参数：-Real.pi。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem polarCoord_target :
    Complex.polarCoord.target = Set.Ioi (0 : ℝ) ×ˢ Set.Ioo (-π) π := rfl

@[simp]
/-
**Complex.polarCoord_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (p : ℝ × ℝ), ↑Complex.polarCoord.symm p = ↑p.1 * (↑(Real.cos p.2) + ↑(Re
al.sin p.2) * Complex.I)
参数：p : ℝ × ℝ；↑(Real.cos p.2) + ↑(Real.sin p.2) * Complex.I。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Homeomorph.transOpenPartialHomeomorph_symm_apply`：∀ {X : Type u_1} {Y : 
Type u_3} {Z : Type u_5} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace 
Y]   [inst_2 : TopologicalSpace Z] (e …
· 使用定理 `polarCoord_symm_apply`：∀ (p : ℝ × ℝ), ↑polarCoord.symm p = (p.1 * Real.c
os p.2, p.1 * Real.sin p.2)
· 使用定理 `Complex.equivRealProdCLM_symm_apply`：∀ (p : ℝ × ℝ), Complex.equivRealPro
dCLM.symm p = ↑p.1 + ↑p.2 * Complex.I
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem polarCoord_symm_apply (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by
  simp [Complex.polarCoord, equivRealProdCLM_symm_apply, mul_add, mul_assoc]
/-
**Complex.measurableEquivRealProd_symm_polarCoord_symm_apply** 是 Mathlib 中的一个定理，
位于命名空间 `Complex`。
形式化陈述：measurableEquivRealProd_symm_polarCoord_symm_apply (p : Real × Real) : (me
asurableEquivRealProd.symm (polarCoord.symm p)) = Complex.polarCoord.symm p
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem measurableEquivRealProd_symm_polarCoord_symm_apply (p : ℝ × ℝ) :
    (measurableEquivRealProd.symm (polarCoord.symm p)) = Complex.polarCoord.symm p := rfl
/-
**Complex.norm_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：norm_polarCoord_symm (p : Real × Real) : ‖Complex.polarCoord.symm p‖ = |p.
1|
参数：p : Real × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.polarCoord_symm_apply`：∀ (p : ℝ × ℝ), ↑Complex.polarCoord.symm p
 = ↑p.1 * (↑(Real.cos p.2) + ↑(Real.sin p.2) * Complex.I)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.norm_mul`：∀ (z w : ℂ), ‖z * w‖ = ‖z‖ * ‖w‖
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Complex.norm_cos_add_sin_mul_I`：norm_cos_add_sin_mul_I (x : Real) : ‖cos
 x + sin x * I‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem norm_polarCoord_symm (p : ℝ × ℝ) :
    ‖Complex.polarCoord.symm p‖ = |p.1| := by simp
/-
**Complex.integral_comp_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℝ E] 
(f : ℂ → E),   ∫ (p : ℝ × ℝ) in polarCoord.target, p.1 • f (↑Complex.polarCoord.
symm p) = ∫ (p : ℂ), f p
参数：f : ℂ → E；p : ℝ × ℝ；↑Complex.polarCoord.symm p；p : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Complex.volume_preserving_equiv_real_prod`：volume_preserving_equiv_real_
prod : MeasurePreserving measurableEquivRealProd
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `integral_comp_polarCoord_symm`：integral_comp_polarCoord_symm {E : Type*}
 [NormedAddCommGroup E] [NormedSpace Real E] (f : Real × Real -> E) : (∫ p in po
larCoord.target, p.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem integral_comp_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) :
    (∫ p in polarCoord.target, p.1 • f (Complex.polarCoord.symm p)) = ∫ p, f p := by
  rw [← (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
    measurableEquivRealProd.symm.measurableEmbedding, ← integral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]
/-
**Complex.lintegral_comp_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ (f : ℂ → ENNReal),   ∫⁻ (p : ℝ × ℝ) in polarCoord.target, ENNReal.ofReal
 p.1 • f (↑Complex.polarCoord.symm p) = ∫⁻ (p : ℂ), f p
参数：f : ℂ → ENNReal；p : ℝ × ℝ；↑Complex.polarCoord.symm p；p : ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_comp_emb`：lintegral_comp_emb (
hge : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b 
∂ν
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Complex.volume_preserving_equiv_real_prod`：volume_preserving_equiv_real_
prod : MeasurePreserving measurableEquivRealProd
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `lintegral_comp_polarCoord_symm`：lintegral_comp_polarCoord_symm (f : Real
 × Real -> Real>=0∞) : ∫⁻ (p : Real × Real) in polarCoord.target, ENNReal.ofReal
 p.1 • f (polarCoord…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem lintegral_comp_polarCoord_symm (f : ℂ → ℝ≥0∞) :
    (∫⁻ p in polarCoord.target, ENNReal.ofReal p.1 • f (Complex.polarCoord.symm p)) =
      ∫⁻ p, f p := by
  rw [← (volume_preserving_equiv_real_prod.symm).lintegral_comp_emb
    measurableEquivRealProd.symm.measurableEmbedding, ← lintegral_comp_polarCoord_symm]
  simp_rw [measurableEquivRealProd_symm_polarCoord_symm_apply]

end Complex

section Pi

open ENNReal MeasureTheory MeasureTheory.Measure

variable {ι : Type*}

open ContinuousLinearMap in
/-- The derivative of `polarCoord.symm` on `ι → ℝ × ℝ`, see `hasFDerivAt_pi_polarCoord_symm`. -/
/-
**fderivPiPolarCoordSymm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fderivPiPolarCoordSymm (p : ι -> Real × Real) : (ι -> Real × Real) ->L[Rea
l] ι -> Real × Real
参数：p : ι -> Real × Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The derivative of `polarCoord.symm` on `ι → ℝ × ℝ`, see `hasFDerivAt_pi_polarCoo
rd_symm`.
-/
noncomputable def fderivPiPolarCoordSymm (p : ι → ℝ × ℝ) : (ι → ℝ × ℝ) →L[ℝ] ι → ℝ × ℝ :=
  pi fun i ↦ (fderivPolarCoordSymm (p i)).comp (proj i)
/-
**injOn_pi_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injOn_pi_polarCoord_symm : Set.InjOn (fun p (i : ι) => polarCoord.symm (p 
i)) (Set.univ.pi fun _ => polarCoord.target)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `OpenPartialHomeomorph.injOn`：∀ {X : Type u_1} {Y : Type u_3} [inst : Top
ologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph X Y)
, Set.InjOn (↑e) …
· 使用定理 `trivial`：True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `funext_iff`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g
 ↔ ∀ (x : α), f x = g x
-/
theorem injOn_pi_polarCoord_symm :
    Set.InjOn (fun p (i : ι) ↦ polarCoord.symm (p i)) (Set.univ.pi fun _ ↦ polarCoord.target) :=
  fun _ hx _ hy h ↦ funext fun i ↦ polarCoord.symm.injOn (hx i trivial) (hy i trivial)
    ((funext_iff.mp h) i)
/-
**abs_fst_of_mem_pi_polarCoord_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：abs_fst_of_mem_pi_polarCoord_target {p : ι -> Real × Real} (hp : p in (Set
.univ.pi fun _ : ι => polarCoord.target)) (i : ι) : |(p i).1| = (p i).1
参数：hp : p in (Set.univ.pi fun _ : ι => polarCoord.target)；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_univ_pi`：mem_univ_pi : f in pi univ t ↔ forall i, f i in t i
-/
theorem abs_fst_of_mem_pi_polarCoord_target {p : ι → ℝ × ℝ}
    (hp : p ∈ (Set.univ.pi fun _ : ι ↦ polarCoord.target)) (i : ι) :
    |(p i).1| = (p i).1 :=
  abs_of_pos ((Set.mem_univ_pi.mp hp) i).1
/-
**hasFDerivAt_pi_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasFDerivAt_pi_polarCoord_symm [Finite ι] (p : ι -> Real × Real) : HasFDer
ivAt (fun x i => polarCoord.symm (x i)) (fderivPiPolarCoordSymm p) p
参数：p : ι -> Real × Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fderivPiPolarCoordSymm.eq_1`：∀ {ι : Type u_1} (p : ι → ℝ × ℝ),   fderivP
iPolarCoordSymm p = ContinuousLinearMap.pi fun i => fderivPolarCoordSymm (p i) ∘
SL ContinuousLine…
· 使用定理 `hasFDerivAt_pi`：hasFDerivAt_pi : HasFDerivAt (fun x i => φ i x) (Continu
ousLinearMap.pi φ') x ↔ forall i, HasFDerivAt (φ i) (φ' i) x
· 使用定理 `HasFDerivAt.comp`：HasFDerivAt.comp {g : F -> G} {g' : F ->L[𝕜] G} (hg : 
HasFDerivAt g g' (f x)) (hf : HasFDerivAt f f' x) : HasFDerivAt (g ∘ f) (g'.comp
 f') x
· 使用定理 `hasFDerivAt_polarCoord_symm`：hasFDerivAt_polarCoord_symm (p : Real × Rea
l) : HasFDerivAt polarCoord.symm (fderivPolarCoordSymm p) p
· 使用定理 `hasFDerivAt_apply`：hasFDerivAt_apply (i : ι) (f : forall i, F' i) : HasF
DerivAt (𝕜
-/
theorem hasFDerivAt_pi_polarCoord_symm [Finite ι] (p : ι → ℝ × ℝ) :
    HasFDerivAt (fun x i ↦ polarCoord.symm (x i)) (fderivPiPolarCoordSymm p) p := by
  have := Fintype.ofFinite ι
  rw [fderivPiPolarCoordSymm, hasFDerivAt_pi]
  exact fun i ↦ HasFDerivAt.comp _ (hasFDerivAt_polarCoord_symm _) (hasFDerivAt_apply i _)
/-
**measurableSet_pi_polarCoord_target** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：measurableSet_pi_polarCoord_target [Finite ι] : MeasurableSet (Set.univ.pi
 fun _ : ι => polarCoord.target)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasurableSet.univ_pi`：∀ {δ : Type u_4} {X : δ → Type u_6} [inst : (a : 
δ) → MeasurableSpace (X a)] [Countable δ] {t : (i : δ) → Set (X i)},   (∀ (i : δ
), Measurab…
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `OpenPartialHomeomorph.open_target`：∀ {X : Type u_7} {Y : Type u_8} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (self : OpenPartialHomeom
orph X Y), IsOpen self.…
-/
theorem measurableSet_pi_polarCoord_target [Finite ι] :
    MeasurableSet (Set.univ.pi fun _ : ι ↦ polarCoord.target) :=
  MeasurableSet.univ_pi fun _ ↦ polarCoord.open_target.measurableSet

variable [Fintype ι]
/-
**det_fderivPiPolarCoordSymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：det_fderivPiPolarCoordSymm (p : ι -> Real × Real) : (fderivPiPolarCoordSym
m p).det = ∏ i, (p i).1
参数：p : ι -> Real × Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.det_pi`：det_pi {ι R M : Type*} [Fintype ι] [CommRing
 R] [AddCommGroup M] [TopologicalSpace M] [Module R M] [Module.Free R M] [Module
.Finite R M] (f …
· 使用定理 `Module.Free.prod`：∀ (R : Type u_7) (M : Type u_8) (N : Type u_9) [inst :
 Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 :
 AddCo…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `det_fderivPolarCoordSymm`：det_fderivPolarCoordSymm (p : Real × Real) : (
fderivPolarCoordSymm p).det = p.1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_fderivPiPolarCoordSymm (p : ι → ℝ × ℝ) :
    (fderivPiPolarCoordSymm p).det = ∏ i, (p i).1 := by
  simp_rw [fderivPiPolarCoordSymm, ContinuousLinearMap.det_pi, det_fderivPolarCoordSymm]
/-
**pi_polarCoord_symm_target_ae_eq_univ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pi_polarCoord_symm_target_ae_eq_univ : (Pi.map (fun _ : ι => polarCoord.sy
mm) '' Set.univ.pi fun _ => polarCoord.target) =ᵐ[volume] Set.univ
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.piMap_image_univ_pi`：piMap_image_univ_pi (f : forall i, α i -> β i) 
(t : forall i, Set (α i)) : Pi.map f '' univ.pi t = univ.pi fun i => f i '' t i
· 使用定理 `OpenPartialHomeomorph.symm_image_target_eq_source`：symm_image_target_eq_
source : e.symm '' e.target = e.source
· 使用定理 `MeasureTheory.volume_pi`：volume_pi [forall i, MeasureSpace (α i)] : (vol
ume : Measure (forall i, α i)) = Measure.pi fun _ => volume
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.pi_univ`：pi_univ (s : Set ι) : (pi s fun i => (univ : Set (α i))) = 
univ
· 使用定理 `MeasureTheory.Measure.ae_eq_set_pi`：ae_eq_set_pi {I : Set ι} {s t : fora
ll i, Set (α i)} (h : forall i in I, s i =ᵐ[μ i] t i) : Set.pi I s =ᵐ[Measure.pi
 μ] Set.pi I t
· 使用定理 `MeasureTheory.Measure.instSigmaFiniteProdVolume`：∀ {α : Type u_4} {β : T
ype u_5} [inst : MeasureTheory.MeasureSpace α] [MeasureTheory.SigmaFinite Measur
eTheory.volume]   [inst_2 : MeasureTh…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `polarCoord_source_ae_eq_univ`：polarCoord_source_ae_eq_univ : polarCoord.
source =ᵐ[volume] univ
-/
theorem pi_polarCoord_symm_target_ae_eq_univ :
    (Pi.map (fun _ : ι ↦ polarCoord.symm) '' Set.univ.pi fun _ ↦ polarCoord.target)
        =ᵐ[volume] Set.univ := by
  rw [Set.piMap_image_univ_pi, polarCoord.symm_image_target_eq_source, volume_pi, ← Set.pi_univ]
  exact ae_eq_set_pi fun _ _ ↦ polarCoord_source_ae_eq_univ
/-
**integral_comp_pi_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_comp_pi_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [Norme
dSpace Real E] (f : (ι -> Real × Real) -> E) : (∫ p in (Set.univ.pi fun _ : ι =>
 polarCoord.target), (∏ i, (p i).1) • f (fun i => polarCoord.symm (p i))) = ∫ p,
 f p
参数：f : (ι -> Real × Real) -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_set`：setIntegral_congr_set (hst : s =ᵐ[μ
] t) : ∫ x in s, f x ∂μ = ∫ x in t, f x ∂μ
· 使用定理 `pi_polarCoord_symm_target_ae_eq_univ`：pi_polarCoord_symm_target_ae_eq_un
iv : (Pi.map (fun _ : ι => polarCoord.symm) '' Set.univ.pi fun _ => polarCoord.t
arget) =ᵐ[volume] Set.univ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_pi_polarCoord_target`：measurableSet_pi_polarCoord_target [
Finite ι] : MeasurableSet (Set.univ.pi fun _ : ι => polarCoord.target)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `det_fderivPiPolarCoordSymm`：det_fderivPiPolarCoordSymm (p : ι -> Real × 
Real) : (fderivPiPolarCoordSymm p).det = ∏ i, (p i).1
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `abs_fst_of_mem_pi_polarCoord_target`：abs_fst_of_mem_pi_polarCoord_target
 {p : ι -> Real × Real} (hp : p in (Set.univ.pi fun _ : ι => polarCoord.target))
 (i : ι) : |(p i).1| = (p…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul`：integral_i
mage_eq_integral_abs_det_fderiv_smul (hs : MeasurableSet s) (hf' : forall x in s
, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s)…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
· 使用定理 `ContinuousAdd.measurableAdd`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Add γ]   [SeparatelyCont
inuousAdd γ], Mea…
· 使用定理 `Prod.separatelyContinuousAdd`：∀ {M : Type u_6} {N : Type u_7} [inst : To
pologicalSpace M] [inst_1 : Add M] [SeparatelyContinuousAdd M]   [inst_3 : Topol
ogicalSpace N] [in…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
（共 46 条，此处仅展示前 30 条）
-/
theorem integral_comp_pi_polarCoord_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ × ℝ) → E) :
    (∫ p in (Set.univ.pi fun _ : ι ↦ polarCoord.target),
      (∏ i, (p i).1) • f (fun i ↦ polarCoord.symm (p i))) = ∫ p, f p := by
  rw [← setIntegral_univ (f := f), ← setIntegral_congr_set pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (integral_image_eq_integral_abs_det_fderiv_smul volume measurableSet_pi_polarCoord_target
        (fun p _ ↦ (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setIntegral_congr_fun measurableSet_pi_polarCoord_target fun x hx ↦ ?_
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, abs_fst_of_mem_pi_polarCoord_target hx]
/-
**Complex.integral_comp_pi_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] {E : Type u_2} [inst_1 : NormedAddComm
Group E] [inst_2 : NormedSpace ℝ E]   (f : (ι → ℂ) → E),   (∫ (p : ι → ℝ × ℝ) in
 Set.univ.pi fun x => Complex.polarCoord.target,       (∏ i, (p i).1) • f fun i 
=> ↑Complex.polarCoord.symm (p i)) =     ∫ (p : ι → ℂ), f p
参数：f : (ι → ℂ) → E；∫ (p : ι → ℝ × ℝ) in Set.univ.pi fun x => Complex.polarCoord.
target,       (∏ i, (p i).1) • f fun i => ↑Complex.polarCoord.symm (p i)；p : ι →
 ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.volume_preserving_pi`：volume_preserving_pi {α' β' : ι -> T
ype*} [forall i, MeasureSpace (α' i)] [forall i, MeasureSpace (β' i)] [forall i,
 SigmaFinite (volume : M…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Complex.volume_preserving_equiv_real_prod`：volume_preserving_equiv_real_
prod : MeasurePreserving measurableEquivRealProd
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.integral_comp`：∀ {α : Type u_1} {G : Typ
e u_5} [inst : NormedAddCommGroup G] [inst_1 : NormedSpace ℝ G] {m : MeasurableS
pace α}   {μ : MeasureTheory.Measur…
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `integral_comp_pi_polarCoord_symm`：integral_comp_pi_polarCoord_symm {E : 
Type*} [NormedAddCommGroup E] [NormedSpace Real E] (f : (ι -> Real × Real) -> E)
 : (∫ p in (Set.univ.p…
-/
protected theorem Complex.integral_comp_pi_polarCoord_symm {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : (ι → ℂ) → E) :
    (∫ p in (Set.univ.pi fun _ : ι ↦ Complex.polarCoord.target),
      (∏ i, (p i).1) • f (fun i ↦ Complex.polarCoord.symm (p i))) = ∫ p, f p := by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι ↦ measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι ↦ Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.integral_comp this e.measurableEmbedding f]
  exact integral_comp_pi_polarCoord_symm (f ∘ e)
/-
**lintegral_comp_pi_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lintegral_comp_pi_polarCoord_symm (f : (ι -> Real × Real) -> Real>=0∞) : ∫
⁻ p in (Set.univ.pi fun _ : ι => polarCoord.target), (∏ i, .ofReal (p i).1) * f 
(fun i => polarCoord.symm (p i)) = ∫⁻ p, f p
参数：f : (ι -> Real × Real) -> Real>=0∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setLIntegral_univ`：setLIntegral_univ (f : α -> Real>=0∞) :
 ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ
· 使用定理 `MeasureTheory.setLIntegral_congr`：setLIntegral_congr {f : α -> Real>=0∞}
 {s t : Set α} (h : s =ᵐ[μ] t) : ∫⁻ x in s, f x ∂μ = ∫⁻ x in t, f x ∂μ
· 使用定理 `pi_polarCoord_symm_target_ae_eq_univ`：pi_polarCoord_symm_target_ae_eq_un
iv : (Pi.map (fun _ : ι => polarCoord.symm) '' Set.univ.pi fun _ => polarCoord.t
arget) =ᵐ[volume] Set.univ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.setLIntegral_congr_fun`：setLIntegral_congr_fun {f g : α ->
 Real>=0∞} {s : Set α} (hs : MeasurableSet s) (hfg : EqOn f g s) : ∫⁻ x in s, f 
x ∂μ = ∫⁻ x in s, g x ∂μ
· 使用定理 `measurableSet_pi_polarCoord_target`：measurableSet_pi_polarCoord_target [
Finite ι] : MeasurableSet (Set.univ.pi fun _ : ι => polarCoord.target)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `det_fderivPiPolarCoordSymm`：det_fderivPiPolarCoordSymm (p : ι -> Real × 
Real) : (fderivPiPolarCoordSymm p).det = ∏ i, (p i).1
· 使用引理 `Finset.abs_prod`：abs_prod [CommRing R] [LinearOrder R] [IsStrictOrderedR
ing R] (s : Finset ι) (f : ι -> R) : |∏ x in s, f x| = ∏ x in s, |f x|
· 使用定理 `ENNReal.ofReal_prod_of_nonneg`：ofReal_prod_of_nonneg {α : Type*} {s : Fi
nset α} {f : α -> Real} (hf : forall i, i in s -> 0 <= f i) : ENNReal.ofReal (∏ 
i in s, f i) = ∏ i …
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `abs_fst_of_mem_pi_polarCoord_target`：abs_fst_of_mem_pi_polarCoord_target
 {p : ι -> Real × Real} (hp : p in (Set.univ.pi fun _ : ι => polarCoord.target))
 (i : ι) : |(p i).1| = (p…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.lintegral_image_eq_lintegral_abs_det_fderiv_mul`：lintegral
_image_eq_lintegral_abs_det_fderiv_mul (hs : MeasurableSet s) (hf' : forall x in
 s, HasFDerivWithinAt f (f' x) s x) (hf : InjOn f s…
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyProd`：∀ {α : Type u} [t : To
pologicalSpace α] {β : Type u_1} [inst : TopologicalSpace β] [SecondCountableTop
ology α]   [SecondCountableTopology β]…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `MeasureTheory.Measure.instIsAddHaarMeasureForallVolumeOfMeasurableAddOfS
igmaFinite`：∀ {ι : Type u_1} [inst : Fintype ι] {G : ι → Type u_4} [inst_1 : (i 
: ι) → AddGroup (G i)]   [inst_2 : (i : ι) → MeasureTheory.MeasureSpace …
（共 50 条，此处仅展示前 30 条）
-/
theorem lintegral_comp_pi_polarCoord_symm (f : (ι → ℝ × ℝ) → ℝ≥0∞) :
    ∫⁻ p in (Set.univ.pi fun _ : ι ↦ polarCoord.target),
      (∏ i, .ofReal (p i).1) * f (fun i ↦ polarCoord.symm (p i)) = ∫⁻ p, f p := by
  rw [← setLIntegral_univ f, ← setLIntegral_congr pi_polarCoord_symm_target_ae_eq_univ]
  convert!
    (lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_pi_polarCoord_target
        (fun p _ ↦ (hasFDerivAt_pi_polarCoord_symm p).hasFDerivWithinAt) injOn_pi_polarCoord_symm
        f).symm using 1
  refine setLIntegral_congr_fun measurableSet_pi_polarCoord_target (fun x hx ↦ ?_)
  simp_rw [det_fderivPiPolarCoordSymm, Finset.abs_prod, ENNReal.ofReal_prod_of_nonneg (fun _ _ ↦
    abs_nonneg _), abs_fst_of_mem_pi_polarCoord_target hx]
/-
**Complex.lintegral_comp_pi_polarCoord_symm** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：∀ {ι : Type u_1} [inst : Fintype ι] (f : (ι → ℂ) → ENNReal),   (∫⁻ (p : ι 
→ ℝ × ℝ) in Set.univ.pi fun x => Complex.polarCoord.target,       (∏ i, ENNReal.
ofReal (p i).1) * f fun i => ↑Complex.polarCoord.symm (p i)) =     ∫⁻ (p : ι → ℂ
), f p
参数：f : (ι → ℂ) → ENNReal；∫⁻ (p : ι → ℝ × ℝ) in Set.univ.pi fun x => Complex.pola
rCoord.target,       (∏ i, ENNReal.ofReal (p i).1) * f fun i => ↑Complex.polarCo
ord.symm (p i)；p : ι → ℂ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.volume_preserving_pi`：volume_preserving_pi {α' β' : ι -> T
ype*} [forall i, MeasureSpace (α' i)] [forall i, MeasureSpace (β' i)] [forall i,
 SigmaFinite (volume : M…
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `MeasureTheory.MeasurePreserving.symm`：symm (e : α ≃ᵐ β) {μa : Measure α}
 {μb : Measure β} (h : MeasurePreserving e μa μb) : MeasurePreserving e.symm μb 
μa
· 使用定理 `Complex.volume_preserving_equiv_real_prod`：volume_preserving_equiv_real_
prod : MeasurePreserving measurableEquivRealProd
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.MeasurePreserving.lintegral_comp_emb`：lintegral_comp_emb (
hge : MeasurableEmbedding g) (f : β -> Real>=0∞) : ∫⁻ a, f (g a) ∂μ = ∫⁻ b, f b 
∂ν
· 使用定理 `MeasurableEquiv.measurableEmbedding`：∀ {α : Type u_1} {β : Type u_2} [in
st : MeasurableSpace α] [inst_1 : MeasurableSpace β] (e : α ≃ᵐ β),   MeasurableE
mbedding ⇑e
· 使用定理 `lintegral_comp_pi_polarCoord_symm`：lintegral_comp_pi_polarCoord_symm (f 
: (ι -> Real × Real) -> Real>=0∞) : ∫⁻ p in (Set.univ.pi fun _ : ι => polarCoord
.target), (∏ i, .ofReal…
-/
protected theorem Complex.lintegral_comp_pi_polarCoord_symm (f : (ι → ℂ) → ℝ≥0∞) :
    ∫⁻ p in (Set.univ.pi fun _ : ι ↦ Complex.polarCoord.target),
      (∏ i, .ofReal (p i).1) * f (fun i ↦ Complex.polarCoord.symm (p i)) = ∫⁻ p, f p := by
  let e := MeasurableEquiv.piCongrRight (fun _ : ι ↦ measurableEquivRealProd.symm)
  have := volume_preserving_pi (fun _ : ι ↦ Complex.volume_preserving_equiv_real_prod.symm)
  rw [← MeasurePreserving.lintegral_comp_emb this e.measurableEmbedding]
  exact lintegral_comp_pi_polarCoord_symm (f ∘ e)

end Pi

