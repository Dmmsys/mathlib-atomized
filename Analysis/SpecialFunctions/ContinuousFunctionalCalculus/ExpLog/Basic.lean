/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity

/-!
# The exponential and logarithm based on the continuous functional calculus

This file defines the logarithm via the continuous functional calculus (CFC) and builds its API.
This allows one to take logs of matrices, operators, elements of a C⋆-algebra, etc.

It also shows that exponentials defined via the continuous functional calculus are equal to
`NormedSpace.exp` (defined via power series) whenever the former are not junk values.

## Main declarations

+ `CFC.log`: the real log function based on the CFC, i.e. `cfc Real.log`
+ `CFC.exp_eq_normedSpace_exp`: exponentials based on the CFC are equal to exponentials based
  on power series.
+ `CFC.log_exp` and `CFC.exp_log`: `CFC.log` and `NormedSpace.exp ℝ` are inverses of each other.

## Implementation notes

Since `cfc Real.exp` and `cfc Complex.exp` are strictly less general than `NormedSpace.exp`
(defined via power series), we only give minimal API for these here in order to relate
`NormedSpace.exp` to functions defined via the CFC. In particular, we don't give separate
definitions for them.

## TODO

+ Show that `log (a * b) = log a + log b` whenever `a` and `b` commute (and the same for indexed
  products).
+ Relate `CFC.log` to `rpow`, `zpow`, `sqrt`, `inv`.
-/

@[expose] public section

open NormedSpace

section general_exponential
variable {𝕜 : Type*} {α : Type*} [RCLike 𝕜] [TopologicalSpace α] [CompactSpace α]

/-
**NormedSpace.exp_continuousMap_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NormedSpace.exp_continuousMap_eq (f : C(α, 𝕜)) : exp f = (⟨exp ∘ f, exp_co
ntinuous.comp f.continuous⟩ : C(α, 𝕜))
参数：f : C(α, 𝕜)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `NormedSpace.exp_continuous`：exp_continuous : Continuous (exp : 𝔸 -> 𝔸)
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `ContinuousMap.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] (f : C(X, Y)), Continuous ⇑f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `SMulCommClass.continuousConstSMul`：∀ {R : Type u_6} {A : Type u_7} [inst
 : Monoid A] [inst_1 : SMul R A] [SMulCommClass R A A]   [inst_3 : TopologicalSp
ace A] [SeparatelyConti…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `NormedSpace.exp_eq_expSeries_sum`：exp_eq_expSeries_sum [CharZero 𝕂] : ex
p = (expSeries 𝕂 𝔸).sum
· 使用定理 `NormedSpace.expSeries_summable`：expSeries_summable (x : 𝔸) : Summable fu
n n => expSeries 𝕂 𝔸 n fun _ => x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `instWeaklyLocallyCompactSpaceOfCompactSpace`：∀ {X : Type u_1} [inst : To
pologicalSpace X] [CompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `ContinuousMap.tsum_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] [T2Space β]   [inst_3 : AddCommMonoi
d β] [inst_4 :…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
（共 36 条，此处仅展示前 30 条）
-/
lemma NormedSpace.exp_continuousMap_eq (f : C(α, 𝕜)) :
    exp f = (⟨exp ∘ f, exp_continuous.comp f.continuous⟩ : C(α, 𝕜)) := by
  ext a
  simp_rw [NormedSpace.exp_eq_expSeries_sum (𝔸 := C(α, 𝕜)) 𝕜, FormalMultilinearSeries.sum]
  have h_sum := NormedSpace.expSeries_summable (𝕂 := 𝕜) f
  simp_rw [← ContinuousMap.tsum_apply h_sum a, NormedSpace.expSeries_apply_eq]
  simp [NormedSpace.exp_eq_tsum 𝕜]

end general_exponential

namespace CFC
section RCLikeNormed

variable {𝕜 : Type*} {A : Type*} [RCLike 𝕜] {p : A → Prop} [NormedRing A]
  [StarRing A] [NormedAlgebra 𝕜 A] [ContinuousFunctionalCalculus 𝕜 A p]

open scoped ContinuousFunctionalCalculus in
/-
**CFC.exp_eq_normedSpace_exp** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：exp_eq_normedSpace_exp {a : A} (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用引理 `cfcHom_continuous`：cfcHom_continuous : Continuous (cfcHom ha : C(spectru
m R a, R) ->⋆ₐ[R] A)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `NormedSpace.exp_continuous`：exp_continuous : Continuous (exp : 𝔸 -> 𝔸)
· 使用定理 `RCLike.charZero_rclike`：∀ {K : Type u_1} [inst : RCLike K], CharZero K
· 使用定理 `RCLike.toCompleteSpace`：∀ {K : semiOutParam (Type u_1)} [self : RCLike K
], CompleteSpace K
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `NormedSpace.map_exp`：map_exp [Algebra Rat 𝔹] {F} [FunLike F 𝔸 𝔹] [RingHo
mClass F 𝔸 𝔹] (f : F) (hf : Continuous f) (x : 𝔸) : f (exp x) = exp (f x)
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 34 条，此处仅展示前 30 条）
-/
lemma exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc (exp : 𝕜 → 𝕜) a = exp a := by
  conv_rhs => rw [← cfc_id 𝕜 a ha, cfc_apply id a ha]
  have h := cfcHom_continuous (R := 𝕜) ha
  have _ : ContinuousOn exp (spectrum 𝕜 a) := exp_continuous.continuousOn
  let +nondep : Algebra ℚ A := .restrictScalars ℚ 𝕜 A
  simp_rw [← map_exp _ h, cfc_apply exp a ha]
  congr 1
  ext
  simp [exp_continuousMap_eq]

end RCLikeNormed

section RealNormed

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-
**CFC.real_exp_eq_normedSpace_exp** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：real_exp_eq_normedSpace_exp {a : A} (ha : IsSelfAdjoint a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用引理 `CFC.exp_eq_normedSpace_exp`：exp_eq_normedSpace_exp {a : A} (ha : p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.exp_eq_exp_ℝ`：Real.exp = NormedSpace.exp
-/
lemma real_exp_eq_normedSpace_exp {a : A} (ha : IsSelfAdjoint a := by cfc_tac) :
    cfc Real.exp a = exp a :=
  Real.exp_eq_exp_ℝ ▸ exp_eq_normedSpace_exp ha

@[aesop safe apply (rule_sets := [CStarAlgebra])]
/-
**CFC._root_.IsSelfAdjoint.exp_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsSelfAdjoint.exp_nonneg
    [PartialOrder A] [StarOrderedRing A] {a : A} (ha : IsSelfAdjoint a) :
    0 ≤ exp a := by
  rw [← real_exp_eq_normedSpace_exp]
  exact cfc_nonneg fun x _ => Real.exp_nonneg x

end RealNormed

section ComplexNormed

variable {A : Type*} {p : A → Prop} [NormedRing A] [StarRing A]
  [NormedAlgebra ℂ A] [ContinuousFunctionalCalculus ℂ A p]

/-
**CFC.complex_exp_eq_normedSpace_exp** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：complex_exp_eq_normedSpace_exp {a : A} (ha : p a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用引理 `CFC.exp_eq_normedSpace_exp`：exp_eq_normedSpace_exp {a : A} (ha : p a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.exp_eq_exp_ℂ`：Complex.exp = NormedSpace.exp
-/
lemma complex_exp_eq_normedSpace_exp {a : A} (ha : p a := by cfc_tac) :
    cfc Complex.exp a = exp a :=
  Complex.exp_eq_exp_ℂ ▸ exp_eq_normedSpace_exp ha

end ComplexNormed


section real_log

open scoped ComplexOrder

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [ContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- The real logarithm, defined via the continuous functional calculus. This can be used on
matrices, operators on a Hilbert space, elements of a C⋆-algebra, etc. -/
/-
**CFC.log** 是 Mathlib 中的一个定义，位于命名空间 `CFC`。
形式化陈述：log (a : A) : A
参数：a : A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ

--- 原说明 ---
The real logarithm, defined via the continuous functional calculus. This can be 
used on
matrices, operators on a Hilbert space, elements of a C⋆-algebra, etc.
-/
noncomputable def log (a : A) : A := cfc Real.log a

@[simp, grind =>]
/-
**CFC._root_.IsSelfAdjoint.log** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected lemma _root_.IsSelfAdjoint.log {a : A} : IsSelfAdjoint (log a) := cfc_predicate _ a
/-
**CFC.log_zero** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : StarRing A] [inst_2 : Nor
medAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint], CFC
.log 0 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_apply_zero`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : C
ommSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopo
logi…
· 使用定理 `Real.log_zero`：log_zero : log 0 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, grind =] lemma log_zero : log (0 : A) = 0 := by simp [log]
/-
**CFC.log_one** 是 Mathlib 中的一个定理，位于命名空间 `CFC`。
形式化陈述：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : StarRing A] [inst_2 : Nor
medAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ A IsSelfAdjoint], CFC
.log 1 = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `cfc_apply_one`：∀ {R : Type u_1} {A : Type u_2} {p : A → Prop} [inst : Co
mmSemiring R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : IsTopol
ogi…
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, grind =] lemma log_one : log (1 : A) = 0 := by simp [log]

@[simp, grind =]
/-
**CFC.log_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：log_algebraMap {r : Real} : log (algebraMap Real A r) = algebraMap Real A 
(Real.log r)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_algebraMap`：cfc_algebraMap (r : R) (f : R -> R) : cfc f (algebraMap 
R A r) = algebraMap R A (f r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma log_algebraMap {r : ℝ} : log (algebraMap ℝ A r) = algebraMap ℝ A (Real.log r) := by
  simp [log]
/-
**CFC.log_smul** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：log_smul {r : Real} (a : A) (ha₂ : forall x in spectrum Real a, x != 0) (h
r : r != 0) (ha₁ : IsSelfAdjoint a
参数：a : A；ha₂ : forall x in spectrum Real a, x != 0；hr : r != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CFC.log.eq_1`：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : StarRing 
A] [inst_2 : NormedAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ A IsS
el…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_smul_id`：cfc_smul_id {S : Type*} [SMul S R] [ContinuousConstSMul S R
] [SMulZeroClass S A] [IsScalarTower S R A] [IsScalarTower S R (R -> R)] (s : S)
 …
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `cfc_comp`：cfc_comp (g f : R -> R) (a : A) (ha : p a
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousOn.log`：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall 
x in s, f x != 0) : ContinuousOn (fun x => log (f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `ContinuousOn.fun_const_smul`：∀ {M : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : SMul M α] [ContinuousConstSMul M α]   
[inst_3 : Topolog…
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用引理 `cfc_const_add`：cfc_const_add (r : R) (f : R -> R) (a : A) (hf : Continuo
usOn f (spectrum R a)
-/
lemma log_smul {r : ℝ} (a : A) (ha₂ : ∀ x ∈ spectrum ℝ a, x ≠ 0) (hr : r ≠ 0)
    (ha₁ : IsSelfAdjoint a := by cfc_tac) :
    log (r • a) = algebraMap ℝ A (Real.log r) + log a := by
  rw [log, ← cfc_smul_id (R := ℝ) r a, ← cfc_comp Real.log (r • ·) a, log]
  calc
    _ = cfc (fun z => Real.log r + Real.log z) a :=
      cfc_congr (Real.log_mul hr <| ha₂ · ·)
    _ = _ := by rw [cfc_const_add _ _ _]

@[grind =]
/-
**CFC.log_smul'** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：log_smul' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A
] {r : Real} (a : A) (hr : 0 < r) (ha : IsStrictlyPositive a
参数：a : A；hr : 0 < r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma log_smul' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] {r : ℝ} (a : A)
    (hr : 0 < r) (ha : IsStrictlyPositive a := by cfc_tac) :
    log (r • a) = algebraMap ℝ A (Real.log r) + log a := by
  grind [log_smul]
/-
**CFC.log_pow** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：log_pow (n : Nat) (a : A) (ha₂ : forall x in spectrum Real a, x != 0) (ha₁
 : IsSelfAdjoint a
参数：n : Nat；a : A；ha₂ : forall x in spectrum Real a, x != 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.log`：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall 
x in s, f x != 0) : ContinuousOn (fun x => log (f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `CFC.log.eq_1`：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : StarRing 
A] [inst_2 : NormedAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ A IsS
el…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_pow_id`：cfc_pow_id (a : A) (n : Nat) (ha : p a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousOn.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] 
{f : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_pow`：log_pow (x : Real) (n : Nat) : log (x ^ n) = n * log x
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `cfc_const_mul`：cfc_const_mul (r : R) (f : R -> R) (a : A) (hf : Continuo
usOn f (spectrum R a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma log_pow (n : ℕ) (a : A) (ha₂ : ∀ x ∈ spectrum ℝ a, x ≠ 0)
    (ha₁ : IsSelfAdjoint a := by cfc_tac) : log (a ^ n) = n • log a := by
  have ha₂' : ContinuousOn Real.log (spectrum ℝ a) := by fun_prop
  have ha₂'' : ContinuousOn Real.log ((· ^ n) '' spectrum ℝ a) := by fun_prop (disch := aesop)
  rw [log, ← cfc_pow_id (R := ℝ) a n ha₁, ← cfc_comp' Real.log (· ^ n) a ha₂'', log]
  simp_rw [Real.log_pow, ← Nat.cast_smul_eq_nsmul ℝ n, cfc_const_mul (n : ℝ) Real.log a ha₂']

@[grind =]
/-
**CFC.log_pow'** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：log_pow' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A]
 (n : Nat) (a : A) (ha : IsStrictlyPositive a
参数：n : Nat；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
-/
lemma log_pow' [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] (n : ℕ) (a : A)
    (ha : IsStrictlyPositive a := by cfc_tac) :
    log (a ^ n) = n • log a := by
  grind [log_pow]

open NormedSpace in
@[grind =]
/-
**CFC.log_exp** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：log_exp (a : A) (ha : IsSelfAdjoint a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.log`：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall 
x in s, f x != 0) : ContinuousOn (fun x => log (f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `CFC.log.eq_1`：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : StarRing 
A] [inst_2 : NormedAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ A IsS
el…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.real_exp_eq_normedSpace_exp`：real_exp_eq_normedSpace_exp {a : A} (ha
 : IsSelfAdjoint a
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousOn.rexp`：ContinuousOn.rexp (h : ContinuousOn f s) : Continuous
On (fun y => exp (f y)) s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_exp`：log_exp (x : Real) : log (exp x) = x
· 使用引理 `cfc_id'`：cfc_id' (ha : p a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma log_exp (a : A) (ha : IsSelfAdjoint a := by cfc_tac) : log (exp a) = a := by
  have hcont : ContinuousOn Real.log (Real.exp '' spectrum ℝ a) := by fun_prop (disch := simp)
  rw [log, ← real_exp_eq_normedSpace_exp, ← cfc_comp' Real.log Real.exp a hcont]
  simp [cfc_id' (R := ℝ) a]

open NormedSpace in
@[grind =]
/-
**CFC.exp_log** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：exp_log [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass Real A] 
(a : A) (ha : IsStrictlyPositive a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CFC.real_exp_eq_normedSpace_exp`：real_exp_eq_normedSpace_exp {a : A} (ha
 : IsSelfAdjoint a
· 使用定理 `IsSelfAdjoint.log`：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : Star
Ring A] [inst_2 : NormedAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ 
A IsSel…
· 使用定理 `CFC.log.eq_1`：∀ {A : Type u_1} [inst : NormedRing A] [inst_1 : StarRing 
A] [inst_2 : NormedAlgebra ℝ A]   [inst_3 : ContinuousFunctionalCalculus ℝ A IsS
el…
· 使用引理 `cfc_comp'`：cfc_comp' (g f : R -> R) (a : A) (hg : ContinuousOn g (f '' s
pectrum R a)
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `ContinuousOn.rexp`：ContinuousOn.rexp (h : ContinuousOn f s) : Continuous
On (fun y => exp (f y)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `ContinuousOn.log`：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall 
x in s, f x != 0) : ContinuousOn (fun x => log (f x)) s
· 使用引理 `IsSelfAdjoint.of_nonneg`：IsSelfAdjoint.of_nonneg {x : R} (hx : 0 <= x) :
 IsSelfAdjoint x
· 使用定理 `IsStrictlyPositive.nonneg`：∀ {A : Type u_1} [inst : LE A] [inst_1 : Mono
id A] [inst_2 : Zero A] {a : A}, IsStrictlyPositive a → 0 ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `cfc_congr`：cfc_congr {f g : R -> R} {a : A} (hfg : (spectrum R a).EqOn f
 g) : cfc f a = cfc g a
-/
lemma exp_log [PartialOrder A] [StarOrderedRing A] [NonnegSpectrumClass ℝ A] (a : A)
    (ha : IsStrictlyPositive a := by cfc_tac) : exp (log a) = a := by
  have ha₂ : ∀ x ∈ spectrum ℝ a, x ≠ 0 := by grind
  rw [← real_exp_eq_normedSpace_exp .log, log, ← cfc_comp' Real.exp Real.log a (by fun_prop)]
  conv_rhs => rw [← cfc_id (R := ℝ) a]
  refine cfc_congr fun x hx => ?_
  grind [Real.exp_log]
/-
**CFC.continuousOn_log** 是 Mathlib 中的一个引理，位于命名空间 `CFC`。
形式化陈述：continuousOn_log {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra Re
al A] [IsometricContinuousFunctionalCalculus Real A IsSelfAdjoint] [ContinuousSt
ar A] [CompleteSpace A] : ContinuousOn log {a : A | IsSelfAdjoint a ∧ IsUnit a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `ContinuousOn.cfc_of_mem_nhdsSet`：ContinuousOn.cfc_of_mem_nhdsSet [Comple
teSpace A] [TopologicalSpace X] {s : Set 𝕜} (f : 𝕜 -> 𝕜) {a : X -> A} {t : Set X
} (hs : s in 𝓝ˢ (⋃ x …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `OrderTopology.t5Space`：∀ {X : Type u_1} [inst : LinearOrder X] [inst_1 :
 TopologicalSpace X] [OrderTopology X], T5Space X
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `spectrum.zero_notMem`：∀ (R : Type u) {A : Type v} [inst : CommSemiring R
] [inst_1 : Ring A] [inst_2 : Algebra R A] {a : A},   IsUnit a → 0 ∉ spectrum R 
a
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `ContinuousOn.log`：ContinuousOn.log (hf : ContinuousOn f s) (h₀ : forall 
x in s, f x != 0) : ContinuousOn (fun x => log (f x)) s
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma continuousOn_log {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
    [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint] [ContinuousStar A] [CompleteSpace A] :
    ContinuousOn log {a : A | IsSelfAdjoint a ∧ IsUnit a} :=
  continuousOn_id.cfc_of_mem_nhdsSet _ (s := {0}ᶜ) <| by
    simpa using fun _ _ ↦ spectrum.zero_notMem ℝ

end real_log
end CFC

