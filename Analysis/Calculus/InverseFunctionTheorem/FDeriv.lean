/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `HasStrictFDerivAt.toOpenPartialHomeomorph` that repacks a function `f`
with a `hf : HasStrictFDerivAt f f' a`, `f' : E ≃L[𝕜] F`, into an `OpenPartialHomeomorph`.
The `toFun` of this `OpenPartialHomeomorph` is defeq to `f`, so one can apply theorems
about `OpenPartialHomeomorph` to `hf.toOpenPartialHomeomorph f`, and get statements about `f`.

Then we define `HasStrictFDerivAt.localInverse` to be the `invFun` of this `OpenPartialHomeomorph`,
and prove two versions of the inverse function theorem:

* `HasStrictFDerivAt.to_localInverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.localInverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `HasStrictFDerivAt.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in the `Analysis/Calculus/FDeriv` and `Analysis/Calculus/Deriv`
folders, and in `ContDiff.lean`.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/

@[expose] public section

open Function Set Filter Metric

open scoped Topology NNReal

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Asymptotics Filter Metric Set

open ContinuousLinearMap (id)


/-!
### Inverse function theorem

Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `ApproximatesLinearOn` on an open neighborhood
of `a`, and we can apply `ApproximatesLinearOn.toOpenPartialHomeomorph` to construct the inverse
function. -/

namespace HasStrictFDerivAt

/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
/-
**HasStrictFDerivAt.approximates_deriv_on_nhds** 是 Mathlib 中的一个定理，位于命名空间 `HasStr
ictFDerivAt`。
形式化陈述：approximates_deriv_on_nhds {f : E -> F} {f' : E ->L[𝕜] F} {a : E} (hf : Ha
sStrictFDerivAt f f' a) {c : Real>=0} (hc : Subsingleton E ∨ 0 < c) : exists s i
n 𝓝 a, ApproximatesLinearOn f f' s c
参数：hf : HasStrictFDerivAt f f' a；hc : Subsingleton E ∨ 0 < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
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
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Asymptotics.IsLittleO.def`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filte
r α}, f =o[l] g…
· 使用定理 `HasStrictFDerivAt.isLittleO`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormed
Field 𝕜] {E : Type u_2} [inst_1 : SeminormedAddCommGroup E]   [inst_2 : NormedSp
ace 𝕜 E] {F : Typ…
· 使用定理 `Filter.mem_prod_same_iff`：∀ {α : Type u_1} {la : Filter α} {s : Set (α ×
 α)}, s ∈ la ×ˢ la ↔ ∃ t ∈ la, t ×ˢ t ⊆ s
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t

--- 原说明 ---
If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` appr
oximates `f'`
with constant `c` on some neighborhood of `a`.
-/
theorem approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f f' a) {c : ℝ≥0} (hc : Subsingleton E ∨ 0 < c) :
    ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c := by
  rcases hc with hE | hc
  · refine ⟨univ, IsOpen.mem_nhds isOpen_univ trivial, fun x _ y _ => ?_⟩
    simp [@Subsingleton.elim E hE x y]
  have := hf.isLittleO.def hc
  rw [nhds_prod_eq, Filter.Eventually, mem_prod_same_iff] at this
  rcases this with ⟨s, has, hs⟩
  exact ⟨s, has, fun x hx y hy => hs (mk_mem_prod hx hy)⟩
/-
**HasStrictFDerivAt.map_nhds_eq_of_surj** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDer
ivAt`。
形式化陈述：map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E -> F} {f' :
 E ->L[𝕜] F} {a : E} (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) (h : f'.rang
e = ⊤) : map f (𝓝 a) = 𝓝 (f a)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a；h : f'.range = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `ContinuousLinearMap.nonlinearRightInverseOfSurjective_nnnorm_pos`：nonlin
earRightInverseOfSurjective_nnnorm_pos (f : E ->SL[σ] F) (hsurj : f.range = ⊤) :
 0 < (nonlinearRightInverseOfSurjective f hsurj).nnnor…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `HasStrictFDerivAt.approximates_deriv_on_nhds`：approximates_deriv_on_nhds
 {f : E -> F} {f' : E ->L[𝕜] F} {a : E} (hf : HasStrictFDerivAt f f' a) {c : Rea
l>=0} (hc : Subsingleton E ∨ 0 < c…
· 使用定理 `ApproximatesLinearOn.map_nhds_eq`：map_nhds_eq (hf : ApproximatesLinearOn
 f f' s c) (f'symm : f'.NonlinearRightInverse) {x : E} (hs : s in 𝓝 x) (hc : Sub
singleton F ∨ c < f'sy…
· 使用定理 `NNReal.half_lt_self`：∀ {a : NNReal}, a ≠ 0 → a / 2 < a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem map_nhds_eq_of_surj [CompleteSpace E] [CompleteSpace F] {f : E → F} {f' : E →L[𝕜] F} {a : E}
    (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) (h : f'.range = ⊤) :
    map f (𝓝 a) = 𝓝 (f a) := by
  let f'symm := f'.nonlinearRightInverseOfSurjective h
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinearRightInverseOfSurjective_nnnorm_pos h
  have cpos : 0 < c := by simp [hc, inv_pos, f'symm_pos]
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, ApproximatesLinearOn f f' s c :=
    hf.approximates_deriv_on_nhds (Or.inr cpos)
  apply hs.map_nhds_eq f'symm s_nhds (Or.inr (NNReal.half_lt_self _))
  simp [ne_of_gt f'symm_pos]

variable {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
/-
**HasStrictFDerivAt.approximates_deriv_on_open_nhds** 是 Mathlib 中的一个定理，位于命名空间 `H
asStrictFDerivAt`。
形式化陈述：approximates_deriv_on_open_nhds (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F
) a) : exists s : Set E, a in s ∧ IsOpen s ∧ ApproximatesLinearOn f (f' : E ->L[
𝕜] F) s (‖(f'.symm : F ->L[𝕜] E)‖₊⁻¹ / 2)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.exists_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {P : Set α → Prop}, (∀ ⦃
s t : Set α⦄, s …
· 使用定理 `nhds_basis_opens`：nhds_basis_opens (x : X) : (𝓝 x).HasBasis (fun s : Set
 X => x in s ∧ IsOpen s) fun s => s
· 使用定理 `ApproximatesLinearOn.mono_set`：mono_set (hst : s subseteq t) (hf : Appro
ximatesLinearOn f f' t c) : ApproximatesLinearOn f f' s c
· 使用定理 `HasStrictFDerivAt.approximates_deriv_on_nhds`：approximates_deriv_on_nhds
 {f : E -> F} {f' : E ->L[𝕜] F} {a : E} (hf : HasStrictFDerivAt f f' a) {c : Rea
l>=0} (hc : Subsingleton E ∨ 0 < c…
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toPosMulStrictMono`：∀ {α : Type u_3} [se
lf : LinearOrderedCommMonoidWithZero α], PosMulStrictMono α
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `inv_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : PartialOr
der G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a⁻¹ ↔ 0 < a
· 使用定理 `ContinuousLinearEquiv.subsingleton_or_nnnorm_symm_pos`：subsingleton_or_n
nnorm_symm_pos [RingHomIsometric σ₁₂] (e : E ≃SL[σ₁₂] F) : Subsingleton E ∨ 0 < 
‖(e.symm : F ->SL[σ₂₁] E)‖₊
-/
theorem approximates_deriv_on_open_nhds (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∃ s : Set E, a ∈ s ∧ IsOpen s ∧
      ApproximatesLinearOn f (f' : E →L[𝕜] F) s (‖(f'.symm : F →L[𝕜] E)‖₊⁻¹ / 2) := by
  simp only [← and_assoc]
  refine ((nhds_basis_opens a).exists_iff fun s t => ApproximatesLinearOn.mono_set).1 ?_
  exact
    hf.approximates_deriv_on_nhds <|
      f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' => half_pos <| inv_pos.2 hf'

variable (f)
variable [CompleteSpace E]

/-- Given a function with an invertible strict derivative at `a`, returns an `OpenPartialHomeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `HasStrictFDerivAt.to_localInverse` states that the inverse function
of this `OpenPartialHomeomorph` has derivative `f'.symm`. -/
/-
**HasStrictFDerivAt.toOpenPartialHomeomorph** 是 Mathlib 中的一个定义，位于命名空间 `HasStrict
FDerivAt`。
形式化陈述：toOpenPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : O
penPartialHomeomorph E F
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.approximates_deriv_on_open_nhds`：approximates_deriv_on
_open_nhds (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : exists s : Set E, a 
in s ∧ IsOpen s ∧ ApproximatesLinearOn …

--- 原说明 ---
Given a function with an invertible strict derivative at `a`, returns an `OpenPa
rtialHomeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theor
em.
The other part `HasStrictFDerivAt.to_localInverse` states that the inverse funct
ion
of this `OpenPartialHomeomorph` has derivative `f'.symm`.
-/
def toOpenPartialHomeomorph (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
  OpenPartialHomeomorph E F :=
    ApproximatesLinearOn.toOpenPartialHomeomorph f
    (Classical.choose hf.approximates_deriv_on_open_nhds)
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.2
    (f'.subsingleton_or_nnnorm_symm_pos.imp id fun hf' =>
      NNReal.half_lt_self <| ne_of_gt <| inv_pos.2 hf')
    (Classical.choose_spec hf.approximates_deriv_on_open_nhds).2.1

variable {f}

@[simp]
/-
**HasStrictFDerivAt.toOpenPartialHomeomorph_coe** 是 Mathlib 中的一个定理，位于命名空间 `HasSt
rictFDerivAt`。
形式化陈述：toOpenPartialHomeomorph_coe (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a)
 : (hf.toOpenPartialHomeomorph f : E -> F) = f
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toOpenPartialHomeomorph_coe (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    (hf.toOpenPartialHomeomorph f : E → F) = f :=
  rfl
/-
**HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source** 是 Mathlib 中的一个定理，位于命名空间
 `HasStrictFDerivAt`。
形式化陈述：mem_toOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜
] F) a) : a in (hf.toOpenPartialHomeomorph f).source
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `HasStrictFDerivAt.approximates_deriv_on_open_nhds`：approximates_deriv_on
_open_nhds (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : exists s : Set E, a 
in s ∧ IsOpen s ∧ ApproximatesLinearOn …
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem mem_toOpenPartialHomeomorph_source (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    a ∈ (hf.toOpenPartialHomeomorph f).source :=
  (Classical.choose_spec hf.approximates_deriv_on_open_nhds).1
/-
**HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target** 是 Mathlib 中的一个定理，
位于命名空间 `HasStrictFDerivAt`。
形式化陈述：image_mem_toOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E
 ->L[𝕜] F) a) : f a in (hf.toOpenPartialHomeomorph f).target
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_source`：map_source {x : X} (h : x in e.source)
 : e x in e.target
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
-/
theorem image_mem_toOpenPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    f a ∈ (hf.toOpenPartialHomeomorph f).target :=
  (hf.toOpenPartialHomeomorph f).map_source hf.mem_toOpenPartialHomeomorph_source
/-
**HasStrictFDerivAt.map_nhds_eq_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDe
rivAt`。
形式化陈述：map_nhds_eq_of_equiv (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : map 
f (𝓝 a) = 𝓝 (f a)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.map_nhds_eq`：map_nhds_eq {x} (hx : x in e.source) 
: map e (𝓝 x) = 𝓝 (e x)
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
-/
theorem map_nhds_eq_of_equiv (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    map f (𝓝 a) = 𝓝 (f a) :=
  (hf.toOpenPartialHomeomorph f).map_nhds_eq hf.mem_toOpenPartialHomeomorph_source

variable (f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
/-
**HasStrictFDerivAt.localInverse** 是 Mathlib 中的一个定义，位于命名空间 `HasStrictFDerivAt`。
形式化陈述：localInverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : F -> E
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a function `f` with an invertible derivative, returns a function that is l
ocally inverse
to `f`.
-/
def localInverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
  (hf.toOpenPartialHomeomorph f).symm

variable {f f' a}
/-
**HasStrictFDerivAt.localInverse_def** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivA
t`。
形式化陈述：localInverse_def (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : hf.local
Inverse f _ _ = (hf.toOpenPartialHomeomorph f).symm
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem localInverse_def (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f _ _ = (hf.toOpenPartialHomeomorph f).symm :=
  rfl
/-
**HasStrictFDerivAt.eventually_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `HasStrict
FDerivAt`。
形式化陈述：eventually_left_inverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : f
orallᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.eventually_left_inverse`：eventually_left_inverse {
x} (hx : x in e.source) : forallᶠ y in 𝓝 x, e.symm (e y) = y
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
-/
theorem eventually_left_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
  (hf.toOpenPartialHomeomorph f).eventually_left_inverse hf.mem_toOpenPartialHomeomorph_source

@[simp]
/-
**HasStrictFDerivAt.localInverse_apply_image** 是 Mathlib 中的一个定理，位于命名空间 `HasStric
tFDerivAt`。
形式化陈述：localInverse_apply_image (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : 
hf.localInverse f f' a (f a) = a
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.self_of_nhds`：Filter.Eventually.self_of_nhds {p : X ->
 Prop} (h : forallᶠ y in 𝓝 x, p y) : p x
· 使用定理 `HasStrictFDerivAt.eventually_left_inverse`：eventually_left_inverse (hf :
 HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ x in 𝓝 a, hf.localInverse f 
f' a (f x) = x
-/
theorem localInverse_apply_image (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    hf.localInverse f f' a (f a) = a :=
  hf.eventually_left_inverse.self_of_nhds
/-
**HasStrictFDerivAt.eventually_right_inverse** 是 Mathlib 中的一个定理，位于命名空间 `HasStric
tFDerivAt`。
形式化陈述：eventually_right_inverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : 
forallᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse'`：eventually_right_invers
e' {x} (hx : x in e.source) : forallᶠ y in 𝓝 (e x), e (e.symm y) = y
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
-/
theorem eventually_right_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ∀ᶠ y in 𝓝 (f a), f (hf.localInverse f f' a y) = y :=
  (hf.toOpenPartialHomeomorph f).eventually_right_inverse' hf.mem_toOpenPartialHomeomorph_source
/-
**HasStrictFDerivAt.localInverse_continuousAt** 是 Mathlib 中的一个定理，位于命名空间 `HasStri
ctFDerivAt`。
形式化陈述：localInverse_continuousAt (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) :
 ContinuousAt (hf.localInverse f f' a) (f a)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target`：image_mem_to
OpenPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : f 
a in (hf.toOpenPartialHomeomorph f).target
-/
theorem localInverse_continuousAt (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    ContinuousAt (hf.localInverse f f' a) (f a) :=
  (hf.toOpenPartialHomeomorph f).continuousAt_symm hf.image_mem_toOpenPartialHomeomorph_target
/-
**HasStrictFDerivAt.localInverse_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDe
rivAt`。
形式化陈述：localInverse_tendsto (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : Tend
sto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.tendsto_symm`：tendsto_symm {x} (hx : x in e.source
) : Tendsto e.symm (𝓝 (e x)) (𝓝 x)
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
-/
theorem localInverse_tendsto (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    Tendsto (hf.localInverse f f' a) (𝓝 <| f a) (𝓝 a) :=
  (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source
/-
**HasStrictFDerivAt.localInverse_unique** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDer
ivAt`。
形式化陈述：localInverse_unique (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : F 
-> E} (hg : forallᶠ x in 𝓝 a, g (f x) = x) : forallᶠ y in 𝓝 (f a), g y = localIn
verse f f' a hf y
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a；hg : forallᶠ x in 𝓝 a, g (f x) =
 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventuallyEq_of_left_inv_of_right_inv`：eventuallyEq_of_left_inv_o
f_right_inv {f : α -> β} {g₁ g₂ : β -> α} {fa : Filter α} {fb : Filter β} (hleft
 : forallᶠ x in fa, g₁ (f x) = x) …
· 使用定理 `HasStrictFDerivAt.eventually_right_inverse`：eventually_right_inverse (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : forallᶠ y in 𝓝 (f a), f (hf.localI
nverse f f' a y) = y
· 使用定理 `OpenPartialHomeomorph.tendsto_symm`：tendsto_symm {x} (hx : x in e.source
) : Tendsto e.symm (𝓝 (e x)) (𝓝 x)
· 使用定理 `HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source`：mem_toOpenPartialH
omeomorph_source (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : a in (hf.toOpe
nPartialHomeomorph f).source
-/
theorem localInverse_unique (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : ∀ᶠ y in 𝓝 (f a), g y = localInverse f f' a hf y :=
  eventuallyEq_of_left_inv_of_right_inv hg hf.eventually_right_inverse <|
    (hf.toOpenPartialHomeomorph f).tendsto_symm hf.mem_toOpenPartialHomeomorph_source

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.localInverse f` has derivative `f'.symm` at `f a`. -/
/-
**HasStrictFDerivAt.to_localInverse** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFDerivAt
`。
形式化陈述：to_localInverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : HasStrict
FDerivAt (hf.localInverse f f' a) (f'.symm : F ->L[𝕜] E) (f a)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.hasStrictFDerivAt_symm`：OpenPartialHomeomorph.hasS
trictFDerivAt_symm (f : OpenPartialHomeomorph E F) {f' : E ≃L[𝕜] F} {a : F} (ha 
: a in f.target) (htff' : HasStric…
· 使用定理 `HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target`：image_mem_to
OpenPartialHomeomorph_target (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : f 
a in (hf.toOpenPartialHomeomorph f).target
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasStrictFDerivAt.localInverse_apply_image`：localInverse_apply_image (hf
 : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) : hf.localInverse f f' a (f a) = a

--- 原说明 ---
If `f` has an invertible derivative `f'` at `a` in the sense of strict different
iability `(hf)`,
then the inverse function `hf.localInverse f` has derivative `f'.symm` at `f a`.
-/
theorem to_localInverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
    HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
  (hf.toOpenPartialHomeomorph f).hasStrictFDerivAt_symm
    hf.image_mem_toOpenPartialHomeomorph_target <| by
    simpa [← localInverse_def] using hf

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[CompleteSpace E]`
see `of_local_left_inverse`. -/
/-
**HasStrictFDerivAt.to_local_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `HasStrictFD
erivAt`。
形式化陈述：to_local_left_inverse (hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a) {g : 
F -> E} (hg : forallᶠ x in 𝓝 a, g (f x) = x) : HasStrictFDerivAt g (f'.symm : F 
->L[𝕜] E) (f a)
参数：hf : HasStrictFDerivAt f (f' : E ->L[𝕜] F) a；hg : forallᶠ x in 𝓝 a, g (f x) =
 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictFDerivAt.congr_of_eventuallyEq`：HasStrictFDerivAt.congr_of_even
tuallyEq (h : HasStrictFDerivAt f f' x) (h₁ : f =ᶠ[𝓝 x] f₁) : HasStrictFDerivAt 
f₁ f' x
· 使用定理 `HasStrictFDerivAt.to_localInverse`：to_localInverse (hf : HasStrictFDeriv
At f (f' : E ->L[𝕜] F) a) : HasStrictFDerivAt (hf.localInverse f f' a) (f'.symm 
: F ->L[𝕜] E) (f a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `HasStrictFDerivAt.localInverse_unique`：localInverse_unique (hf : HasStri
ctFDerivAt f (f' : E ->L[𝕜] F) a) {g : F -> E} (hg : forallᶠ x in 𝓝 a, g (f x) =
 x) : forallᶠ y in 𝓝 (f a),…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict d
ifferentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at
 `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[Co
mpleteSpace E]`
see `of_local_left_inverse`.
-/
theorem to_local_left_inverse (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) {g : F → E}
    (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) : HasStrictFDerivAt g (f'.symm : F →L[𝕜] E) (f a) :=
  hf.to_localInverse.congr_of_eventuallyEq <| (hf.localInverse_unique hg).mono fun _ => Eq.symm

end HasStrictFDerivAt

/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
/-
**isOpenMap_of_hasStrictFDerivAt_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isOpenMap_of_hasStrictFDerivAt_equiv [CompleteSpace E] {f : E -> F} {f' : 
E -> E ≃L[𝕜] F} (hf : forall x, HasStrictFDerivAt f (f' x : E ->L[𝕜] F) x) : IsO
penMap f
参数：hf : forall x, HasStrictFDerivAt f (f' x : E ->L[𝕜] F) x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpenMap_iff_nhds_le`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [inst
 : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsOpenMap f ↔ ∀ (x : X),
 nhds (f x)…
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `HasStrictFDerivAt.map_nhds_eq_of_equiv`：map_nhds_eq_of_equiv (hf : HasSt
rictFDerivAt f (f' : E ->L[𝕜] F) a) : map f (𝓝 a) = 𝓝 (f a)

--- 原说明 ---
If a function has an invertible strict derivative at all points, then it is an o
pen map.
-/
theorem isOpenMap_of_hasStrictFDerivAt_equiv [CompleteSpace E] {f : E → F} {f' : E → E ≃L[𝕜] F}
    (hf : ∀ x, HasStrictFDerivAt f (f' x : E →L[𝕜] F) x) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => (hf x).map_nhds_eq_of_equiv.ge
