/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.MellinTransform

/-!
# Abstract functional equations for Mellin transforms

This file formalises a general version of an argument used to prove functional equations for
zeta and L-functions.

### FE-pairs

We define a *weak FE-pair* to be a pair of functions `f, g` on the reals which are locally
integrable on `(0, ∞)`, have the form "constant" + "rapidly decaying term" at `∞`, and satisfy a
functional equation of the form

`f (1 / x) = ε * x ^ k * g x`

for some constants `k ∈ ℝ` and `ε ∈ ℂ`. (Modular forms give rise to natural examples
with `k` being the weight and `ε` the global root number; hence the notation.) We could arrange
`ε = 1` by scaling `g`; but this is inconvenient in applications so we set things up more generally.

A *strong FE-pair* is a weak FE-pair where the constant terms of `f` and `g` at `∞` are both 0.

The main property of these pairs is the following: if `f`, `g` are a weak FE-pair, with constant
terms `f₀` and `g₀` at `∞`, then the Mellin transforms `Λ` and `Λ'` of `f - f₀` and `g - g₀`
respectively both have meromorphic continuation and satisfy a functional equation of the form

`Λ (k - s) = ε * Λ' s`.

The poles (and their residues) are explicitly given in terms of `f₀` and `g₀`; in particular, if
`(f, g)` are a strong FE-pair, then the Mellin transforms of `f` and `g` are entire functions.

### Main definitions and results

See the sections *Main theorems on weak FE-pairs* and
*Main theorems on strong FE-pairs* below.

* Weak FE pairs:
  - `WeakFEPair.Λ₀`: and `WeakFEPair.Λ`: functions of `s : ℂ`
  - `WeakFEPair.differentiable_Λ₀`: `Λ₀` is entire
  - `WeakFEPair.differentiableAt_Λ`: `Λ` is differentiable away from `s = 0` and `s = k`
  - `WeakFEPair.hasMellin`: for `k < re s`, `Λ s` equals the Mellin transform of `f - f₀`
  - `WeakFEPair.functional_equation₀`: the functional equation for `Λ₀`
  - `WeakFEPair.functional_equation`: the functional equation for `Λ`
  - `WeakFEPair.Λ_residue_k`: computation of the residue at `k`
  - `WeakFEPair.Λ_residue_zero`: computation of the residue at `0`.

* Strong FE pairs:
  - `IsStrongFEPair.differentiable_Λ`: `Λ` is entire
  - `IsStrongFEPair.hasMellin`: `Λ` is everywhere equal to the Mellin transform of `f`
-/

@[expose] public section


/- TODO: Consider extending the results to allow functional equations of the form
`f (N / x) = (const) • x ^ k • g x` for a real parameter `0 < N`. This could be done either by
generalising the existing proofs in situ, or by a separate wrapper `FEPairWithLevel` which just
applies a scaling factor to `f` and `g` to reduce to the `N = 1` case.
-/

noncomputable section

open Real Complex Filter Topology Asymptotics Set MeasureTheory

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]

/-!
## Definitions and symmetry
-/

/-- A structure designed to hold the hypotheses for the Mellin-functional-equation argument
(most general version: rapid decay at `∞` up to constant terms) -/
/-
**WeakFEPair** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(E : Type u_1) → [inst : NormedAddCommGroup E] → [NormedSpace ℂ E] → Type 
u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A structure designed to hold the hypotheses for the Mellin-functional-equation a
rgument
(most general version: rapid decay at `∞` up to constant terms)
-/
structure WeakFEPair where
  /-- The functions whose Mellin transform we study -/
  (f g : ℝ → E)
  /-- Weight (exponent in the functional equation) -/
  (k : ℝ)
  /-- Root number -/
  (ε : ℂ)
  /-- Constant terms at `∞` -/
  (f₀ g₀ : E)
  (hf_int : LocallyIntegrableOn f (Ioi 0))
  (hg_int : LocallyIntegrableOn g (Ioi 0))
  (hk : 0 < k)
  (hε : ε ≠ 0)
  (h_feq : ∀ x ∈ Ioi 0, f (1 / x) = (ε * ↑(x ^ k)) • g x)
  (hf_top (r : ℝ) : (f · - f₀) =O[atTop] (· ^ r))
  (hg_top (r : ℝ) : (g · - g₀) =O[atTop] (· ^ r))

variable {E}

/-- A *strong FE-pair* is a weak FE-pair in which `f₀` and `g₀` are zero. -/
/-
**IsStrongFEPair** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{E : Type u_1} → [inst : NormedAddCommGroup E] → [inst_1 : NormedSpace ℂ E
] → WeakFEPair E → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A *strong FE-pair* is a weak FE-pair in which `f₀` and `g₀` are zero.
-/
structure IsStrongFEPair (P : WeakFEPair E) : Prop where
  hf₀ : P.f₀ = 0
  hg₀ : P.g₀ = 0

section symmetry

/-- Reformulated functional equation with `f` and `g` interchanged. -/
/-
**WeakFEPair.h_feq'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：WeakFEPair.h_feq' (P : WeakFEPair E) (x : Real) (hx : 0 < x) : P.g (1 / x)
 = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x
参数：P : WeakFEPair E；x : Real；hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WeakFEPair.h_feq`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1
 : NormedSpace ℂ E] (self : WeakFEPair E),   ∀ x ∈ Set.Ioi 0, self.f (1 / x) = (
self.ε…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `div_div_cancel₀`：∀ {G₀ : Type u_3} [inst : CommGroupWithZero G₀] {a b : 
G₀}, a ≠ 0 → a / (a / b) = b
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.inv_rpow`：inv_rpow (hx : 0 <= x) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₂`：mul_eq_eval₂ [CommGroupWithZer
o M] (r₁ r₂ : Int) (x : M) {l₁ l₂ l : NF M} (h : l₁.eval * l₂.eval = l.eval) : (
(r₁, x) ::ᵣ l₁).eval * ((r₂, x…
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Reformulated functional equation with `f` and `g` interchanged.
-/
lemma WeakFEPair.h_feq' (P : WeakFEPair E) (x : ℝ) (hx : 0 < x) :
    P.g (1 / x) = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x := by
  rw [(div_div_cancel₀ (one_ne_zero' ℝ) ▸ P.h_feq (1 / x) (one_div_pos.mpr hx) :), ← mul_smul]
  convert! (one_smul ℂ (P.g (1 / x))).symm using 2
  rw [one_div, inv_rpow hx.le, ofReal_inv]
  field [P.hε, (rpow_pos_of_pos hx _).ne']

/-- The hypotheses are symmetric in `f` and `g`, with the constant `ε` replaced by `ε⁻¹`. -/
@[simps]
/-
**WeakFEPair.symm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：WeakFEPair.symm (P : WeakFEPair E) : WeakFEPair E where f
参数：P : WeakFEPair E。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `WeakFEPair.hg_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.g …
· 使用定理 `WeakFEPair.hf_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.f …
· 使用定理 `WeakFEPair.hk`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), 0 < self.k
· 使用引理 `WeakFEPair.h_feq'`：WeakFEPair.h_feq' (P : WeakFEPair E) (x : Real) (hx :
 0 < x) : P.g (1 / x) = (P.ε⁻¹ * ↑(x ^ P.k)) • P.f x
· 使用定理 `WeakFEPair.hg_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.g x - self.
g₀) =O[…
· 使用定理 `WeakFEPair.hf_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.f x - self.
f₀) =O[…

--- 原说明 ---
The hypotheses are symmetric in `f` and `g`, with the constant `ε` replaced by `
ε⁻¹`.
-/
def WeakFEPair.symm (P : WeakFEPair E) : WeakFEPair E where
  f := P.g
  g := P.f
  k := P.k
  ε := P.ε⁻¹
  f₀ := P.g₀
  g₀ := P.f₀
  hf_int := P.hg_int
  hg_int := P.hf_int
  hf_top := P.hg_top
  hg_top := P.hf_top
  hε := inv_ne_zero P.hε
  hk := P.hk
  h_feq  := P.h_feq'
/-
**isStrongFEPair_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedSpace ℂ E] 
{P : WeakFEPair E},   IsStrongFEPair P.symm ↔ IsStrongFEPair P
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrongFEPair.hg₀`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P → P.g₀ = 0
· 使用定理 `IsStrongFEPair.hf₀`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P → P.f₀ = 0
-/
@[simp] lemma isStrongFEPair_symm {P : WeakFEPair E} :
    IsStrongFEPair P.symm ↔ IsStrongFEPair P where
  mp h := ⟨h.hg₀, h.hf₀⟩
  mpr h := ⟨h.hg₀, h.hf₀⟩
/-
**IsStrongFEPair.symm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsStrongFEPair.symm {P : WeakFEPair E} (hP : IsStrongFEPair P) : IsStrongF
EPair P.symm
参数：hP : IsStrongFEPair P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isStrongFEPair_symm`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [ins
t_1 : NormedSpace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P.symm ↔ IsStrongFEP
air P
-/
lemma IsStrongFEPair.symm {P : WeakFEPair E} (hP : IsStrongFEPair P) :
    IsStrongFEPair P.symm := isStrongFEPair_symm.2 hP

end symmetry

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results I: lemmas on asymptotics
-/

/-- As `x → 0`, we have `f x = x ^ (-P.k) • constant` up to a rapidly decaying error. -/
/-
**WeakFEPair.hf_zero** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：hf_zero (r : Real) : (fun x => P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) =O[𝓝[
>] 0] (· ^ r)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `WeakFEPair.hg_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.g x - self.
g₀) =O[…
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Complex.ofReal_ne_zero`：ofReal_ne_zero {z : Real} : (z : Complex) != 0 ↔
 z != 0
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `WeakFEPair.hε`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), self.ε ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
（共 95 条，此处仅展示前 30 条）

--- 原说明 ---
As `x → 0`, we have `f x = x ^ (-P.k) • constant` up to a rapidly decaying error
.
-/
lemma hf_zero (r : ℝ) :
    (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀) =O[𝓝[>] 0] (· ^ r) := by
  have := (P.hg_top (-(r + P.k))).comp_tendsto tendsto_inv_nhdsGT_zero
  simp_rw [IsBigO, IsBigOWith, eventually_nhdsWithin_iff] at this ⊢
  obtain ⟨C, hC⟩ := this
  use ‖P.ε‖ * C
  filter_upwards [hC] with x hC' (hx : 0 < x)
  have h_nv2 : ↑(x ^ P.k) ≠ (0 : ℂ) := ofReal_ne_zero.mpr (rpow_pos_of_pos hx _).ne'
  have h_nv : P.ε⁻¹ * ↑(x ^ P.k) ≠ 0 := mul_ne_zero P.symm.hε h_nv2
  specialize hC' hx
  simp_rw [Function.comp_apply, ← one_div, P.h_feq' _ hx] at hC'
  rw [← ((mul_inv_cancel₀ h_nv).symm ▸ one_smul ℂ P.g₀ :), mul_smul _ _ P.g₀, ← smul_sub, norm_smul,
    ← le_div_iff₀' (lt_of_le_of_ne (norm_nonneg _) (norm_ne_zero_iff.mpr h_nv).symm)] at hC'
  convert! hC' using 1
  · congr 3
    rw [rpow_neg hx.le]
    simp [field]
  · simp_rw [norm_mul, norm_real, one_div, inv_rpow hx.le, rpow_neg hx.le, inv_inv, norm_inv,
      norm_of_nonneg (rpow_pos_of_pos hx _).le, rpow_add hx]
    field

/-- Power asymptotic for `f - f₀` as `x → 0`. -/
/-
**WeakFEPair.hf_zero'** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：hf_zero' : (fun x : Real => P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_add_sub_cancel`：∀ {G : Type u_3} [inst : AddGroup G] (a b c : G), a 
- b + (b - c) = a - c
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用引理 `WeakFEPair.hf_zero`：hf_zero (r : Real) : (fun x => P.f x - (P.ε * ↑(x ^ 
(-P.k))) • P.g₀) =O[𝓝[>] 0] (· ^ r)
· 使用定理 `Asymptotics.IsBigO.sub`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Asymptotics.isBigO_norm_norm`：isBigO_norm_norm : ((fun x => ‖f' x‖) =O[l
] fun x => ‖g' x‖) ↔ f' =O[l] g'
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `Complex.norm_real`：norm_real (r : Real) : ‖(r : Complex)‖ = ‖r‖
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_le_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 :
 LinearOrder α] [ClosedIciTopology α] {a b : α},   a < b → ∀ᶠ (x : α) in nhds a,
 x ≤ b
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
Power asymptotic for `f - f₀` as `x → 0`.
-/
lemma hf_zero' : (fun x : ℝ ↦ P.f x - P.f₀) =O[𝓝[>] 0] (· ^ (-P.k)) := by
  simp_rw [← fun x ↦ sub_add_sub_cancel (P.f x) ((P.ε * ↑(x ^ (-P.k))) • P.g₀) P.f₀]
  refine (P.hf_zero _).add (IsBigO.sub ?_ ?_)
  · rw [← isBigO_norm_norm]
    simp_rw [mul_smul, norm_smul, mul_comm _ ‖P.g₀‖, ← mul_assoc, norm_real]
    apply (isBigO_refl _ _).const_mul_left
  · refine IsBigO.of_bound ‖P.f₀‖ (eventually_nhdsWithin_iff.mpr ?_)
    filter_upwards [eventually_le_nhds zero_lt_one] with x hx' (hx : 0 < x)
    apply le_mul_of_one_le_right (norm_nonneg _)
    rw [norm_of_nonneg (rpow_pos_of_pos hx _).le, rpow_neg hx.le]
    exact (one_le_inv₀ (rpow_pos_of_pos hx _)).2 (rpow_le_one hx.le hx' P.hk.le)
/-
**WeakFEPair.functional_equation_aux** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem functional_equation_aux (s : ℂ) :
    mellin P.f (P.k - s) = P.ε • mellin P.g s := by
  -- substitute `t ↦ t⁻¹` in `mellin P.g s`
  have step1 := mellin_comp_rpow P.g (-s) (-1)
  simp_rw [abs_neg, abs_one, inv_one, one_smul, ofReal_neg, ofReal_one, div_neg, div_one, neg_neg,
    rpow_neg_one, ← one_div] at step1
  -- introduce a power of `t` to match the hypothesis `P.h_feq`
  have step2 := mellin_cpow_smul (fun t ↦ P.g (1 / t)) (P.k - s) (-P.k)
  rw [← sub_eq_add_neg, sub_right_comm, sub_self, zero_sub, step1] at step2
  -- put in the constant `P.ε`
  have step3 := mellin_const_smul (fun t ↦ (t : ℂ) ^ (-P.k : ℂ) • P.g (1 / t)) (P.k - s) P.ε
  rw [step2] at step3
  rw [← step3]
  -- now the integrand matches `P.h_feq'` on `Ioi 0`, so we can apply `setIntegral_congr_fun`
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht ↦ ?_)
  simp_rw [P.h_feq' t ht, ← mul_smul]
  -- some simple `cpow` arithmetic to finish
  rw [cpow_neg, ofReal_cpow (le_of_lt ht)]
  have : (t : ℂ) ^ (P.k : ℂ) ≠ 0 := by simpa [← ofReal_cpow ht.le] using (rpow_pos_of_pos ht _).ne'
  field_simp [P.hε]

end WeakFEPair

namespace IsStrongFEPair

variable {P : WeakFEPair E} (hP : IsStrongFEPair P)
include hP

/-- As `x → ∞`, `f x` decays faster than any power of `x`. -/
/-
**IsStrongFEPair.hf_top** 是 Mathlib 中的一个引理，位于命名空间 `IsStrongFEPair`。
形式化陈述：hf_top (r : Real) : P.f =O[atTop] (· ^ r)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrongFEPair.hf₀`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P → P.f₀ = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `WeakFEPair.hf_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.f x - self.
f₀) =O[…

--- 原说明 ---
As `x → ∞`, `f x` decays faster than any power of `x`.
-/
lemma hf_top (r : ℝ) : P.f =O[atTop] (· ^ r) := by
  simpa [hP.hf₀] using P.hf_top r

/-- As `x → 0`, `f x` decays faster than any power of `x`. -/
/-
**IsStrongFEPair.hf_zero** 是 Mathlib 中的一个引理，位于命名空间 `IsStrongFEPair`。
形式化陈述：hf_zero (r : Real) : P.f =O[𝓝[>] 0] (· ^ r)
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `WeakFEPair.hf_zero`：hf_zero (r : Real) : (fun x => P.f x - (P.ε * ↑(x ^ 
(-P.k))) • P.g₀) =O[𝓝[>] 0] (· ^ r)
· 使用定理 `IsStrongFEPair.hg₀`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P → P.g₀ = 0

--- 原说明 ---
As `x → 0`, `f x` decays faster than any power of `x`.
-/
lemma hf_zero (r : ℝ) : P.f =O[𝓝[>] 0] (· ^ r) := by
  simpa using (hP.hg₀ ▸ P.hf_zero r :)

/-- The Mellin transform of `P.f` is globally convergent. Private since it is superseded by
`IsStrongFEPair.hasMellin` below, which also identifies its Mellin transform as `P.Λ`. -/
/-
**IsStrongFEPair.mellinConvergent** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mellin transform of `P.f` is globally convergent. Private since it is supers
eded by
`IsStrongFEPair.hasMellin` below, which also identifies its Mellin transform as 
`P.Λ`.
-/
private theorem mellinConvergent (s : ℂ) : MellinConvergent P.f s :=
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellinConvergent_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

/-- The Mellin transform of `P.f` is globally convergent. Private since it is superseded by
`IsStrongFEPair.differentiable_Λ` below. -/
/-
**IsStrongFEPair.differentiable_mellin** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongFEPair
`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Mellin transform of `P.f` is globally convergent. Private since it is supers
eded by
`IsStrongFEPair.differentiable_Λ` below.
-/
private theorem differentiable_mellin : Differentiable ℂ (mellin P.f) := fun s ↦
  let ⟨_, ht⟩ := exists_gt s.re
  let ⟨_, hu⟩ := exists_lt s.re
  mellin_differentiableAt_of_isBigO_rpow P.hf_int (hP.hf_top _) ht (hP.hf_zero _) hu

end IsStrongFEPair

namespace WeakFEPair

variable (P : WeakFEPair E)

/-!
## Auxiliary results II: building a strong FE-pair from a weak FE-pair
-/

/-- Piecewise modified version of `f` with optimal asymptotics. We deliberately choose intervals
which don't quite join up, so the function is `0` at `x = 1`, in order to maintain symmetry;
there is no "good" choice of value at `1`. -/
/-
**WeakFEPair.f_modif** 是 Mathlib 中的一个定义，位于命名空间 `WeakFEPair`。
形式化陈述：f_modif : Real -> E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Piecewise modified version of `f` with optimal asymptotics. We deliberately choo
se intervals
which don't quite join up, so the function is `0` at `x = 1`, in order to mainta
in symmetry;
there is no "good" choice of value at `1`.
-/
def f_modif : ℝ → E :=
  (Ioi 1).indicator (fun x ↦ P.f x - P.f₀) +
  (Ioo 0 1).indicator (fun x ↦ P.f x - (P.ε * ↑(x ^ (-P.k))) • P.g₀)

/-- Piecewise modified version of `g` with optimal asymptotics. -/
/-
**WeakFEPair.g_modif** 是 Mathlib 中的一个定义，位于命名空间 `WeakFEPair`。
形式化陈述：g_modif : Real -> E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Piecewise modified version of `g` with optimal asymptotics.
-/
def g_modif : ℝ → E :=
  (Ioi 1).indicator (fun x ↦ P.g x - P.g₀) +
  (Ioo 0 1).indicator (fun x ↦ P.g x - (P.ε⁻¹ * ↑(x ^ (-P.k))) • P.f₀)
/-
**WeakFEPair.hf_modif_int** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：hf_modif_int : LocallyIntegrableOn P.f_modif (Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.locallyIntegrableOn`：ContinuousOn.locallyIntegrableOn [IsLo
callyFiniteMeasure μ] [SecondCountableTopologyEither X E] (hf : ContinuousOn f K
) (hK : MeasurableSet …
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `secondCountableTopologyEither_of_left`：∀ (α : Type u_6) (β : Type u_7) [
inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolog
y α],   SecondCountableTopo…
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `ContinuousAt.fun_smul`：∀ {M : Type u_1} {X : Type u_2} {Y : Type u_3} [i
nst : TopologicalSpace M] [inst_1 : TopologicalSpace X]   [inst_2 : TopologicalS
pace Y] [in…
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `ContinuousAt.const_mul`：ContinuousAt.const_mul (hf : ContinuousAt f x) (
b : M) : ContinuousAt (b * f ·) x
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `ContinuousAt.comp'`：ContinuousAt.comp' {g : Y -> Z} {x : X} (hg : Contin
uousAt g (f x)) (hf : ContinuousAt f x) : ContinuousAt (fun x => g (f x)) x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Real.continuousAt_rpow_const`：continuousAt_rpow_const (x : Real) (q : Re
al) (h : x != 0 ∨ 0 <= q) : ContinuousAt (fun x : Real => x ^ q) x
· 使用定理 `continuousAt_const`：continuousAt_const : ContinuousAt (fun _ : X => y) x
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.LocallyIntegrableOn.add`：∀ {X : Type u_1} {ε'' : Type u_5}
 [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X]   [inst_2 : Topologica
lSpace ε''] [inst_3 : ESemi…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.LocallyIntegrableOn.sub`：∀ {X : Type u_1} {E : Type u_6} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedAddCommG
roup E]   {μ : MeasureTheor…
· 使用定理 `WeakFEPair.hf_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.f …
· 使用定理 `MeasureTheory.locallyIntegrableOn_const`：locallyIntegrableOn_const [IsLo
callyFiniteMeasure μ] (c : E) : LocallyIntegrableOn (fun _ => c) s μ
· 使用定理 `MeasureTheory.IntegrableOn.indicator`：∀ {α : Type u_1} {ε' : Type u_4} {
mα : MeasurableSpace α} {s t : Set α} {μ : MeasureTheory.Measure α}   [inst : To
pologicalSpace ε'] [inst_1…
（共 31 条，此处仅展示前 30 条）
-/
lemma hf_modif_int :
    LocallyIntegrableOn P.f_modif (Ioi 0) := by
  have : LocallyIntegrableOn (fun x : ℝ ↦ (P.ε * ↑(x ^ (-P.k))) • P.g₀) (Ioi 0) := by
    refine ContinuousOn.locallyIntegrableOn ?_ measurableSet_Ioi
    refine continuousOn_of_forall_continuousAt (fun x (hx : 0 < x) ↦ ?_)
    have : x ≠ 0 ∨ 0 ≤ -P.k := Or.inl hx.ne'
    fun_prop
  refine LocallyIntegrableOn.add (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub (locallyIntegrableOn_const _) x hx
    exact ⟨s, hs, hs'.indicator measurableSet_Ioi⟩
  · obtain ⟨s, hs, hs'⟩ := P.hf_int.sub this x hx
    exact ⟨s, hs, hs'.indicator measurableSet_Ioo⟩
/-
**WeakFEPair.hf_modif_FE** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：hf_modif_FE (x : Real) (hx : 0 < x) : P.f_modif (1 / x) = (P.ε * ↑(x ^ P.k
)) • P.g_modif x
参数：x : Real；hx : 0 < x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div_lt`：one_div_lt (ha : 0 < a) (hb : 0 < b) : 1 / a < b ↔ 1 / b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `WeakFEPair.f_modif.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℂ E] (P : WeakFEPair E),   P.f_modif =     ((Set.Ioi 1).in
dicator fun x…
· 使用定理 `Pi.add_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Add 
(M i)] (f g : (i : ι) → M i) (i : ι), (f + g) i = f i + g i
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_Ioi`：notMem_Ioi : c ∉ Ioi a ↔ c <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `WeakFEPair.g_modif.eq_1`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] 
[inst_1 : NormedSpace ℂ E] (P : WeakFEPair E),   P.g_modif =     ((Set.Ioi 1).in
dicator fun x…
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.notMem_Ioo_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, 
a ≤ c → c ∉ Set.Ioo b a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `WeakFEPair.h_feq`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1
 : NormedSpace ℂ E] (self : WeakFEPair E),   ∀ x ∈ Set.Ioi 0, self.f (1 / x) = (
self.ε…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用引理 `one_div_pos`：one_div_pos : 0 < 1 / a ↔ 0 < a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Real.inv_rpow`：inv_rpow (hx : 0 <= x) (y : Real) : x⁻¹ ^ y = (x ^ y)⁻¹
（共 94 条，此处仅展示前 30 条）
-/
lemma hf_modif_FE (x : ℝ) (hx : 0 < x) :
    P.f_modif (1 / x) = (P.ε * ↑(x ^ P.k)) • P.g_modif x := by
  rcases lt_trichotomy 1 x with hx' | rfl | hx'
  · have : 1 / x < 1 := by rwa [one_div_lt hx one_pos, div_one]
    rw [f_modif, Pi.add_apply, indicator_of_notMem (notMem_Ioi.mpr this.le),
      zero_add, indicator_of_mem (mem_Ioo.mpr ⟨div_pos one_pos hx, this⟩), g_modif, Pi.add_apply,
      indicator_of_mem (mem_Ioi.mpr hx'), indicator_of_notMem
      (notMem_Ioo_of_ge hx'.le), add_zero, P.h_feq _ hx, smul_sub]
    simp_rw [rpow_neg (one_div_pos.mpr hx).le, one_div, inv_rpow hx.le, inv_inv]
  · simp [f_modif, g_modif]
  · have : 1 < 1 / x := by rwa [lt_one_div one_pos hx, div_one]
    rw [f_modif, Pi.add_apply, indicator_of_mem (mem_Ioi.mpr this),
      indicator_of_notMem (notMem_Ioo_of_ge this.le), g_modif, Pi.add_apply,
      indicator_of_notMem (notMem_Ioi.mpr hx'.le),
      indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩), P.h_feq _ hx]
    simp_rw [rpow_neg hx.le]
    match_scalars <;> field [(rpow_pos_of_pos hx P.k).ne', P.hε]
/-
**WeakFEPair.hf_modif_top** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：hf_modif_top (r : Real) : (fun x => P.f_modif x - 0) =O[atTop] fun x => x 
^ r
参数：r : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `WeakFEPair.hf_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.f x - self.
f₀) =O[…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Set.notMem_Ioo_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, 
a ≤ c → c ∉ Set.Ioo b a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
lemma hf_modif_top (r : ℝ) :
    (fun x ↦ P.f_modif x - 0) =O[atTop] fun x ↦ x ^ r := by
  refine (P.hf_top r).congr' ?_ .rfl
  filter_upwards [eventually_gt_atTop 1] with x hx
  simp [f_modif, mem_Ioi.mpr hx, notMem_Ioo_of_ge hx.le]

/-- Given a weak FE-pair `(f, g)`, modify it into a strong FE-pair by subtracting suitable
correction terms from `f` and `g`.

(See `WeakFEPair.isStrongFEPair_toStrongFEPair` for the proof that this is actually a strong
FE-pair.) -/
/-
**WeakFEPair.toStrongFEPair** 是 Mathlib 中的一个定义，位于命名空间 `WeakFEPair`。
形式化陈述：toStrongFEPair : WeakFEPair E where f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `WeakFEPair.hf_modif_int`：hf_modif_int : LocallyIntegrableOn P.f_modif (I
oi 0)
· 使用定理 `WeakFEPair.hk`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), 0 < self.k
· 使用定理 `WeakFEPair.hε`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), self.ε ≠ 0
· 使用引理 `WeakFEPair.hf_modif_FE`：hf_modif_FE (x : Real) (hx : 0 < x) : P.f_modif 
(1 / x) = (P.ε * ↑(x ^ P.k)) • P.g_modif x
· 使用引理 `WeakFEPair.hf_modif_top`：hf_modif_top (r : Real) : (fun x => P.f_modif x
 - 0) =O[atTop] fun x => x ^ r

--- 原说明 ---
Given a weak FE-pair `(f, g)`, modify it into a strong FE-pair by subtracting su
itable
correction terms from `f` and `g`.

(See `WeakFEPair.isStrongFEPair_toStrongFEPair` for the proof that this is actua
lly a strong
FE-pair.)
-/
def toStrongFEPair : WeakFEPair E where
  f := P.f_modif
  g := P.symm.f_modif
  k := P.k
  ε := P.ε
  f₀ := 0
  g₀ := 0
  hf_int := P.hf_modif_int
  hg_int := P.symm.hf_modif_int
  h_feq := P.hf_modif_FE
  hε := P.hε
  hk := P.hk
  hf_top := P.hf_modif_top
  hg_top := P.symm.hf_modif_top
/-
**WeakFEPair.isStrongFEPair_toStrongFEPair** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair
`。
形式化陈述：isStrongFEPair_toStrongFEPair : IsStrongFEPair P.toStrongFEPair where hf₀
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isStrongFEPair_toStrongFEPair : IsStrongFEPair P.toStrongFEPair where
  hf₀ := rfl
  hg₀ := rfl

/-- Alternative form for the difference between `f - f₀` and its modified term. -/
/-
**WeakFEPair.f_modif_aux1** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：f_modif_aux1 : EqOn (fun x => P.f_modif x - P.f x + P.f₀) ((Ioo 0 1).indic
ator (fun x : Real => P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀) + ({1} : Set Real).in
dicator (fun _ => P.f₀ - P.f 1)) (Ioi 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.notMem_Ioi`：notMem_Ioi : c ∉ Ioi a ↔ c <= a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.mem_Ioo`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
oo a b ↔ a < x ∧ x < b
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.AbstractFuncEq.0.WeakFEPair.f_modi
f_aux1._abel_1_2`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : Norme
dSpace ℂ E] (P : WeakFEPair E) ⦃x : ℝ⦄,   0 + (P.f x - (P.ε * ↑(x ^ (-P.k))) •…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_Ioi`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Ioi
 b ↔ b < x
· 使用定理 `Set.notMem_Ioo_of_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, 
a ≤ c → c ∉ Set.Ioo b a
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.AbstractFuncEq.0.WeakFEPair.f_modi
f_aux1._abel_1_3`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : Norme
dSpace ℂ E] (P : WeakFEPair E) ⦃x : ℝ⦄,   P.f x - P.f₀ + 0 - P.f x + P.f₀ = 0 …

--- 原说明 ---
Alternative form for the difference between `f - f₀` and its modified term.
-/
lemma f_modif_aux1 : EqOn (fun x ↦ P.f_modif x - P.f x + P.f₀)
    ((Ioo 0 1).indicator (fun x : ℝ ↦ P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀)
    + ({1} : Set ℝ).indicator (fun _ ↦ P.f₀ - P.f 1)) (Ioi 0) := by
  intro x (hx : 0 < x)
  simp_rw [f_modif, Pi.add_apply]
  rcases lt_trichotomy x 1 with hx' | rfl | hx'
  · simp_rw [indicator_of_notMem (notMem_Ioi.mpr hx'.le), indicator_of_mem (mem_Ioo.mpr ⟨hx, hx'⟩),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne)]
    abel
  · simp [add_comm, sub_eq_add_neg]
  · simp_rw [indicator_of_mem (mem_Ioi.mpr hx'), indicator_of_notMem (notMem_Ioo_of_ge hx'.le),
      indicator_of_notMem (mem_singleton_iff.not.mpr hx'.ne')]
    abel

/-- Compute the Mellin transform of the modifying term used to kill off the constants at
`0` and `∞`. -/
/-
**WeakFEPair.f_modif_aux2** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
形式化陈述：f_modif_aux2 [CompleteSpace E] {s : Complex} (hs : P.k < re s) : mellin (f
un x => P.f_modif x - P.f x + P.f₀) s = (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g
₀
参数：hs : P.k < re s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `WeakFEPair.hk`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), 0 < self.k
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeakFEPair.f_modif_aux1`：f_modif_aux1 : EqOn (fun x => P.f_modif x - P.f
 x + P.f₀) ((Ioo 0 1).indicator (fun x : Real => P.f₀ - (P.ε * ↑(x ^ (-P.k))) • 
P.g₀) + ({1} …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_singleton`：∀ {ι : Type u_6} [inst : DecidableEq ι] {M : Ty
pe u_7} [inst_1 : Zero M] (i : ι) (f : ι → M),   {i}.indicator f = Pi.single i (
f i)
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_congr_ae`：setIntegral_congr_ae (hs : Measurabl
eSet s) (h : forallᵐ x ∂μ, x in s -> f x = g x) : ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
Compute the Mellin transform of the modifying term used to kill off the constant
s at
`0` and `∞`.
-/
lemma f_modif_aux2 [CompleteSpace E] {s : ℂ} (hs : P.k < re s) :
    mellin (fun x ↦ P.f_modif x - P.f x + P.f₀) s = (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀ := by
  have h_re1 : -1 < re (s - 1) := by simpa using P.hk.trans hs
  have h_re2 : -1 < re (s - P.k - 1) := by simpa using hs
  calc
  _ = ∫ (x : ℝ) in Ioi 0, (x : ℂ) ^ (s - 1) •
      ((Ioo 0 1).indicator (fun t : ℝ ↦ P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x
      + ({1} : Set ℝ).indicator (fun _ ↦ P.f₀ - P.f 1) x) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx ↦ by simp [f_modif_aux1 P hx])
  _ = ∫ (x : ℝ) in Ioi 0, (x : ℂ) ^ (s - 1) • ((Ioo 0 1).indicator
      (fun t : ℝ ↦ P.f₀ - (P.ε * ↑(t ^ (-P.k))) • P.g₀) x) := by
    refine setIntegral_congr_ae measurableSet_Ioi (eventually_of_mem (U := {1}ᶜ)
        (compl_mem_ae_iff.mpr (subsingleton_singleton.measure_zero _)) (fun x hx _ ↦ ?_))
    rw [indicator_of_notMem hx, add_zero]
  _ = ∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s - 1) • (P.f₀ - (P.ε * ↑(x ^ (-P.k))) • P.g₀) := by
    simp_rw [← indicator_smul, setIntegral_indicator measurableSet_Ioo,
      inter_eq_right.mpr Ioo_subset_Ioi_self, integral_Ioc_eq_integral_Ioo]
  _ = ∫ x : ℝ in Ioc 0 1, ((x : ℂ) ^ (s - 1) • P.f₀ - P.ε • (x : ℂ) ^ (s - P.k - 1) • P.g₀) := by
    refine setIntegral_congr_fun measurableSet_Ioc (fun x ⟨hx, _⟩ ↦ ?_)
    rw [ofReal_cpow hx.le, ofReal_neg, smul_sub, ← mul_smul, mul_comm, mul_assoc, mul_smul,
      mul_comm, ← cpow_add _ _ (ofReal_ne_zero.mpr hx.ne'), ← sub_eq_add_neg, sub_right_comm]
  _ = (∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s - 1)) • P.f₀
        - P.ε • (∫ (x : ℝ) in Ioc 0 1, (x : ℂ) ^ (s - P.k - 1)) • P.g₀ := by
    rw [integral_sub, integral_smul, integral_smul_const, integral_smul_const]
    · apply Integrable.smul_const
      rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re1
    · refine (Integrable.smul_const ?_ _).smul _
      rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_cpow' h_re2
  _ = _ := by
      simp_rw [← intervalIntegral.integral_of_le zero_le_one]
      match_scalars
      · simp [integral_cpow (.inl h_re1), zero_cpow (show s ≠ 0 by grind [P.hk, zero_re])]
      · simp [integral_cpow (.inl h_re2), zero_cpow (show s - P.k ≠ 0 by grind [P.hk, ofReal_re])]
        grind
/-!
## Main theorems on weak FE-pairs
-/

/-- An entire function which differs from the Mellin transform of `f - f₀`, where defined, by a
correction term of the form `A / s + B / (k - s)`. -/
/-
**WeakFEPair.** 是 Mathlib 中的一个定义，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An entire function which differs from the Mellin transform of `f - f₀`, where de
fined, by a
correction term of the form `A / s + B / (k - s)`.
-/
def Λ₀ : ℂ → E := mellin P.f_modif

/-- A meromorphic function which agrees with the Mellin transform of `f - f₀` where defined -/
/-
**WeakFEPair.** 是 Mathlib 中的一个定义，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A meromorphic function which agrees with the Mellin transform of `f - f₀` where 
defined
-/
def Λ (s : ℂ) : E := P.Λ₀ s - (1 / s) • P.f₀ - (P.ε / (P.k - s)) • P.g₀
/-
**WeakFEPair.** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma Λ₀_eq (s : ℂ) : P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ + (P.ε / (P.k - s)) • P.g₀ := by
  unfold Λ Λ₀
  abel
/-
**WeakFEPair.symm_** 是 Mathlib 中的一个引理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_Λ₀_eq (s : ℂ) :
    P.symm.Λ₀ s = P.symm.Λ s + (1 / s) • P.g₀ + (P.ε⁻¹ / (P.k - s)) • P.f₀ := by
  simp [P.symm.Λ₀_eq]
/-
**WeakFEPair.differentiable_** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiable_Λ₀ : Differentiable ℂ P.Λ₀ :=
  P.isStrongFEPair_toStrongFEPair.differentiable_mellin
/-
**WeakFEPair.differentiableAt_** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem differentiableAt_Λ {s : ℂ} (hs : s ≠ 0 ∨ P.f₀ = 0) (hs' : s ≠ P.k ∨ P.g₀ = 0) :
    DifferentiableAt ℂ P.Λ s := by
  refine ((P.differentiable_Λ₀ s).sub ?_).sub ?_
  · rcases hs with hs | hs
    · fun_prop
    · simp [hs]
  · rcases hs' with hs' | hs'
    · fun_prop (disch := grind)
    · simp [hs']

/-- Relation between `Λ s` and the Mellin transform of `f - f₀`, where the latter is defined.
(Compare `IsStrongFEPair.hasMellin` for a version without assumptions on `s.re` assuming the
FE-pair is strong.) -/
/-
**WeakFEPair.hasMellin** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
形式化陈述：hasMellin [CompleteSpace E] {s : Complex} (hs : P.k < s.re) : HasMellin (P
.f · - P.f₀) s (P.Λ s)
参数：hs : P.k < s.re。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NoMaxOrder.exists_gt`：∀ {α : Type u_3} {inst : LT α} [self : NoMaxOrder 
α] (a : α), ∃ b, a < b
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `mellinConvergent_of_isBigO_rpow`：mellinConvergent_of_isBigO_rpow [Normed
Space Complex E] {a b : Real} {f : Real -> E} {s : Complex} (hfc : LocallyIntegr
ableOn f <| Ioi 0) (h…
· 使用定理 `MeasureTheory.LocallyIntegrableOn.sub`：∀ {X : Type u_1} {E : Type u_6} [
inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2 : NormedAddCommG
roup E]   {μ : MeasureTheor…
· 使用定理 `WeakFEPair.hf_int`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E),   MeasureTheory.LocallyIntegrableOn 
self.f …
· 使用定理 `MeasureTheory.locallyIntegrableOn_const`：locallyIntegrableOn_const [IsLo
callyFiniteMeasure μ] (c : E) : LocallyIntegrableOn (fun _ => c) s μ
· 使用定理 `WeakFEPair.hf_top`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_
1 : NormedSpace ℂ E] (self : WeakFEPair E) (r : ℝ),   (fun x => self.f x - self.
f₀) =O[…
· 使用引理 `WeakFEPair.hf_zero'`：hf_zero' : (fun x : Real => P.f x - P.f₀) =O[𝓝[>] 0
] (· ^ (-P.k))
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.AbstractFuncEq.0.IsStrongFEPair.me
llinConvergent`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedS
pace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P → ∀ (s : ℂ), MellinConverge…
· 使用引理 `WeakFEPair.isStrongFEPair_toStrongFEPair`：isStrongFEPair_toStrongFEPair 
: IsStrongFEPair P.toStrongFEPair where hf₀
· 使用引理 `WeakFEPair.f_modif_aux2`：f_modif_aux2 [CompleteSpace E] {s : Complex} (h
s : P.k < re s) : mellin (fun x => P.f_modif x - P.f x + P.f₀) s = (1 / s) • P.f
₀ + (P.ε / (P…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `hasMellin_sub`：hasMellin_sub {f g : Real -> E} {s : Complex} (hf : Melli
nConvergent f s) (hg : MellinConvergent g s) : HasMellin (fun t => f t - g t) s 
(me…

--- 原说明 ---
Relation between `Λ s` and the Mellin transform of `f - f₀`, where the latter is
 defined.
(Compare `IsStrongFEPair.hasMellin` for a version without assumptions on `s.re` 
assuming the
FE-pair is strong.)
-/
theorem hasMellin [CompleteSpace E]
    {s : ℂ} (hs : P.k < s.re) : HasMellin (P.f · - P.f₀) s (P.Λ s) := by
  have hc1 : MellinConvergent (P.f · - P.f₀) s :=
    let ⟨_, ht⟩ := exists_gt s.re
    mellinConvergent_of_isBigO_rpow (P.hf_int.sub (locallyIntegrableOn_const _)) (P.hf_top _) ht
      P.hf_zero' hs
  refine ⟨hc1, ?_⟩
  have hc2 : MellinConvergent P.f_modif s :=
    P.isStrongFEPair_toStrongFEPair.mellinConvergent s
  have hc3 : mellin (fun x ↦ f_modif P x - f P x + P.f₀) s =
    (1 / s) • P.f₀ + (P.ε / (↑P.k - s)) • P.g₀ := P.f_modif_aux2 hs
  have := (hasMellin_sub hc2 hc1).2
  simp only [Λ, Λ₀] at *
  grind

/-- Functional equation formulated for `Λ₀`. -/
/-
**WeakFEPair.functional_equation** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
形式化陈述：functional_equation (s : Complex) : P.Λ (P.k - s) = P.ε • P.symm.Λ s
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `WeakFEPair.functional_equation₀`：functional_equation₀ (s : Complex) : P.
Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeakFEPair.Λ₀_eq`：Λ₀_eq (s : Complex) : P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ 
+ (P.ε / (P.k - s)) • P.g₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeakFEPair.symm_Λ₀_eq`：symm_Λ₀_eq (s : Complex) : P.symm.Λ₀ s = P.symm.Λ
 s + (1 / s) • P.g₀ + (P.ε⁻¹ / (P.k - s)) • P.f₀
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `WeakFEPair.hε`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), self.ε ≠ 0
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_const`：eq_cons_const [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : r = 0) (h2 
: l.eval = n) : ((r, m) ::ᵣ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation formulated for `Λ₀`.
-/
theorem functional_equation₀ (s : ℂ) : P.Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s :=
  P.toStrongFEPair.functional_equation_aux s

/-- Functional equation formulated for `Λ`. -/
/-
**WeakFEPair.functional_equation** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
形式化陈述：functional_equation (s : Complex) : P.Λ (P.k - s) = P.ε • P.symm.Λ s
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_of_eq`：eq_of_eq [Add α] [IsRightCanc
elAdd α] (p : (a : α) = b) (H : a' + b = b' + a) : a' = b'
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Mathlib.Tactic.LinearCombination.add_eq_eq`：add_eq_eq [Add α] (p₁ : (a₁ 
: α) = b₁) (p₂ : a₂ = b₂) : a₁ + a₂ = b₁ + b₂
· 使用定理 `WeakFEPair.functional_equation₀`：functional_equation₀ (s : Complex) : P.
Λ₀ (P.k - s) = P.ε • P.symm.Λ₀ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WeakFEPair.Λ₀_eq`：Λ₀_eq (s : Complex) : P.Λ₀ s = P.Λ s + (1 / s) • P.f₀ 
+ (P.ε / (P.k - s)) • P.g₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `WeakFEPair.symm_Λ₀_eq`：symm_Λ₀_eq (s : Complex) : P.symm.Λ₀ s = P.symm.Λ
 s + (1 / s) • P.g₀ + (P.ε⁻¹ / (P.k - s)) • P.f₀
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `WeakFEPair.hε`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : 
NormedSpace ℂ E] (self : WeakFEPair E), self.ε ≠ 0
· 使用定理 `Mathlib.Tactic.LinearCombination.eq_rearrange`：∀ {G : Type u_3} [inst : 
AddGroup G] {a b : G}, a - b = 0 → a = b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₃`：add_eq_eval₃ [Semiring R] [AddCom
mMonoid M] [Module R M] {a₁ : R × M} (a₂ : R × M) {l₁ l₂ l : NF R M} (h : (a₁ ::
ᵣ l₁).eval + l₂.eval = l.ev…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_const`：eq_cons_const [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : r = 0) (h2 
: l.eval = n) : ((r, m) ::ᵣ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
（共 74 条，此处仅展示前 30 条）

--- 原说明 ---
Functional equation formulated for `Λ`.
-/
theorem functional_equation (s : ℂ) :
    P.Λ (P.k - s) = P.ε • P.symm.Λ s := by
  linear_combination (norm := module) P.functional_equation₀ s - P.Λ₀_eq (P.k - s)
    + congr(P.ε • $(P.symm_Λ₀_eq s)) + congr(($(mul_inv_cancel₀ P.hε) / (P.k - s)) • P.f₀)

/-- The residue of `Λ` at `s = k` is equal to `ε • g₀`. -/
/-
**WeakFEPair.** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue of `Λ` at `s = k` is equal to `ε • g₀`.
-/
theorem Λ_residue_k :
    Tendsto (fun s : ℂ ↦ (s - P.k) • P.Λ s) (𝓝[≠] P.k) (𝓝 (P.ε • P.g₀)) := by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (P.ε • P.g₀) = 𝓝 (0 - 0 - -P.ε • P.g₀))]
  refine ((Tendsto.sub ?_ ?_).mono_left nhdsWithin_le_nhds).sub ?_
  · rw [(by simp : 𝓝 0 = 𝓝 ((P.k - P.k : ℂ) • P.Λ₀ P.k))]
    apply ((continuous_sub_right _).smul P.differentiable_Λ₀.continuous).tendsto
  · rw [(by simp : 𝓝 0 = 𝓝 ((P.k - P.k : ℂ) • (1 / P.k : ℂ) • P.f₀))]
    refine (continuous_sub_right _).continuousAt.smul (ContinuousAt.smul ?_ continuousAt_const)
    have := ofReal_ne_zero.mpr P.hk.ne'
    fun_prop
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ P.k)
    match_scalars
    grind

/-- The residue of `Λ` at `s = 0` is equal to `-f₀`. -/
/-
**WeakFEPair.** 是 Mathlib 中的一个定理，位于命名空间 `WeakFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The residue of `Λ` at `s = 0` is equal to `-f₀`.
-/
theorem Λ_residue_zero : Tendsto (fun s ↦ s • P.Λ s) (𝓝[≠] 0) (𝓝 (-P.f₀)) := by
  simp_rw [Λ, smul_sub, (by simp : 𝓝 (-P.f₀) = 𝓝 (((0 : ℂ) • P.Λ₀ 0) - P.f₀ - 0))]
  refine ((Tendsto.mono_left ?_ nhdsWithin_le_nhds).sub ?_).sub ?_
  · exact (continuous_id.smul P.differentiable_Λ₀.continuous).tendsto _
  · refine (tendsto_const_nhds.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s (hs : s ≠ 0)
    match_scalars
    grind
  · rw [show 𝓝 0 = 𝓝 ((0 : ℂ) • (P.ε / (P.k - 0 : ℂ)) • P.g₀) by rw [zero_smul]]
    exact (continuousAt_id.smul ((continuousAt_const.div ((continuous_sub_left _).continuousAt)
      (by simpa using P.hk.ne')).smul continuousAt_const)).mono_left nhdsWithin_le_nhds

end WeakFEPair

namespace IsStrongFEPair
/-!
## Main theorems on strong FE-pairs
-/

open WeakFEPair

variable {P : WeakFEPair E} (hP : IsStrongFEPair P)
include hP

/-- For strong FE-pairs, `P.Λ` is everywhere equal to the Mellin transform of `P.f`. -/
/-
**IsStrongFEPair.** 是 Mathlib 中的一个引理，位于命名空间 `IsStrongFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For strong FE-pairs, `P.Λ` is everywhere equal to the Mellin transform of `P.f`.
-/
lemma Λ_eq : P.Λ = mellin P.f := by
  ext s
  simp only [mellin, Λ, Λ₀, f_modif, hP.hf₀, sub_zero, hP.hg₀, smul_zero]
  refine integral_congr_ae <| (ae_restrict_iff' measurableSet_Ioi).mpr ?_
  filter_upwards [compl_mem_ae_iff.mpr (Subsingleton.measure_zero (s := {1}) (by simp) _)]
    with t (ht₁ : t ≠ 1) (ht₀ : 0 < t)
  by_cases ht : t < 1 <;> [rw [add_comm] ; skip] <;>
  rw [Pi.add_apply, indicator_of_mem (by grind), indicator_of_notMem (by grind), add_zero]
/-
**IsStrongFEPair.symm_** 是 Mathlib 中的一个引理，位于命名空间 `IsStrongFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_Λ_eq : P.symm.Λ = mellin P.g := hP.symm.Λ_eq

/-- The Mellin transform of `f` is well-defined and equal to `P.Λ s`, for all `s`. -/
/-
**IsStrongFEPair.hasMellin** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongFEPair`。
形式化陈述：hasMellin (s : Complex) : HasMellin P.f s (P.Λ s)
参数：s : Complex。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.NumberTheory.LSeries.AbstractFuncEq.0.IsStrongFEPair.me
llinConvergent`：∀ {E : Type u_1} [inst : NormedAddCommGroup E] [inst_1 : NormedS
pace ℂ E] {P : WeakFEPair E},   IsStrongFEPair P → ∀ (s : ℂ), MellinConverge…
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsStrongFEPair.Λ_eq`：Λ_eq : P.Λ = mellin P.f

--- 原说明 ---
The Mellin transform of `f` is well-defined and equal to `P.Λ s`, for all `s`.
-/
theorem hasMellin (s : ℂ) : HasMellin P.f s (P.Λ s) :=
  ⟨hP.mellinConvergent s, congr_fun hP.Λ_eq.symm s⟩

/-- If `P` is a strong FE pair, then `P.Λ` is entire. -/
/-
**IsStrongFEPair.differentiable_** 是 Mathlib 中的一个定理，位于命名空间 `IsStrongFEPair`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `P` is a strong FE pair, then `P.Λ` is entire.
-/
theorem differentiable_Λ : Differentiable ℂ P.Λ :=
  hP.Λ_eq ▸ hP.differentiable_mellin

end IsStrongFEPair

