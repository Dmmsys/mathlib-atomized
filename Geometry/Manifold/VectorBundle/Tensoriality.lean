/-
Copyright (c) 2025 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Michael Rothgang, Heather Macbeth
-/
module

public import Mathlib.Geometry.Manifold.VectorBundle.MDifferentiable
public import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
public import Mathlib.Topology.Algebra.Module.TransferInstance
public import Mathlib.Topology.VectorBundle.FiniteDimensional
import Mathlib.Geometry.Manifold.Notation
import Mathlib.Geometry.Manifold.VectorBundle.LocalFrame

/-!
# The tensoriality criterion

Given vector bundles `V` and `W` over a manifold `M`, one can construct a section of the hom-bundle
`Π x, V x →L[𝕜] W x` from a *tensorial* operation sending sections of `V` to sections of `W`.
This file provides this construction.

In fact, we define tensoriality, and provide the above criterion, in slightly greater generality:
for operations sending sections of `V` to a vector space `A` (which in the above application is the
fibre `W x`), the construction produces a continuous linear map `V x →L[𝕜] A`.

## Main definitions

* `TensorialAt`: Propositional structure stating that an operation on sections of a vector bundle
  `V` is tensorial.

* `TensorialAt.mkHom`: An operation on sections of `V` which is tensorial at `x` defines a
  continuous linear map out of `V x`.

* `TensorialAt.mkHom₂`: An operation on sections of `V` and `V'` which is tensorial at `x` in both
  arguments defines a continuous bilinear map out of `V x` and `V' x`.

-/

open Bundle FiberBundle Topology Module

open scoped Manifold ContDiff

@[expose] public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

variable
  (F : Type*) [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x : M, TopologicalSpace (V x)]
  [FiberBundle F V]

variable
  (F' : Type*) [NormedAddCommGroup F'] [NormedSpace 𝕜 F']
  {V' : M → Type*} [TopologicalSpace (TotalSpace F' V')]
  [∀ x, AddCommGroup (V' x)] [∀ x, Module 𝕜 (V' x)] [∀ x : M, TopologicalSpace (V' x)]
  [FiberBundle F' V']

variable {A : Type*} [AddCommGroup A] [Module 𝕜 A]

/-- An operation `Φ` on sections of a vector bundle `V` over `M` is *tensorial* at `x : M`, if it
respects addition and scalar multiplication by germs of differentiable functions at `f`. -/
/-
**TensorialAt** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {H : Type u_3} →             [inst_3 : TopologicalSpace H] →          
     ModelWithCorners 𝕜 E H →                 {M : Type u_4} →                  
 [inst_4 : TopologicalSpace M] →                     [ChartedSpace H M] →       
                (F : Type u_5) →                         [inst_6 : NormedAddComm
Group F] →                           [NormedSpace 𝕜 F] →                        
     {V : M → Type u_6} →                               [inst_8 : TopologicalSpa
ce (Bundle.TotalSpace F V)] →                                 [inst_9 : (x : M) 
→ AddCommGroup (V x)] →                                   [(x : M) → _root_.Modu
le 𝕜 (V x)] →                                     [inst_11 : (x : M) → Topologic
alSpace (V x)] →                                       [FiberBundle F V] →      
                                   {A : Type u_9} →                             
              [inst_13 : AddCommGroup A] →                                      
       [_root_.Module 𝕜 A] → (((x : M) → V x) → A) → M → Prop
参数：F : Type u_5；Bundle.TotalSpace F V；x : M；V x；x : M；V x；x : M；V x；((x : M) → V
 x) → A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An operation `Φ` on sections of a vector bundle `V` over `M` is *tensorial* at `
x : M`, if it
respects addition and scalar multiplication by germs of differentiable functions
 at `f`.
-/
structure TensorialAt (Φ : (Π x : M, V x) → A) (x : M) : Prop where
  smul : ∀ {f : M → 𝕜} {σ : Π x : M, V x}, MDiffAt f x → MDiffAt (T% σ) x → Φ (f • σ) = f x • Φ σ
  add : ∀ {σ σ'}, MDiffAt (T% σ) x → MDiffAt (T% σ') x → Φ (σ + σ') = Φ σ + Φ σ'

variable {Φ : (Π x : M, V x) → A} {x : M}
variable {I F F'}

namespace TensorialAt

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
only on the germ of the section at `x`.

This is later superseded by `TensorialAt.pointwise`, showing that `Φ` depends only on the value at
`x` itself. -/
/-
**TensorialAt.** 是 Mathlib 中的一个定理，位于命名空间 `TensorialAt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, the
n it depends
only on the germ of the section at `x`.

This is later superseded by `TensorialAt.pointwise`, showing that `Φ` depends on
ly on the value at
`x` itself.
-/
protected theorem «local» (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : ∀ᶠ x' in 𝓝 x, σ x' = σ' x') :
    Φ σ = Φ σ' := by
  classical
  -- Introduce the indicator function of a neighbourhood `t` of `x` on which equality holds,
  -- and cut off the two sections `σ` and `σ'` using this indicator function.
  let ψ (x' : M) : 𝕜 := if σ x' = σ' x' then 1 else 0
  have hψx : ψ x = 1 := by simp [ψ, hσσ'.self_of_nhds]
  have (x' : M) : (ψ • σ) x' = (ψ • σ') x' := by
    dsimp [ψ]
    split_ifs with hx' <;> simp [hx']
  have hψ' : MDiffAt ψ x := by
    have : MDiffAt (fun (_x : M) ↦ (1 : 𝕜)) x := mdifferentiableAt_const
    exact this.congr_of_eventuallyEq (hσσ'.mono fun x' hx' ↦ by simp [ψ, hx'])
  calc Φ σ
    _ = Φ (ψ • σ) := by simp [hΦ.smul hψ' hσ, hψx]
    _ = Φ (ψ • σ') := by rw [funext this]
    _ = Φ σ' := by simp [hΦ.smul hψ' hσ', hψx]

variable [VectorBundle 𝕜 F V] [VectorBundle 𝕜 F' V']

/-- A tensorial operation on sections of a vector bundle respects zero (since it respects scalar
multiplication). -/
/-
**TensorialAt.zero** 是 Mathlib 中的一个定理，位于命名空间 `TensorialAt`。
形式化陈述：zero (hΦ : TensorialAt I F Φ x) : Φ 0 = 0
参数：hΦ : TensorialAt I F Φ x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `TensorialAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `mdifferentiableAt_const`：mdifferentiableAt_const : MDiffAt (fun _ : M =>
 c) x
· 使用定理 `Bundle.mdifferentiable_zeroSection`：mdifferentiable_zeroSection : MDiff 
(zeroSection F E)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0

--- 原说明 ---
A tensorial operation on sections of a vector bundle respects zero (since it res
pects scalar
multiplication).
-/
theorem zero (hΦ : TensorialAt I F Φ x) : Φ 0 = 0 := by
  calc
    Φ 0 = Φ ((0 : M → 𝕜) • (0 : Π x, V x)) := by simp
    _   = 0 • Φ 0 := hΦ.smul mdifferentiableAt_const (mdifferentiable_zeroSection ..)
    _   = 0 := by simp

/-- A tensorial operation on sections of a vector bundle respects sums (since it respects binary
addition). -/
/-
**TensorialAt.sum** 是 Mathlib 中的一个定理，位于命名空间 `TensorialAt`。
形式化陈述：sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι -> Π x : 
M, V x) (hσ : forall i in s, MDiffAt (T% (σ i)) x) : Φ (fun x' => ∑ i in s, σ i 
x') = ∑ i in s, Φ (σ i)
参数：hΦ : TensorialAt I F Φ x；σ : ι -> Π x : M, V x；hσ : forall i in s, MDiffAt (T
% (σ i)) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `TensorialAt.zero`：zero (hΦ : TensorialAt I F Φ x) : Φ 0 = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `TensorialAt.add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E 
: Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : Ty
pe u_…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `MDifferentiableAt.sum_section`：MDifferentiableAt.sum_section {ι : Type*}
 {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B} (hs : forall i in s, MDiffAt 
(T% (t i ·)) x₀) : …

--- 原说明 ---
A tensorial operation on sections of a vector bundle respects sums (since it res
pects binary
addition).
-/
theorem sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset ι} (σ : ι → Π x : M, V x)
    (hσ : ∀ i ∈ s, MDiffAt (T% (σ i)) x) :
    Φ (fun x' ↦ ∑ i ∈ s, σ i x') = ∑ i ∈ s, Φ (σ i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty]
      exact hΦ.zero
  | insert a s ha h =>
      simp only [Finset.mem_insert, forall_eq_or_imp] at hσ
      simp only [Finset.sum_insert ha, ← h hσ.2]
      exact hΦ.add (hσ.1) (.sum_section hσ.2)

variable [CompleteSpace 𝕜] [FiniteDimensional 𝕜 F] [FiniteDimensional 𝕜 F']
  [ContMDiffVectorBundle 1 F V I] [ContMDiffVectorBundle 1 F' V' I]

/-- If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, then it depends
only on the value of the section at `x`. -/
/-
**TensorialAt.pointwise** 是 Mathlib 中的一个引理，位于命名空间 `TensorialAt`。
形式化陈述：pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x} (hσ : MDiffAt (
T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) : Φ σ = Φ σ'
参数：hΦ : TensorialAt I F Φ x；hσ : MDiffAt (T% σ) x；hσ' : MDiffAt (T% σ') x；hσσ' :
 σ x = σ' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_localFrame_of_mem`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `mdifferentiableAt_localFrameCoeff`：mdifferentiableAt_localFrameCoeff (hx
e : x in e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) : MDiffAt ((LinearMap.piAppl
y (e.localFrameCoeff I …
· 使用定理 `TensorialAt.local`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : 
Type u_…
· 使用引理 `MDifferentiableAt.sum_section`：MDifferentiableAt.sum_section {ι : Type*}
 {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B} (hs : forall i in s, MDiffAt 
(T% (t i ·)) x₀) : …
· 使用引理 `MDifferentiableAt.smul_section`：MDifferentiableAt.smul_section (hf : MDi
ffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀
· 使用引理 `Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul`：eventuall
y_eq_localFrame_sum_coeff_smul [Fintype ι] (hxe : x in e.baseSet) : forallᶠ x' i
n 𝓝 x, s x' = ∑ i, e.localFrameCoeff I b i x' (s x'…
· 使用定理 `TensorialAt.sum`：sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset 
ι} (σ : ι -> Π x : M, V x) (hσ : forall i in s, MDiffAt (T% (σ i)) x) : Φ (fun x
' => …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `TensorialAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the operation `Φ` on sections of a vector bundle `V` is tensorial at `x`, the
n it depends
only on the value of the section at `x`.
-/
lemma pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) :
    Φ σ = Φ σ' := by
  -- Select a local frame `s` for the bundle `V` near `x`,
  -- and let `c` be the family of linear maps evaluating the coefficients of a section relative to
  -- this frame
  let t := trivializationAt F V x
  have x_mem : x ∈ t.baseSet := FiberBundle.mem_baseSet_trivializationAt F V x
  let b := Basis.ofVectorSpace 𝕜 F
  let s := t.localFrame b
  let c := t.localFrameCoeff I b
  have hs (i) : MDiffAt (T% (s i)) x :=
    (contMDiffAt_localFrame_of_mem 1 _ b i x_mem).mdifferentiableAt (by simp)
  have hc {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) (i) :
      MDiffAt (LinearMap.piApply (c i) σ) x :=
    mdifferentiableAt_localFrameCoeff b x_mem hσ i
  -- By the locality of the operation `(Φ · x)`, its value on `σ` agrees with the value of `Φ` on
  -- the expansion of `σ` into coefficients relative to the frame.
  have hΦ_eq {σ : (x : M) → V x} (hσ : MDiffAt (T% σ) x) :
      Φ σ = Φ (fun x' ↦ ∑ i, c i x' (σ x') • s i x') :=
    hΦ.local hσ
      (.sum_section fun i _ ↦ (hc hσ i).smul_section (hs i))
      (t.eventually_eq_localFrame_sum_coeff_smul b x_mem)
  -- Now evaluate using the tensoriality properties.
  rw [hΦ_eq hσ, hΦ_eq hσ', hΦ.sum, hΦ.sum]
  · congr! 1 with i
    calc Φ ((LinearMap.piApply (c i) σ) • (s i))
        = c i x (σ x) • Φ (s i) := hΦ.smul (hc hσ i) (hs i)
      _ = c i x (σ' x) • Φ (s i) := by rw [hσσ']
      _ = Φ ((LinearMap.piApply (c i) σ') • (s i)) :=
          hΦ.smul (hc hσ' i) (hs i) |>.symm
  · exact fun i _ ↦ (hc hσ' i).smul_section (hs i)
  · exact fun i _ ↦ (hc hσ i).smul_section (hs i)

/-- If the operation `Φ` on sections of vector bundles `V` and `V'` is tensorial at `x` in each
argument, then it depends only on the value of the sections at `x`. -/
/-
**TensorialAt.pointwise** 是 Mathlib 中的一个引理，位于命名空间 `TensorialAt`。
形式化陈述：pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x : M, V x} (hσ : MDiffAt (
T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) : Φ σ = Φ σ'
参数：hΦ : TensorialAt I F Φ x；hσ : MDiffAt (T% σ) x；hσ' : MDiffAt (T% σ') x；hσσ' :
 σ x = σ' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FiberBundle.mem_baseSet_trivializationAt`：mem_baseSet_trivializationAt :
 b in (trivializationAt F E b).baseSet
· 使用定理 `instMemTrivializationAtlasTrivializationAt`：∀ {B : Type u_2} {F : Type u
_3} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F] {E : B → Type u_5}
   [inst_2 : TopologicalSpace (B…
· 使用定理 `ContMDiffAt.mdifferentiableAt`：ContMDiffAt.mdifferentiableAt (hf : CMDif
fAt n f x) (hn : n != 0) : MDiffAt f x
· 使用定理 `contMDiffAt_localFrame_of_mem`：∀ {𝕜 : Type u_1} [inst : NontriviallyNorm
edField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpac
e 𝕜 E] {H : Type u_…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `mdifferentiableAt_localFrameCoeff`：mdifferentiableAt_localFrameCoeff (hx
e : x in e.baseSet) (hs : MDiffAt (T% s) x) (i : ι) : MDiffAt ((LinearMap.piAppl
y (e.localFrameCoeff I …
· 使用定理 `TensorialAt.local`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {
E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : 
Type u_…
· 使用引理 `MDifferentiableAt.sum_section`：MDifferentiableAt.sum_section {ι : Type*}
 {s : Finset ι} {t : ι -> (x : B) -> E x} {x₀ : B} (hs : forall i in s, MDiffAt 
(T% (t i ·)) x₀) : …
· 使用引理 `MDifferentiableAt.smul_section`：MDifferentiableAt.smul_section (hf : MDi
ffAt f x₀) (hs : MDiffAt (T% s) x₀) : MDiffAt (T% (f • s)) x₀
· 使用引理 `Bundle.Trivialization.eventually_eq_localFrame_sum_coeff_smul`：eventuall
y_eq_localFrame_sum_coeff_smul [Fintype ι] (hxe : x in e.baseSet) : forallᶠ x' i
n 𝓝 x, s x' = ∑ i, e.localFrameCoeff I b i x' (s x'…
· 使用定理 `TensorialAt.sum`：sum (hΦ : TensorialAt I F Φ x) {ι : Type*} {s : Finset 
ι} (σ : ι -> Π x : M, V x) (hσ : forall i in s, MDiffAt (T% (σ i)) x) : Φ (fun x
' => …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `TensorialAt.smul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E
 : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {H : T
ype u_…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the operation `Φ` on sections of vector bundles `V` and `V'` is tensorial at 
`x` in each
argument, then it depends only on the value of the sections at `x`.
-/
lemma pointwise₂
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ ·) x)
    {σ σ' : Π x : M, V x} {τ τ' : Π x : M, V' x}
    (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x)
    (hτ : MDiffAt (T% τ) x) (hτ' : MDiffAt (T% τ') x)
    (hσσ' : σ x = σ' x) (hττ' : τ x = τ' x) :
    Φ σ τ = Φ σ' τ' := by
  trans Φ σ' τ
  · exact (hΦ₁ _ hτ).pointwise hσ hσ' hσσ'
  · exact (hΦ₂ _ hσ').pointwise hτ hτ' hττ'

variable [TopologicalSpace A] [IsTopologicalAddGroup A] [ContinuousSMul 𝕜 A]

/-- Given an `A`-valued operation `Φ` on sections of a vector bundle `V` which is tensorial at `x`,
the construction `TensorialAt.mkHom` provides the associated continuous linear map `V x →L[𝕜] A`. -/
/-
**TensorialAt.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorialAt`。
形式化陈述：mkHom -- `Φ` and `x` explicit to make it easier to generate the side condi
tion at point of use (Φ : (Π x : M, V x) -> A) (x : M) (hΦ : TensorialAt I F Φ x
) : V x ->L[𝕜] A
参数：Φ : (Π x : M, V x) -> A；x : M；hΦ : TensorialAt I F Φ x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundle.finiteDimensional`：∀ (R : Type u_1) {B : Type u_2} (F : Typ
e u_3) (E : B → Type u_4) [inst : NontriviallyNormedField R]   [inst_1 : Topolog
icalSpace B] [inst_2…

--- 原说明 ---
Given an `A`-valued operation `Φ` on sections of a vector bundle `V` which is te
nsorial at `x`,
the construction `TensorialAt.mkHom` provides the associated continuous linear m
ap `V x →L[𝕜] A`.
-/
noncomputable def mkHom
    -- `Φ` and `x` explicit to make it easier to generate the side condition at point of use
    (Φ : (Π x : M, V x) → A) (x : M) (hΦ : TensorialAt I F Φ x) :
    V x →L[𝕜] A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  LinearMap.toContinuousLinearMap {
    toFun v := Φ (extend F v)
    map_add' v₁ v₂ := by
      rw [← hΦ.add (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)]
      apply hΦ.pointwise (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      simp
    map_smul' c v := by
      dsimp
      rw [← hΦ.smul (f := fun _ ↦ c) (mdifferentiable_const ..) (mdifferentiableAt_extend ..)]
      apply hΦ.pointwise (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
      simp }
/-
**TensorialAt.mkHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `TensorialAt`。
形式化陈述：mkHom_apply {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F (Φ ·) x) {
σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) : mkHom Φ x hΦ (σ x) = Φ σ
参数：Π x : M, V x；hΦ : TensorialAt I F (Φ ·) x；hσ : MDiffAt (T% σ) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `TensorialAt.pointwise`：pointwise (hΦ : TensorialAt I F Φ x) {σ σ' : Π x 
: M, V x} (hσ : MDiffAt (T% σ) x) (hσ' : MDiffAt (T% σ') x) (hσσ' : σ x = σ' x) 
: Φ σ = Φ σ…
· 使用引理 `FiberBundle.mdifferentiableAt_extend`：mdifferentiableAt_extend {x : M} (
σ₀ : V x) : MDiffAt (T% (extend F σ₀)) x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FiberBundle.extend_apply_self`：∀ {B : Type u_2} (F : Type u_3) {E : B → 
Type u_5} [inst : TopologicalSpace B] [inst_1 : TopologicalSpace F]   [inst_2 : 
(x : B) → Topologic…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem mkHom_apply {Φ : (Π x : M, V x) → A} {x} (hΦ : TensorialAt I F (Φ ·) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) :
    mkHom Φ x hΦ (σ x) = Φ σ :=
  hΦ.pointwise (mdifferentiableAt_extend ..) hσ (by simp)
/-
**TensorialAt.mkHom_apply_eq_extend** 是 Mathlib 中的一个定理，位于命名空间 `TensorialAt`。
形式化陈述：mkHom_apply_eq_extend {Φ : (Π x : M, V x) -> A} {x} (hΦ : TensorialAt I F 
Φ x) (σ : V x) : mkHom Φ x hΦ σ = Φ (extend F σ)
参数：Π x : M, V x；hΦ : TensorialAt I F Φ x；σ : V x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mkHom_apply_eq_extend {Φ : (Π x : M, V x) → A} {x} (hΦ : TensorialAt I F Φ x) (σ : V x) :
    mkHom Φ x hΦ σ = Φ (extend F σ) :=
  rfl

/-- Given an `A`-valued operation `Φ` on sections of vector bundles `V` and `V'` which is tensorial
at `x` in each argument, the construction `TensorialAt.mkHom₂` provides the associated continuous
linear map `V x →L[𝕜] V' x →L[𝕜] A`. -/
/-
**TensorialAt.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorialAt`。
形式化陈述：mkHom -- `Φ` and `x` explicit to make it easier to generate the side condi
tion at point of use (Φ : (Π x : M, V x) -> A) (x : M) (hΦ : TensorialAt I F Φ x
) : V x ->L[𝕜] A
参数：Φ : (Π x : M, V x) -> A；x : M；hΦ : TensorialAt I F Φ x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundle.finiteDimensional`：∀ (R : Type u_1) {B : Type u_2} (F : Typ
e u_3) (E : B → Type u_4) [inst : NontriviallyNormedField R]   [inst_1 : Topolog
icalSpace B] [inst_2…

--- 原说明 ---
Given an `A`-valued operation `Φ` on sections of vector bundles `V` and `V'` whi
ch is tensorial
at `x` in each argument, the construction `TensorialAt.mkHom₂` provides the asso
ciated continuous
linear map `V x →L[𝕜] V' x →L[𝕜] A`.
-/
noncomputable def mkHom₂
    -- `Φ` and `x` explicit to make it easier to generate the side conditions at point of use
    (Φ : (Π x : M, V x) → (Π x : M, V' x) → A) (x : M)
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ) x) :
    V x →L[𝕜] V' x →L[𝕜] A :=
  have : T2Space (V x) := FiberBundle.t2Space F V x
  have : FiniteDimensional 𝕜 (V x) := VectorBundle.finiteDimensional 𝕜 F V x
  have : T2Space (V' x) := FiberBundle.t2Space F' V' x
  have : FiniteDimensional 𝕜 (V' x) := VectorBundle.finiteDimensional 𝕜 F' V' x
  have : IsTopologicalAddGroup (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).toContinuousAddEquiv.isTopologicalAddGroup
  have : IsTopologicalAddGroup (V' x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F' V' x).toContinuousAddEquiv.isTopologicalAddGroup
  have (x : M) : ContinuousSMul 𝕜 (V x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F V x).continuousSMul
  have (x : M) : ContinuousSMul 𝕜 (V' x) :=
    (VectorBundle.continuousLinearEquivAt 𝕜 F' V' x).continuousSMul
  have H : IsBilinearMap 𝕜
    (fun (v : V x) (w : V' x) ↦ Φ (extend F v) (extend F' w)) :=
  { add_left v₁ v₂ w := by
      rw [← (hΦ₁ _ (mdifferentiableAt_extend ..)).add (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) _
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) _ rfl
      · exact mdifferentiableAt_add_section (mdifferentiableAt_extend ..)
          (mdifferentiableAt_extend ..)
      · simp
    smul_left c v w := by
      rw [← (hΦ₁ _ (mdifferentiableAt_extend ..)).smul (f := fun _ ↦ c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..))
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      · simp
      · rfl
    add_right v w₁ w₂ := by
      rw [← (hΦ₂ _ (mdifferentiableAt_extend ..)).add (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_add_section (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..)
      · rfl
      · simp
    smul_right c v w := by
      rw [← (hΦ₂ _ (mdifferentiableAt_extend ..)).smul (f := fun _ ↦ c) (mdifferentiable_const ..)
        (mdifferentiableAt_extend ..)]
      apply TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..)
        (mdifferentiableAt_extend ..) (mdifferentiableAt_extend ..) <|
        mdifferentiableAt_const.smul_section (mdifferentiableAt_extend ..)
      · rfl
      · simp }
  H.toLinearMap.toContinuousBilinearMap
/-
**TensorialAt.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorialAt`。
形式化陈述：mkHom -- `Φ` and `x` explicit to make it easier to generate the side condi
tion at point of use (Φ : (Π x : M, V x) -> A) (x : M) (hΦ : TensorialAt I F Φ x
) : V x ->L[𝕜] A
参数：Φ : (Π x : M, V x) -> A；x : M；hΦ : TensorialAt I F Φ x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundle.finiteDimensional`：∀ (R : Type u_1) {B : Type u_2} (F : Typ
e u_3) (E : B → Type u_4) [inst : NontriviallyNormedField R]   [inst_1 : Topolog
icalSpace B] [inst_2…
-/
theorem mkHom₂_apply
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ) x)
    {σ : Π x : M, V x} (hσ : MDiffAt (T% σ) x) {τ : Π x : M, V' x} (hτ : MDiffAt (T% τ) x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ (σ x) (τ x) = Φ σ τ :=
  TensorialAt.pointwise₂ hΦ₁ hΦ₂ (mdifferentiableAt_extend ..) hσ (mdifferentiableAt_extend ..) hτ
    (by simp) (by simp)
/-
**TensorialAt.mkHom** 是 Mathlib 中的一个定义，位于命名空间 `TensorialAt`。
形式化陈述：mkHom -- `Φ` and `x` explicit to make it easier to generate the side condi
tion at point of use (Φ : (Π x : M, V x) -> A) (x : M) (hΦ : TensorialAt I F Φ x
) : V x ->L[𝕜] A
参数：Φ : (Π x : M, V x) -> A；x : M；hΦ : TensorialAt I F Φ x。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `VectorBundle.finiteDimensional`：∀ (R : Type u_1) {B : Type u_2} (F : Typ
e u_3) (E : B → Type u_4) [inst : NontriviallyNormedField R]   [inst_1 : Topolog
icalSpace B] [inst_2…
-/
theorem mkHom₂_apply_eq_extend
    {Φ : (Π x : M, V x) → (Π x : M, V' x) → A} {x}
    (hΦ₁ : ∀ τ, MDiffAt (T% τ) x → TensorialAt I F (Φ · τ) x)
    (hΦ₂ : ∀ σ, MDiffAt (T% σ) x → TensorialAt I F' (Φ σ) x)
    (σ : V x) (τ : V' x) :
    mkHom₂ Φ x hΦ₁ hΦ₂ σ τ = Φ (extend F σ) (extend F' τ) :=
  rfl

end TensorialAt

