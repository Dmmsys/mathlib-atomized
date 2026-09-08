/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Growth estimates on `x ^ y` for complex `x`, `y`

Let `l` be a filter on `ℂ` such that `Complex.re` tends to infinity along `l` and `Complex.im z`
grows at a subexponential rate compared to `Complex.re z`. Then

- `Complex.isLittleO_log_abs_re`: `Real.log ∘ Complex.abs` is `o`-small of
  `Complex.re` along `l`;

- `Complex.isLittleO_cpow_mul_exp`: $z^{a_1}e^{b_1 * z} = o\left(z^{a_1}e^{b_1 * z}\right)$
  along `l` for any complex `a₁`, `a₂` and real `b₁ < b₂`.

We use these assumptions on `l` for two reasons. First, these are the assumptions that naturally
appear in the proof. Second, in some applications (e.g., in Ilyashenko's proof of the individual
finiteness theorem for limit cycles of polynomial ODEs with hyperbolic singularities only) natural
stronger assumptions (e.g., `im z` is bounded from below and from above) are not available.

-/

public section


open Asymptotics Filter Function
open scoped Topology

namespace Complex

/-- We say that `l : Filter ℂ` is an *exponential comparison filter* if the real part tends to
infinity along `l` and the imaginary part grows subexponentially compared to the real part. These
properties guarantee that `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`
for any complex `a₁`, `a₂` and real `b₁ < b₂`.

In particular, the second property is automatically satisfied if the imaginary part is bounded along
`l`. -/
/-
**Complex.IsExpCmpFilter** 是 Mathlib 中的一个归纳类型，位于命名空间 `Complex`。
形式化陈述：Filter ℂ → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `l : Filter ℂ` is an *exponential comparison filter* if the real par
t tends to
infinity along `l` and the imaginary part grows subexponentially compared to the
 real part. These
properties guarantee that `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂
 * exp (b₂ * z))`
for any complex `a₁`, `a₂` and real `b₁ < b₂`.

In particular, the second property is automatically satisfied if the imaginary p
art is bounded along
`l`.
-/
structure IsExpCmpFilter (l : Filter ℂ) : Prop where
  tendsto_re : Tendsto re l atTop
  isBigO_im_pow_re : ∀ n : ℕ, (fun z : ℂ => z.im ^ n) =O[l] fun z => Real.exp z.re

namespace IsExpCmpFilter

variable {l : Filter ℂ}

/-!
### Alternative constructors
-/

/-
**Complex.IsExpCmpFilter.of_isBigO_im_re_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex
.IsExpCmpFilter`。
形式化陈述：of_isBigO_im_re_rpow (hre : Tendsto re l atTop) (r : Real) (hr : im =O[l] 
fun z => z.re ^ r) : IsExpCmpFilter l
参数：hre : Tendsto re l atTop；r : Real；hr : im =O[l] fun z => z.re ^ r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.IsBigO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} [NormOn…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `isLittleO_rpow_exp_atTop`：isLittleO_rpow_exp_atTop (s : Real) : (fun x :
 Real => x ^ s) =o[atTop] exp

--- 原说明 ---
### Alternative constructors
-/
theorem of_isBigO_im_re_rpow (hre : Tendsto re l atTop) (r : ℝ) (hr : im =O[l] fun z => z.re ^ r) :
    IsExpCmpFilter l :=
  ⟨hre, fun n =>
    IsLittleO.isBigO <|
      calc
        (fun z : ℂ => z.im ^ n) =O[l] fun z => (z.re ^ r) ^ n := hr.pow n
        _ =ᶠ[l] fun z => z.re ^ (r * n) :=
          ((hre.eventually_ge_atTop 0).mono fun z hz => by
            simp only [Real.rpow_mul hz r n, Real.rpow_natCast])
        _ =o[l] fun z => Real.exp z.re := (isLittleO_rpow_exp_atTop _).comp_tendsto hre ⟩
/-
**Complex.IsExpCmpFilter.of_isBigO_im_re_pow** 是 Mathlib 中的一个定理，位于命名空间 `Complex.
IsExpCmpFilter`。
形式化陈述：of_isBigO_im_re_pow (hre : Tendsto re l atTop) (n : Nat) (hr : im =O[l] fu
n z => z.re ^ n) : IsExpCmpFilter l
参数：hre : Tendsto re l atTop；n : Nat；hr : im =O[l] fun z => z.re ^ n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.IsExpCmpFilter.of_isBigO_im_re_rpow`：of_isBigO_im_re_rpow (hre :
 Tendsto re l atTop) (r : Real) (hr : im =O[l] fun z => z.re ^ r) : IsExpCmpFilt
er l
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
-/
theorem of_isBigO_im_re_pow (hre : Tendsto re l atTop) (n : ℕ) (hr : im =O[l] fun z => z.re ^ n) :
    IsExpCmpFilter l :=
  of_isBigO_im_re_rpow hre n <| mod_cast hr
/-
**Complex.IsExpCmpFilter.of_boundedUnder_abs_im** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex.IsExpCmpFilter`。
形式化陈述：of_boundedUnder_abs_im (hre : Tendsto re l atTop) (him : IsBoundedUnder (·
 <= ·) l fun z => |z.im|) : IsExpCmpFilter l
参数：hre : Tendsto re l atTop；him : IsBoundedUnder (· <= ·) l fun z => |z.im|。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.IsExpCmpFilter.of_isBigO_im_re_pow`：of_isBigO_im_re_pow (hre : T
endsto re l atTop) (n : Nat) (hr : im =O[l] fun z => z.re ^ n) : IsExpCmpFilter 
l
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Filter.IsBoundedUnder.isBigO_const`：∀ {α : Type u_1} {E : Type u_3} {F''
 : Type u_10} [inst : Norm E] [inst_1 : NormedAddCommGroup F''] {f : α → E}   {l
 : Filter α}, Filter.IsB…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem of_boundedUnder_abs_im (hre : Tendsto re l atTop)
    (him : IsBoundedUnder (· ≤ ·) l fun z => |z.im|) : IsExpCmpFilter l :=
  of_isBigO_im_re_pow hre 0 <| by
    simpa only [pow_zero] using him.isBigO_const (f := im) one_ne_zero
/-
**Complex.IsExpCmpFilter.of_boundedUnder_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex.I
sExpCmpFilter`。
形式化陈述：of_boundedUnder_im (hre : Tendsto re l atTop) (him_le : IsBoundedUnder (· 
<= ·) l im) (him_ge : IsBoundedUnder (· >= ·) l im) : IsExpCmpFilter l
参数：hre : Tendsto re l atTop；him_le : IsBoundedUnder (· <= ·) l im；him_ge : IsBou
ndedUnder (· >= ·) l im。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.IsExpCmpFilter.of_boundedUnder_abs_im`：of_boundedUnder_abs_im (h
re : Tendsto re l atTop) (him : IsBoundedUnder (· <= ·) l fun z => |z.im|) : IsE
xpCmpFilter l
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.isBoundedUnder_le_abs`：isBoundedUnder_le_abs [AddCommGroup α] [Li
nearOrder α] [IsOrderedAddMonoid α] {f : Filter β} {u : β -> α} : (f.IsBoundedUn
der (· <= ·) fun a…
-/
theorem of_boundedUnder_im (hre : Tendsto re l atTop) (him_le : IsBoundedUnder (· ≤ ·) l im)
    (him_ge : IsBoundedUnder (· ≥ ·) l im) : IsExpCmpFilter l :=
  of_boundedUnder_abs_im hre <| isBoundedUnder_le_abs.2 ⟨him_le, him_ge⟩

/-!
### Preliminary lemmas
-/

/-
**Complex.IsExpCmpFilter.eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsExpC
mpFilter`。
形式化陈述：eventually_ne (hl : IsExpCmpFilter l) : forallᶠ w : Complex in l, w != 0
参数：hl : IsExpCmpFilter l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_ne_atTop'`：∀ {α : Type u_3} {β : Type u_4} [in
st : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l
 Filter.atTop → ∀ (c : α)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Complex.IsExpCmpFilter.tendsto_re`：∀ {l : Filter ℂ}, Complex.IsExpCmpFil
ter l → Filter.Tendsto Complex.re l Filter.atTop

--- 原说明 ---
### Preliminary lemmas
-/
theorem eventually_ne (hl : IsExpCmpFilter l) : ∀ᶠ w : ℂ in l, w ≠ 0 :=
  hl.tendsto_re.eventually_ne_atTop' _
/-
**Complex.IsExpCmpFilter.tendsto_abs_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsExp
CmpFilter`。
形式化陈述：tendsto_abs_re (hl : IsExpCmpFilter l) : Tendsto (fun z : Complex => |z.re
|) l atTop
参数：hl : IsExpCmpFilter l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
· 使用定理 `Complex.IsExpCmpFilter.tendsto_re`：∀ {l : Filter ℂ}, Complex.IsExpCmpFil
ter l → Filter.Tendsto Complex.re l Filter.atTop
-/
theorem tendsto_abs_re (hl : IsExpCmpFilter l) : Tendsto (fun z : ℂ => |z.re|) l atTop :=
  tendsto_abs_atTop_atTop.comp hl.tendsto_re
/-
**Complex.IsExpCmpFilter.tendsto_norm** 是 Mathlib 中的一个定理，位于命名空间 `Complex.IsExpCm
pFilter`。
形式化陈述：tendsto_norm (hl : IsExpCmpFilter l) : Tendsto norm l atTop
参数：hl : IsExpCmpFilter l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `Complex.abs_re_le_norm`：abs_re_le_norm (z : Complex) : |z.re| <= ‖z‖
· 使用定理 `Complex.IsExpCmpFilter.tendsto_abs_re`：tendsto_abs_re (hl : IsExpCmpFilt
er l) : Tendsto (fun z : Complex => |z.re|) l atTop
-/
theorem tendsto_norm (hl : IsExpCmpFilter l) : Tendsto norm l atTop :=
  tendsto_atTop_mono abs_re_le_norm hl.tendsto_abs_re
/-
**Complex.IsExpCmpFilter.isLittleO_log_re_re** 是 Mathlib 中的一个定理，位于命名空间 `Complex.
IsExpCmpFilter`。
形式化陈述：isLittleO_log_re_re (hl : IsExpCmpFilter l) : (fun z => Real.log z.re) =o[
l] re
参数：hl : IsExpCmpFilter l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Real.isLittleO_log_id_atTop`：isLittleO_log_id_atTop : log =o[atTop] id
· 使用定理 `Complex.IsExpCmpFilter.tendsto_re`：∀ {l : Filter ℂ}, Complex.IsExpCmpFil
ter l → Filter.Tendsto Complex.re l Filter.atTop
-/
theorem isLittleO_log_re_re (hl : IsExpCmpFilter l) : (fun z => Real.log z.re) =o[l] re :=
  Real.isLittleO_log_id_atTop.comp_tendsto hl.tendsto_re

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**Complex.IsExpCmpFilter.isLittleO_im_pow_exp_re** 是 Mathlib 中的一个定理，位于命名空间 `Comp
lex.IsExpCmpFilter`。
形式化陈述：isLittleO_im_pow_exp_re (hl : IsExpCmpFilter l) (n : Nat) : (fun z : Compl
ex => z.im ^ n) =o[l] fun z => Real.exp z.re
参数：hl : IsExpCmpFilter l；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_pow`：∀ {α : Type u_1} {R : Type u_13} [inst : S
eminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l :
 Filter α} [NormOn…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_mul'`：pow_mul' (a : M) (m n : Nat) : a ^ (m * n) = (a ^ n) ^ m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Complex.IsExpCmpFilter.isBigO_im_pow_re`：∀ {l : Filter ℂ}, Complex.IsExp
CmpFilter l → ∀ (n : ℕ), (fun z => z.im ^ n) =O[l] fun z => Real.exp z.re
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Asymptotics.isLittleO_pow_pow_atTop_of_lt`：Asymptotics.isLittleO_pow_pow
_atTop_of_lt [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {p q : Na
t} (hpq : p < q) : (fun x : 𝕜 =…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
· 使用定理 `Complex.IsExpCmpFilter.tendsto_re`：∀ {l : Filter ℂ}, Complex.IsExpCmpFil
ter l → Filter.Tendsto Complex.re l Filter.atTop
-/
theorem isLittleO_im_pow_exp_re (hl : IsExpCmpFilter l) (n : ℕ) :
    (fun z : ℂ => z.im ^ n) =o[l] fun z => Real.exp z.re :=
  flip IsLittleO.of_pow two_ne_zero <|
    calc
      (fun z : ℂ ↦ (z.im ^ n) ^ 2) = (fun z ↦ z.im ^ (2 * n)) := by simp only [pow_mul']
      _ =O[l] fun z ↦ Real.exp z.re := hl.isBigO_im_pow_re _
      _ =     fun z ↦ (Real.exp z.re) ^ 1 := by simp only [pow_one]
      _ =o[l] fun z ↦ (Real.exp z.re) ^ 2 :=
        (isLittleO_pow_pow_atTop_of_lt one_lt_two).comp_tendsto <|
          Real.tendsto_exp_atTop.comp hl.tendsto_re
/-
**Complex.IsExpCmpFilter.abs_im_pow_eventuallyLE_exp_re** 是 Mathlib 中的一个定理，位于命名空
间 `Complex.IsExpCmpFilter`。
形式化陈述：abs_im_pow_eventuallyLE_exp_re (hl : IsExpCmpFilter l) (n : Nat) : (fun z 
: Complex => |z.im| ^ n) <=ᶠ[l] fun z => Real.exp z.re
参数：hl : IsExpCmpFilter l；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.abs_exp`：abs_exp (x : Real) : |exp x| = exp x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsLittleO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   
f =o[l] g → ∀ ⦃c …
· 使用定理 `Complex.IsExpCmpFilter.isLittleO_im_pow_exp_re`：isLittleO_im_pow_exp_re 
(hl : IsExpCmpFilter l) (n : Nat) : (fun z : Complex => z.im ^ n) =o[l] fun z =>
 Real.exp z.re
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem abs_im_pow_eventuallyLE_exp_re (hl : IsExpCmpFilter l) (n : ℕ) :
    (fun z : ℂ => |z.im| ^ n) ≤ᶠ[l] fun z => Real.exp z.re := by
  simpa using! (hl.isLittleO_im_pow_exp_re n).bound zero_lt_one

/-- If `l : Filter ℂ` is an "exponential comparison filter", then $\log |z| =o(ℜ z)$ along `l`.
This is the main lemma in the proof of `Complex.IsExpCmpFilter.isLittleO_cpow_exp` below.
-/
/-
**Complex.IsExpCmpFilter.isLittleO_log_norm_re** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x.IsExpCmpFilter`。
形式化陈述：isLittleO_log_norm_re (hl : IsExpCmpFilter l) : (fun z => Real.log ‖z‖) =o
[l] re
参数：hl : IsExpCmpFilter l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Asymptotics.IsBigO.of_norm_eventuallyLE`：∀ {α : Type u_1} {E : Type u_3}
 [inst : Norm E] {f : α → E} {l : Filter α} {g : α → ℝ},   (fun x => ‖f x‖) ≤ᶠ[l
] g → f =O[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Complex.IsExpCmpFilter.tendsto_re`：∀ {l : Filter ℂ}, Complex.IsExpCmpFil
ter l → Filter.Tendsto Complex.re l Filter.atTop
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Complex.re_le_norm`：re_le_norm (z : Complex) : z.re <= ‖z‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Real.log_nonneg`：log_nonneg (hx : 1 <= x) : 0 <= log x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.log_le_log_iff`：log_le_log_iff (h : 0 < x) (h₁ : 0 < y) : log x <= 
log y ↔ x <= y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Complex.norm_le_sqrt_two_mul_max`：norm_le_sqrt_two_mul_max (z : Complex)
 : ‖z‖ <= √2 * max |z.re| |z.im|
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
If `l : Filter ℂ` is an "exponential comparison filter", then $\log |z| =o(ℜ z)$
 along `l`.
This is the main lemma in the proof of `Complex.IsExpCmpFilter.isLittleO_cpow_ex
p` below.
-/
theorem isLittleO_log_norm_re (hl : IsExpCmpFilter l) : (fun z => Real.log ‖z‖) =o[l] re :=
  calc
    (fun z => Real.log ‖z‖) =O[l] fun z => Real.log (√2) + Real.log (max z.re |z.im|) :=
      .of_norm_eventuallyLE <|
        (hl.tendsto_re.eventually_ge_atTop 1).mono fun z hz => by
          have h2 : 0 < √2 := by simp
          have hz' : 1 ≤ ‖z‖ := hz.trans (re_le_norm z)
          have hm₀ : 0 < max z.re |z.im| := lt_max_iff.2 (Or.inl <| one_pos.trans_le hz)
          simp only [Real.norm_of_nonneg (Real.log_nonneg hz')]
          rw [← Real.log_mul, Real.log_le_log_iff, ← abs_of_nonneg (le_trans zero_le_one hz)]
          exacts [norm_le_sqrt_two_mul_max z, one_pos.trans_le hz', mul_pos h2 hm₀, h2.ne', hm₀.ne']
    _ =o[l] re :=
      IsLittleO.add (isLittleO_const_left.2 <| Or.inr <| hl.tendsto_abs_re) <|
        isLittleO_iff_nat_mul_le.2 fun n => by
          filter_upwards [isLittleO_iff_nat_mul_le'.1 hl.isLittleO_log_re_re n,
            hl.abs_im_pow_eventuallyLE_exp_re n,
            hl.tendsto_re.eventually_gt_atTop 1] with z hre him h₁
          rcases le_total |z.im| z.re with hle | hle
          · rwa [max_eq_left hle]
          · have H : 1 < |z.im| := h₁.trans_le hle
            norm_cast at *
            rwa [max_eq_right hle, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.log_pos H),
              ← Real.log_pow, Real.log_le_iff_le_exp (pow_pos (one_pos.trans H) _),
              abs_of_pos (one_pos.trans h₁)]

/-!
### Main results
-/

/-
**Complex.IsExpCmpFilter.isTheta_cpow_exp_re_mul_log** 是 Mathlib 中的一个引理，位于命名空间 `
Complex.IsExpCmpFilter`。
形式化陈述：isTheta_cpow_exp_re_mul_log (hl : IsExpCmpFilter l) (a : Complex) : (· ^ a
) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖)
参数：hl : IsExpCmpFilter l；a : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.isTheta_cpow_const_rpow`：isTheta_cpow_const_rpow {b : Complex} (
hl : b.re = 0 -> b != 0 -> forallᶠ x in l, f x != 0) : (fun x => f x ^ b) =Θ[l] 
fun x => ‖f x‖ ^ b.re
· 使用定理 `Complex.IsExpCmpFilter.eventually_ne`：eventually_ne (hl : IsExpCmpFilter
 l) : forallᶠ w : Complex in l, w != 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
### Main results
-/
lemma isTheta_cpow_exp_re_mul_log (hl : IsExpCmpFilter l) (a : ℂ) :
    (· ^ a) =Θ[l] fun z ↦ Real.exp (re a * Real.log ‖z‖) :=
  calc
    (fun z => z ^ a) =Θ[l] (fun z : ℂ => ‖z‖ ^ re a) :=
      isTheta_cpow_const_rpow fun _ _ => hl.eventually_ne
    _ =ᶠ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      (hl.eventually_ne.mono fun z hz => by simp
        [Real.rpow_def_of_pos, norm_pos_iff.mpr hz, mul_comm])

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
positive real `b`, we have `(fun z ↦ z ^ a) =o[l] (fun z ↦ exp (b * z))`. -/
/-
**Complex.IsExpCmpFilter.isLittleO_cpow_exp** 是 Mathlib 中的一个定理，位于命名空间 `Complex.I
sExpCmpFilter`。
形式化陈述：isLittleO_cpow_exp (hl : IsExpCmpFilter l) (a : Complex) {b : Real} (hb : 
0 < b) : (fun z => z ^ a) =o[l] fun z => exp (b * z)
参数：hl : IsExpCmpFilter l；a : Complex；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Complex.IsExpCmpFilter.isTheta_cpow_exp_re_mul_log`：isTheta_cpow_exp_re_
mul_log (hl : IsExpCmpFilter l) (a : Complex) : (· ^ a) =Θ[l] fun z => Real.exp 
(re a * Real.log ‖z‖)
· 使用定理 `Asymptotics.IsLittleO.of_norm_right`：∀ {α : Type u_1} {E : Type u_3} {F'
 : Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   
{g' : α → F'} {l : Filter…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Asymptotics.IsEquivalent.sub_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用定理 `Asymptotics.IsLittleO.const_mul_right`：∀ {α : Type u_1} {E : Type u_3} [
inst : Norm E] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S] {f : α →
 E}   {l : Filter α} {g : α…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…
· 使用定理 `Complex.IsExpCmpFilter.isLittleO_log_norm_re`：isLittleO_log_norm_re (hl 
: IsExpCmpFilter l) : (fun z => Real.log ‖z‖) =o[l] re
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Complex.IsExpCmpFilter.tendsto_re`：∀ {l : Filter ℂ}, Complex.IsExpCmpFil
ter l → Filter.Tendsto Complex.re l Filter.atTop

--- 原说明 ---
If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a
` and any
positive real `b`, we have `(fun z ↦ z ^ a) =o[l] (fun z ↦ exp (b * z))`.
-/
theorem isLittleO_cpow_exp (hl : IsExpCmpFilter l) (a : ℂ) {b : ℝ} (hb : 0 < b) :
    (fun z => z ^ a) =o[l] fun z => exp (b * z) :=
  calc
    (fun z => z ^ a) =Θ[l] fun z => Real.exp (re a * Real.log ‖z‖) :=
      hl.isTheta_cpow_exp_re_mul_log a
    _ =o[l] fun z => exp (b * z) :=
      IsLittleO.of_norm_right <| by
        simp only [norm_exp, re_ofReal_mul, Real.isLittleO_exp_comp_exp_comp]
        refine (IsEquivalent.refl.sub_isLittleO ?_).symm.tendsto_atTop
          (hl.tendsto_re.const_mul_atTop hb)
        exact (hl.isLittleO_log_norm_re.const_mul_left _).const_mul_right hb.ne'

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
real `b₁ < b₂`, we have `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
/-
**Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex.IsExpCmpFilter`。
形式化陈述：isLittleO_cpow_mul_exp {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b
₂) (a₁ a₂ : Complex) : (fun z => z ^ a₁ * exp (b₁ * z)) =o[l] fun z => z ^ a₂ * 
exp (b₂ * z)
参数：hl : IsExpCmpFilter l；hb : b₁ < b₂；a₁ a₂ : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Complex.IsExpCmpFilter.eventually_ne`：eventually_ne (hl : IsExpCmpFilter
 l) : forallᶠ w : Complex in l, w != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.cpow_add`：cpow_add {x : Complex} (y z : Complex) (hx : x != 0) :
 x ^ (y + z) = x ^ y * x ^ z
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Complex.IsExpCmpFilter.isLittleO_cpow_exp`：isLittleO_cpow_exp (hl : IsEx
pCmpFilter l) (a : Complex) {b : Real} (hb : 0 < b) : (fun z => z ^ a) =o[l] fun
 z => exp (b * z)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f

--- 原说明 ---
If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a
₁`, `a₂` and any
real `b₁ < b₂`, we have `(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ *
 exp (b₂ * z))`.
-/
theorem isLittleO_cpow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : ℂ) :
    (fun z => z ^ a₁ * exp (b₁ * z)) =o[l] fun z => z ^ a₂ * exp (b₂ * z) :=
  calc
    (fun z => z ^ a₁ * exp (b₁ * z)) =ᶠ[l] fun z => z ^ a₂ * exp (b₁ * z) * z ^ (a₁ - a₂) :=
      hl.eventually_ne.mono fun z hz => by
        simp only
        rw [mul_right_comm, ← cpow_add _ _ hz, add_sub_cancel]
    _ =o[l] fun z => z ^ a₂ * exp (b₁ * z) * exp (↑(b₂ - b₁) * z) :=
      ((isBigO_refl (fun z => z ^ a₂ * exp (b₁ * z)) l).mul_isLittleO <|
        hl.isLittleO_cpow_exp _ (sub_pos.2 hb))
    _ =ᶠ[l] fun z => z ^ a₂ * exp (b₂ * z) := by
      simp only [ofReal_sub, sub_mul, mul_assoc, ← exp_add, add_sub_cancel]
      norm_cast

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a` and any
negative real `b`, we have `(fun z ↦ exp (b * z)) =o[l] (fun z ↦ z ^ a)`. -/
/-
**Complex.IsExpCmpFilter.isLittleO_exp_cpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex.I
sExpCmpFilter`。
形式化陈述：isLittleO_exp_cpow (hl : IsExpCmpFilter l) (a : Complex) {b : Real} (hb : 
b < 0) : (fun z => exp (b * z)) =o[l] fun z => z ^ a
参数：hl : IsExpCmpFilter l；a : Complex；hb : b < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_zero`：cpow_zero (x : Complex) : x ^ (0 : Complex) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.exp_zero`：exp_zero : exp 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp`：isLittleO_cpow_mul_exp {b
₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : Complex) : (fun z =
> z ^ a₁ * exp (b₁ * z)) =o[l] fun …

--- 原说明 ---
If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a
` and any
negative real `b`, we have `(fun z ↦ exp (b * z)) =o[l] (fun z ↦ z ^ a)`.
-/
theorem isLittleO_exp_cpow (hl : IsExpCmpFilter l) (a : ℂ) {b : ℝ} (hb : b < 0) :
    (fun z => exp (b * z)) =o[l] fun z => z ^ a := by simpa using hl.isLittleO_cpow_mul_exp hb 0 a

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
natural `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
/-
**Complex.IsExpCmpFilter.isLittleO_pow_mul_exp** 是 Mathlib 中的一个定理，位于命名空间 `Comple
x.IsExpCmpFilter`。
形式化陈述：isLittleO_pow_mul_exp {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂
) (m n : Nat) : (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ *
 z)
参数：hl : IsExpCmpFilter l；hb : b₁ < b₂；m n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_natCast`：cpow_natCast (x : Complex) (n : Nat) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp`：isLittleO_cpow_mul_exp {b
₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : Complex) : (fun z =
> z ^ a₁ * exp (b₁ * z)) =o[l] fun …

--- 原说明 ---
If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a
₁`, `a₂` and any
natural `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`.
-/
theorem isLittleO_pow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : ℕ) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_natCast] using hl.isLittleO_cpow_mul_exp hb m n

/-- If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a₁`, `a₂` and any
integer `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`. -/
/-
**Complex.IsExpCmpFilter.isLittleO_zpow_mul_exp** 是 Mathlib 中的一个定理，位于命名空间 `Compl
ex.IsExpCmpFilter`。
形式化陈述：isLittleO_zpow_mul_exp {b₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b
₂) (m n : Int) : (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ 
* z)
参数：hl : IsExpCmpFilter l；hb : b₁ < b₂；m n : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Complex.cpow_intCast`：cpow_intCast (x : Complex) (n : Int) : x ^ (n : Co
mplex) = x ^ n
· 使用定理 `Complex.IsExpCmpFilter.isLittleO_cpow_mul_exp`：isLittleO_cpow_mul_exp {b
₁ b₂ : Real} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (a₁ a₂ : Complex) : (fun z =
> z ^ a₁ * exp (b₁ * z)) =o[l] fun …

--- 原说明 ---
If `l : Filter ℂ` is an "exponential comparison filter", then for any complex `a
₁`, `a₂` and any
integer `b₁ < b₂`, we have
`(fun z ↦ z ^ a₁ * exp (b₁ * z)) =o[l] (fun z ↦ z ^ a₂ * exp (b₂ * z))`.
-/
theorem isLittleO_zpow_mul_exp {b₁ b₂ : ℝ} (hl : IsExpCmpFilter l) (hb : b₁ < b₂) (m n : ℤ) :
    (fun z => z ^ m * exp (b₁ * z)) =o[l] fun z => z ^ n * exp (b₂ * z) := by
  simpa only [cpow_intCast] using hl.isLittleO_cpow_mul_exp hb m n

end IsExpCmpFilter

end Complex

