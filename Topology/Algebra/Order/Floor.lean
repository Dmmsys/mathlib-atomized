/-
Copyright (c) 2020 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Order.Filter.AtTopBot.Floor
public import Mathlib.Topology.Algebra.Order.Group

/-!
# Topological facts about `Int.floor`, `Int.ceil` and `Int.fract`

This file proves statements about limits and continuity of functions involving `floor`, `ceil` and
`fract`.

## Main declarations

* `tendsto_floor_atTop`, `tendsto_floor_atBot`, `tendsto_ceil_atTop`, `tendsto_ceil_atBot`:
  `Int.floor` and `Int.ceil` tend to +-∞ in +-∞.
* `continuousOn_floor`: `Int.floor` is continuous on `Ico n (n + 1)`, because constant.
* `continuousOn_ceil`: `Int.ceil` is continuous on `Ioc n (n + 1)`, because constant.
* `continuousOn_fract`: `Int.fract` is continuous on `Ico n (n + 1)`.
* `ContinuousOn.comp_fract`: Precomposing a continuous function satisfying `f 0 = f 1` with
  `Int.fract` yields another continuous function.
-/

public section


open Filter Function Int Set Topology

namespace FloorSemiring

open scoped Nat

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorSemiring K]
  [TopologicalSpace K] [OrderTopology K]

/-
**FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop** 是 Mathlib 中的一个定理，位于命名空
间 `FloorSemiring`。
形式化陈述：tendsto_mul_pow_div_factorial_sub_atTop (a c : K) (d : Nat) : Tendsto (fun
 n => a * c ^ n / (n - d)!) atTop (𝓝 0)
参数：a c : K；d : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_order`：tendsto_order [OrderTopology α] {f : β -> α} {a : α} {x :
 Filter β} : Tendsto f x (𝓝 a) ↔ (forall a' < a, forallᶠ b in x, a' < f b) ∧ for
all…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `FloorSemiring.eventually_mul_pow_lt_factorial_sub`：FloorSemiring.eventua
lly_mul_pow_lt_factorial_sub (a c : K) (d : Nat) : forallᶠ n in atTop, a * c ^ n
 < (n - d)!
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `lt_div_iff₀'`：lt_div_iff₀' (hc : 0 < c) : a < b / c ↔ c * a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.factorial_pos`：∀ (n : ℕ), 0 < n.factorial
· 使用定理 `div_lt_iff_of_neg`：div_lt_iff_of_neg (hc : c < 0) : b / c < a ↔ a * c < 
b where mp h
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
· 使用引理 `div_lt_iff₀'`：div_lt_iff₀' (hc : 0 < c) : b / c < a ↔ b < c * a
· 使用引理 `div_lt_iff₀`：div_lt_iff₀ (hc : 0 < c) : b / c < a ↔ b < a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
-/
theorem tendsto_mul_pow_div_factorial_sub_atTop (a c : K) (d : ℕ) :
    Tendsto (fun n ↦ a * c ^ n / (n - d)!) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  all_goals
    intro ε hε
    filter_upwards [eventually_mul_pow_lt_factorial_sub (a * ε⁻¹) c d] with n h
    rw [mul_right_comm, ← div_eq_mul_inv] at h
  · rw [div_lt_iff_of_neg hε] at h
    rwa [lt_div_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]
  · rw [div_lt_iff₀ hε] at h
    rwa [div_lt_iff₀' (Nat.cast_pos.mpr (Nat.factorial_pos _))]
/-
**FloorSemiring.tendsto_pow_div_factorial_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Floor
Semiring`。
形式化陈述：tendsto_pow_div_factorial_atTop (c : K) : Tendsto (fun n => c ^ n / n !) a
tTop (𝓝 0)
参数：c : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop`：tendsto_mul_pow_d
iv_factorial_sub_atTop (a c : K) (d : Nat) : Tendsto (fun n => a * c ^ n / (n - 
d)!) atTop (𝓝 0)
-/
theorem tendsto_pow_div_factorial_atTop (c : K) :
    Tendsto (fun n ↦ c ^ n / n !) atTop (𝓝 0) := by
  convert! tendsto_mul_pow_div_factorial_sub_atTop 1 c 0
  rw [one_mul]

end FloorSemiring

variable {α β γ : Type*} [Ring α] [LinearOrder α] [FloorRing α]

section
variable [IsStrictOrderedRing α]
-- TODO: move to `Mathlib/Order/Filter/AtTopBot/Floor.lean`

/-
**tendsto_floor_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_atTop : Tendsto (floor : α -> Int) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Int.floor_mono`：floor_mono : Monotone (floor : R -> Int)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `lt_add_one`：lt_add_one [One α] [AddZeroClass α] [PartialOrder α] [ZeroLE
OneClass α] [NeZero (1 : α)] [AddLeftStrictMono α] (a : α) : a < a + 1
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem tendsto_floor_atTop : Tendsto (floor : α → ℤ) atTop atTop :=
  floor_mono.tendsto_atTop_atTop fun b =>
    ⟨(b + 1 : ℤ), by rw [floor_intCast]; exact (lt_add_one _).le⟩
/-
**tendsto_floor_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_atBot : Tendsto (floor : α -> Int) atBot atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atBot_atBot`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, f a
 ≤ b) → Filter.Ten…
· 使用定理 `Int.floor_mono`：floor_mono : Monotone (floor : R -> Int)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_floor_atBot : Tendsto (floor : α → ℤ) atBot atBot :=
  floor_mono.tendsto_atBot_atBot fun b => ⟨b, (floor_intCast _).le⟩
/-
**tendsto_ceil_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_atTop : Tendsto (ceil : α -> Int) atTop atTop
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atTop_atTop`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, b ≤
 f a) → Filter.Ten…
· 使用定理 `Int.ceil_mono`：ceil_mono : Monotone (ceil : R -> Int)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_ceil_atTop : Tendsto (ceil : α → ℤ) atTop atTop :=
  ceil_mono.tendsto_atTop_atTop fun b => ⟨b, (ceil_intCast _).ge⟩
/-
**tendsto_ceil_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_atBot : Tendsto (ceil : α -> Int) atBot atBot
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Monotone.tendsto_atBot_atBot`：∀ {α : Type u_3} {β : Type u_4} [inst : Pr
eorder α] [inst_1 : Preorder β] {f : α → β},   Monotone f → (∀ (b : β), ∃ a, f a
 ≤ b) → Filter.Ten…
· 使用定理 `Int.ceil_mono`：ceil_mono : Monotone (ceil : R -> Int)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `sub_one_lt`：sub_one_lt [ZeroLEOneClass R] [NeZero (1 : R)] [AddLeftStric
tMono R] (a : R) : a - 1 < a
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
-/
theorem tendsto_ceil_atBot : Tendsto (ceil : α → ℤ) atBot atBot :=
  ceil_mono.tendsto_atBot_atBot fun b =>
    ⟨(b - 1 : ℤ), by rw [ceil_intCast]; exact (sub_one_lt _).le⟩

end

variable [TopologicalSpace α]

/-
**continuousOn_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_floor (n : Int) : ContinuousOn (fun x => floor x : α -> α) (I
co n (n + 1) : Set α)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_congr`：continuousOn_congr (h' : EqOn g f s) : ContinuousOn 
g s ↔ ContinuousOn f s
· 使用定理 `Int.floor_eq_on_Ico'`：floor_eq_on_Ico' (n : Int) : forall a in Set.Ico (
n : R) (n + 1), (⌊a⌋ : R) = n
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem continuousOn_floor (n : ℤ) :
    ContinuousOn (fun x => floor x : α → α) (Ico n (n + 1) : Set α) :=
  (continuousOn_congr <| floor_eq_on_Ico' n).mpr continuousOn_const
/-
**continuousOn_ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_ceil (n : Int) : ContinuousOn (fun x => ceil x : α -> α) (Ioc
 (n - 1) n : Set α)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuousOn_congr`：continuousOn_congr (h' : EqOn g f s) : ContinuousOn 
g s ↔ ContinuousOn f s
· 使用定理 `Int.ceil_eq_on_Ioc'`：ceil_eq_on_Ioc' (z : Int) : forall a in Set.Ioc (z 
- 1 : R) z, (⌈a⌉ : R) = z
· 使用定理 `continuousOn_const`：continuousOn_const {s : Set α} {c : β} : ContinuousO
n (fun _ => c) s
-/
theorem continuousOn_ceil (n : ℤ) :
    ContinuousOn (fun x => ceil x : α → α) (Ioc (n - 1) n : Set α) :=
  (continuousOn_congr <| ceil_eq_on_Ioc' n).mpr continuousOn_const

section OrderClosedTopology

variable [IsStrictOrderedRing α] [OrderClosedTopology α]

omit [IsStrictOrderedRing α] in
/-
**tendsto_floor_right_pure_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_right_pure_floor (x : α) : Tendsto (floor : α -> Int) (𝓝[>=]
 x) (pure ⌊x⌋)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ico_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ico b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Int.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋ + 1
· 使用定理 `Int.floor_eq_on_Ico`：floor_eq_on_Ico (n : Int) : forall a in Set.Ico (n 
: R) (n + 1), ⌊a⌋ = n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_floor_right_pure_floor (x : α) : Tendsto (floor : α → ℤ) (𝓝[≥] x) (pure ⌊x⌋) :=
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsGE <| lt_floor_add_one x) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨(floor_le x).trans hy.1, hy.2⟩
/-
**tendsto_floor_right_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_right_pure (n : Int) : Tendsto (floor : α -> Int) (𝓝[>=] n) 
(pure n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `tendsto_floor_right_pure_floor`：tendsto_floor_right_pure_floor (x : α) :
 Tendsto (floor : α -> Int) (𝓝[>=] x) (pure ⌊x⌋)
-/
theorem tendsto_floor_right_pure (n : ℤ) : Tendsto (floor : α → ℤ) (𝓝[≥] n) (pure n) := by
  simpa only [floor_intCast] using tendsto_floor_right_pure_floor (n : α)
/-
**tendsto_ceil_left_pure_ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_left_pure_ceil (x : α) : Tendsto (ceil : α -> Int) (𝓝[<=] x) 
(pure ⌈x⌉)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioc_mem_nhdsLE`：Ioc_mem_nhdsLE (H : a < b) : Ioc a b in 𝓝[<=] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ceil_lt_add_one`：ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1
· 使用定理 `Int.ceil_eq_on_Ioc`：ceil_eq_on_Ioc (z : Int) : forall a in Set.Ioc (z - 
1 : R) z, ⌈a⌉ = z
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
-/
theorem tendsto_ceil_left_pure_ceil (x : α) : Tendsto (ceil : α → ℤ) (𝓝[≤] x) (pure ⌈x⌉) :=
  tendsto_pure.2 <| mem_of_superset
    (Ioc_mem_nhdsLE <| sub_lt_iff_lt_add.2 <| ceil_lt_add_one _) fun _y hy =>
      ceil_eq_on_Ioc _ _ ⟨hy.1, hy.2.trans (le_ceil _)⟩
/-
**tendsto_ceil_left_pure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_left_pure (n : Int) : Tendsto (ceil : α -> Int) (𝓝[<=] n) (pu
re n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `tendsto_ceil_left_pure_ceil`：tendsto_ceil_left_pure_ceil (x : α) : Tends
to (ceil : α -> Int) (𝓝[<=] x) (pure ⌈x⌉)
-/
theorem tendsto_ceil_left_pure (n : ℤ) : Tendsto (ceil : α → ℤ) (𝓝[≤] n) (pure n) := by
  simpa only [ceil_intCast] using tendsto_ceil_left_pure_ceil (n : α)
/-
**tendsto_floor_left_pure_ceil_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_left_pure_ceil_sub_one (x : α) : Tendsto (floor : α -> Int) 
(𝓝[<] x) (pure (⌈x⌉ - 1))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `sub_lt_iff_lt_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [A
ddRightStrictMono α] {a b c : α}, a - c < b ↔ a < b + c
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
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Int.ceil_lt_add_one`：ceil_lt_add_one (a : R) : (⌈a⌉ : R) < a + 1
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `Int.le_ceil`：le_ceil (a : α) : a <= ⌈a⌉
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ico_mem_nhdsLT`：Ico_mem_nhdsLT (H : a < b) : Ico a b in 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `Int.floor_eq_on_Ico`：floor_eq_on_Ico (n : Int) : forall a in Set.Ico (n 
: R) (n + 1), ⌊a⌋ = n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_floor_left_pure_ceil_sub_one (x : α) :
    Tendsto (floor : α → ℤ) (𝓝[<] x) (pure (⌈x⌉ - 1)) :=
  have h₁ : ↑(⌈x⌉ - 1) < x := by rw [cast_sub, cast_one, sub_lt_iff_lt_add]; exact ceil_lt_add_one _
  have h₂ : x ≤ ↑(⌈x⌉ - 1) + 1 := by rw [cast_sub, cast_one, sub_add_cancel]; exact le_ceil _
  tendsto_pure.2 <| mem_of_superset (Ico_mem_nhdsLT h₁) fun _y hy =>
    floor_eq_on_Ico _ _ ⟨hy.1, hy.2.trans_le h₂⟩
/-
**tendsto_floor_left_pure_sub_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_left_pure_sub_one (n : Int) : Tendsto (floor : α -> Int) (𝓝[
<] n) (pure (n - 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.ceil_intCast`：ceil_intCast (z : Int) : ⌈(z : R)⌉ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `tendsto_floor_left_pure_ceil_sub_one`：tendsto_floor_left_pure_ceil_sub_o
ne (x : α) : Tendsto (floor : α -> Int) (𝓝[<] x) (pure (⌈x⌉ - 1))
-/
theorem tendsto_floor_left_pure_sub_one (n : ℤ) :
    Tendsto (floor : α → ℤ) (𝓝[<] n) (pure (n - 1)) := by
  simpa only [ceil_intCast] using tendsto_floor_left_pure_ceil_sub_one (n : α)

omit [IsStrictOrderedRing α] in
/-
**tendsto_ceil_right_pure_floor_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_right_pure_floor_add_one (x : α) : Tendsto (ceil : α -> Int) 
(𝓝[>] x) (pure (⌊x⌋ + 1))
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_pure`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {a : Fi
lter α} {b : β},   Filter.Tendsto f a (pure b) ↔ ∀ᶠ (x : α) in a, f x = b
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Ioc_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Ioc b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `Int.lt_succ_floor`：lt_succ_floor (a : R) : a < ⌊a⌋.succ
· 使用定理 `Int.ceil_eq_on_Ioc`：ceil_eq_on_Ioc (z : Int) : forall a in Set.Ioc (z - 
1 : R) z, ⌈a⌉ = z
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem tendsto_ceil_right_pure_floor_add_one (x : α) :
    Tendsto (ceil : α → ℤ) (𝓝[>] x) (pure (⌊x⌋ + 1)) :=
  have : ↑(⌊x⌋ + 1) - 1 ≤ x := by rw [cast_add, cast_one, add_sub_cancel_right]; exact floor_le _
  tendsto_pure.2 <| mem_of_superset (Ioc_mem_nhdsGT <| lt_succ_floor _) fun _y hy =>
    ceil_eq_on_Ioc _ _ ⟨this.trans_lt hy.1, hy.2⟩
/-
**tendsto_ceil_right_pure_add_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_right_pure_add_one (n : Int) : Tendsto (ceil : α -> Int) (𝓝[>
] n) (pure (n + 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.floor_intCast`：floor_intCast (z : Int) : ⌊(z : R)⌋ = z
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `tendsto_ceil_right_pure_floor_add_one`：tendsto_ceil_right_pure_floor_add
_one (x : α) : Tendsto (ceil : α -> Int) (𝓝[>] x) (pure (⌊x⌋ + 1))
-/
theorem tendsto_ceil_right_pure_add_one (n : ℤ) :
    Tendsto (ceil : α → ℤ) (𝓝[>] n) (pure (n + 1)) := by
  simpa only [floor_intCast] using tendsto_ceil_right_pure_floor_add_one (n : α)
/-
**tendsto_floor_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_right (n : Int) : Tendsto (fun x => floor x : α -> α) (𝓝[>=]
 n) (𝓝[>=] n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `tendsto_floor_right_pure`：tendsto_floor_right_pure (n : Int) : Tendsto (
floor : α -> Int) (𝓝[>=] n) (pure n)
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tendsto_floor_right (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝[≥] n) :=
  ((tendsto_pure_pure _ _).comp (tendsto_floor_right_pure n)).mono_right <|
    pure_le_nhdsWithin le_rfl
/-
**tendsto_floor_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_right' (n : Int) : Tendsto (fun x => floor x : α -> α) (𝓝[>=
] n) (𝓝 n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_floor_right`：tendsto_floor_right (n : Int) : Tendsto (fun x => f
loor x : α -> α) (𝓝[>=] n) (𝓝[>=] n)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_floor_right' (n : ℤ) : Tendsto (fun x => floor x : α → α) (𝓝[≥] n) (𝓝 n) :=
  (tendsto_floor_right n).mono_right inf_le_left
/-
**tendsto_ceil_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_left (n : Int) : Tendsto (fun x => ceil x : α -> α) (𝓝[<=] n)
 (𝓝[<=] n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `tendsto_ceil_left_pure`：tendsto_ceil_left_pure (n : Int) : Tendsto (ceil
 : α -> Int) (𝓝[<=] n) (pure n)
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tendsto_ceil_left (n : ℤ) : Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝[≤] n) :=
  ((tendsto_pure_pure _ _).comp (tendsto_ceil_left_pure n)).mono_right <|
    pure_le_nhdsWithin le_rfl
/-
**tendsto_ceil_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_left' (n : Int) : Tendsto (fun x => ceil x : α -> α) (𝓝[<=] n
) (𝓝 n)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_ceil_left`：tendsto_ceil_left (n : Int) : Tendsto (fun x => ceil 
x : α -> α) (𝓝[<=] n) (𝓝[<=] n)
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_ceil_left' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[≤] n) (𝓝 n) :=
  (tendsto_ceil_left n).mono_right inf_le_left
/-
**tendsto_floor_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_left (n : Int) : Tendsto (fun x => floor x : α -> α) (𝓝[<] n
) (𝓝[<=] (n - 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `tendsto_floor_left_pure_sub_one`：tendsto_floor_left_pure_sub_one (n : In
t) : Tendsto (floor : α -> Int) (𝓝[<] n) (pure (n - 1))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_sub`：cast_sub (m n) : ((m - n : Int) : R) = m - n
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tendsto_floor_left (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝[≤] (n - 1)) :=
  ((tendsto_pure_pure _ _).comp (tendsto_floor_left_pure_sub_one n)).mono_right <| by
    rw [← @cast_one α, ← cast_sub]; exact pure_le_nhdsWithin le_rfl
/-
**tendsto_ceil_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_right (n : Int) : Tendsto (fun x => ceil x : α -> α) (𝓝[>] n)
 (𝓝[>=] (n + 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_pure_pure`：tendsto_pure_pure (f : α -> β) (a : α) : Tends
to f (pure a) (pure (f a))
· 使用定理 `tendsto_ceil_right_pure_add_one`：tendsto_ceil_right_pure_add_one (n : In
t) : Tendsto (ceil : α -> Int) (𝓝[>] n) (pure (n + 1))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Int.cast_add`：∀ {R : Type u} [inst : AddGroupWithOne R] (m n : ℤ), ↑(m +
 n) = ↑m + ↑n
· 使用定理 `pure_le_nhdsWithin`：pure_le_nhdsWithin {a : α} {s : Set α} (ha : a in s)
 : pure a <= 𝓝[s] a
· 使用引理 `le_rfl`：le_rfl : a <= a
-/
theorem tendsto_ceil_right (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝[≥] (n + 1)) :=
  ((tendsto_pure_pure _ _).comp (tendsto_ceil_right_pure_add_one n)).mono_right <| by
    rw [← @cast_one α, ← cast_add]; exact pure_le_nhdsWithin le_rfl
/-
**tendsto_floor_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_floor_left' (n : Int) : Tendsto (fun x => floor x : α -> α) (𝓝[<] 
n) (𝓝 (n - 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_floor_left`：tendsto_floor_left (n : Int) : Tendsto (fun x => flo
or x : α -> α) (𝓝[<] n) (𝓝[<=] (n - 1))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_floor_left' (n : ℤ) :
    Tendsto (fun x => floor x : α → α) (𝓝[<] n) (𝓝 (n - 1)) :=
  (tendsto_floor_left n).mono_right inf_le_left
/-
**tendsto_ceil_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_ceil_right' (n : Int) : Tendsto (fun x => ceil x : α -> α) (𝓝[>] n
) (𝓝 (n + 1))
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `tendsto_ceil_right`：tendsto_ceil_right (n : Int) : Tendsto (fun x => cei
l x : α -> α) (𝓝[>] n) (𝓝[>=] (n + 1))
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem tendsto_ceil_right' (n : ℤ) :
    Tendsto (fun x => ceil x : α → α) (𝓝[>] n) (𝓝 (n + 1)) :=
  (tendsto_ceil_right n).mono_right inf_le_left

end OrderClosedTopology

/-
**continuousOn_fract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousOn_fract [IsTopologicalAddGroup α] (n : Int) : ContinuousOn (fra
ct : α -> α) (Ico n (n + 1) : Set α)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalSpa
ce X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g : 
X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `continuousOn_floor`：continuousOn_floor (n : Int) : ContinuousOn (fun x =
> floor x : α -> α) (Ico n (n + 1) : Set α)
-/
theorem continuousOn_fract [IsTopologicalAddGroup α] (n : ℤ) :
    ContinuousOn (fract : α → α) (Ico n (n + 1) : Set α) :=
  continuousOn_id.sub (continuousOn_floor n)
/-
**continuousAt_fract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_fract [OrderClosedTopology α] [IsTopologicalAddGroup α] {x : 
α} (h : x != ⌊x⌋) : ContinuousAt fract x
参数：h : x != ⌊x⌋。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousOn.continuousAt`：ContinuousOn.continuousAt (h : ContinuousOn f
 s) (hx : s in 𝓝 x) : ContinuousAt f x
· 使用定理 `continuousOn_fract`：continuousOn_fract [IsTopologicalAddGroup α] (n : In
t) : ContinuousOn (fract : α -> α) (Ico n (n + 1) : Set α)
· 使用定理 `Ico_mem_nhds`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Linea
rOrder α] [OrderClosedTopology α] {a b x : α},   b < x → x < a → Set.Ico b a ∈ n
hd…
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Int.floor_le`：floor_le (a : α) : (⌊a⌋ : α) <= a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Int.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋ + 1
-/
theorem continuousAt_fract [OrderClosedTopology α] [IsTopologicalAddGroup α]
    {x : α} (h : x ≠ ⌊x⌋) : ContinuousAt fract x :=
  (continuousOn_fract ⌊x⌋).continuousAt <|
    Ico_mem_nhds ((floor_le _).lt_of_ne h.symm) (lt_floor_add_one _)

variable [IsStrictOrderedRing α]
/-
**tendsto_fract_left'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_fract_left' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n :
 Int) : Tendsto (fract : α -> α) (𝓝[<] n) (𝓝 1)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `tendsto_floor_left'`：tendsto_floor_left' (n : Int) : Tendsto (fun x => f
loor x : α -> α) (𝓝[<] n) (𝓝 (n - 1))
-/
theorem tendsto_fract_left' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝 1) := by
  rw [← sub_sub_cancel (n : α) 1]
  refine (tendsto_id.mono_left nhdsWithin_le_nhds).sub ?_
  exact tendsto_floor_left' n
/-
**tendsto_fract_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_fract_left [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : 
Int) : Tendsto (fract : α -> α) (𝓝[<] n) (𝓝[<] 1)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `tendsto_fract_left'`：tendsto_fract_left' [OrderClosedTopology α] [IsTopo
logicalAddGroup α] (n : Int) : Tendsto (fract : α -> α) (𝓝[<] n) (𝓝 1)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Int.fract_lt_one`：fract_lt_one (a : R) : fract a < 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_fract_left [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[<] n) (𝓝[<] 1) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_left' _)
    (Eventually.of_forall fract_lt_one)
/-
**tendsto_fract_right'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_fract_right' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n 
: Int) : Tendsto (fract : α -> α) (𝓝[>=] n) (𝓝 0)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds`：tendsto_nhdsWithin_of_tendsto_nhds {
f : α -> β} {a : α} {s : Set α} {l : Filter β} (h : Tendsto f (𝓝 a) l) : Tendsto
 f (𝓝[s] a) l
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_floor_right'`：tendsto_floor_right' (n : Int) : Tendsto (fun x =>
 floor x : α -> α) (𝓝[>=] n) (𝓝 n)
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
-/
theorem tendsto_fract_right' [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝 0) :=
  sub_self (n : α) ▸ (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).sub (tendsto_floor_right' n)
/-
**tendsto_fract_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_fract_right [OrderClosedTopology α] [IsTopologicalAddGroup α] (n :
 Int) : Tendsto (fract : α -> α) (𝓝[>=] n) (𝓝[>=] 0)
参数：n : Int。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within`：tendsto_nhdsWit
hin_of_tendsto_nhds_of_eventually_within {a : α} {l : Filter β} {s : Set α} (f :
 β -> α) (h1 : Tendsto f l (𝓝 a)) (h2 : foral…
· 使用定理 `tendsto_fract_right'`：tendsto_fract_right' [OrderClosedTopology α] [IsTo
pologicalAddGroup α] (n : Int) : Tendsto (fract : α -> α) (𝓝[>=] n) (𝓝 0)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Int.fract_nonneg`：fract_nonneg (a : R) : 0 <= fract a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem tendsto_fract_right [OrderClosedTopology α] [IsTopologicalAddGroup α] (n : ℤ) :
    Tendsto (fract : α → α) (𝓝[≥] n) (𝓝[≥] 0) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ (tendsto_fract_right' _)
    (Eventually.of_forall fract_nonneg)

local notation "I" => (Icc 0 1 : Set α)

variable [OrderTopology α] [TopologicalSpace β] [TopologicalSpace γ]

/-- Do not use this, use `ContinuousOn.comp_fract` instead. -/
/-
**ContinuousOn.comp_fract'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp_fract' {f : β -> α -> γ} (h : ContinuousOn (uncurry f) <
| univ ×ˢ I) (hf : forall s, f s 0 = f s 1) : Continuous fun st : β × α => f st.
1 (fract st.2)
参数：h : ContinuousOn (uncurry f) <| univ ×ˢ I；hf : forall s, f s 0 = f s 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `nhds_prod_eq`：nhds_prod_eq {x : X} {y : Y} : 𝓝 (x, y) = 𝓝 x ×ˢ 𝓝 y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsLT_sup_nhdsGE`：nhdsLT_sup_nhdsGE (a : α) : 𝓝[<] a ⊔ 𝓝[>=] a = 𝓝 a
· 使用定理 `Filter.prod_sup`：prod_sup (f : Filter α) (g₁ g₂ : Filter β) : f ×ˢ (g₁ ⊔
 g₂) = (f ×ˢ g₁) ⊔ (f ×ˢ g₂)
· 使用定理 `Filter.tendsto_sup`：tendsto_sup {f : α -> β} {x₁ x₂ : Filter α} {y : Fil
ter β} : Tendsto f (x₁ ⊔ x₂) y ↔ Tendsto f x₁ y ∧ Tendsto f x₂ y
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousWithinAt.tendsto`：ContinuousWithinAt.tendsto (h : ContinuousWi
thinAt f s x) : Tendsto f (𝓝[s] x) (𝓝 (f x))
· 使用定理 `trivial`：True
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `FloorSemiring.instZeroLEOneClass`：∀ {α : Type u_2} [inst : Semiring α] [
inst_1 : PartialOrder α] [FloorSemiring α], ZeroLEOneClass α
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `nhdsWithin_prod_eq`：nhdsWithin_prod_eq (x : X) (y : Y) (s : Set X) (t : 
Set Y) : 𝓝[s ×ˢ t] (x, y) = 𝓝[s] x ×ˢ 𝓝[t] y
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `nhdsWithin_Ico_eq_nhdsLT`：nhdsWithin_Ico_eq_nhdsLT (h : a < b) : 𝓝[Ico a
 b] b = 𝓝[<] b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.prod_mono`：prod_mono {f₁ f₂ : Filter α} {g₁ g₂ : Filter β} (hf : 
f₁ <= f₂) (hg : g₁ <= g₂) : f₁ ×ˢ g₁ <= f₂ ×ˢ g₂
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ico_subset_Icc_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ico b a ⊆ Set.Icc b a
· 使用定理 `Filter.Tendsto.prodMap`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {
δ : Type u_6} {f : α → γ} {g : β → δ} {a : Filter α} {b : Filter β}   {c : Filte
r γ} {d : Fi…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `tendsto_fract_left`：tendsto_fract_left [OrderClosedTopology α] [IsTopolo
gicalAddGroup α] (n : Int) : Tendsto (fract : α -> α) (𝓝[<] n) (𝓝[<] 1)
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Do not use this, use `ContinuousOn.comp_fract` instead.
-/
theorem ContinuousOn.comp_fract' {f : β → α → γ} (h : ContinuousOn (uncurry f) <| univ ×ˢ I)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun st : β × α => f st.1 (fract st.2) := by
  change Continuous (uncurry f ∘ Prod.map id fract)
  rw [continuous_iff_continuousAt]
  rintro ⟨s, t⟩
  rcases em (∃ n : ℤ, t = n) with (⟨n, rfl⟩ | ht)
  · rw [ContinuousAt, nhds_prod_eq, ← nhdsLT_sup_nhdsGE (n : α), prod_sup, tendsto_sup]
    constructor
    · refine (((h (s, 1) ⟨trivial, zero_le_one, le_rfl⟩).tendsto.mono_left ?_).comp
        (tendsto_id.prodMap (tendsto_fract_left _))).mono_right (le_of_eq ?_)
      · rw [nhdsWithin_prod_eq, nhdsWithin_univ, ← nhdsWithin_Ico_eq_nhdsLT one_pos]
        exact Filter.prod_mono le_rfl (nhdsWithin_mono _ Ico_subset_Icc_self)
      · simp [hf]
    · refine (((h (s, 0) ⟨trivial, le_rfl, zero_le_one⟩).tendsto.mono_left <| le_of_eq ?_).comp
        (tendsto_id.prodMap (tendsto_fract_right _))).mono_right (le_of_eq ?_) <;>
        simp [nhdsWithin_prod_eq, nhdsWithin_univ]
  · replace ht : t ≠ ⌊t⌋ := fun ht' => ht ⟨_, ht'⟩
    refine (h.continuousAt ?_).comp (continuousAt_id.prodMap (continuousAt_fract ht))
    exact prod_mem_nhds univ_mem (Icc_mem_nhds (fract_pos.2 ht) (fract_lt_one _))
/-
**ContinuousOn.comp_fract** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp_fract {X Y : Type*} [TopologicalSpace X] [TopologicalSpa
ce Y] {f : X → ℝ → Y} {g : X → ℝ} (hf : Continuous ↿f) (hg : Continuous g) (h : 
∀ s, f s 0 = f s 1) : Continuous (fun x ↦ f x (fract (g x))) ``` With `Continuou
sAt` you can be even more precise about what to prove in case of discontinuities
, see e.g. `ContinuousAt.comp_div_cases`. - /  library_note «comp_of_eq lemmas» 
/-- Lean's elaborator has trouble elaborating applications of lemmas that state 
that the composition of two
参数：hf : Continuous ↿f；hg : Continuous g；h : ∀ s, f s 0 = f s 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `ContinuousOn.comp_fract'`：ContinuousOn.comp_fract' {f : β -> α -> γ} (h 
: ContinuousOn (uncurry f) <| univ ×ˢ I) (hf : forall s, f s 0 = f s 1) : Contin
uous fun st : …
· 使用定理 `Continuous.prodMk`：Continuous.prodMk {f : Z -> X} {g : Z -> Y} (hf : Con
tinuous f) (hg : Continuous g) : Continuous fun x => (f x, g x)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x) -/
-/
theorem ContinuousOn.comp_fract {s : β → α} {f : β → α → γ}
    (h : ContinuousOn (uncurry f) <| univ ×ˢ Icc 0 1) (hs : Continuous s)
    (hf : ∀ s, f s 0 = f s 1) : Continuous fun x : β => f x <| Int.fract (s x) :=
  (h.comp_fract' hf).comp (continuous_id.prodMk hs)

/-- A special case of `ContinuousOn.comp_fract`. -/
/-
**ContinuousOn.comp_fract''** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousOn.comp_fract'' {f : α -> β} (h : ContinuousOn f I) (hf : f 0 = 
f 1) : Continuous (f ∘ fract)
参数：h : ContinuousOn f I；hf : f 0 = f 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ContinuousOn.comp_fract`：ContinuousOn.comp_fract {X Y : Type*} [Topologi
calSpace X] [TopologicalSpace Y] {f : X → ℝ → Y} {g : X → ℝ} (hf : Continuous ↿f
) (hg : Conti…
· 使用定理 `ContinuousOn.comp`：ContinuousOn.comp {g : β -> γ} {t : Set β} (hg : Cont
inuousOn g t) (hf : ContinuousOn f s) (h : MapsTo f s t) : ContinuousOn (g ∘ f) 
s
· 使用定理 `continuousOn_snd`：continuousOn_snd {s : Set (α × β)} : ContinuousOn Prod
.snd s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)

--- 原说明 ---
A special case of `ContinuousOn.comp_fract`.
-/
theorem ContinuousOn.comp_fract'' {f : α → β} (h : ContinuousOn f I) (hf : f 0 = f 1) :
    Continuous (f ∘ fract) :=
  ContinuousOn.comp_fract (h.comp continuousOn_snd fun _x hx => (mem_prod.mp hx).2) continuous_id
    fun _ => hf
