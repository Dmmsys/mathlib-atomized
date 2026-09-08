/-
Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir, María Inés de Frutos-Fernández
-/
module

public import Mathlib.Topology.Algebra.LinearTopology
public import Mathlib.RingTheory.Ideal.Basic

/-! # Topologically nilpotent elements

Let `M` be a monoid with zero `M`, endowed with a topology.

* `IsTopologicallyNilpotent a` says that `a : M` is *topologically nilpotent*,
  i.e., its powers converge to zero.

* `IsTopologicallyNilpotent.map`:
  The image of a topologically nilpotent element under a continuous morphism of
  monoids with zero endowed with a topology is topologically nilpotent.

* `IsTopologicallyNilpotent.zero`: `0` is topologically nilpotent.

Let `R` be a commutative ring with a linear topology.

* `IsTopologicallyNilpotent.mul_left`: if `a : R` is topologically nilpotent,
  then `a*b` is topologically nilpotent.

* `IsTopologicallyNilpotent.mul_right`: if `a : R` is topologically nilpotent,
  then `a * b` is topologically nilpotent.

* `IsTopologicallyNilpotent.add`: if `a b : R` are topologically nilpotent,
  then `a + b` is topologically nilpotent.

These lemmas are actually deduced from their analogues for commuting elements of rings.

-/

@[expose] public section

open Filter

open scoped Topology

/-- An element is topologically nilpotent if its powers converge to `0`. -/
/-
**IsTopologicallyNilpotent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsTopologicallyNilpotent {R : Type*} [MonoidWithZero R] [TopologicalSpace 
R] (a : R) : Prop
参数：a : R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An element is topologically nilpotent if its powers converge to `0`.
-/
def IsTopologicallyNilpotent
    {R : Type*} [MonoidWithZero R] [TopologicalSpace R] (a : R) : Prop :=
  Tendsto (a ^ ·) atTop (𝓝 0)

namespace IsTopologicallyNilpotent

section MonoidWithZero

variable {R S : Type*} [TopologicalSpace R] [MonoidWithZero R]
  [MonoidWithZero S] [TopologicalSpace S]

/-- The image of a topologically nilpotent element under a continuous morphism
  is topologically nilpotent -/
/-
**IsTopologicallyNilpotent.map** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologicallyNilpote
nt`。
形式化陈述：map {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {φ : F} (hφ
 : Continuous φ) {a : R} (ha : IsTopologicallyNilpotent a) : IsTopologicallyNilp
otent (φ a)
参数：hφ : Continuous φ；ha : IsTopologicallyNilpotent a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
The image of a topologically nilpotent element under a continuous morphism
  is topologically nilpotent
-/
theorem map {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S]
    {φ : F} (hφ : Continuous φ) {a : R} (ha : IsTopologicallyNilpotent a) :
    IsTopologicallyNilpotent (φ a) := by
  unfold IsTopologicallyNilpotent at ha ⊢
  simp_rw [← map_pow]
  exact (map_zero φ ▸ hφ.tendsto 0).comp ha

/-- `0` is topologically nilpotent -/
/-
**IsTopologicallyNilpotent.zero** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologicallyNilpot
ent`。
形式化陈述：zero : IsTopologicallyNilpotent (0 : R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_atTop_of_eventually_const`：tendsto_atTop_of_eventually_const {ι 
: Type*} [Preorder ι] {u : ι -> X} {i₀ : ι} (h : forall i >= i₀, u i = x) : Tend
sto u atTop (𝓝 x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.ne_zero_iff_zero_lt`：∀ {n : ℕ}, n ≠ 0 ↔ 0 < n

--- 原说明 ---
`0` is topologically nilpotent
-/
theorem zero : IsTopologicallyNilpotent (0 : R) :=
  tendsto_atTop_of_eventually_const (i₀ := 1)
    (fun _ hi => by rw [zero_pow (Nat.ne_zero_iff_zero_lt.mpr hi)])
/-
**IsTopologicallyNilpotent._root_.IsNilpotent.isTopologicallyNilpotent** 是 Mathl
ib 中的一个定理，位于命名空间 `IsTopologicallyNilpotent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.IsNilpotent.isTopologicallyNilpotent {a : R} (ha : IsNilpotent a) :
    IsTopologicallyNilpotent a := by
  obtain ⟨n, hn⟩ := ha
  apply tendsto_atTop_of_eventually_const (i₀ := n)
  intro i hi
  rw [← Nat.add_sub_of_le hi, pow_add, hn, zero_mul]
/-
**IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds** 是 Mathlib 中的一个定理，位于命名空间 
`IsTopologicallyNilpotent`。
形式化陈述：exists_pow_mem_of_mem_nhds {a : R} (ha : IsTopologicallyNilpotent a) {v : 
Set R} (hv : v in 𝓝 0) : exists n, a ^ n in v
参数：ha : IsTopologicallyNilpotent a；hv : v in 𝓝 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_mem`：∀ {α : Type u_1} {β : Type u_2} {f : α → 
β} {l₁ : Filter α} {l₂ : Filter β} {s : Set β},   Filter.Tendsto f l₁ l₂ → s ∈ l
₂ → ∀ᶠ (x : α) in l…
-/
theorem exists_pow_mem_of_mem_nhds {a : R} (ha : IsTopologicallyNilpotent a)
    {v : Set R} (hv : v ∈ 𝓝 0) :
    ∃ n, a ^ n ∈ v :=
  (ha.eventually_mem hv).exists

end MonoidWithZero

section Ring

variable {R : Type*} [TopologicalSpace R] [Ring R]

/-- If `a` and `b` commute and `a` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
/-
**IsTopologicallyNilpotent.mul_right_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsTop
ologicallyNilpotent`。
形式化陈述：mul_right_of_commute [IsLinearTopology Rᵐᵒᵖ R] {a b : R} (ha : IsTopologic
allyNilpotent a) (hab : Commute a b) : IsTopologicallyNilpotent (a * b)
参数：ha : IsTopologicallyNilpotent a；hab : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `IsLinearTopology.tendsto_mul_zero_of_left`：tendsto_mul_zero_of_left [IsL
inearTopology Rᵐᵒᵖ R] {ι : Type*} {f : Filter ι} (a b : ι -> R) (ha : Tendsto a 
f (𝓝 0)) : Tendsto (a * b) f (𝓝…

--- 原说明 ---
If `a` and `b` commute and `a` is topologically nilpotent,
  then `a * b` is topologically nilpotent.
-/
theorem mul_right_of_commute [IsLinearTopology Rᵐᵒᵖ R]
    {a b : R} (ha : IsTopologicallyNilpotent a) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_left _ _ ha

/-- If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent. -/
/-
**IsTopologicallyNilpotent.mul_left_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsTopo
logicallyNilpotent`。
形式化陈述：mul_left_of_commute [IsLinearTopology R R] {a b : R} (hb : IsTopologically
Nilpotent b) (hab : Commute a b) : IsTopologicallyNilpotent (a * b)
参数：hb : IsTopologicallyNilpotent b；hab : Commute a b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Commute.mul_pow`：∀ {M : Type u_2} [inst : Monoid M] {a b : M}, Commute a
 b → ∀ (n : ℕ), (a * b) ^ n = a ^ n * b ^ n
· 使用定理 `IsLinearTopology.tendsto_mul_zero_of_right`：tendsto_mul_zero_of_right [I
sLinearTopology R R] {ι : Type*} {f : Filter ι} (a b : ι -> R) (hb : Tendsto b f
 (𝓝 0)) : Tendsto (a * b) f (𝓝 0…

--- 原说明 ---
If `a` and `b` commute and `b` is topologically nilpotent,
  then `a * b` is topologically nilpotent.
-/
theorem mul_left_of_commute [IsLinearTopology R R] {a b : R}
    (hb : IsTopologicallyNilpotent b) (hab : Commute a b) :
    IsTopologicallyNilpotent (a * b) := by
  simp_rw [IsTopologicallyNilpotent, hab.mul_pow]
  exact IsLinearTopology.tendsto_mul_zero_of_right _ _ hb

/-- If `a` and `b` are topologically nilpotent and commute,
  then `a + b` is topologically nilpotent. -/
/-
**IsTopologicallyNilpotent.add_of_commute** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologic
allyNilpotent`。
形式化陈述：add_of_commute [IsLinearTopology R R] {a b : R} (ha : IsTopologicallyNilpo
tent a) (hb : IsTopologicallyNilpotent b) (h : Commute a b) : IsTopologicallyNil
potent (a + b)
参数：ha : IsTopologicallyNilpotent a；hb : IsTopologicallyNilpotent b；h : Commute a
 b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `Filter.atTop_basis`：atTop_basis [Nonempty α] : (@atTop α _).HasBasis (fu
n _ => True) Ici
· 使用定理 `IsLinearTopology.hasBasis_ideal`：hasBasis_ideal [IsLinearTopology R R] :
 (𝓝 0).HasBasis (fun I : Ideal R => (I : Set R) in 𝓝 0) (fun I : Ideal R => (I :
 Set R))
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `IsTopologicallyNilpotent.exists_pow_mem_of_mem_nhds`：exists_pow_mem_of_m
em_nhds {a : R} (ha : IsTopologicallyNilpotent a) {v : Set R} (hv : v in 𝓝 0) : 
exists n, a ^ n in v
· 使用定理 `Ideal.add_pow_mem_of_pow_mem_of_le_of_commute`：add_pow_mem_of_pow_mem_of
_le_of_commute {m n k : Nat} (ha : a ^ m in I) (hb : b ^ n in I) (hk : m + n <= 
k + 1) (hab : Commute a b) : (a + b…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k

--- 原说明 ---
If `a` and `b` are topologically nilpotent and commute,
  then `a + b` is topologically nilpotent.
-/
theorem add_of_commute [IsLinearTopology R R] {a b : R}
    (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) (h : Commute a b) :
    IsTopologicallyNilpotent (a + b) := by
  simp only [IsTopologicallyNilpotent, atTop_basis.tendsto_iff IsLinearTopology.hasBasis_ideal,
    true_and]
  intro I I_mem_nhds
  obtain ⟨na, ha⟩ := ha.exists_pow_mem_of_mem_nhds I_mem_nhds
  obtain ⟨nb, hb⟩ := hb.exists_pow_mem_of_mem_nhds I_mem_nhds
  exact ⟨na + nb, fun m hm ↦
    I.add_pow_mem_of_pow_mem_of_le_of_commute ha hb (le_trans hm (Nat.le_add_right _ _)) h⟩

end Ring

section CommRing

variable {R : Type*} [TopologicalSpace R] [CommRing R] [IsLinearTopology R R]

/-- If `a` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
/-
**IsTopologicallyNilpotent.mul_right** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologicallyN
ilpotent`。
形式化陈述：mul_right {a : R} (ha : IsTopologicallyNilpotent a) (b : R) : IsTopologica
llyNilpotent (a * b)
参数：ha : IsTopologicallyNilpotent a；b : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.mul_right_of_commute`：mul_right_of_commute [IsL
inearTopology Rᵐᵒᵖ R] {a b : R} (ha : IsTopologicallyNilpotent a) (hab : Commute
 a b) : IsTopologicallyNilpotent (a…
· 使用定理 `IsLinearTopology.instMulOpposite`：∀ {R : Type u_1} [inst : CommRing R] [
inst_1 : TopologicalSpace R] [IsLinearTopology R R], IsLinearTopology Rᵐᵒᵖ R
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
If `a` is topologically nilpotent, then `a * b` is topologically nilpotent.
-/
theorem mul_right {a : R} (ha : IsTopologicallyNilpotent a) (b : R) :
    IsTopologicallyNilpotent (a * b) :=
  ha.mul_right_of_commute (Commute.all ..)

/-- If `b` is topologically nilpotent, then `a * b` is topologically nilpotent. -/
/-
**IsTopologicallyNilpotent.mul_left** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologicallyNi
lpotent`。
形式化陈述：mul_left (a : R) {b : R} (hb : IsTopologicallyNilpotent b) : IsTopological
lyNilpotent (a * b)
参数：a : R；hb : IsTopologicallyNilpotent b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.mul_left_of_commute`：mul_left_of_commute [IsLin
earTopology R R] {a b : R} (hb : IsTopologicallyNilpotent b) (hab : Commute a b)
 : IsTopologicallyNilpotent (a * b…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
If `b` is topologically nilpotent, then `a * b` is topologically nilpotent.
-/
theorem mul_left (a : R) {b : R} (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a * b) :=
  hb.mul_left_of_commute (Commute.all ..)

/-- If `a` and `b` are topologically nilpotent, then `a + b` is topologically nilpotent. -/
/-
**IsTopologicallyNilpotent.add** 是 Mathlib 中的一个定理，位于命名空间 `IsTopologicallyNilpote
nt`。
形式化陈述：add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpo
tent b) : IsTopologicallyNilpotent (a + b)
参数：ha : IsTopologicallyNilpotent a；hb : IsTopologicallyNilpotent b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicallyNilpotent.add_of_commute`：add_of_commute [IsLinearTopolog
y R R] {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpoten
t b) (h : Commute a b) : IsTo…
· 使用定理 `Commute.all`：∀ {S : Type u_3} [inst : CommMagma S] (a b : S), Commute a 
b

--- 原说明 ---
If `a` and `b` are topologically nilpotent, then `a + b` is topologically nilpot
ent.
-/
theorem add {a b : R} (ha : IsTopologicallyNilpotent a) (hb : IsTopologicallyNilpotent b) :
    IsTopologicallyNilpotent (a + b) :=
  ha.add_of_commute hb (Commute.all ..)

variable (R) in
/-- The topological nilradical of a ring with a linear topology -/
@[simps]
/-
**IsTopologicallyNilpotent._root_.topologicalNilradical** 是 Mathlib 中的一个定义，位于命名空
间 `IsTopologicallyNilpotent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topological nilradical of a ring with a linear topology
-/
def _root_.topologicalNilradical : Ideal R where
  carrier := {a | IsTopologicallyNilpotent a}
  add_mem' := add
  zero_mem' := zero
  smul_mem' := mul_left

set_option backward.isDefEq.respectTransparency false in
/-
**IsTopologicallyNilpotent.mem_topologicalNilradical_iff** 是 Mathlib 中的一个定理，位于命名
空间 `IsTopologicallyNilpotent`。
形式化陈述：mem_topologicalNilradical_iff {a : R} : a in topologicalNilradical R ↔ IsT
opologicallyNilpotent a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicallyNilpotent.add`：add {a b : R} (ha : IsTopologicallyNilpote
nt a) (hb : IsTopologicallyNilpotent b) : IsTopologicallyNilpotent (a + b)
· 使用定理 `IsTopologicallyNilpotent.mul_left`：mul_left (a : R) {b : R} (hb : IsTopo
logicallyNilpotent b) : IsTopologicallyNilpotent (a * b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_topologicalNilradical_iff {a : R} :
    a ∈ topologicalNilradical R ↔ IsTopologicallyNilpotent a := by
  simp [topologicalNilradical]

end CommRing

end IsTopologicallyNilpotent

