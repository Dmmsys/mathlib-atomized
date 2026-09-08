/-
Copyright (c) 2022 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, David Loeffler
-/
module

public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Algebra.Algebra.Pi

/-!
# Zero and Bounded at filter

Given a filter `l` we define the notion of a function being `ZeroAtFilter` as well as being
`BoundedAtFilter`. Alongside this we construct the `Submodule`, `AddSubmonoid` of functions
that are `ZeroAtFilter`. Similarly, we construct the `Submodule` and `Subalgebra` of functions
that are `BoundedAtFilter`.

-/

@[expose] public section


namespace Filter

variable {𝕜 α β : Type*}

open Topology

/-- If `l` is a filter on `α`, then a function `f : α → β` is `ZeroAtFilter l`
  if it tends to zero along `l`. -/
/-
**Filter.ZeroAtFilter** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α -> β) : P
rop
参数：l : Filter α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `l` is a filter on `α`, then a function `f : α → β` is `ZeroAtFilter l`
  if it tends to zero along `l`.
-/
def ZeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) (f : α → β) : Prop :=
  Filter.Tendsto f l (𝓝 0)
/-
**Filter.zero_zeroAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) : ZeroAtFil
ter l (0 : α -> β)
参数：l : Filter α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem zero_zeroAtFilter [Zero β] [TopologicalSpace β] (l : Filter α) :
    ZeroAtFilter l (0 : α → β) :=
  tendsto_const_nhds

nonrec theorem ZeroAtFilter.add [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    {l : Filter α} {f g : α → β} (hf : ZeroAtFilter l f) (hg : ZeroAtFilter l g) :
    ZeroAtFilter l (f + g) := by
  simpa using! hf.add hg

nonrec theorem ZeroAtFilter.neg [TopologicalSpace β] [SubtractionMonoid β] [ContinuousNeg β]
    {l : Filter α} {f : α → β} (hf : ZeroAtFilter l f) : ZeroAtFilter l (-f) := by
  simpa using! hf.neg
/-
**Filter.ZeroAtFilter.smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.ZeroAtFilter`。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} {β : Type u_3} [inst : TopologicalSpace β]
 [inst_1 : Zero β]   [inst_2 : SMulZeroClass 𝕜 β] [ContinuousConstSMul 𝕜 β] {l :
 Filter α} {f : α → β} (c : 𝕜),   l.ZeroAtFilter f → l.ZeroAtFilter (c • f)
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `Filter.Tendsto.const_smul`：Filter.Tendsto.const_smul {f : β -> α} {l : F
ilter β} {a : α} (hf : Tendsto f l (𝓝 a)) (c : M) : Tendsto (fun x => c • f x) l
 (𝓝 (c • a))
-/
theorem ZeroAtFilter.smul [TopologicalSpace β] [Zero β]
    [SMulZeroClass 𝕜 β] [ContinuousConstSMul 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜)
    (hf : ZeroAtFilter l f) : ZeroAtFilter l (c • f) := by simpa using! hf.const_smul c

variable (𝕜) in
/-- `zeroAtFilterSubmodule l` is the submodule of `f : α → β` which
tend to zero along `l`. -/
/-
**Filter.zeroAtFilterSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：zeroAtFilterSubmodule [TopologicalSpace β] [Semiring 𝕜] [AddCommMonoid β] 
[Module 𝕜 β] [ContinuousAdd β] [ContinuousConstSMul 𝕜 β] (l : Filter α) : Submod
ule 𝕜 (α -> β) where carrier
参数：l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`zeroAtFilterSubmodule l` is the submodule of `f : α → β` which
tend to zero along `l`.
-/
def zeroAtFilterSubmodule
    [TopologicalSpace β] [Semiring 𝕜] [AddCommMonoid β] [Module 𝕜 β]
    [ContinuousAdd β] [ContinuousConstSMul 𝕜 β]
    (l : Filter α) : Submodule 𝕜 (α → β) where
  carrier := {f | ZeroAtFilter l f}
  zero_mem' := zero_zeroAtFilter l
  add_mem' ha hb := ha.add hb
  smul_mem' c _ hf := hf.smul c

/-- `zeroAtFilterAddSubmonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`. -/
/-
**Filter.zeroAtFilterAddSubmonoid** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [Continuous
Add β] (l : Filter α) : AddSubmonoid (α -> β) where carrier
参数：l : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.ZeroAtFilter.add`：∀ {α : Type u_2} {β : Type u_3} [inst : Topolog
icalSpace β] [inst_1 : AddZeroClass β] [ContinuousAdd β] {l : Filter α}   {f g :
 α → β}, l.Ze…

--- 原说明 ---
`zeroAtFilterAddSubmonoid l` is the additive submonoid of `f : α → β`
which tend to zero along `l`.
-/
def zeroAtFilterAddSubmonoid [TopologicalSpace β] [AddZeroClass β] [ContinuousAdd β]
    (l : Filter α) : AddSubmonoid (α → β) where
  carrier := {f | ZeroAtFilter l f}
  add_mem' ha hb := ha.add hb
  zero_mem' := zero_zeroAtFilter l

/-- If `l` is a filter on `α`, then a function `f: α → β` is `BoundedAtFilter l`
if `f =O[l] 1`. -/
/-
**Filter.BoundedAtFilter** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：BoundedAtFilter [Norm β] (l : Filter α) (f : α -> β) : Prop
参数：l : Filter α；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `l` is a filter on `α`, then a function `f: α → β` is `BoundedAtFilter l`
if `f =O[l] 1`.
-/
def BoundedAtFilter [Norm β] (l : Filter α) (f : α → β) : Prop :=
  Asymptotics.IsBigO l f (1 : α → ℝ)
/-
**Filter.ZeroAtFilter.boundedAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.ZeroAtFi
lter`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedAddGroup β] {l : Filter 
α} {f : α → β},   l.ZeroAtFilter f → l.BoundedAtFilter f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem ZeroAtFilter.boundedAtFilter [SeminormedAddGroup β] {l : Filter α} {f : α → β}
    (hf : ZeroAtFilter l f) : BoundedAtFilter l f :=
  ((Asymptotics.isLittleO_one_iff _).mpr hf).isBigO
/-
**Filter.const_boundedAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：const_boundedAtFilter [Norm β] (l : Filter α) (c : β) : BoundedAtFilter l 
(Function.const α c : α -> β)
参数：l : Filter α；c : β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_const_const`：isBigO_const_const (c : E) {c' : F''} (h
c' : c' != 0) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => c'
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem const_boundedAtFilter [Norm β] (l : Filter α) (c : β) :
    BoundedAtFilter l (Function.const α c : α → β) :=
  Asymptotics.isBigO_const_const c one_ne_zero l

-- TODO(https://github.com/leanprover-community/mathlib4/issues/19288): Remove all Comm in the next
-- three lemmas. This would require modifying the corresponding general asymptotics lemma.
nonrec theorem BoundedAtFilter.add [SeminormedAddCommGroup β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f + g) := by
  simpa using! hf.add hg
/-
**Filter.BoundedAtFilter.neg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.BoundedAtFilter`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedAddCommGroup β] {l : Fil
ter α} {f : α → β},   l.BoundedAtFilter f → l.BoundedAtFilter (-f)
参数：-f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type 
u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α 
→ E'} {l : Filter…
-/
theorem BoundedAtFilter.neg [SeminormedAddCommGroup β] {l : Filter α} {f : α → β}
    (hf : BoundedAtFilter l f) : BoundedAtFilter l (-f) :=
  hf.neg_left
/-
**Filter.BoundedAtFilter.smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.BoundedAtFilter`
。
形式化陈述：∀ {𝕜 : Type u_1} {α : Type u_2} {β : Type u_3} [inst : SeminormedRing 𝕜] [
inst_1 : SeminormedAddCommGroup β]   [inst_2 : _root_.Module 𝕜 β] [IsBoundedSMul
 𝕜 β] {l : Filter α} {f : α → β} (c : 𝕜),   l.BoundedAtFilter f → l.BoundedAtFil
ter (c • f)
参数：c : 𝕜；c • f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.const_smul_left`：∀ {α : Type u_1} {F : Type u_4} {E' 
: Type u_6} {R : Type u_13} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E']
   [inst_2 : SeminormedR…
-/
theorem BoundedAtFilter.smul
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β]
    {l : Filter α} {f : α → β} (c : 𝕜) (hf : BoundedAtFilter l f) : BoundedAtFilter l (c • f) :=
  hf.const_smul_left c

nonrec theorem BoundedAtFilter.mul [SeminormedRing β] {l : Filter α} {f g : α → β}
    (hf : BoundedAtFilter l f) (hg : BoundedAtFilter l g) : BoundedAtFilter l (f * g) := by
  refine (hf.mul hg).trans ?_
  convert! Asymptotics.isBigO_refl (E := ℝ) _ l
  simp
/-
**Filter.ZeroAtFilter.mul_boundedAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Zero
AtFilter`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedRing β] {l : Filter α} {
f g : α → β},   l.ZeroAtFilter f → l.BoundedAtFilter g → l.ZeroAtFilter (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.ZeroAtFilter.eq_1`：∀ {α : Type u_2} {β : Type u_3} [inst : Zero β
] [inst_1 : TopologicalSpace β] (l : Filter α) (f : α → β),   l.ZeroAtFilter f =
 Filter.Tendst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem ZeroAtFilter.mul_boundedAtFilter [SeminormedRing β] {l : Filter α}
    {f g : α → β} (hf : ZeroAtFilter l f) (hg : BoundedAtFilter l g) : ZeroAtFilter l (f * g) := by
  rw [ZeroAtFilter, ← Asymptotics.isLittleO_one_iff (F := ℝ)] at hf ⊢
  simpa using! hf.mul_isBigO hg
/-
**Filter.BoundedAtFilter.mul_zeroAtFilter** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Boun
dedAtFilter`。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} [inst : SeminormedRing β] {l : Filter α} {
f g : α → β},   l.BoundedAtFilter f → l.ZeroAtFilter g → l.ZeroAtFilter (f * g)
参数：f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.ZeroAtFilter.eq_1`：∀ {α : Type u_2} {β : Type u_3} [inst : Zero β
] [inst_1 : TopologicalSpace β] (l : Filter α) (f : α → β),   l.ZeroAtFilter f =
 Filter.Tendst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem BoundedAtFilter.mul_zeroAtFilter [SeminormedRing β] {l : Filter α}
    {f g : α → β} (hf : BoundedAtFilter l f) (hg : ZeroAtFilter l g) : ZeroAtFilter l (f * g) := by
  rw [ZeroAtFilter, ← Asymptotics.isLittleO_one_iff (F := ℝ)] at hg ⊢
  simpa using! hf.mul_isLittleO hg

variable (𝕜) in
/-- The submodule of functions that are bounded along a filter `l`. -/
/-
**Filter.boundedFilterSubmodule** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：boundedFilterSubmodule [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Modu
le 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) : Submodule 𝕜 (α -> β) where carrier
参数：l : Filter α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.BoundedAtFilter.add`：∀ {α : Type u_2} {β : Type u_3} [inst : Semi
normedAddCommGroup β] {l : Filter α} {f g : α → β},   l.BoundedAtFilter f → l.Bo
undedAtFilter g …
· 使用定理 `Filter.BoundedAtFilter.smul`：∀ {𝕜 : Type u_1} {α : Type u_2} {β : Type u
_3} [inst : SeminormedRing 𝕜] [inst_1 : SeminormedAddCommGroup β]   [inst_2 : _r
oot_.Module 𝕜 β] …

--- 原说明 ---
The submodule of functions that are bounded along a filter `l`.
-/
def boundedFilterSubmodule
    [SeminormedRing 𝕜] [SeminormedAddCommGroup β] [Module 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) :
    Submodule 𝕜 (α → β) where
  carrier := {f | BoundedAtFilter l f}
  zero_mem' := const_boundedAtFilter l 0
  add_mem' hf hg := hf.add hg
  smul_mem' c _ hf := hf.smul c

variable (𝕜) in
/-- The subalgebra of functions that are bounded along a filter `l`. -/
/-
**Filter.boundedFilterSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：boundedFilterSubalgebra [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra
 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) : Subalgebra 𝕜 (α -> β)
参数：l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subalgebra of functions that are bounded along a filter `l`.
-/
def boundedFilterSubalgebra
    [SeminormedCommRing 𝕜] [SeminormedRing β] [Algebra 𝕜 β] [IsBoundedSMul 𝕜 β] (l : Filter α) :
    Subalgebra 𝕜 (α → β) :=
  Submodule.toSubalgebra
    (boundedFilterSubmodule 𝕜 l)
    (const_boundedAtFilter l (1 : β))
    (fun f g hf hg ↦ by simpa only [Pi.one_apply, mul_one, norm_mul] using! hf.mul hg)
/-
**Filter.BoundedAtFilter.prod** 是 Mathlib 中的一个定理，位于命名空间 `Filter.BoundedAtFilter`
。
形式化陈述：∀ {α : Type u_2} {β : Type u_3} {ι : Type} (s : Finset ι) [inst : Seminorm
edCommRing β] {l : Filter α} {f : ι → α → β},   (∀ i ∈ s, l.BoundedAtFilter (f i
)) → l.BoundedAtFilter (∏ i ∈ s, f i)
参数：s : Finset ι；∀ i ∈ s, l.BoundedAtFilter (f i)；∏ i ∈ s, f i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.prod_mem`：∀ {R : Type u} {A : Type v} [inst : CommSemiring R]
 [inst_1 : CommSemiring A] [inst_2 : Algebra R A]   (S : Subalgebra R A) {ι : Ty
pe w} {t …
-/
theorem BoundedAtFilter.prod {ι : Type} (s : Finset ι) [SeminormedCommRing β]
    {l : Filter α} {f : ι → α → β} (h : ∀ i ∈ s, BoundedAtFilter l (f i)) :
    BoundedAtFilter l (∏ i ∈ s, f i) :=
  (boundedFilterSubalgebra β l).prod_mem (f := f) h

end Filter

