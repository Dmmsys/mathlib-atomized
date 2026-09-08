/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Yury Kudryashov
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Analysis.Normed.Group.InfiniteSum
public import Mathlib.Analysis.Normed.MulAction
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity

/-!
# Further basic lemmas about asymptotics

-/

public section

open Set Topology Filter NNReal

namespace Asymptotics


variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {E''' : Type*}
  {R : Type*} {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]
variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedAddGroup E''']
  [SeminormedRing R']

variable [NormedDivisionRing 𝕜] [NormedDivisionRing 𝕜']
variable {c c' c₁ c₂ : ℝ} {f : α → E} {g : α → F} {k : α → G}
variable {f' : α → E'} {g' : α → F'} {k' : α → G'}
variable {f'' : α → E''} {g'' : α → F''} {k'' : α → G''}
variable {l l' : Filter α}
@[simp]
/-
**Asymptotics.isBigOWith_principal** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ forall x in s,
 ‖f x‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.eventually_principal`：eventually_principal {a : Set α} {p : α -> 
Prop} : (forallᶠ x in 𝓟 a, p x) ↔ forall x in a, p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBigOWith_principal {s : Set α} : IsBigOWith c (𝓟 s) f g ↔ ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [IsBigOWith_def, eventually_principal]
/-
**Asymptotics.isBigO_principal** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ exists c, forall x in s, ‖f x
‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_principal {s : Set α} : f =O[𝓟 s] g ↔ ∃ c, ∀ x ∈ s, ‖f x‖ ≤ c * ‖g x‖ := by
  simp_rw [isBigO_iff, eventually_principal]

@[simp]
/-
**Asymptotics.isLittleO_principal** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_principal {s : Set α} : f'' =o[𝓟 s] g' ↔ forall x in s, f'' x = 
0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `le_of_tendsto_of_tendsto`：le_of_tendsto_of_tendsto {f g : β -> α} {b : F
ilter β} {a₁ a₂ : α} [hb : NeBot b] (hf : Tendsto f b (𝓝 a₁)) (hg : Tendsto g b 
(𝓝 a₂)) (h : f…
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Filter.eventually_principal`：eventually_principal {a : Set α} {p : α -> 
Prop} : (forallᶠ x in 𝓟 a, p x) ↔ forall x in a, p x
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem isLittleO_principal {s : Set α} : f'' =o[𝓟 s] g' ↔ ∀ x ∈ s, f'' x = 0 := by
  refine ⟨fun h x hx ↦ norm_le_zero_iff.1 ?_, fun h ↦ ?_⟩
  · simp only [isLittleO_iff] at h
    have : Tendsto (fun c : ℝ => c * ‖g' x‖) (𝓝[>] 0) (𝓝 0) :=
      ((continuous_id.mul continuous_const).tendsto' _ _ (zero_mul _)).mono_left
        inf_le_left
    apply le_of_tendsto_of_tendsto tendsto_const_nhds this
    apply eventually_nhdsWithin_iff.2 (Eventually.of_forall (fun c hc ↦ ?_))
    exact eventually_principal.1 (h hc) x hx
  · apply (isLittleO_zero g' _).congr' ?_ EventuallyEq.rfl
    exact fun x hx ↦ (h x hx).symm

@[simp]
/-
**Asymptotics.isBigOWith_top** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_top : IsBigOWith c ⊤ f g ↔ forall x, ‖f x‖ <= c * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.eventually_top`：eventually_top {p : α -> Prop} : (forallᶠ x in ⊤,
 p x) ↔ forall x, p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBigOWith_top : IsBigOWith c ⊤ f g ↔ ∀ x, ‖f x‖ ≤ c * ‖g x‖ := by
  rw [IsBigOWith_def, eventually_top]

@[simp]
/-
**Asymptotics.isBigO_top** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_top : f =O[⊤] g ↔ exists C, forall x, ‖f x‖ <= C * ‖g x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_top : f =O[⊤] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  simp_rw [isBigO_iff, eventually_top]

@[simp]
/-
**Asymptotics.isLittleO_top** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_top : f'' =o[⊤] g' ↔ forall x, f'' x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleO_top : f'' =o[⊤] g' ↔ ∀ x, f'' x = 0 := by
  simp only [← principal_univ, isLittleO_principal, mem_univ, forall_true_left]

section

variable (F)
variable [One F] [NormOneClass F]

/-
**Asymptotics.isBigOWith_const_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_const_one (c : E) (l : Filter α) : IsBigOWith ‖c‖ l (fun _x : α
 => c) fun _x => (1 : F)
参数：c : E；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
-/
theorem isBigOWith_const_one (c : E) (l : Filter α) :
    IsBigOWith ‖c‖ l (fun _x : α => c) fun _x => (1 : F) := by simp [isBigOWith_iff]
/-
**Asymptotics.isBigO_const_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_one (c : E) (l : Filter α) : (fun _x : α => c) =O[l] fun _x =
> (1 : F)
参数：c : E；l : Filter α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.isBigOWith_const_one`：isBigOWith_const_one (c : E) (l : Filt
er α) : IsBigOWith ‖c‖ l (fun _x : α => c) fun _x => (1 : F)
-/
theorem isBigO_const_one (c : E) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => (1 : F) :=
  (isBigOWith_const_one F c l).isBigO
/-
**Asymptotics.isLittleO_const_iff_isLittleO_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics`。
形式化陈述：isLittleO_const_iff_isLittleO_one {c : F''} (hc : c != 0) : (f =o[l] fun _
x => c) ↔ f =o[l] fun _x => (1 : F)
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} 
{F : Type u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G
]   {c : ℝ} {f : α → E} {g :…
· 使用定理 `Asymptotics.isBigOWith_const_one`：isBigOWith_const_one (c : E) (l : Filt
er α) : IsBigOWith ‖c‖ l (fun _x : α => c) fun _x => (1 : F)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Asymptotics.isBigO_const_const`：isBigO_const_const (c : E) {c' : F''} (h
c' : c' != 0) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => c'
-/
theorem isLittleO_const_iff_isLittleO_one {c : F''} (hc : c ≠ 0) :
    (f =o[l] fun _x => c) ↔ f =o[l] fun _x => (1 : F) :=
  ⟨fun h => h.trans_isBigOWith (isBigOWith_const_one _ _ _) (norm_pos_iff.2 hc),
   fun h => h.trans_isBigO <| isBigO_const_const _ hc _⟩

@[simp]
/-
**Asymptotics.isLittleO_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_one_iff {f : α -> E'''} : f =o[l] (fun _x => 1 : α -> F) ↔ Tends
to f l (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isLittleO_one_iff {f : α → E'''} : f =o[l] (fun _x => 1 : α → F) ↔ Tendsto f l (𝓝 0) := by
  simp only [isLittleO_iff, norm_one, mul_one, Metric.nhds_basis_closedBall.tendsto_right_iff,
    Metric.mem_closedBall, dist_zero_right]

@[simp]
/-
**Asymptotics.isBigO_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_one_iff : f =O[l] (fun _x => 1 : α -> F) ↔ IsBoundedUnder (· <= ·) 
l fun x => ‖f x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_one_iff : f =O[l] (fun _x => 1 : α → F) ↔
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ := by
  simp only [isBigO_iff, norm_one, mul_one, IsBoundedUnder, IsBounded, eventually_map]

alias ⟨_, _root_.Filter.IsBoundedUnder.isBigO_one⟩ := isBigO_one_iff

@[simp]
/-
**Asymptotics.isLittleO_one_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_one_left_iff : (fun _x => 1 : α -> F) =o[l] f ↔ Tendsto (fun x =
> ‖f x‖) l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_iff_nat_mul_le_aux`：isLittleO_iff_nat_mul_le_aux (
h₀ : (forall x, 0 <= ‖f x‖) ∨ forall x, 0 <= ‖g x‖) : f =o[l] g ↔ forall n : Nat
, forallᶠ x in l, ↑n * ‖f x‖ <…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.HasCountableBasis.toHasBasis`：∀ {α : Type u_1} {ι : Type u_4} {l 
: Filter α} {p : ι → Prop} {s : ι → Set α}, l.HasCountableBasis p s → l.HasBasis
 p s
· 使用定理 `atTop_hasCountableBasis_of_archimedean`：atTop_hasCountableBasis_of_archi
medean [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] : (atTop 
: Filter R).HasCountableBasi…
-/
theorem isLittleO_one_left_iff : (fun _x => 1 : α → F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop :=
  calc
    (fun _x => 1 : α → F) =o[l] f ↔ ∀ n : ℕ, ∀ᶠ x in l, ↑n * ‖(1 : F)‖ ≤ ‖f x‖ :=
      isLittleO_iff_nat_mul_le_aux <| Or.inl fun _x => by simp only [norm_one, zero_le_one]
    _ ↔ ∀ n : ℕ, True → ∀ᶠ x in l, ‖f x‖ ∈ Ici (n : ℝ) := by
      simp only [norm_one, mul_one, true_imp_iff, mem_Ici]
    _ ↔ Tendsto (fun x => ‖f x‖) l atTop :=
      atTop_hasCountableBasis_of_archimedean.1.tendsto_right_iff.symm
/-
**Asymptotics._root_.Filter.Tendsto.isBigO_one** 是 Mathlib 中的一个定理，位于命名空间 `Asympt
otics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.isBigO_one {c : E'} (h : Tendsto f' l (𝓝 c)) :
    f' =O[l] (fun _x => 1 : α → F) :=
  h.norm.isBoundedUnder_le.isBigO_one F
/-
**Asymptotics.IsBigO.trans_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sBigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} (F : Type u_4) {F' : Type u_7} [inst : Nor
m E] [inst_1 : Norm F]   [inst_2 : SeminormedAddCommGroup F'] {f : α → E} {g' : 
α → F'} {l : Filter α} [inst_3 : One F] [NormOneClass F],   f =O[l] g' → ∀ {y : 
F'}, Filter.Tendsto g' l (nhds y) → f =O[l] fun _x => 1
参数：F : Type u_4；nhds y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
-/
theorem IsBigO.trans_tendsto_nhds (hfg : f =O[l] g') {y : F'} (hg : Tendsto g' l (𝓝 y)) :
    f =O[l] (fun _x => 1 : α → F) :=
  hfg.trans <| hg.isBigO_one F

/-- The condition `f = O[𝓝[≠] a] 1` is equivalent to `f = O[𝓝 a] 1`. -/
/-
**Asymptotics.isBigO_one_nhds_ne_iff** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_one_nhds_ne_iff [TopologicalSpace α] {a : α} : f =O[𝓝[!=] a] (fun _
 => 1 : α -> F) ↔ f =O[𝓝 a] (fun _ => 1 : α -> F)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `le_max_right`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), b ≤ max
 a b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a

--- 原说明 ---
The condition `f = O[𝓝[≠] a] 1` is equivalent to `f = O[𝓝 a] 1`.
-/
lemma isBigO_one_nhds_ne_iff [TopologicalSpace α] {a : α} :
    f =O[𝓝[≠] a] (fun _ ↦ 1 : α → F) ↔ f =O[𝓝 a] (fun _ ↦ 1 : α → F) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.mono nhdsWithin_le_nhds⟩
  simp only [isBigO_one_iff, IsBoundedUnder, IsBounded, eventually_map] at h ⊢
  obtain ⟨c, hc⟩ := h
  use max c ‖f a‖
  filter_upwards [eventually_nhdsWithin_iff.mp hc] with b hb
  rcases eq_or_ne b a with rfl | hb'
  · apply le_max_right
  · exact (hb hb').trans (le_max_left ..)

end

/-
**Asymptotics.isLittleO_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_const_iff {c : F''} (hc : c != 0) : (f'' =o[l] fun _x => c) ↔ Te
ndsto f'' l (𝓝 0)
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isLittleO_const_iff_isLittleO_one`：isLittleO_const_iff_isLit
tleO_one {c : F''} (hc : c != 0) : (f =o[l] fun _x => c) ↔ f =o[l] fun _x => (1 
: F)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
-/
theorem isLittleO_const_iff {c : F''} (hc : c ≠ 0) :
    (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0) :=
  (isLittleO_const_iff_isLittleO_one ℝ hc).trans (isLittleO_one_iff _)
/-
**Asymptotics.isLittleO_id_const** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_id_const {c : F''} (hc : c != 0) : (fun x : E'' => x) =o[𝓝 0] fu
n _x => c
参数：hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_iff`：isLittleO_const_iff {c : F''} (hc : c !
= 0) : (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0)
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
-/
theorem isLittleO_id_const {c : F''} (hc : c ≠ 0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c :=
  (isLittleO_const_iff hc).mpr (continuous_id.tendsto 0)
/-
**Asymptotics._root_.Filter.IsBoundedUnder.isBigO_const** 是 Mathlib 中的一个定理，位于命名空
间 `Asymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.IsBoundedUnder.isBigO_const (h : IsBoundedUnder (· ≤ ·) l (norm ∘ f))
    {c : F''} (hc : c ≠ 0) : f =O[l] fun _x => c :=
  (h.isBigO_one ℝ).trans (isBigO_const_const _ hc _)
/-
**Asymptotics.isBigO_const_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc 
: c != 0) : f'' =O[l] fun _x => c
参数：h : Tendsto f'' l (𝓝 y)；hc : c != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.isBigO_const`：∀ {α : Type u_1} {E : Type u_3} {F''
 : Type u_10} [inst : Norm E] [inst_1 : NormedAddCommGroup F''] {f : α → E}   {l
 : Filter α}, Filter.IsB…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
-/
theorem isBigO_const_of_tendsto {y : E''} (h : Tendsto f'' l (𝓝 y)) {c : F''} (hc : c ≠ 0) :
    f'' =O[l] fun _x => c :=
  h.norm.isBoundedUnder_le.isBigO_const hc
/-
**Asymptotics.IsBigO.isBoundedUnder_le** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigO`。
形式化陈述：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : N
orm F] {f : α → E} {l : Filter α} {c : F},   (f =O[l] fun _x => c) → Filter.IsBo
undedUnder (fun x1 x2 => x1 ≤ x2) l (norm ∘ f)
参数：f =O[l] fun _x => c；fun x1 x2 => x1 ≤ x2；norm ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
O[l] g → ∃ c, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
-/
theorem IsBigO.isBoundedUnder_le {c : F} (h : f =O[l] fun _x => c) :
    IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  let ⟨c', hc'⟩ := h.bound
  ⟨c' * ‖c‖, eventually_map.2 hc'⟩
/-
**Asymptotics.isBigO_const_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_of_ne {c : F''} (hc : c != 0) : (f =O[l] fun _x => c) ↔ IsBou
ndedUnder (· <= ·) l (norm ∘ f)
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBoundedUnder_le`：∀ {α : Type u_1} {E : Type u_3} {F
 : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {l : Filter α} {c : F
},   (f =O[l] fun _x => c)…
· 使用定理 `Filter.IsBoundedUnder.isBigO_const`：∀ {α : Type u_1} {E : Type u_3} {F''
 : Type u_10} [inst : Norm E] [inst_1 : NormedAddCommGroup F''] {f : α → E}   {l
 : Filter α}, Filter.IsB…
-/
theorem isBigO_const_of_ne {c : F''} (hc : c ≠ 0) :
    (f =O[l] fun _x => c) ↔ IsBoundedUnder (· ≤ ·) l (norm ∘ f) :=
  ⟨fun h => h.isBoundedUnder_le, fun h => h.isBigO_const hc⟩
/-
**Asymptotics.isBigO_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_iff {c : F''} : (f'' =O[l] fun _x => c) ↔ (c = 0 -> f'' =ᶠ[l]
 0) ∧ IsBoundedUnder (· <= ·) l fun x => ‖f'' x‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_zero_right_iff`：isBigO_zero_right_iff : (f'' =O[l] fu
n _x => (0 : F')) ↔ f'' =ᶠ[l] 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.IsBigO.isBoundedUnder_le`：∀ {α : Type u_1} {E : Type u_3} {F
 : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {l : Filter α} {c : F
},   (f =O[l] fun _x => c)…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Filter.EventuallyEq.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : T
ype u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g :
 α → F}, f₁ =ᶠ[l] f₂ →…
· 使用定理 `Asymptotics.isBigO_zero`：isBigO_zero : (fun _x => (0 : E')) =O[l] g
· 使用定理 `Filter.IsBoundedUnder.isBigO_const`：∀ {α : Type u_1} {E : Type u_3} {F''
 : Type u_10} [inst : Norm E] [inst_1 : NormedAddCommGroup F''] {f : α → E}   {l
 : Filter α}, Filter.IsB…
-/
theorem isBigO_const_iff {c : F''} : (f'' =O[l] fun _x => c) ↔
    (c = 0 → f'' =ᶠ[l] 0) ∧ IsBoundedUnder (· ≤ ·) l fun x => ‖f'' x‖ := by
  refine ⟨fun h => ⟨fun hc => isBigO_zero_right_iff.1 (by rwa [← hc]), h.isBoundedUnder_le⟩, ?_⟩
  rintro ⟨hcf, hf⟩
  rcases eq_or_ne c 0 with (hc | hc)
  exacts [(hcf hc).trans_isBigO (isBigO_zero _ _), hf.isBigO_const hc]
/-
**Asymptotics.isBigO_iff_isBoundedUnder_le_div** 是 Mathlib 中的一个定理，位于命名空间 `Asympt
otics`。
形式化陈述：isBigO_iff_isBoundedUnder_le_div (h : forallᶠ x in l, g'' x != 0) : f =O[l
] g'' ↔ IsBoundedUnder (· <= ·) l fun x => ‖f x‖ / ‖g'' x‖
参数：h : forallᶠ x in l, g'' x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem isBigO_iff_isBoundedUnder_le_div (h : ∀ᶠ x in l, g'' x ≠ 0) :
    f =O[l] g'' ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x‖ / ‖g'' x‖ := by
  simp only [isBigO_iff, IsBoundedUnder, IsBounded, eventually_map]
  exact
    exists_congr fun c =>
      eventually_congr <| h.mono fun x hx => (div_le_iff₀ <| norm_pos_iff.2 hx).symm

/-- `(fun x ↦ c) =O[l] f` if and only if `f` is bounded away from zero. -/
/-
**Asymptotics.isBigO_const_left_iff_pos_le_norm** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics`。
形式化陈述：isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c != 0) : (fun _x => c) 
=O[l] f' ↔ exists b, 0 < b ∧ forallᶠ x in l, b <= ‖f' x‖
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用引理 `div_le_iff₀'`：div_le_iff₀' (hc : 0 < c) : b / c <= a ↔ b <= c * a
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_mul_eq_mul_div`：div_mul_eq_mul_div : a / b * c = a * c / b
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a

--- 原说明 ---
`(fun x ↦ c) =O[l] f` if and only if `f` is bounded away from zero.
-/
theorem isBigO_const_left_iff_pos_le_norm {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =O[l] f' ↔ ∃ b, 0 < b ∧ ∀ᶠ x in l, b ≤ ‖f' x‖ := by
  constructor
  · intro h
    rcases h.exists_pos with ⟨C, hC₀, hC⟩
    refine ⟨‖c‖ / C, div_pos (norm_pos_iff.2 hc) hC₀, ?_⟩
    exact hC.bound.mono fun x => (div_le_iff₀' hC₀).2
  · rintro ⟨b, hb₀, hb⟩
    refine IsBigO.of_bound (‖c‖ / b) (hb.mono fun x hx => ?_)
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact le_mul_of_one_le_right (norm_nonneg _) ((one_le_div hb₀).2 hx)
/-
**Asymptotics.IsBigO.trans_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {α : Type u_1} {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommG
roup E''] [inst_1 : NormedAddCommGroup F'']   {f'' : α → E''} {g'' : α → F''} {l
 : Filter α},   f'' =O[l] g'' → Filter.Tendsto g'' l (nhds 0) → Filter.Tendsto f
'' l (nhds 0)
参数：nhds 0；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem IsBigO.trans_tendsto (hfg : f'' =O[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  (isLittleO_one_iff ℝ).1 <| hfg.trans_isLittleO <| (isLittleO_one_iff ℝ).2 hg
/-
**Asymptotics.IsLittleO.trans_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {α : Type u_1} {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommG
roup E''] [inst_1 : NormedAddCommGroup F'']   {f'' : α → E''} {g'' : α → F''} {l
 : Filter α},   f'' =o[l] g'' → Filter.Tendsto g'' l (nhds 0) → Filter.Tendsto f
'' l (nhds 0)
参数：nhds 0；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_tendsto`：∀ {α : Type u_1} {E'' : Type u_9} {F''
 : Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] 
  {f'' : α → E''} {g''…
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
-/
theorem IsLittleO.trans_tendsto (hfg : f'' =o[l] g'') (hg : Tendsto g'' l (𝓝 0)) :
    Tendsto f'' l (𝓝 0) :=
  hfg.isBigO.trans_tendsto hg
/-
**Asymptotics.isLittleO_id_one** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_id_one [One F''] [NeZero (1 : F'')] : (fun x : E'' => x) =o[𝓝 0]
 (1 : E'' -> F'')
参数：1 : F''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_id_const`：isLittleO_id_const {c : F''} (hc : c != 
0) : (fun x : E'' => x) =o[𝓝 0] fun _x => c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
-/
lemma isLittleO_id_one [One F''] [NeZero (1 : F'')] : (fun x : E'' => x) =o[𝓝 0] (1 : E'' → F'') :=
  isLittleO_id_const one_ne_zero
/-
**Asymptotics.continuousAt_iff_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：continuousAt_iff_isLittleO {α : Type*} {E : Type*} [NormedRing E] [One F] 
[NormOneClass F] [TopologicalSpace α] {f : α -> E} {x : α} : (ContinuousAt f x) 
↔ (f · - f x) =o[𝓝 x] (fun (_ : α) => (1 : F))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem continuousAt_iff_isLittleO {α : Type*} {E : Type*} [NormedRing E] [One F] [NormOneClass F]
    [TopologicalSpace α] {f : α → E} {x : α} :
    (ContinuousAt f x) ↔ (f · - f x) =o[𝓝 x] (fun (_ : α) ↦ (1 : F)) := by
  simp [ContinuousAt, ← tendsto_sub_nhds_zero_iff]
/-
**Asymptotics._root_.ContinuousAt.isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousAt.isLittleO {α : Type*} {E : Type*} [NormedRing E] [One F]
    [NormOneClass F] [TopologicalSpace α] {f : α → E} {x : α} (hcont : ContinuousAt f x) :
    (f · - f x) =o[𝓝 x] (fun _ ↦ (1 : F)) :=
  continuousAt_iff_isLittleO.mp hcont
/-
**Asymptotics._root_.ContinuousAt.isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.ContinuousAt.isBigO {α : Type*} {E : Type*} [NormedRing E] [One F] [NormOneClass F]
    [TopologicalSpace α] {f : α → E} {x : α} (hcont : ContinuousAt f x) :
    f =O[𝓝 x] (fun _ ↦ (1 : F)) :=
  hcont.isLittleO.isBigO.congr_of_sub.mpr (isBigO_const_one ..)

/-! ### Multiplication -/

/-
**Asymptotics.IsBigO.of_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Type u_15} [inst : SeminormedRing R]
 [inst_1 : NormedDivisionRing 𝕜]   {l : Filter α} {f : α → 𝕜} {g : α → R} {n : ℕ
}, n ≠ 0 → (f ^ n) =O[l] (g ^ n) → f =O[l] g
参数：f ^ n；g ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.of_pow`：∀ {α : Type u_1} {R : Type u_13} [inst : 
SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {c 
c' : ℝ} {l : Filter…
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α

--- 原说明 ---
### Multiplication
-/
theorem IsBigO.of_pow {f : α → 𝕜} {g : α → R} {n : ℕ} (hn : n ≠ 0) (h : (f ^ n) =O[l] (g ^ n)) :
    f =O[l] g := by
  rcases h.exists_pos with ⟨C, _hC₀, hC⟩
  obtain ⟨c : ℝ, hc₀ : 0 ≤ c, hc : C ≤ c ^ n⟩ :=
    ((eventually_ge_atTop _).and <| (tendsto_pow_atTop hn).eventually_ge_atTop C).exists
  exact (hC.of_pow hn hc hc₀).isBigO
/-
**Asymptotics.IsBigO.pow_of_le_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gO`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {f : α → ℝ}, 1 ≤ᶠ[l] f → ∀ {m n : ℕ}, n ≤ 
m → (f ^ n) =O[l] (f ^ m)
参数：f ^ n；f ^ m。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_eq_self`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : LinearOr
der G] [IsOrderedAddMonoid G] {a : G}, |a| = a ↔ 0 ≤ a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `pow_le_pow_right₀`：pow_le_pow_right₀ [ZeroLEOneClass M₀] [PosMulMono M₀]
 (ha : 1 <= a) (hmn : m <= n) : a ^ m <= a ^ n
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
-/
theorem IsBigO.pow_of_le_right {f : α → ℝ}
    (hf : 1 ≤ᶠ[l] f) {m n : ℕ}
    (h : n ≤ m) : (f ^ n) =O[l] (f ^ m) := by
  rw [IsBigO_def]
  refine ⟨1, ?_⟩
  rw [IsBigOWith_def]
  exact hf.mono fun x hx ↦ by simp [abs_eq_self.mpr (zero_le_one.trans hx), pow_le_pow_right₀ hx h]

/-! ### Scalar multiplication -/

section SMulConst

variable [Module R E'] [IsBoundedSMul R E']

/-
**Asymptotics.IsBigOWith.const_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {R : Type u_13} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedRing R]   {f' : α → E'} {l : Filter α} [inst_2 : _
root_.Module R E'] [IsBoundedSMul R E'] (c' : R),   Asymptotics.IsBigOWith ‖c'‖ 
l (fun x => c' • f' x) f'
参数：c' : R；fun x => c' • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigOWith_of_le'`：isBigOWith_of_le' (hfg : forall x, ‖f x‖ 
<= c * ‖g x‖) : IsBigOWith c l f g
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
-/
theorem IsBigOWith.const_smul_self (c' : R) :
    IsBigOWith (‖c'‖) l (fun x => c' • f' x) f' :=
  isBigOWith_of_le' _ fun _ => norm_smul_le _ _
/-
**Asymptotics.IsBigO.const_smul_self** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {R : Type u_13} [inst : SeminormedAddComm
Group E'] [inst_1 : SeminormedRing R]   {f' : α → E'} {l : Filter α} [inst_2 : _
root_.Module R E'] [IsBoundedSMul R E'] (c' : R),   (fun x => c' • f' x) =O[l] f
'
参数：c' : R；fun x => c' • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.const_smul_self`：∀ {α : Type u_1} {E' : Type u_6}
 {R : Type u_13} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedRing R] 
  {f' : α → E'} {l : Filter …
-/
theorem IsBigO.const_smul_self (c' : R) : (fun x => c' • f' x) =O[l] f' :=
  (IsBigOWith.const_smul_self _).isBigO
/-
**Asymptotics.IsBigOWith.const_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} {R : Type u_13} [inst : No
rm F] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedRing R] {c : ℝ}
 {g : α → F} {f' : α → E'} {l : Filter α} [inst_3 : _root_.Module R E']   [IsBou
ndedSMul R E'],   Asymptotics.IsBigOWith c l f' g → ∀ (c' : R), Asymptotics.IsBi
gOWith (‖c'‖ * c) l (fun x => c' • f' x) g
参数：c' : R；‖c'‖ * c；fun x => c' • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {c c' 
: ℝ} {f : α → E} {…
· 使用定理 `Asymptotics.IsBigOWith.const_smul_self`：∀ {α : Type u_1} {E' : Type u_6}
 {R : Type u_13} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedRing R] 
  {f' : α → E'} {l : Filter …
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem IsBigOWith.const_smul_left (h : IsBigOWith c l f' g) (c' : R) :
    IsBigOWith (‖c'‖ * c) l (fun x => c' • f' x) g :=
  .trans (.const_smul_self _) h (norm_nonneg _)
/-
**Asymptotics.IsBigO.const_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBi
gO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} {R : Type u_13} [inst : No
rm F] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedRing R] {g : α 
→ F} {f' : α → E'} {l : Filter α} [inst_3 : _root_.Module R E']   [IsBoundedSMul
 R E'], f' =O[l] g → ∀ (c : R), (c • f') =O[l] g
参数：c : R；c • f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.const_smul_left`：∀ {α : Type u_1} {F : Type u_4} 
{E' : Type u_6} {R : Type u_13} [inst : Norm F] [inst_1 : SeminormedAddCommGroup
 E']   [inst_2 : SeminormedR…
-/
theorem IsBigO.const_smul_left (h : f' =O[l] g) (c : R) : (c • f') =O[l] g :=
  let ⟨_b, hb⟩ := h.isBigOWith
  (hb.const_smul_left _).isBigO
/-
**Asymptotics.IsLittleO.const_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.I
sLittleO`。
形式化陈述：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} {R : Type u_13} [inst : No
rm F] [inst_1 : SeminormedAddCommGroup E']   [inst_2 : SeminormedRing R] {g : α 
→ F} {f' : α → E'} {l : Filter α} [inst_3 : _root_.Module R E']   [IsBoundedSMul
 R E'], f' =o[l] g → ∀ (c : R), (c • f') =o[l] g
参数：c : R；c • f'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.IsBigO.const_smul_self`：∀ {α : Type u_1} {E' : Type u_6} {R 
: Type u_13} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedRing R]   {f
' : α → E'} {l : Filter …
-/
theorem IsLittleO.const_smul_left (h : f' =o[l] g) (c : R) : (c • f') =o[l] g :=
  (IsBigO.const_smul_self _).trans_isLittleO h

variable [Module 𝕜 E'] [NormSMulClass 𝕜 E']
/-
**Asymptotics.isBigO_const_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_smul_left {c : 𝕜} (hc : c != 0) : (fun x => c • f' x) =O[l] g
 ↔ f' =O[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_norm_left`：isBigO_norm_left : (fun x => ‖f' x‖) =O[l]
 g ↔ f' =O[l] g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `Asymptotics.isBigO_const_mul_left_iff`：isBigO_const_mul_left_iff {f : α 
-> S} {c : S} (hc : c != 0) : (fun x => c * f x) =O[l] g ↔ f =O[l] g
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBigO_const_smul_left {c : 𝕜} (hc : c ≠ 0) : (fun x => c • f' x) =O[l] g ↔ f' =O[l] g := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_left]
  simp only [norm_smul]
  rw [isBigO_const_mul_left_iff cne0, isBigO_norm_left]
/-
**Asymptotics.isLittleO_const_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_const_smul_left {c : 𝕜} (hc : c != 0) : (fun x => c • f' x) =o[l
] g ↔ f' =o[l] g
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_norm_left`：isLittleO_norm_left : (fun x => ‖f' x‖)
 =o[l] g ↔ f' =o[l] g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `Asymptotics.isLittleO_const_mul_left_iff`：isLittleO_const_mul_left_iff {
f : α -> S} {c : S} (hc : c != 0) : (fun x => c * f x) =o[l] g ↔ f =o[l] g
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLittleO_const_smul_left {c : 𝕜} (hc : c ≠ 0) :
    (fun x => c • f' x) =o[l] g ↔ f' =o[l] g := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_left]
  simp only [norm_smul]
  rw [isLittleO_const_mul_left_iff cne0, isLittleO_norm_left]
/-
**Asymptotics.isBigO_const_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_const_smul_right {c : 𝕜} (hc : c != 0) : (f =O[l] fun x => c • f' x
) ↔ f =O[l] f'
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_norm_right`：isBigO_norm_right : (f =O[l] fun x => ‖g'
 x‖) ↔ f =O[l] g'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `Asymptotics.isBigO_const_mul_right_iff`：isBigO_const_mul_right_iff {g : 
α -> S} {c : S} (hc : c != 0) : (f =O[l] fun x => c * g x) ↔ f =O[l] g
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBigO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =O[l] fun x => c • f' x) ↔ f =O[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isBigO_norm_right]
  simp only [norm_smul]
  rw [isBigO_const_mul_right_iff cne0, isBigO_norm_right]
/-
**Asymptotics.isLittleO_const_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isLittleO_const_smul_right {c : 𝕜} (hc : c != 0) : (f =o[l] fun x => c • f
' x) ↔ f =o[l] f'
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_norm_right`：isLittleO_norm_right : (f =o[l] fun x 
=> ‖g' x‖) ↔ f =o[l] g'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `Asymptotics.isLittleO_const_mul_right_iff`：isLittleO_const_mul_right_iff
 {g : α -> S} {c : S} (hc : c != 0) : (f =o[l] fun x => c * g x) ↔ f =o[l] g
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLittleO_const_smul_right {c : 𝕜} (hc : c ≠ 0) :
    (f =o[l] fun x => c • f' x) ↔ f =o[l] f' := by
  have cne0 : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [← isLittleO_norm_right]
  simp only [norm_smul]
  rw [isLittleO_const_mul_right_iff cne0, isLittleO_norm_right]

end SMulConst

section SMul

variable [Module R E'] [IsBoundedSMul R E'] [Module 𝕜' F'] [NormSMulClass 𝕜' F']
variable {k₁ : α → R} {k₂ : α → 𝕜'}

/-
**Asymptotics.IsBigOWith.smul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`
。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {R : Type u_13} {𝕜' : Typ
e u_16} [inst : SeminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'
] [inst_2 : SeminormedRing R] [inst_3 : NormedDivisionRing 𝕜'] {c c' : ℝ}   {f' 
: α → E'} {g' : α → F'} {l : Filter α} [inst_4 : _root_.Module R E'] [IsBoundedS
Mul R E']   [inst_6 : _root_.Module 𝕜' F'] [NormSMulClass 𝕜' F'] {k₁ : α → R} {k
₂ : α → 𝕜'},   Asymptotics.IsBigOWith c l k₁ k₂ →     Asymptotics.IsBigOWith c' 
l f' g' → Asymptotics.IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x
 • g' x
参数：c * c'；fun x => k₁ x • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `mul_mul_mul_comm`：mul_mul_mul_comm (a b c d : G) : a * b * (c * d) = a *
 c * (b * d)
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
-/
theorem IsBigOWith.smul (h₁ : IsBigOWith c l k₁ k₂) (h₂ : IsBigOWith c' l f' g') :
    IsBigOWith (c * c') l (fun x => k₁ x • f' x) fun x => k₂ x • g' x := by
  simp only [IsBigOWith_def] at *
  filter_upwards [h₁, h₂] with _ hx₁ hx₂
  apply le_trans (norm_smul_le _ _)
  convert! mul_le_mul hx₁ hx₂ (norm_nonneg _) (le_trans (norm_nonneg _) hx₁) using 1
  rw [norm_smul, mul_mul_mul_comm]
/-
**Asymptotics.IsBigO.smul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {R : Type u_13} {𝕜' : Typ
e u_16} [inst : SeminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'
] [inst_2 : SeminormedRing R] [inst_3 : NormedDivisionRing 𝕜'] {f' : α → E'}   {
g' : α → F'} {l : Filter α} [inst_4 : _root_.Module R E'] [IsBoundedSMul R E'] [
inst_6 : _root_.Module 𝕜' F']   [NormSMulClass 𝕜' F'] {k₁ : α → R} {k₂ : α → 𝕜'}
,   k₁ =O[l] k₂ → f' =O[l] g' → (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' 
x
参数：fun x => k₁ x • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.smul`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type
 u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E']   [ins
t_1 : SeminormedA…
-/
theorem IsBigO.smul (h₁ : k₁ =O[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =O[l] fun x => k₂ x • g' x := by
  obtain ⟨c₁, h₁⟩ := h₁.isBigOWith
  obtain ⟨c₂, h₂⟩ := h₂.isBigOWith
  exact (h₁.smul h₂).isBigO
/-
**Asymptotics.IsBigO.smul_isLittleO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBig
O`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {R : Type u_13} {𝕜' : Typ
e u_16} [inst : SeminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'
] [inst_2 : SeminormedRing R] [inst_3 : NormedDivisionRing 𝕜'] {f' : α → E'}   {
g' : α → F'} {l : Filter α} [inst_4 : _root_.Module R E'] [IsBoundedSMul R E'] [
inst_6 : _root_.Module 𝕜' F']   [NormSMulClass 𝕜' F'] {k₁ : α → R} {k₂ : α → 𝕜'}
,   k₁ =O[l] k₂ → f' =o[l] g' → (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' 
x
参数：fun x => k₁ x • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.smul`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type
 u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E']   [ins
t_1 : SeminormedA…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `mul_div_cancel₀`：mul_div_cancel₀ (a : G₀) (hb : b != 0) : b * (a / b) = 
a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem IsBigO.smul_isLittleO (h₁ : k₁ =O[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₁.exists_pos with ⟨c', c'pos, hc'⟩
  exact (hc'.smul (h₂ (div_pos cpos c'pos))).congr_const (mul_div_cancel₀ _ (ne_of_gt c'pos))
/-
**Asymptotics.IsLittleO.smul_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLit
tleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {R : Type u_13} {𝕜' : Typ
e u_16} [inst : SeminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'
] [inst_2 : SeminormedRing R] [inst_3 : NormedDivisionRing 𝕜'] {f' : α → E'}   {
g' : α → F'} {l : Filter α} [inst_4 : _root_.Module R E'] [IsBoundedSMul R E'] [
inst_6 : _root_.Module 𝕜' F']   [NormSMulClass 𝕜' F'] {k₁ : α → R} {k₂ : α → 𝕜'}
,   k₁ =o[l] k₂ → f' =O[l] g' → (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' 
x
参数：fun x => k₁ x • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.congr_const`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {f : α → E} {g : α → F}
   {l : Filter α}, Asymp…
· 使用定理 `Asymptotics.IsBigOWith.smul`：∀ {α : Type u_1} {E' : Type u_6} {F' : Type
 u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E']   [ins
t_1 : SeminormedA…
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem IsLittleO.smul_isBigO (h₁ : k₁ =o[l] k₂) (h₂ : f' =O[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x := by
  simp only [IsLittleO_def] at *
  intro c cpos
  rcases h₂.exists_pos with ⟨c', c'pos, hc'⟩
  exact ((h₁ (div_pos cpos c'pos)).smul hc').congr_const (div_mul_cancel₀ _ (ne_of_gt c'pos))
/-
**Asymptotics.IsLittleO.smul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {F' : Type u_7} {R : Type u_13} {𝕜' : Typ
e u_16} [inst : SeminormedAddCommGroup E']   [inst_1 : SeminormedAddCommGroup F'
] [inst_2 : SeminormedRing R] [inst_3 : NormedDivisionRing 𝕜'] {f' : α → E'}   {
g' : α → F'} {l : Filter α} [inst_4 : _root_.Module R E'] [IsBoundedSMul R E'] [
inst_6 : _root_.Module 𝕜' F']   [NormSMulClass 𝕜' F'] {k₁ : α → R} {k₂ : α → 𝕜'}
,   k₁ =o[l] k₂ → f' =o[l] g' → (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' 
x
参数：fun x => k₁ x • f' x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.smul_isBigO`：∀ {α : Type u_1} {E' : Type u_6} {F' 
: Type u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E'] 
  [inst_1 : SeminormedA…
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
-/
theorem IsLittleO.smul (h₁ : k₁ =o[l] k₂) (h₂ : f' =o[l] g') :
    (fun x => k₁ x • f' x) =o[l] fun x => k₂ x • g' x :=
  h₁.smul_isBigO h₂.isBigO

end SMul

section Prod
variable {ι : Type*}

/-
**Asymptotics.IsBigO.listProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Type u_15} [inst : SeminormedRing R]
 [inst_1 : NormedDivisionRing 𝕜]   {l : Filter α} {ι : Type u_17} {L : List ι} {
f : ι → α → R} {g : ι → α → 𝕜},   (∀ i ∈ L, f i =O[l] g i) →     (fun x => (List
.map (fun x_1 => f x_1 x) L).prod) =O[l] fun x => (List.map (fun x_1 => g x_1 x)
 L).prod
参数：∀ i ∈ L, f i =O[l] g i；fun x => (List.map (fun x_1 => f x_1 x) L).prod；List.m
ap (fun x_1 => g x_1 x) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `List.map_nil`：∀ {α : Type u} {β : Type v} {f : α → β}, List.map f [] = [
]
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem IsBigO.listProd {L : List ι} {f : ι → α → R} {g : ι → α → 𝕜}
    (hf : ∀ i ∈ L, f i =O[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) =O[l] (fun x ↦ (L.map (g · x)).prod) := by
  induction L with
  | nil => simp [isBoundedUnder_const]
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons] at hf ⊢
    exact hf.1.mul (ihL hf.2)
/-
**Asymptotics.IsBigO.multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Type u_17} {R : Type u_18} {𝕜 : Type 
u_19} [inst : SeminormedCommRing R]   [inst_1 : NormedField 𝕜] {s : Multiset ι} 
{f : ι → α → R} {g : ι → α → 𝕜},   (∀ i ∈ s, f i =O[l] g i) →     (fun x => (Mul
tiset.map (fun x_1 => f x_1 x) s).prod) =O[l] fun x => (Multiset.map (fun x_1 =>
 g x_1 x) s).prod
参数：∀ i ∈ s, f i =O[l] g i；fun x => (Multiset.map (fun x_1 => f x_1 x) s).prod；Mu
ltiset.map (fun x_1 => g x_1 x) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
· 使用定理 `Asymptotics.IsBigO.listProd`：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Type 
u_15} [inst : SeminormedRing R] [inst_1 : NormedDivisionRing 𝕜]   {l : Filter α}
 {ι : Type u_17} …
-/
theorem IsBigO.multisetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Multiset ι} {f : ι → α → R} {g : ι → α → 𝕜} (hf : ∀ i ∈ s, f i =O[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) =O[l] (fun x ↦ (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsBigO.listProd hf
/-
**Asymptotics.IsBigO.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Type u_17} {R : Type u_18} {𝕜 : Type 
u_19} [inst : SeminormedCommRing R]   [inst_1 : NormedField 𝕜] {s : Finset ι} {f
 : ι → α → R} {g : ι → α → 𝕜},   (∀ i ∈ s, f i =O[l] g i) → (fun x => ∏ i ∈ s, f
 i x) =O[l] fun x => ∏ i ∈ s, g i x
参数：∀ i ∈ s, f i =O[l] g i；fun x => ∏ i ∈ s, f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.multisetProd`：∀ {α : Type u_1} {l : Filter α} {ι : Ty
pe u_17} {R : Type u_18} {𝕜 : Type u_19} [inst : SeminormedCommRing R]   [inst_1
 : NormedField 𝕜] {s …
-/
theorem IsBigO.finsetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Finset ι} {f : ι → α → R} {g : ι → α → 𝕜}
    (hf : ∀ i ∈ s, f i =O[l] g i) : (∏ i ∈ s, f i ·) =O[l] (∏ i ∈ s, g i ·) :=
  .multisetProd hf
/-
**Asymptotics.IsLittleO.listProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittle
O`。
形式化陈述：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Type u_15} [inst : SeminormedRing R]
 [inst_1 : NormedDivisionRing 𝕜]   {l : Filter α} {ι : Type u_17} {L : List ι} {
f : ι → α → R} {g : ι → α → 𝕜},   (∀ i ∈ L, f i =O[l] g i) →     (∃ i ∈ L, f i =
o[l] g i) →       (fun x => (List.map (fun x_1 => f x_1 x) L).prod) =o[l] fun x 
=> (List.map (fun x_1 => g x_1 x) L).prod
参数：∀ i ∈ L, f i =O[l] g i；∃ i ∈ L, f i =o[l] g i；fun x => (List.map (fun x_1 => 
f x_1 x) L).prod；List.map (fun x_1 => g x_1 x) L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `List.map_cons`：∀ {α : Type u} {β : Type v} {f : α → β} {a : α} {l : List
 α}, List.map f (a :: l) = f a :: List.map f l
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigO.listProd`：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Type 
u_15} [inst : SeminormedRing R] [inst_1 : NormedDivisionRing 𝕜]   {l : Filter α}
 {ι : Type u_17} …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
-/
theorem IsLittleO.listProd {L : List ι} {f : ι → α → R} {g : ι → α → 𝕜}
    (h₁ : ∀ i ∈ L, f i =O[l] g i) (h₂ : ∃ i ∈ L, f i =o[l] g i) :
    (fun x ↦ (L.map (f · x)).prod) =o[l] (fun x ↦ (L.map (g · x)).prod) := by
  induction L with
  | nil => simp at h₂
  | cons i L ihL =>
    simp only [List.map_cons, List.prod_cons, List.forall_mem_cons, List.exists_mem_cons_iff]
      at h₁ h₂ ⊢
    cases h₂ with
    | inl hi => exact hi.mul_isBigO <| .listProd h₁.2
    | inr hL => exact h₁.1.mul_isLittleO <| ihL h₁.2 hL
/-
**Asymptotics.IsLittleO.multisetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLi
ttleO`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Type u_17} {R : Type u_18} {𝕜 : Type 
u_19} [inst : SeminormedCommRing R]   [inst_1 : NormedField 𝕜] {s : Multiset ι} 
{f : ι → α → R} {g : ι → α → 𝕜},   (∀ i ∈ s, f i =O[l] g i) →     (∃ i ∈ s, f i 
=o[l] g i) →       (fun x => (Multiset.map (fun x_1 => f x_1 x) s).prod) =o[l] f
un x => (Multiset.map (fun x_1 => g x_1 x) s).prod
参数：∀ i ∈ s, f i =O[l] g i；∃ i ∈ s, f i =o[l] g i；fun x => (Multiset.map (fun x_1
 => f x_1 x) s).prod；Multiset.map (fun x_1 => g x_1 x) s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
· 使用定理 `Asymptotics.IsLittleO.listProd`：∀ {α : Type u_1} {R : Type u_13} {𝕜 : Ty
pe u_15} [inst : SeminormedRing R] [inst_1 : NormedDivisionRing 𝕜]   {l : Filter
 α} {ι : Type u_17} …
-/
theorem IsLittleO.multisetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Multiset ι} {f : ι → α → R} {g : ι → α → 𝕜} (h₁ : ∀ i ∈ s, f i =O[l] g i)
    (h₂ : ∃ i ∈ s, f i =o[l] g i) :
    (fun x ↦ (s.map (f · x)).prod) =o[l] (fun x ↦ (s.map (g · x)).prod) := by
  obtain ⟨l, rfl⟩ : ∃ l : List ι, ↑l = s := Quotient.mk_surjective s
  exact mod_cast IsLittleO.listProd h₁ h₂
/-
**Asymptotics.IsLittleO.finsetProd** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLitt
leO`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {ι : Type u_17} {R : Type u_18} {𝕜 : Type 
u_19} [inst : SeminormedCommRing R]   [inst_1 : NormedField 𝕜] {s : Finset ι} {f
 : ι → α → R} {g : ι → α → 𝕜},   (∀ i ∈ s, f i =O[l] g i) → (∃ i ∈ s, f i =o[l] 
g i) → (fun x => ∏ i ∈ s, f i x) =o[l] fun x => ∏ i ∈ s, g i x
参数：∀ i ∈ s, f i =O[l] g i；∃ i ∈ s, f i =o[l] g i；fun x => ∏ i ∈ s, f i x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.multisetProd`：∀ {α : Type u_1} {l : Filter α} {ι :
 Type u_17} {R : Type u_18} {𝕜 : Type u_19} [inst : SeminormedCommRing R]   [ins
t_1 : NormedField 𝕜] {s …
-/
theorem IsLittleO.finsetProd {R 𝕜 : Type*} [SeminormedCommRing R] [NormedField 𝕜]
    {s : Finset ι} {f : ι → α → R} {g : ι → α → 𝕜} (h₁ : ∀ i ∈ s, f i =O[l] g i)
    (h₂ : ∃ i ∈ s, f i =o[l] g i) : (∏ i ∈ s, f i ·) =o[l] (∏ i ∈ s, g i ·) :=
  .multisetProd h₁ h₂

end Prod

/-! ### Relation between `f = o(g)` and `f / g → 0` -/

/-
**Asymptotics.IsLittleO.tendsto_div_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `Asympto
tics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} [inst : NormedDivisionRing 𝕜] {l : Filter
 α} {f g : α → 𝕜},   f =o[l] g → Filter.Tendsto (fun x => f x / g x) l (nhds 0)
参数：fun x => f x / g x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1

--- 原说明 ---
### Relation between `f = o(g)` and `f / g → 0`
-/
theorem IsLittleO.tendsto_div_nhds_zero {f g : α → 𝕜} (h : f =o[l] g) :
    Tendsto (fun x => f x / g x) l (𝓝 0) :=
  (isLittleO_one_iff 𝕜).mp <| by
    calc
      (fun x => f x / g x) =o[l] fun x => g x / g x := by
        simpa only [div_eq_mul_inv] using h.mul_isBigO (isBigO_refl _ _)
      _ =O[l] fun _x => (1 : 𝕜) := isBigO_of_le _ fun x => by simp [div_self_le_one]
/-
**Asymptotics.IsLittleO.tendsto_inv_smul_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 `As
ymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {𝕜 : Type u_15} [inst : SeminormedAddComm
Group E'] [inst_1 : NormedDivisionRing 𝕜]   [inst_2 : _root_.Module 𝕜 E'] [NormS
MulClass 𝕜 E'] {f : α → E'} {g : α → 𝕜} {l : Filter α},   f =o[l] g → Filter.Ten
dsto (fun x => (g x)⁻¹ • f x) l (nhds 0)
参数：fun x => (g x)⁻¹ • f x；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …
· 使用定理 `Asymptotics.IsLittleO.norm_norm`：∀ {α : Type u_1} {E' : Type u_6} {F' : 
Type u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F'
]   {f' : α → E'} {g'…
-/
theorem IsLittleO.tendsto_inv_smul_nhds_zero [Module 𝕜 E'] [NormSMulClass 𝕜 E']
    {f : α → E'} {g : α → 𝕜}
    {l : Filter α} (h : f =o[l] g) : Tendsto (fun x => (g x)⁻¹ • f x) l (𝓝 0) := by
  simpa only [div_eq_inv_mul, ← norm_inv, ← norm_smul, ← tendsto_zero_iff_norm_tendsto_zero] using
    h.norm_norm.tendsto_div_nhds_zero
/-
**Asymptotics.isLittleO_iff_tendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_iff_tendsto' {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f 
x = 0) : f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0)
参数：hgf : forallᶠ x in l, g x = 0 -> f x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `div_mul_cancel_of_imp`：div_mul_cancel_of_imp (h : b = 0 -> a = 0) : a / 
b * b = a
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem isLittleO_iff_tendsto' {f g : α → 𝕜} (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  ⟨IsLittleO.tendsto_div_nhds_zero, fun h =>
    (((isLittleO_one_iff _).mpr h).mul_isBigO (isBigO_refl g l)).congr'
      (hgf.mono fun _x => div_mul_cancel_of_imp) (Eventually.of_forall fun _x => one_mul _)⟩
/-
**Asymptotics.isLittleO_iff_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_iff_tendsto {f g : α -> 𝕜} (hgf : forall x, g x = 0 -> f x = 0) 
: f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0)
参数：hgf : forall x, g x = 0 -> f x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_iff_tendsto'`：isLittleO_iff_tendsto' {f g : α -> 𝕜
} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x
 / g x) l (𝓝 0)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem isLittleO_iff_tendsto {f g : α → 𝕜} (hgf : ∀ x, g x = 0 → f x = 0) :
    f =o[l] g ↔ Tendsto (fun x => f x / g x) l (𝓝 0) :=
  isLittleO_iff_tendsto' (Eventually.of_forall hgf)

alias ⟨_, isLittleO_of_tendsto'⟩ := isLittleO_iff_tendsto'

alias ⟨_, isLittleO_of_tendsto⟩ := isLittleO_iff_tendsto
/-
**Asymptotics.isLittleO_const_left_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isLittleO_const_left_of_ne {c : E''} (hc : c != 0) : (fun _x => c) =o[l] g
 ↔ Tendsto (fun x => ‖g x‖) l atTop
参数：hc : c != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_left_iff`：isLittleO_one_left_iff : (fun _x => 
1 : α -> F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Asymptotics.isBigO_const_const`：isBigO_const_const (c : E) {c' : F''} (h
c' : c' != 0) (l : Filter α) : (fun _x : α => c) =O[l] fun _x => c'
· 使用定理 `Asymptotics.isBigO_const_one`：isBigO_const_one (c : E) (l : Filter α) : 
(fun _x : α => c) =O[l] fun _x => (1 : F)
-/
theorem isLittleO_const_left_of_ne {c : E''} (hc : c ≠ 0) :
    (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop := by
  simp only [← isLittleO_one_left_iff ℝ]
  exact ⟨(isBigO_const_const (1 : ℝ) hc l).trans_isLittleO,
    (isBigO_const_one ℝ c l).trans_isLittleO⟩

@[simp]
/-
**Asymptotics.isLittleO_const_left** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_const_left {c : E''} : (fun _x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto
 (norm ∘ g'') l atTop
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_const_left_of_ne`：isLittleO_const_left_of_ne {c : 
E''} (hc : c != 0) : (fun _x => c) =o[l] g ↔ Tendsto (fun x => ‖g x‖) l atTop
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isLittleO_const_left {c : E''} :
    (fun _x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop := by
  rcases eq_or_ne c 0 with (rfl | hc)
  · simp only [isLittleO_zero, true_or]
  · simp only [hc, false_or, isLittleO_const_left_of_ne hc]; rfl

@[simp high] -- Increase priority so that this triggers before `isLittleO_const_left`
/-
**Asymptotics.isLittleO_const_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} : ((fun _x => d) =
o[l] fun _x => c) ↔ d = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem isLittleO_const_const_iff [NeBot l] {d : E''} {c : F''} :
    ((fun _x => d) =o[l] fun _x => c) ↔ d = 0 := by
  have : ¬Tendsto (Function.const α ‖c‖) l atTop :=
    not_tendsto_atTop_of_tendsto_nhds tendsto_const_nhds
  simp only [isLittleO_const_left, or_iff_left_iff_imp]
  exact fun h => (this h).elim

@[simp]
/-
**Asymptotics.isLittleO_pure** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_congr`：isLittleO_congr (hf : f₁ =ᶠ[l] f₂) (hg : g₁
 =ᶠ[l] g₂) : f₁ =o[l] g₁ ↔ f₂ =o[l] g₂
· 使用定理 `Asymptotics.isLittleO_const_const_iff`：isLittleO_const_const_iff [NeBot 
l] {d : E''} {c : F''} : ((fun _x => d) =o[l] fun _x => c) ↔ d = 0
-/
theorem isLittleO_pure {x} : f'' =o[pure x] g'' ↔ f'' x = 0 :=
  calc
    f'' =o[pure x] g'' ↔ (fun _y : α => f'' x) =o[pure x] fun _ => g'' x := isLittleO_congr rfl rfl
    _ ↔ f'' x = 0 := isLittleO_const_const_iff
/-
**Asymptotics.isLittleO_const_id_cobounded** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：isLittleO_const_id_cobounded (c : F'') : (fun _ => c) =o[Bornology.cobound
ed E''] id
参数：c : F''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `tendsto_norm_cobounded_atTop`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E], Filter.Tendsto norm (Bornology.cobounded E) Filter.atTop
-/
theorem isLittleO_const_id_cobounded (c : F'') :
    (fun _ => c) =o[Bornology.cobounded E''] id :=
  isLittleO_const_left.2 <| .inr tendsto_norm_cobounded_atTop
/-
**Asymptotics.isLittleO_const_id_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_const_id_atTop (c : E'') : (fun _x : Real => c) =o[atTop] id
参数：c : E''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
-/
theorem isLittleO_const_id_atTop (c : E'') : (fun _x : ℝ => c) =o[atTop] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atTop_atTop
/-
**Asymptotics.isLittleO_const_id_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_const_id_atBot (c : E'') : (fun _x : Real => c) =o[atBot] id
参数：c : E''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `Filter.tendsto_abs_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto abs Filter.at
Bot Filter.atTop
-/
theorem isLittleO_const_id_atBot (c : E'') : (fun _x : ℝ => c) =o[atBot] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_abs_atBot_atTop

/-! ### Relation between `f = o(g)` and `g / f → ∞` -/

section div_tendsto_infty

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
  {l : Filter α} {f g : α → 𝕜}

/-
**Asymptotics.IsLittleO.of_tendsto_div_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_17} [inst : NormedField 𝕜] [inst_1 : LinearOr
der 𝕜] [IsStrictOrderedRing 𝕜]   [OrderTopology 𝕜] {l : Filter α} {f g : α → 𝕜},
 Filter.Tendsto (fun x => g x / f x) l Filter.atTop → f =o[l] g
参数：fun x => g x / f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto'`：∀ {α : Type u_1} {𝕜 : Type u_15} [ins
t : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ᶠ (x : α) in l, g x 
= 0 → f x = 0) → Filter…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_inv_atTop_zero`：tendsto_inv_atTop_zero : Tendsto (fun r : 𝕜 => r
⁻¹) atTop (𝓝 0)
-/
theorem IsLittleO.of_tendsto_div_atTop (h : Tendsto (fun x ↦ g x / f x) l atTop) : f =o[l] g := by
  apply Asymptotics.isLittleO_of_tendsto'
  · apply (Filter.Tendsto.eventually_ge_atTop h 1).mono
    intro x h h0
    simp only [h0, zero_div] at h
    grind
  · convert! Tendsto.comp tendsto_inv_atTop_zero h
    simp
/-
**Asymptotics.IsLittleO.of_tendsto_div_atBot** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_17} [inst : NormedField 𝕜] [inst_1 : LinearOr
der 𝕜] [IsStrictOrderedRing 𝕜]   [OrderTopology 𝕜] {l : Filter α} {f g : α → 𝕜},
 Filter.Tendsto (fun x => g x / f x) l Filter.atBot → f =o[l] g
参数：fun x => g x / f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' :
 Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f
' : α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsLittleO.of_tendsto_div_atTop`：∀ {α : Type u_1} {𝕜 : Type u
_17} [inst : NormedField 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]   [
OrderTopology 𝕜] {l : Filter α} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.tendsto_neg_atBot_iff`：∀ {α : Type u_1} {G : Type u_2} [inst : Ad
dCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] {l : Filter α}   
{f : α → G}, Filte…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `div_neg_eq_neg_div`：div_neg_eq_neg_div (a b : R) : b / -a = -(b / a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsLittleO.of_tendsto_div_atBot (h : Tendsto (fun x ↦ g x / f x) l atBot) : f =o[l] g := by
  refine IsLittleO.of_neg_left (IsLittleO.of_tendsto_div_atTop ?_)
  rw [← tendsto_neg_atBot_iff]
  convert h
  simp [div_neg_eq_neg_div]

end div_tendsto_infty

/-! ### Equivalent definitions of the form `∃ φ, u =ᶠ[l] φ * v` in a `NormedField`. -/

section ExistsMulEq

variable {u v : α → 𝕜}

/-- If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `IsBigOWith c u v l`.
This does not require any assumptions on `c`, which is why we keep this version along with
`IsBigOWith_iff_exists_eq_mul`. -/
/-
**Asymptotics.isBigOWith_of_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_of_eq_mul {u v : α -> R} (φ : α -> R) (hφ : forallᶠ x in l, ‖φ 
x‖ <= c) (h : u =ᶠ[l] φ * v) : IsBigOWith c l u v
参数：φ : α -> R；hφ : forallᶠ x in l, ‖φ x‖ <= c；h : u =ᶠ[l] φ * v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.EventuallyEq.rw`：∀ {α : Type u} {β : Type v} {l : Filter α} {f g 
: α → β},   f =ᶠ[l] g → ∀ (p : α → β → Prop), (∀ᶠ (x : α) in l, p x (f x)) → ∀ᶠ 
(x : α) in l…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
If `‖φ‖` is eventually bounded by `c`, and `u =ᶠ[l] φ * v`, then we have `IsBigO
With c u v l`.
This does not require any assumptions on `c`, which is why we keep this version 
along with
`IsBigOWith_iff_exists_eq_mul`.
-/
theorem isBigOWith_of_eq_mul {u v : α → R} (φ : α → R) (hφ : ∀ᶠ x in l, ‖φ x‖ ≤ c)
    (h : u =ᶠ[l] φ * v) :
    IsBigOWith c l u v := by
  simp only [IsBigOWith_def]
  refine h.symm.rw (fun x a => ‖a‖ ≤ c * ‖v x‖) (hφ.mono fun x hx => ?_)
  simp only [Pi.mul_apply]
  refine (norm_mul_le _ _).trans ?_
  gcongr
/-
**Asymptotics.isBigOWith_iff_exists_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：isBigOWith_iff_exists_eq_mul (hc : 0 <= c) : IsBigOWith c l u v ↔ exists φ
 : α -> 𝕜, (forallᶠ x in l, ‖φ x‖ <= c) ∧ u =ᶠ[l] φ * v
参数：hc : 0 <= c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Asymptotics.IsBigOWith.eventually_mul_div_cancel`：∀ {α : Type u_1} {𝕜 : 
Type u_15} [inst : NormedDivisionRing 𝕜] {c : ℝ} {l : Filter α} {u v : α → 𝕜},  
 Asymptotics.IsBigOWith c l u v → u / …
· 使用定理 `Asymptotics.isBigOWith_of_eq_mul`：isBigOWith_of_eq_mul {u v : α -> R} (φ
 : α -> R) (hφ : forallᶠ x in l, ‖φ x‖ <= c) (h : u =ᶠ[l] φ * v) : IsBigOWith c 
l u v
-/
theorem isBigOWith_iff_exists_eq_mul (hc : 0 ≤ c) :
    IsBigOWith c l u v ↔ ∃ φ : α → 𝕜, (∀ᶠ x in l, ‖φ x‖ ≤ c) ∧ u =ᶠ[l] φ * v := by
  constructor
  · intro h
    use fun x => u x / v x
    refine ⟨Eventually.mono h.bound fun y hy => ?_, h.eventually_mul_div_cancel.symm⟩
    simpa using div_le_of_le_mul₀ (norm_nonneg _) hc hy
  · rintro ⟨φ, hφ, h⟩
    exact isBigOWith_of_eq_mul φ hφ h
/-
**Asymptotics.IsBigOWith.exists_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigOWith`。
形式化陈述：∀ {α : Type u_1} {𝕜 : Type u_15} [inst : NormedDivisionRing 𝕜] {c : ℝ} {l 
: Filter α} {u v : α → 𝕜},   Asymptotics.IsBigOWith c l u v → 0 ≤ c → ∃ φ, (∀ᶠ (
x : α) in l, ‖φ x‖ ≤ c) ∧ u =ᶠ[l] φ * v
参数：∀ᶠ (x : α) in l, ‖φ x‖ ≤ c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigOWith_iff_exists_eq_mul`：isBigOWith_iff_exists_eq_mul (
hc : 0 <= c) : IsBigOWith c l u v ↔ exists φ : α -> 𝕜, (forallᶠ x in l, ‖φ x‖ <=
 c) ∧ u =ᶠ[l] φ * v
-/
theorem IsBigOWith.exists_eq_mul (h : IsBigOWith c l u v) (hc : 0 ≤ c) :
    ∃ φ : α → 𝕜, (∀ᶠ x in l, ‖φ x‖ ≤ c) ∧ u =ᶠ[l] φ * v :=
  (isBigOWith_iff_exists_eq_mul hc).mp h
/-
**Asymptotics.isBigO_iff_exists_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_iff_exists_eq_mul : u =O[l] v ↔ exists φ : α -> 𝕜, l.IsBoundedUnder
 (· <= ·) (norm ∘ φ) ∧ u =ᶠ[l] φ * v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.exists_eq_mul`：∀ {α : Type u_1} {𝕜 : Type u_15} [
inst : NormedDivisionRing 𝕜] {c : ℝ} {l : Filter α} {u v : α → 𝕜},   Asymptotics
.IsBigOWith c l u v → 0 ≤ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `Asymptotics.isBigOWith_of_eq_mul`：isBigOWith_of_eq_mul {u v : α -> R} (φ
 : α -> R) (hφ : forallᶠ x in l, ‖φ x‖ <= c) (h : u =ᶠ[l] φ * v) : IsBigOWith c 
l u v
-/
theorem isBigO_iff_exists_eq_mul :
    u =O[l] v ↔ ∃ φ : α → 𝕜, l.IsBoundedUnder (· ≤ ·) (norm ∘ φ) ∧ u =ᶠ[l] φ * v := by
  constructor
  · rintro h
    rcases h.exists_nonneg with ⟨c, hnnc, hc⟩
    rcases hc.exists_eq_mul hnnc with ⟨φ, hφ, huvφ⟩
    exact ⟨φ, ⟨c, hφ⟩, huvφ⟩
  · rintro ⟨φ, ⟨c, hφ⟩, huvφ⟩
    exact isBigO_iff_isBigOWith.2 ⟨c, isBigOWith_of_eq_mul φ hφ huvφ⟩

alias ⟨IsBigO.exists_eq_mul, _⟩ := isBigO_iff_exists_eq_mul
/-
**Asymptotics.isLittleO_iff_exists_eq_mul** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
`。
形式化陈述：isLittleO_iff_exists_eq_mul : u =o[l] v ↔ exists φ : α -> 𝕜, Tendsto φ l (
𝓝 0) ∧ u =ᶠ[l] φ * v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `Asymptotics.IsLittleO.eventually_mul_div_cancel`：∀ {α : Type u_1} {𝕜 : T
ype u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {u v : α → 𝕜},   u =o[l] 
v → u / v * v =ᶠ[l] u
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `Asymptotics.isBigOWith_of_eq_mul`：isBigOWith_of_eq_mul {u v : α -> R} (φ
 : α -> R) (hφ : forallᶠ x in l, ‖φ x‖ <= c) (h : u =ᶠ[l] φ * v) : IsBigOWith c 
l u v
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedAddGroup.tendsto_nhds_zero`：∀ {α : Type u_2} {E : Type u_5} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto f l (nhds 0
) ↔ ∀ ε > 0, ∀ᶠ (x : α…
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem isLittleO_iff_exists_eq_mul :
    u =o[l] v ↔ ∃ φ : α → 𝕜, Tendsto φ l (𝓝 0) ∧ u =ᶠ[l] φ * v := by
  constructor
  · exact fun h => ⟨fun x => u x / v x, h.tendsto_div_nhds_zero, h.eventually_mul_div_cancel.symm⟩
  · simp only [IsLittleO_def]
    rintro ⟨φ, hφ, huvφ⟩ c hpos
    rw [NormedAddGroup.tendsto_nhds_zero] at hφ
    exact isBigOWith_of_eq_mul _ ((hφ c hpos).mono fun x => le_of_lt) huvφ

alias ⟨IsLittleO.exists_eq_mul, _⟩ := isLittleO_iff_exists_eq_mul

end ExistsMulEq

/-! ### Miscellaneous lemmas -/

/-
**Asymptotics.div_isBoundedUnder_of_isBigO** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotic
s`。
形式化陈述：div_isBoundedUnder_of_isBigO {α : Type*} {l : Filter α} {f g : α -> 𝕜} (h 
: f =O[l] g) : IsBoundedUnder (· <= ·) l fun x => ‖f x / g x‖
参数：h : f =O[l] g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用引理 `div_le_of_le_mul₀`：div_le_of_le_mul₀ (hb : 0 <= b) (hc : 0 <= c) (h : a 
<= c * b) : a / b <= c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
### Miscellaneous lemmas
-/
theorem div_isBoundedUnder_of_isBigO {α : Type*} {l : Filter α} {f g : α → 𝕜} (h : f =O[l] g) :
    IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  obtain ⟨c, h₀, hc⟩ := h.exists_nonneg
  refine ⟨c, eventually_map.2 (hc.bound.mono fun x hx => ?_)⟩
  rw [norm_div]
  exact div_le_of_le_mul₀ (norm_nonneg _) h₀ hx
/-
**Asymptotics.isBigO_iff_div_isBoundedUnder** 是 Mathlib 中的一个定理，位于命名空间 `Asymptoti
cs`。
形式化陈述：isBigO_iff_div_isBoundedUnder {α : Type*} {l : Filter α} {f g : α -> 𝕜} (h
gf : forallᶠ x in l, g x = 0 -> f x = 0) : f =O[l] g ↔ IsBoundedUnder (· <= ·) l
 fun x => ‖f x / g x‖
参数：hgf : forallᶠ x in l, g x = 0 -> f x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.div_isBoundedUnder_of_isBigO`：div_isBoundedUnder_of_isBigO {
α : Type*} {l : Filter α} {f g : α -> 𝕜} (h : f =O[l] g) : IsBoundedUnder (· <= 
·) l fun x => ‖f x / g x‖
· 使用定理 `Asymptotics.IsBigO.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}   (
c : ℝ), (∀ᶠ (x : …
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem isBigO_iff_div_isBoundedUnder {α : Type*} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) :
    f =O[l] g ↔ IsBoundedUnder (· ≤ ·) l fun x => ‖f x / g x‖ := by
  refine ⟨div_isBoundedUnder_of_isBigO, fun h => ?_⟩
  obtain ⟨c, hc⟩ := h
  simp only [eventually_map, norm_div] at hc
  refine IsBigO.of_bound c (hc.mp <| hgf.mono fun x hx₁ hx₂ => ?_)
  by_cases hgx : g x = 0
  · simp [hx₁ hgx, hgx]
  · exact (div_le_iff₀ (norm_pos_iff.2 hgx)).mp hx₂
/-
**Asymptotics.isBigO_of_div_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`
。
形式化陈述：isBigO_of_div_tendsto_nhds {α : Type*} {l : Filter α} {f g : α -> 𝕜} (hgf 
: forallᶠ x in l, g x = 0 -> f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c
)) : f =O[l] g
参数：hgf : forallᶠ x in l, g x = 0 -> f x = 0；c : 𝕜；H : Filter.Tendsto (f / g) l (
𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff_div_isBoundedUnder`：isBigO_iff_div_isBoundedUnder
 {α : Type*} {l : Filter α} {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f x
 = 0) : f =O[l] g ↔ IsBoundedUn…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
-/
theorem isBigO_of_div_tendsto_nhds {α : Type*} {l : Filter α} {f g : α → 𝕜}
    (hgf : ∀ᶠ x in l, g x = 0 → f x = 0) (c : 𝕜) (H : Filter.Tendsto (f / g) l (𝓝 c)) :
    f =O[l] g :=
  (isBigO_iff_div_isBoundedUnder hgf).2 <| H.norm.isBoundedUnder_le
/-
**Asymptotics.IsLittleO.tendsto_zero_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} {𝕜 : Type u_15} [inst : SeminormedAddComm
Group E'] [inst_1 : NormedDivisionRing 𝕜]   {u : α → E'} {v : α → 𝕜} {l : Filter
 α} {y : 𝕜}, u =o[l] v → Filter.Tendsto v l (nhds y) → Filter.Tendsto u l (nhds 
0)
参数：nhds y；nhds 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans_isBigO`：∀ {α : Type u_1} {E : Type u_3} {F :
 Type u_4} {G' : Type u_8} [inst : Norm E] [inst_1 : Norm F]   [inst_2 : Seminor
medAddCommGroup G'] {l :…
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
-/
theorem IsLittleO.tendsto_zero_of_tendsto {u : α → E'} {v : α → 𝕜} {l : Filter α} {y : 𝕜}
    (huv : u =o[l] v) (hv : Tendsto v l (𝓝 y)) :
    Tendsto u l (𝓝 0) := by
  suffices h : u =o[l] fun _x => (1 : 𝕜) by
    rwa [isLittleO_one_iff] at h
  exact huv.trans_isBigO (hv.isBigO_one 𝕜)
/-
**Asymptotics.isBigOWith_of_div_tendsto_nhds** 是 Mathlib 中的一个定理，位于命名空间 `Asymptot
ics`。
形式化陈述：isBigOWith_of_div_tendsto_nhds {C : Real} {a : 𝕜} {f g : α -> 𝕜} {l : Filt
er α} (h : Tendsto (fun x => g x / f x) l (𝓝 a)) (hC : 0 < C) (ha : C⁻¹ < ‖a‖) :
 IsBigOWith C l f g
参数：h : Tendsto (fun x => g x / f x) l (𝓝 a)；hC : 0 < C；ha : C⁻¹ < ‖a‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_const_le`：Filter.Tendsto.eventually_const_le {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Tendsto f l (𝓝 v)) : fora
llᶠ a in l, u <= f a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 75 条，此处仅展示前 30 条）
-/
theorem isBigOWith_of_div_tendsto_nhds {C : ℝ} {a : 𝕜} {f g : α → 𝕜} {l : Filter α}
    (h : Tendsto (fun x ↦ g x / f x) l (𝓝 a)) (hC : 0 < C) (ha : C⁻¹ < ‖a‖) :
    IsBigOWith C l f g := by
  simp only [IsBigOWith]
  apply (((continuous_norm.tendsto _).comp h).eventually_const_le ha).mono
  intro x hx
  simp only [Function.comp_apply, norm_div] at hx
  by_cases hf : f x = 0
  · simp [hf] at hx
    linarith
  rw [le_div_iff₀ (by positivity)] at hx
  field_simp at hx
  exact hx
/-
**Asymptotics.isBigO_of_div_tendsto_nhds_of_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `A
symptotics`。
形式化陈述：isBigO_of_div_tendsto_nhds_of_ne_zero {l : Filter α} {f g : α -> 𝕜} {a : 𝕜
} (h : Tendsto (fun x => g x / f x) l (𝓝 a)) (ha : a != 0) : f =O[l] g
参数：h : Tendsto (fun x => g x / f x) l (𝓝 a)；ha : a != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos'`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α]
 [AddLeftMono α] {a b : α}, 0 < a → 0 < b → 0 < a + b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `inv_pos_of_pos`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] [inst_1 : Pa
rtialOrder G₀] [PosMulReflectLT G₀] {a : G₀}, 0 < a → 0 < a⁻¹
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.FieldSimp.lt_eq_cancel_lt`：lt_eq_cancel_lt {M : Type*} [M
onoidWithZero M] [PartialOrder M] [PosMulStrictMono M] [PosMulReflectLT M] {e₁ e
₂ f₁ f₂ L : M} (H₁ : e₁ = L * …
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval`：eval_cons_mul_eval [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : ((n, e) ::ᵣ L).eval * l.eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 41 条，此处仅展示前 30 条）
-/
theorem isBigO_of_div_tendsto_nhds_of_ne_zero {l : Filter α} {f g : α → 𝕜}
    {a : 𝕜} (h : Tendsto (fun x ↦ g x / f x) l (𝓝 a)) (ha : a ≠ 0) :
    f =O[l] g := by
  obtain ⟨C, hC, ha⟩ : ∃ C, 0 < C ∧ C⁻¹ < ‖a‖ := ⟨‖a‖⁻¹ + 1, by positivity, by field_simp; simpa⟩
  simp only [IsBigO]
  exact ⟨C, isBigOWith_of_div_tendsto_nhds h hC ha⟩
/-
**Asymptotics.isLittleO_pow_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_pow_pow {m n : Nat} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] f
un x => x ^ m
参数：h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `lt_iff_exists_add`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : Part
ialOrder α] [CanonicallyOrderedAdd α] {a b : α}   [AddLeftStrictMono α], a < b ↔
 ∃ c > …
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
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Semi
normedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Fi
lter α} {f : α …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isLittleO_pow_pow {m n : ℕ} (h : m < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m := by
  rcases lt_iff_exists_add.1 h with ⟨p, hp0 : 0 < p, rfl⟩
  suffices (fun x : 𝕜 => x ^ m * x ^ p) =o[𝓝 0] fun x => x ^ m * 1 ^ p by
    simpa only [pow_add, one_pow, mul_one]
  exact IsBigO.mul_isLittleO (isBigO_refl _ _)
    (IsLittleO.pow ((isLittleO_one_iff _).2 tendsto_id) hp0)
/-
**Asymptotics.isLittleO_norm_pow_norm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
`。
形式化陈述：isLittleO_norm_pow_norm_pow {m n : Nat} (h : m < n) : (fun x : E' => ‖x‖ ^
 n) =o[𝓝 0] fun x => ‖x‖ ^ m
参数：h : m < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Asymptotics.isLittleO_pow_pow`：isLittleO_pow_pow {m n : Nat} (h : m < n)
 : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
· 使用定理 `tendsto_norm_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Filte
r.Tendsto (fun a => ‖a‖) (nhds 0) (nhds 0)
-/
theorem isLittleO_norm_pow_norm_pow {m n : ℕ} (h : m < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m :=
  (isLittleO_pow_pow h).comp_tendsto tendsto_norm_zero
/-
**Asymptotics.isLittleO_pow_id** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_pow_id {n : Nat} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun 
x => x
参数：h : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Asymptotics.isLittleO_pow_pow`：isLittleO_pow_pow {m n : Nat} (h : m < n)
 : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
-/
theorem isLittleO_pow_id {n : ℕ} (h : 1 < n) : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x := by
  convert! isLittleO_pow_pow h (𝕜 := 𝕜)
  simp only [pow_one]
/-
**Asymptotics.isLittleO_norm_pow_id** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_norm_pow_id {n : Nat} (h : 1 < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝
 0] fun x => x
参数：h : 1 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_norm_pow_norm_pow`：isLittleO_norm_pow_norm_pow {m 
n : Nat} (h : m < n) : (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => ‖x‖ ^ m
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isLittleO_norm_right`：isLittleO_norm_right : (f =o[l] fun x 
=> ‖g' x‖) ↔ f =o[l] g'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
-/
theorem isLittleO_norm_pow_id {n : ℕ} (h : 1 < n) :
    (fun x : E' => ‖x‖ ^ n) =o[𝓝 0] fun x => x := by
  have := @isLittleO_norm_pow_norm_pow E' _ _ _ h
  simp only [pow_one] at this
  exact isLittleO_norm_right.mp this
/-
**Asymptotics.IsBigO.eq_zero_of_norm_pow_within** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics.IsBigO`。
形式化陈述：∀ {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommGroup E''] [inst
_1 : NormedAddCommGroup F''] {f : E'' → F''}   {s : Set E''} {x₀ : E''} {n : ℕ},
 (f =O[nhdsWithin x₀ s] fun x => ‖x - x₀‖ ^ n) → x₀ ∈ s → n ≠ 0 → f x₀ = 0
参数：f =O[nhdsWithin x₀ s] fun x => ‖x - x₀‖ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_of_mem_nhdsWithin`：mem_of_mem_nhdsWithin {a : α} {s t : Set α} (ha :
 a in s) (ht : t in 𝓝[s] a) : a in t
· 使用定理 `Asymptotics.IsBigO.eq_zero_imp`：∀ {α : Type u_1} {E'' : Type u_9} {F'' :
 Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F'']   
{f'' : α → E''} {g''…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsBigO.eq_zero_of_norm_pow_within {f : E'' → F''} {s : Set E''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝[s] x₀] fun x => ‖x - x₀‖ ^ n) (hx₀ : x₀ ∈ s) (hn : n ≠ 0) : f x₀ = 0 :=
  mem_of_mem_nhdsWithin hx₀ h.eq_zero_imp <| by simp_rw [sub_self, norm_zero, zero_pow hn]
/-
**Asymptotics.IsBigO.eq_zero_of_norm_pow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsBigO`。
形式化陈述：∀ {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommGroup E''] [inst
_1 : NormedAddCommGroup F''] {f : E'' → F''}   {x₀ : E''} {n : ℕ}, (f =O[nhds x₀
] fun x => ‖x - x₀‖ ^ n) → n ≠ 0 → f x₀ = 0
参数：f =O[nhds x₀] fun x => ‖x - x₀‖ ^ n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.eq_zero_of_norm_pow_within`：∀ {E'' : Type u_9} {F'' :
 Type u_10} [inst : NormedAddCommGroup E''] [inst_1 : NormedAddCommGroup F''] {f
 : E'' → F''}   {s : Set E''} {x₀ :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem IsBigO.eq_zero_of_norm_pow {f : E'' → F''} {x₀ : E''} {n : ℕ}
    (h : f =O[𝓝 x₀] fun x => ‖x - x₀‖ ^ n) (hn : n ≠ 0) : f x₀ = 0 := by
  rw [← nhdsWithin_univ] at h
  exact h.eq_zero_of_norm_pow_within (mem_univ _) hn
/-
**Asymptotics.isLittleO_pow_sub_pow_sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_pow_sub_pow_sub (x₀ : E') {n m : Nat} (h : n < m) : (fun x => ‖x
 - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n
参数：x₀ : E'；h : n < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Asymptotics.isLittleO_pow_pow`：isLittleO_pow_pow {m n : Nat} (h : m < n)
 : (fun x : 𝕜 => x ^ n) =o[𝓝 0] fun x => x ^ m
· 使用定理 `tendsto_norm_sub_self`：∀ {E : Type u_4} [inst : SeminormedAddCommGroup E
] (x : E), Filter.Tendsto (fun a => ‖a - x‖) (nhds x) (nhds 0)
-/
theorem isLittleO_pow_sub_pow_sub (x₀ : E') {n m : ℕ} (h : n < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ ^ n :=
  (isLittleO_pow_pow h).comp_tendsto (tendsto_norm_sub_self x₀)
/-
**Asymptotics.isLittleO_pow_sub_sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_pow_sub_sub (x₀ : E') {m : Nat} (h : 1 < m) : (fun x => ‖x - x₀‖
 ^ m) =o[𝓝 x₀] fun x => x - x₀
参数：x₀ : E'；h : 1 < m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Asymptotics.isLittleO_pow_sub_pow_sub`：isLittleO_pow_sub_pow_sub (x₀ : E
') {n m : Nat} (h : n < m) : (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => ‖x - x₀‖ 
^ n
-/
theorem isLittleO_pow_sub_sub (x₀ : E') {m : ℕ} (h : 1 < m) :
    (fun x => ‖x - x₀‖ ^ m) =o[𝓝 x₀] fun x => x - x₀ := by
  simpa only [isLittleO_norm_right, pow_one] using isLittleO_pow_sub_pow_sub x₀ h
/-
**Asymptotics.IsBigOWith.right_le_sub_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {c : ℝ
} {l : Filter α} {f₁ f₂ : α → E'},   Asymptotics.IsBigOWith c l f₁ f₂ → c < 1 → 
Asymptotics.IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x
参数：1 / (1 - c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
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
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `sub_le_sub_left`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Add
LeftMono α] [AddRightMono α] {a b : α},   a ≤ b → ∀ (c : α), c - b ≤ c - a
· 使用定理 `norm_sub_norm_le`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), ‖a‖ - ‖b‖ ≤ ‖a - b‖
-/
theorem IsBigOWith.right_le_sub_of_lt_one {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₂ x - f₁ x :=
  IsBigOWith.of_bound <|
    mem_of_superset h.bound fun x hx => by
      simp only [mem_ofPred_eq] at hx ⊢
      rw [mul_comm, one_div, ← div_eq_mul_inv, le_div_iff₀, mul_sub, mul_one, mul_comm]
      · exact le_trans (sub_le_sub_left hx _) (norm_sub_norm_le _ _)
      · exact sub_pos.2 hc
/-
**Asymptotics.IsBigOWith.right_le_add_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymp
totics.IsBigOWith`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {c : ℝ
} {l : Filter α} {f₁ f₂ : α → E'},   Asymptotics.IsBigOWith c l f₁ f₂ → c < 1 → 
Asymptotics.IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x
参数：1 / (1 - c)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α →
 E} {g₁ g₂ : α → F…
· 使用定理 `Asymptotics.IsBigOWith.of_neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' 
: Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {c : ℝ} {g : α 
→ F}   {f' : α → E'} {l …
· 使用定理 `Asymptotics.IsBigOWith.neg_right`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {c : ℝ} {f : α → 
E}   {g' : α → F'} {l …
· 使用定理 `Asymptotics.IsBigOWith.right_le_sub_of_lt_one`：∀ {α : Type u_1} {E' : Ty
pe u_6} [inst : SeminormedAddCommGroup E'] {c : ℝ} {l : Filter α} {f₁ f₂ : α → E
'},   Asymptotics.IsBigOWith c l f₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
-/
theorem IsBigOWith.right_le_add_of_lt_one {f₁ f₂ : α → E'} (h : IsBigOWith c l f₁ f₂) (hc : c < 1) :
    IsBigOWith (1 / (1 - c)) l f₂ fun x => f₁ x + f₂ x :=
  (h.neg_right.right_le_sub_of_lt_one hc).neg_right.of_neg_left.congr rfl (fun _ ↦ rfl) fun x ↦ by
    rw [neg_sub, sub_neg_eq_add]
/-
**Asymptotics.IsLittleO.right_isBigO_sub** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {f₁ f₂ : α → E'},   f₁ =o[l] f₂ → f₂ =O[l] fun x => f₂ x - f₁ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Asymptotics.IsBigOWith.right_le_sub_of_lt_one`：∀ {α : Type u_1} {E' : Ty
pe u_6} [inst : SeminormedAddCommGroup E'] {c : ℝ} {l : Filter α} {f₁ f₂ : α → E
'},   Asymptotics.IsBigOWith c l f₁…
· 使用定理 `Asymptotics.IsLittleO.def'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filt
er α}, f =o[l] g…
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_half_lt_one`：one_half_lt_one : (1 / 2 : α) < 1
-/
theorem IsLittleO.right_isBigO_sub {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₂ x - f₁ x :=
  ((h.def' one_half_pos).right_le_sub_of_lt_one one_half_lt_one).isBigO
/-
**Asymptotics.IsLittleO.right_isBigO_add** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.
IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {f₁ f₂ : α → E'},   f₁ =o[l] f₂ → f₂ =O[l] fun x => f₁ x + f₂ x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Asymptotics.IsBigOWith.right_le_add_of_lt_one`：∀ {α : Type u_1} {E' : Ty
pe u_6} [inst : SeminormedAddCommGroup E'] {c : ℝ} {l : Filter α} {f₁ f₂ : α → E
'},   Asymptotics.IsBigOWith c l f₁…
· 使用定理 `Asymptotics.IsLittleO.def'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Filt
er α}, f =o[l] g…
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_half_lt_one`：one_half_lt_one : (1 / 2 : α) < 1
-/
theorem IsLittleO.right_isBigO_add {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] fun x => f₁ x + f₂ x :=
  ((h.def' one_half_pos).right_le_add_of_lt_one one_half_lt_one).isBigO
/-
**Asymptotics.IsLittleO.right_isBigO_add'** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics
.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {E' : Type u_6} [inst : SeminormedAddCommGroup E'] {l : F
ilter α} {f₁ f₂ : α → E'},   f₁ =o[l] f₂ → f₂ =O[l] (f₂ + f₁)
参数：f₂ + f₁。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.right_isBigO_add`：∀ {α : Type u_1} {E' : Type u_6}
 [inst : SeminormedAddCommGroup E'] {l : Filter α} {f₁ f₂ : α → E'},   f₁ =o[l] 
f₂ → f₂ =O[l] fun x => f₁ x …
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem IsLittleO.right_isBigO_add' {f₁ f₂ : α → E'} (h : f₁ =o[l] f₂) :
    f₂ =O[l] (f₂ + f₁) :=
  add_comm f₁ f₂ ▸ h.right_isBigO_add

/-- If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` such that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`. -/
/-
**Asymptotics.bound_of_isBigO_cofinite** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：bound_of_isBigO_cofinite (h : f =O[cofinite] g'') : exists C > 0, forall ⦃
x⦄, g'' x != 0 -> ‖f x‖ <= C * ‖g'' x‖
参数：h : f =O[cofinite] g''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_cofinite`：eventually_cofinite {p : α -> Prop} : (foral
lᶠ x in cofinite, p x) ↔ { x | ¬p x }.Finite
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
· 使用定理 `Finset.exists_le`：Finset.exists_le [Nonempty α] [Preorder α] [IsDirected
Order α] (s : Finset α) : exists M, forall i in s, i <= M
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.Finite.toFinset.congr_simp`：∀ {α : Type u} {s s_1 : Set α} (e_s : s 
= s_1) (h : s.Finite), h.toFinset = ⋯.toFinset
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用定理 `max_mul_of_nonneg`：max_mul_of_nonneg [MulPosMono R] (a b : R) (hc : 0 <=
 c) : max a b * c = max (a * c) (b * c)
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_max_iff`：le_max_iff : a <= max b c ↔ a <= b ∨ a <= c
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0

--- 原说明 ---
If `f x = O(g x)` along `cofinite`, then there exists a positive constant `C` su
ch that
`‖f x‖ ≤ C * ‖g x‖` whenever `g x ≠ 0`.
-/
theorem bound_of_isBigO_cofinite (h : f =O[cofinite] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ := by
  rcases h.exists_pos with ⟨C, C₀, hC⟩
  rw [IsBigOWith_def, eventually_cofinite] at hC
  rcases (hC.toFinset.image fun x => ‖f x‖ / ‖g'' x‖).exists_le with ⟨C', hC'⟩
  have : ∀ x, C * ‖g'' x‖ < ‖f x‖ → ‖f x‖ / ‖g'' x‖ ≤ C' := by simpa using hC'
  refine ⟨max C C', lt_max_iff.2 (Or.inl C₀), fun x h₀ => ?_⟩
  rw [max_mul_of_nonneg _ _ (norm_nonneg _), le_max_iff, or_iff_not_imp_left, not_le]
  exact fun hx => (div_le_iff₀ (norm_pos_iff.2 h₀)).1 (this _ hx)
/-
**Asymptotics.isBigO_cofinite_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_cofinite_iff (h : forall x, g'' x = 0 -> f'' x = 0) : f'' =O[cofini
te] g'' ↔ exists C, forall x, ‖f'' x‖ <= C * ‖g'' x‖
参数：h : forall x, g'' x = 0 -> f'' x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.bound_of_isBigO_cofinite`：bound_of_isBigO_cofinite (h : f =O
[cofinite] g'') : exists C > 0, forall ⦃x⦄, g'' x != 0 -> ‖f x‖ <= C * ‖g'' x‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_top`：isBigO_top : f =O[⊤] g ↔ exists C, forall x, ‖f 
x‖ <= C * ‖g x‖
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem isBigO_cofinite_iff (h : ∀ x, g'' x = 0 → f'' x = 0) :
    f'' =O[cofinite] g'' ↔ ∃ C, ∀ x, ‖f'' x‖ ≤ C * ‖g'' x‖ := by
  classical
  exact ⟨fun h' =>
    let ⟨C, _C₀, hC⟩ := bound_of_isBigO_cofinite h'
    ⟨C, fun x => if hx : g'' x = 0 then by simp [h _ hx, hx] else hC hx⟩,
    fun h => (isBigO_top.2 h).mono le_top⟩
/-
**Asymptotics.bound_of_isBigO_nat_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：bound_of_isBigO_nat_atTop {f : Nat -> E} {g'' : Nat -> E''} (h : f =O[atTo
p] g'') : exists C > 0, forall ⦃x⦄, g'' x != 0 -> ‖f x‖ <= C * ‖g'' x‖
参数：h : f =O[atTop] g''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.bound_of_isBigO_cofinite`：bound_of_isBigO_cofinite (h : f =O
[cofinite] g'') : exists C > 0, forall ⦃x⦄, g'' x != 0 -> ‖f x‖ <= C * ‖g'' x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem bound_of_isBigO_nat_atTop {f : ℕ → E} {g'' : ℕ → E''} (h : f =O[atTop] g'') :
    ∃ C > 0, ∀ ⦃x⦄, g'' x ≠ 0 → ‖f x‖ ≤ C * ‖g'' x‖ :=
  bound_of_isBigO_cofinite <| by rwa [Nat.cofinite_eq_atTop]
/-
**Asymptotics.isBigO_nat_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_nat_atTop_iff {f : Nat -> E''} {g : Nat -> F''} (h : forall x, g x 
= 0 -> f x = 0) : f =O[atTop] g ↔ exists C, forall x, ‖f x‖ <= C * ‖g x‖
参数：h : forall x, g x = 0 -> f x = 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `Asymptotics.isBigO_cofinite_iff`：isBigO_cofinite_iff (h : forall x, g'' 
x = 0 -> f'' x = 0) : f'' =O[cofinite] g'' ↔ exists C, forall x, ‖f'' x‖ <= C * 
‖g'' x‖
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBigO_nat_atTop_iff {f : ℕ → E''} {g : ℕ → F''} (h : ∀ x, g x = 0 → f x = 0) :
    f =O[atTop] g ↔ ∃ C, ∀ x, ‖f x‖ ≤ C * ‖g x‖ := by
  rw [← Nat.cofinite_eq_atTop, isBigO_cofinite_iff h]
/-
**Asymptotics.isBigO_one_nat_atTop_iff** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_one_nat_atTop_iff {f : Nat -> E''} : f =O[atTop] (fun _n => 1 : Nat
 -> Real) ↔ exists C, forall n, ‖f n‖ <= C
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Asymptotics.isBigO_nat_atTop_iff`：isBigO_nat_atTop_iff {f : Nat -> E''} 
{g : Nat -> F''} (h : forall x, g x = 0 -> f x = 0) : f =O[atTop] g ↔ exists C, 
forall x, ‖f x‖ <= C *…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_one_nat_atTop_iff {f : ℕ → E''} :
    f =O[atTop] (fun _n => 1 : ℕ → ℝ) ↔ ∃ C, ∀ n, ‖f n‖ ≤ C :=
  Iff.trans (isBigO_nat_atTop_iff fun _ h => (one_ne_zero h).elim) <| by
    simp only [norm_one, mul_one]
/-
**Asymptotics.IsBigO.nat_of_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`
。
形式化陈述：∀ {E'' : Type u_9} {F'' : Type u_10} [inst : NormedAddCommGroup E''] [inst
_1 : NormedAddCommGroup F''] {f : ℕ → E''}   {g : ℕ → F''}, f =O[Filter.atTop] g
 → ∀ {l : Filter ℕ}, (∀ᶠ (n : ℕ) in l, g n = 0 → f n = 0) → f =O[l] g
参数：∀ᶠ (n : ℕ) in l, g n = 0 → f n = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.bound_of_isBigO_nat_atTop`：bound_of_isBigO_nat_atTop {f : Na
t -> E} {g'' : Nat -> E''} (h : f =O[atTop] g'') : exists C > 0, forall ⦃x⦄, g''
 x != 0 -> ‖f x‖ <= C * ‖g'…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
theorem IsBigO.nat_of_atTop {f : ℕ → E''} {g : ℕ → F''} (hfg : f =O[atTop] g)
    {l : Filter ℕ} (h : ∀ᶠ n in l, g n = 0 → f n = 0) : f =O[l] g := by
  obtain ⟨C, hC_pos, hC⟩ := bound_of_isBigO_nat_atTop hfg
  refine isBigO_iff.mpr ⟨C, ?_⟩
  filter_upwards [h] with x h
  by_cases hf : f x = 0
  · simp [hf, hC_pos]
  exact hC fun a ↦ hf (h a)
/-
**Asymptotics.isBigOWith_pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigOWith_pi {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, Seminor
medAddCommGroup (E' i)] {f : α -> forall i, E' i} {C : Real} (hC : 0 <= C) : IsB
igOWith C l f g' ↔ forall i, IsBigOWith C l (fun x => f x i) g'
参数：E' i；hC : 0 <= C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pi_norm_le_iff_of_nonneg`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : Fi
ntype ι] [inst_1 : (i : ι) → SeminormedAddGroup (G i)] {x : (i : ι) → G i}   {r 
: ℝ}, 0 ≤ r → …
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigOWith_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} {C : ℝ} (hC : 0 ≤ C) :
    IsBigOWith C l f g' ↔ ∀ i, IsBigOWith C l (fun x => f x i) g' := by
  have this (x) : 0 ≤ C * ‖g' x‖ := by positivity
  simp only [isBigOWith_iff, pi_norm_le_iff_of_nonneg (this _), eventually_all]

@[simp]
/-
**Asymptotics.isBigO_pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_pi {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, SeminormedA
ddCommGroup (E' i)] {f : α -> forall i, E' i} : f =O[l] g' ↔ forall i, (fun x =>
 f x i) =O[l] g'
参数：E' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Filter.eventually_congr`：eventually_congr {f : Filter α} {p q : α -> Pro
p} (h : forallᶠ x in f, p x ↔ q x) : (forallᶠ x in f, p x) ↔ forallᶠ x in f, q x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Asymptotics.isBigOWith_pi`：isBigOWith_pi {ι : Type*} [Fintype ι] {E' : ι
 -> Type*} [forall i, SeminormedAddCommGroup (E' i)] {f : α -> forall i, E' i} {
C : Real} (hC :…
-/
theorem isBigO_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =O[l] g' ↔ ∀ i, (fun x => f x i) =O[l] g' := by
  simp only [isBigO_iff_eventually_isBigOWith, ← eventually_all]
  exact eventually_congr (eventually_atTop.2 ⟨0, fun c => isBigOWith_pi⟩)

@[simp]
/-
**Asymptotics.isLittleO_pi** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics`。
形式化陈述：isLittleO_pi {ι : Type*} [Fintype ι] {E' : ι -> Type*} [forall i, Seminorm
edAddCommGroup (E' i)] {f : α -> forall i, E' i} : f =o[l] g' ↔ forall i, (fun x
 => f x i) =o[l] g'
参数：E' i。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
theorem isLittleO_pi {ι : Type*} [Fintype ι] {E' : ι → Type*} [∀ i, SeminormedAddCommGroup (E' i)]
    {f : α → ∀ i, E' i} : f =o[l] g' ↔ ∀ i, (fun x => f x i) =o[l] g' := by
  simp +contextual only [IsLittleO_def, isBigOWith_pi, le_of_lt]
  exact ⟨fun h i c hc => h hc i, fun h c hc i => h i hc⟩
/-
**Asymptotics.IsBigO.natCast_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO
`。
形式化陈述：∀ {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {R : Typ
e u_17} [inst_2 : Semiring R]   [inst_3 : PartialOrder R] [IsStrictOrderedRing R
] [Archimedean R] {f : R → E} {g : R → F},   f =O[Filter.atTop] g → (fun n => f 
↑n) =O[Filter.atTop] fun n => g ↑n
参数：fun n => f ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem IsBigO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R]
    {f : R → E} {g : R → F} (h : f =O[atTop] g) :
    (fun (n : ℕ) => f n) =O[atTop] (fun n => g n) :=
  IsBigO.comp_tendsto h tendsto_natCast_atTop_atTop
/-
**Asymptotics.IsLittleO.natCast_atTop** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsL
ittleO`。
形式化陈述：∀ {E : Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {R : Typ
e u_17} [inst_2 : Semiring R]   [inst_3 : PartialOrder R] [IsStrictOrderedRing R
] [Archimedean R] {f : R → E} {g : R → F},   f =o[Filter.atTop] g → (fun n => f 
↑n) =o[Filter.atTop] fun n => g ↑n
参数：fun n => f ↑n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
-/
theorem IsLittleO.natCast_atTop {R : Type*} [Semiring R] [PartialOrder R] [IsStrictOrderedRing R]
    [Archimedean R]
    {f : R → E} {g : R → F} (h : f =o[atTop] g) :
    (fun (n : ℕ) => f n) =o[atTop] (fun n => g n) :=
  IsLittleO.comp_tendsto h tendsto_natCast_atTop_atTop
/-
**Asymptotics.isBigO_atTop_iff_eventually_exists** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics`。
形式化陈述：isBigO_atTop_iff_eventually_exists {α : Type*} [SemilatticeSup α] [Nonempt
y α] {f : α -> E} {g : α -> F} : f =O[atTop] g ↔ forallᶠ n₀ in atTop, exists c, 
forall n >= n₀, ‖f n‖ <= c * ‖g n‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用引理 `Filter.exists_eventually_atTop`：exists_eventually_atTop {r : α -> β -> P
rop} : (exists b, forallᶠ a in atTop, r a b) ↔ forallᶠ a₀ in atTop, exists b, fo
rall a, a₀ <= a -> r…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isBigO_atTop_iff_eventually_exists {α : Type*} [SemilatticeSup α] [Nonempty α]
    {f : α → E} {g : α → F} : f =O[atTop] g ↔ ∀ᶠ n₀ in atTop, ∃ c, ∀ n ≥ n₀, ‖f n‖ ≤ c * ‖g n‖ := by
  rw [isBigO_iff, exists_eventually_atTop]
/-
**Asymptotics.isBigO_atTop_iff_eventually_exists_pos** 是 Mathlib 中的一个定理，位于命名空间 `
Asymptotics`。
形式化陈述：isBigO_atTop_iff_eventually_exists_pos {α : Type*} [SemilatticeSup α] [Non
empty α] {f : α -> G} {g : α -> G'} : f =O[atTop] g ↔ forallᶠ n₀ in atTop, exist
s c > 0, forall n >= n₀, c * ‖f n‖ <= ‖g n‖
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isBigO_atTop_iff_eventually_exists_pos {α : Type*}
    [SemilatticeSup α] [Nonempty α] {f : α → G} {g : α → G'} :
    f =O[atTop] g ↔ ∀ᶠ n₀ in atTop, ∃ c > 0, ∀ n ≥ n₀, c * ‖f n‖ ≤ ‖g n‖ := by
  simp_rw [isBigO_iff'', ← exists_prop, Subtype.exists', exists_eventually_atTop]
/-
**Asymptotics.isBigOWith_mul_iff_isBigOWith_div** 是 Mathlib 中的一个引理，位于命名空间 `Asymp
totics`。
形式化陈述：isBigOWith_mul_iff_isBigOWith_div {f g h : α -> 𝕜} {c : Real} (hf : forall
ᶠ x in l, f x != 0) : IsBigOWith c l (fun x => f x * g x) h ↔ IsBigOWith c l g (
fun x => h x / f x)
参数：hf : forallᶠ x in l, f x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigOWith_iff`：isBigOWith_iff : IsBigOWith c l f g ↔ forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.Eventually.congr`：∀ {α : Type u} {f : Filter α} {p q : α → Prop},
   (∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x ↔ q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_div_assoc`：mul_div_assoc (a b c : G) : a * b / c = a * (b / c)
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isBigOWith_mul_iff_isBigOWith_div {f g h : α → 𝕜} {c : ℝ} (hf : ∀ᶠ x in l, f x ≠ 0) :
    IsBigOWith c l (fun x ↦ f x * g x) h ↔ IsBigOWith c l g (fun x ↦ h x / f x) := by
  rw [isBigOWith_iff, isBigOWith_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;>
  · refine h.congr <| Eventually.mp hf <| Eventually.of_forall fun x hx ↦ ?_
    rw [norm_mul, norm_div, ← mul_div_assoc, le_div_iff₀' (norm_pos_iff.mpr hx)]
/-
**Asymptotics.isBigO_mul_iff_isBigO_div** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`。
形式化陈述：isBigO_mul_iff_isBigO_div {f g h : α -> 𝕜} (hf : forallᶠ x in l, f x != 0)
 : (fun x => f x * g x) =O[l] h ↔ g =O[l] (fun x => h x / f x)
参数：hf : forallᶠ x in l, f x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigO_iff_isBigOWith`：isBigO_iff_isBigOWith : f =O[l] g ↔ e
xists c : Real, IsBigOWith c l f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Asymptotics.isBigOWith_mul_iff_isBigOWith_div`：isBigOWith_mul_iff_isBigO
With_div {f g h : α -> 𝕜} {c : Real} (hf : forallᶠ x in l, f x != 0) : IsBigOWit
h c l (fun x => f x * g x) h ↔ IsBi…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isBigO_mul_iff_isBigO_div {f g h : α → 𝕜} (hf : ∀ᶠ x in l, f x ≠ 0) :
    (fun x ↦ f x * g x) =O[l] h ↔ g =O[l] (fun x ↦ h x / f x) := by
  rw [isBigO_iff_isBigOWith, isBigO_iff_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]
/-
**Asymptotics.isLittleO_mul_iff_isLittleO_div** 是 Mathlib 中的一个引理，位于命名空间 `Asympto
tics`。
形式化陈述：isLittleO_mul_iff_isLittleO_div {f g h : α -> 𝕜} (hf : forallᶠ x in l, f x
 != 0) : (fun x => f x * g x) =o[l] h ↔ g =o[l] (fun x => h x / f x)
参数：hf : forallᶠ x in l, f x != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isLittleO_iff_forall_isBigOWith`：isLittleO_iff_forall_isBigO
With : f =o[l] g ↔ forall ⦃c : Real⦄, 0 < c -> IsBigOWith c l f g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Asymptotics.isBigOWith_mul_iff_isBigOWith_div`：isBigOWith_mul_iff_isBigO
With_div {f g h : α -> 𝕜} {c : Real} (hf : forallᶠ x in l, f x != 0) : IsBigOWit
h c l (fun x => f x * g x) h ↔ IsBi…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma isLittleO_mul_iff_isLittleO_div {f g h : α → 𝕜} (hf : ∀ᶠ x in l, f x ≠ 0) :
    (fun x ↦ f x * g x) =o[l] h ↔ g =o[l] (fun x ↦ h x / f x) := by
  rw [isLittleO_iff_forall_isBigOWith, isLittleO_iff_forall_isBigOWith]
  simp [isBigOWith_mul_iff_isBigOWith_div hf]
/-
**Asymptotics.isBigO_nat_atTop_induction** 是 Mathlib 中的一个引理，位于命名空间 `Asymptotics`
。
形式化陈述：isBigO_nat_atTop_induction {f : Nat -> E''} {g : Nat -> F''} (h : forallᶠ 
n in atTop, g n = 0 -> f n = 0) (hrec : forallᶠ n₀ in atTop, exists C₀, forallᶠ 
n in atTop, forall C >= C₀, (forall m in Finset.Ico n₀ n, ‖f m‖ <= C * ‖g m‖) ->
 ‖f n‖ <= C * ‖g n‖) : f =O[atTop] g
参数：h : forallᶠ n in atTop, g n = 0 -> f n = 0；hrec : forallᶠ n₀ in atTop, exists
 C₀, forallᶠ n in atTop, forall C >= C₀, (forall m in Finset.Ico n₀ n, ‖f m‖ <= 
C * ‖g m‖) -> ‖f n‖ <= C * ‖g n‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_forall_ge_atTop`：eventually_forall_ge_atTop [Preorder 
α] {p : α -> Prop} : (forallᶠ x in atTop, forall y, x <= y -> p y) ↔ forallᶠ x i
n atTop, p x
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用引理 `Finset.sup'`：sup'_one [SemilatticeSup β] (f : α -> β) : sup' 1 one_nonem
pty f = f 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.nonempty_Icc`：nonempty_Icc : (Icc a b).Nonempty ↔ a <= b
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Finset.le_sup'`：le_sup' {b : β} (h : b in s) : f b <= s.sup' ⟨b, h⟩ f
· 使用定理 `Finset.mem_def`：mem_def {a : α} {s : Finset α} : a in s ↔ a in s.1
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
lemma isBigO_nat_atTop_induction {f : ℕ → E''} {g : ℕ → F''}
    (h : ∀ᶠ n in atTop, g n = 0 → f n = 0)
    (hrec : ∀ᶠ n₀ in atTop, ∃ C₀, ∀ᶠ n in atTop, ∀ C ≥ C₀,
      (∀ m ∈ Finset.Ico n₀ n, ‖f m‖ ≤ C * ‖g m‖) → ‖f n‖ ≤ C * ‖g n‖) :
    f =O[atTop] g := by
  rw [← eventually_forall_ge_atTop] at h
  obtain ⟨n₀, h, hrec⟩ := h.and hrec |>.exists
  obtain ⟨C₀, hrec⟩ := hrec
  rw [isBigO_iff]
  rw [← eventually_forall_ge_atTop] at hrec
  obtain ⟨n₁, H₁, H₂⟩ := (eventually_ge_atTop n₀).and hrec |>.exists
  let ubounds := {C | ∀ m ∈ Finset.Icc n₀ n₁, ‖f m‖ ≤ C * ‖g m‖}
  let C₁ := (Finset.Icc n₀ n₁).sup' (Finset.nonempty_Icc.mpr H₁) fun n => ‖f n‖ / ‖g n‖
  have C₁_mem : C₁ ∈ ubounds := by
    rw [Set.mem_ofPred]
    intro m hm
    calc ‖f m‖ = (‖f m‖ / ‖g m‖) * ‖g m‖ := by by_cases hm' : g m = 0 <;> grind [norm_eq_zero]
      _ ≤ C₁ * ‖g m‖ := by
        gcongr
        exact Finset.le_sup' (fun x => ‖f x‖ / ‖g x‖) (Finset.mem_def.mpr hm)
  refine ⟨max C₀ C₁, ?_⟩
  filter_upwards [eventually_ge_atTop n₁] with n hn
  induction n using Nat.strongRecOn with
  | ind n h_ind =>
    refine H₂ _ (by grind) _ (by grind) fun m hm => ?_
    by_cases hbase : m < n₁
    · have hC₁ : C₁ ≤ max C₀ C₁ := by grind
      grw [← hC₁]
      grind
    · grind
/-
**Asymptotics.isBigO_nat_atTop_induction_of_eventually_pos** 是 Mathlib 中的一个引理，位于
命名空间 `Asymptotics`。
形式化陈述：isBigO_nat_atTop_induction_of_eventually_pos {f g : Nat -> Real} (hf : for
allᶠ n in atTop, 0 <= f n) (hg : forallᶠ n in atTop, 0 < g n) (hrec : forallᶠ n₀
 in atTop, exists C₀, forallᶠ n in atTop, forall C >= C₀, (forall m in Finset.Ic
o n₀ n, f m <= C * g m) -> f n <= C * g n) : f =O[atTop] g
参数：hf : forallᶠ n in atTop, 0 <= f n；hg : forallᶠ n in atTop, 0 < g n；hrec : for
allᶠ n₀ in atTop, exists C₀, forallᶠ n in atTop, forall C >= C₀, (forall m in Fi
nset.Ico n₀ n, f m <= C * g m) -> f n <= C * g n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Asymptotics.isBigO_nat_atTop_induction`：isBigO_nat_atTop_induction {f : 
Nat -> E''} {g : Nat -> F''} (h : forallᶠ n in atTop, g n = 0 -> f n = 0) (hrec 
: forallᶠ n₀ in atTop, exist…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_forall_ge_atTop`：eventually_forall_ge_atTop [Preorder 
α] {p : α -> Prop} : (forallᶠ x in atTop, forall y, x <= y -> p y) ↔ forallᶠ x i
n atTop, p x
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
-/
lemma isBigO_nat_atTop_induction_of_eventually_pos {f g : ℕ → ℝ}
    (hf : ∀ᶠ n in atTop, 0 ≤ f n) (hg : ∀ᶠ n in atTop, 0 < g n)
    (hrec : ∀ᶠ n₀ in atTop, ∃ C₀, ∀ᶠ n in atTop, ∀ C ≥ C₀,
      (∀ m ∈ Finset.Ico n₀ n, f m ≤ C * g m) → f n ≤ C * g n) :
    f =O[atTop] g := by
  refine isBigO_nat_atTop_induction ?hzero ?hrec
  case hzero => filter_upwards [hf, hg]; grind
  case hrec =>
    filter_upwards [eventually_forall_ge_atTop.mpr hg, eventually_forall_ge_atTop.mpr hf, hrec]
      with n₀ hn₀ hn₀' hnrec
    obtain ⟨C₀, hnrec⟩ := hnrec
    refine ⟨C₀, ?_⟩
    filter_upwards [hnrec, eventually_ge_atTop n₀]
    grind [Real.norm_eq_abs]

end Asymptotics

open Asymptotics

/-
**summable_of_isBigO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] [CompleteSpace E] {f :
 ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofinite] g) : Summable f
参数：hg : Summable g；h : f =O[cofinite] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α}, 
  f =O[l] g → ∃ c, …
· 使用定理 `Summable.of_norm_bounded_eventually`：Summable.of_norm_bounded_eventually
 {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : forallᶠ i in cofinite, ‖f i
‖ <= g i) : Summable f
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Summable.abs`：∀ {ι : Type u_1} {α : Type u_3} [inst : AddCommGroup α] [i
nst_1 : LinearOrder α] [IsOrderedAddMonoid α]   [inst_3 : UniformSpace α] [IsUni
fo…
· 使用定理 `instIsUniformAddGroupReal`：IsUniformAddGroup ℝ
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
-/
theorem summable_of_isBigO {ι E} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ι → E} {g : ι → ℝ} (hg : Summable g) (h : f =O[cofinite] g) : Summable f :=
  let ⟨_, hC⟩ := h.isBigOWith
  .of_norm_bounded_eventually (hg.abs.mul_left _) hC.bound
/-
**summable_of_isBigO_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_isBigO_nat {E} [SeminormedAddCommGroup E] [CompleteSpace E] {f
 : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : f =O[atTop] g) : Summable 
f
参数：hg : Summable g；h : f =O[atTop] g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
-/
theorem summable_of_isBigO_nat {E} [SeminormedAddCommGroup E] [CompleteSpace E]
    {f : ℕ → E} {g : ℕ → ℝ} (hg : Summable g) (h : f =O[atTop] g) : Summable f :=
  summable_of_isBigO hg <| Nat.cofinite_eq_atTop.symm ▸ h
/-
**Asymptotics.IsBigO.comp_summable_norm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Asymptotics.IsBigO.comp_summable_norm {ι E F : Type*} [SeminormedAddCommGr
oup E] [SeminormedAddCommGroup F] {f : E -> F} {g : ι -> E} (hf : f =O[𝓝 0] id) 
(hg : Summable (‖g ·‖)) : Summable (‖f <| g ·‖)
参数：hf : f =O[𝓝 0] id；hg : Summable (‖g ·‖)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `Asymptotics.IsBigO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E : Ty
pe u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}
   {l : Filter α}, f …
· 使用定理 `Asymptotics.IsBigO.norm_norm`：∀ {α : Type u_1} {E' : Type u_6} {F' : Typ
e u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F']  
 {f' : α → E'} {g'…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
-/
lemma Asymptotics.IsBigO.comp_summable_norm {ι E F : Type*}
    [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] {f : E → F} {g : ι → E}
    (hf : f =O[𝓝 0] id) (hg : Summable (‖g ·‖)) : Summable (‖f <| g ·‖) :=
  summable_of_isBigO hg <| hf.norm_norm.comp_tendsto <|
    tendsto_zero_iff_norm_tendsto_zero.2 hg.tendsto_cofinite_zero
/-
**Summable.mul_tendsto_const** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Summable.mul_tendsto_const {F ι : Type*} [NormedRing F] [NormMulClass F] [
NormOneClass F] [CompleteSpace F] {f g : ι -> F} (hf : Summable fun n => ‖f n‖) 
{c : F} (hg : Tendsto g cofinite (𝓝 c)) : Summable fun n => f n * g n
参数：hf : Summable fun n => ‖f n‖；hg : Tendsto g cofinite (𝓝 c)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_of_isBigO`：summable_of_isBigO {ι E} [SeminormedAddCommGroup E] 
[CompleteSpace E] {f : ι -> E} {g : ι -> Real} (hg : Summable g) (h : f =O[cofin
ite] g) …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `Asymptotics.isBigO_const_mul_self`：isBigO_const_mul_self (c : R) (f : α 
-> R) (l : Filter α) : (fun x => c * f x) =O[l] f
· 使用定理 `Filter.Tendsto.isBigO_one`：∀ {α : Type u_1} (F : Type u_4) {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {f' : α → E'}   {l : Fil
ter α} [inst_2 …
-/
lemma Summable.mul_tendsto_const {F ι : Type*} [NormedRing F] [NormMulClass F] [NormOneClass F]
    [CompleteSpace F] {f g : ι → F} (hf : Summable fun n ↦ ‖f n‖) {c : F}
    (hg : Tendsto g cofinite (𝓝 c)) : Summable fun n ↦ f n * g n := by
  apply summable_of_isBigO hf
  simpa using (isBigO_const_mul_self 1 f _).mul (hg.isBigO_one F)

namespace OpenPartialHomeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {E : Type*} [Norm E] {F : Type*} [Norm F]

/-- Transfer `IsBigOWith` over an `OpenPartialHomeomorph`. -/
/-
**OpenPartialHomeomorph.isBigOWith_congr** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialH
omeomorph`。
形式化陈述：isBigOWith_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.targ
et) {f : β -> E} {g : β -> F} {C : Real} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C
 (𝓝 (e.symm b)) (f ∘ e) (g ∘ e)
参数：e : OpenPartialHomeomorph α β；hb : b in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E 
: Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E}
   {g : α → F} {l : Filte…
· 使用定理 `OpenPartialHomeomorph.continuousAt`：∀ {X : Type u_1} {Y : Type u_3} [ins
t : TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomor
ph X Y) {x : X}, x ∈ e.s…
· 使用定理 `OpenPartialHomeomorph.map_target`：map_target {x : Y} (h : x in e.target)
 : e.symm x in e.source
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OpenPartialHomeomorph.rightInvOn`：∀ {X : Type u_1} {Y : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   (e : OpenPartialHomeomorph
 X Y), Set.RightInvOn …
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `Asymptotics.IsBigOWith.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c₁ c₂ : ℝ} {l : Filter α}   {f₁ f₂ : α 
→ E} {g₁ g₂ : α → F…
· 使用定理 `OpenPartialHomeomorph.continuousAt_symm`：continuousAt_symm {x : Y} (h : 
x in e.target) : ContinuousAt e.symm x
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `OpenPartialHomeomorph.eventually_right_inverse`：eventually_right_inverse
 {x} (hx : x in e.target) : forallᶠ y in 𝓝 x, e (e.symm y) = y
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂

--- 原说明 ---
Transfer `IsBigOWith` over an `OpenPartialHomeomorph`.
-/
theorem isBigOWith_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} {C : ℝ} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  ⟨fun h =>
    h.comp_tendsto <| by
      have := e.continuousAt (e.map_target hb)
      rwa [ContinuousAt, e.rightInvOn hb] at this,
    fun h =>
    (h.comp_tendsto (e.continuousAt_symm hb)).congr' rfl
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg f hx)
      ((e.eventually_right_inverse hb).mono fun _ hx => congr_arg g hx)⟩

/-- Transfer `IsBigO` over an `OpenPartialHomeomorph`. -/
/-
**OpenPartialHomeomorph.isBigO_congr** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHomeo
morph`。
形式化陈述：isBigO_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.target) 
{f : β -> E} {g : β -> F} : f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e)
参数：e : OpenPartialHomeomorph α β；hb : b in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `OpenPartialHomeomorph.isBigOWith_congr`：isBigOWith_congr (e : OpenPartia
lHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E} {g : β -> F} {C : Rea
l} : IsBigOWith C (𝓝 b) f g …

--- 原说明 ---
Transfer `IsBigO` over an `OpenPartialHomeomorph`.
-/
theorem isBigO_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr hb

/-- Transfer `IsLittleO` over an `OpenPartialHomeomorph`. -/
/-
**OpenPartialHomeomorph.isLittleO_congr** 是 Mathlib 中的一个定理，位于命名空间 `OpenPartialHo
meomorph`。
形式化陈述：isLittleO_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b in e.targe
t) {f : β -> E} {g : β -> F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e)
参数：e : OpenPartialHomeomorph α β；hb : b in e.target。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `OpenPartialHomeomorph.isBigOWith_congr`：isBigOWith_congr (e : OpenPartia
lHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E} {g : β -> F} {C : Rea
l} : IsBigOWith C (𝓝 b) f g …

--- 原说明 ---
Transfer `IsLittleO` over an `OpenPartialHomeomorph`.
-/
theorem isLittleO_congr (e : OpenPartialHomeomorph α β) {b : β} (hb : b ∈ e.target) {f : β → E}
    {g : β → F} : f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr hb

end OpenPartialHomeomorph

namespace Homeomorph

variable {α : Type*} {β : Type*} [TopologicalSpace α] [TopologicalSpace β]
variable {E : Type*} [Norm E] {F : Type*} [Norm F]

open Asymptotics

/-- Transfer `IsBigOWith` over a `Homeomorph`. -/
/-
**Homeomorph.isBigOWith_congr** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} {C : Real}
 : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e)
参数：e : α ≃ₜ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenPartialHomeomorph.isBigOWith_congr`：isBigOWith_congr (e : OpenPartia
lHomeomorph α β) {b : β} (hb : b in e.target) {f : β -> E} {g : β -> F} {C : Rea
l} : IsBigOWith C (𝓝 b) f g …
· 使用定理 `trivial`：True

--- 原说明 ---
Transfer `IsBigOWith` over a `Homeomorph`.
-/
theorem isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} {C : ℝ} :
    IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.symm b)) (f ∘ e) (g ∘ e) :=
  e.toOpenPartialHomeomorph.isBigOWith_congr trivial

/-- Transfer `IsBigO` over a `Homeomorph`. -/
/-
**Homeomorph.isBigO_congr** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isBigO_congr (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} : f =O[𝓝 b] g 
↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e)
参数：e : α ≃ₜ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsBigO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u_20
} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F), f 
=O[l] g = ∃ …
· 使用定理 `exists_congr`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a) 
→ ((∃ a, p a) ↔ ∃ a, q a)
· 使用定理 `Homeomorph.isBigOWith_congr`：isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : 
β -> E} {g : β -> F} {C : Real} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.sy
mm b)) (f ∘ e) (g…

--- 原说明 ---
Transfer `IsBigO` over a `Homeomorph`.
-/
theorem isBigO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =O[𝓝 b] g ↔ (f ∘ e) =O[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsBigO_def]
  exact exists_congr fun C => e.isBigOWith_congr

/-- Transfer `IsLittleO` over a `Homeomorph`. -/
/-
**Homeomorph.isLittleO_congr** 是 Mathlib 中的一个定理，位于命名空间 `Homeomorph`。
形式化陈述：isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β -> E} {g : β -> F} : f =o[𝓝 b]
 g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e)
参数：e : α ≃ₜ β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.IsLittleO_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type u
_20} [inst : Norm E] [inst_1 : Norm F] (l : Filter α) (f : α → E)   (g : α → F),
 f =o[l] g = ∀ …
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `Homeomorph.isBigOWith_congr`：isBigOWith_congr (e : α ≃ₜ β) {b : β} {f : 
β -> E} {g : β -> F} {C : Real} : IsBigOWith C (𝓝 b) f g ↔ IsBigOWith C (𝓝 (e.sy
mm b)) (f ∘ e) (g…

--- 原说明 ---
Transfer `IsLittleO` over a `Homeomorph`.
-/
theorem isLittleO_congr (e : α ≃ₜ β) {b : β} {f : β → E} {g : β → F} :
    f =o[𝓝 b] g ↔ (f ∘ e) =o[𝓝 (e.symm b)] (g ∘ e) := by
  simp only [IsLittleO_def]
  exact forall₂_congr fun c _hc => e.isBigOWith_congr

end Homeomorph

namespace ContinuousOn

variable {α E F : Type*} [TopologicalSpace α] {s : Set α} {f : α → E} {c : F}

section IsBigO

variable [SeminormedAddGroup E] [Norm F]

/-
**ContinuousOn.isBigOWith_principal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : TopologicalSpace α]
 {s : Set α} {f : α → E} {c : F}   [inst_1 : SeminormedAddGroup E] [inst_2 : Nor
m F],   ContinuousOn f s →     IsCompact s → ‖c‖ ≠ 0 → Asymptotics.IsBigOWith (s
Sup (norm '' f '' s) / ‖c‖) (Filter.principal s) f fun x => c
参数：sSup (norm '' f '' s) / ‖c‖；Filter.principal s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isBigOWith_principal`：isBigOWith_principal {s : Set α} : IsB
igOWith c (𝓟 s) f g ↔ forall x in s, ‖f x‖ <= c * ‖g x‖
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsCompact.isLUB_sSup`：IsCompact.isLUB_sSup [ClosedIciTopology α] {s : Se
t α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsLUB s (sSup s)
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
protected theorem isBigOWith_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hc : ‖c‖ ≠ 0) :
    IsBigOWith (sSup (Norm.norm '' f '' s) / ‖c‖) (𝓟 s) f fun _ => c := by
  rw [isBigOWith_principal, div_mul_cancel₀ _ hc]
  exact fun x hx ↦ hs.image_of_continuousOn hf |>.image continuous_norm
   |>.isLUB_sSup (Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩)
   |>.left <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx
/-
**ContinuousOn.isBigO_principal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : TopologicalSpace α]
 {s : Set α} {f : α → E} {c : F}   [inst_1 : SeminormedAddGroup E] [inst_2 : Nor
m F],   ContinuousOn f s → IsCompact s → ‖c‖ ≠ 0 → f =O[Filter.principal s] fun 
x => c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `ContinuousOn.isBigOWith_principal`：∀ {α : Type u_1} {E : Type u_2} {F : 
Type u_3} [inst : TopologicalSpace α] {s : Set α} {f : α → E} {c : F}   [inst_1 
: SeminormedAddGroup E]…
-/
protected theorem isBigO_principal (hf : ContinuousOn f s) (hs : IsCompact s)
    (hc : ‖c‖ ≠ 0) : f =O[𝓟 s] fun _ => c :=
  (hf.isBigOWith_principal hs hc).isBigO

end IsBigO

section IsBigORev

variable [NormedAddGroup E] [SeminormedAddGroup F]

/-
**ContinuousOn.isBigOWith_rev_principal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`
。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : TopologicalSpace α]
 {s : Set α} {f : α → E}   [inst_1 : NormedAddGroup E] [inst_2 : SeminormedAddGr
oup F],   ContinuousOn f s →     IsCompact s →       (∀ i ∈ s, f i ≠ 0) →       
  ∀ (c : F), Asymptotics.IsBigOWith (‖c‖ / sInf (norm '' f '' s)) (Filter.princi
pal s) (fun x => c) f
参数：∀ i ∈ s, f i ≠ 0；c : F；‖c‖ / sInf (norm '' f '' s)；Filter.principal s；fun x =
> c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigOWith_principal`：isBigOWith_principal {s : Set α} : IsB
igOWith c (𝓟 s) f g ↔ forall x in s, ‖f x‖ <= c * ‖g x‖
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用定理 `continuous_norm`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Continu
ous fun a => ‖a‖
· 使用定理 `IsCompact.isGLB_sInf`：IsCompact.isGLB_sInf [ClosedIicTopology α] {s : Se
t α} (hs : IsCompact s) (ne_s : s.Nonempty) : IsGLB s (sInf s)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `le_mul_of_one_le_right`：le_mul_of_one_le_right [PosMulMono α] (ha : 0 <=
 a) (h : 1 <= b) : a <= a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `one_le_div`：one_le_div (hb : 0 < b) : 1 <= a / b ↔ b <= a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsCompact.sInf_mem`：IsCompact.sInf_mem [ClosedIicTopology α] {s : Set α}
 (hs : IsCompact s) (ne_s : s.Nonempty) : sInf s in s
· 使用定理 `IsGLB.nonempty`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α}
 [NoTopOrder α], IsGLB s a → s.Nonempty
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `norm_ne_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≠ 0 ↔ a ≠ 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
-/
protected theorem isBigOWith_rev_principal
    (hf : ContinuousOn f s) (hs : IsCompact s) (hC : ∀ i ∈ s, f i ≠ 0) (c : F) :
    IsBigOWith (‖c‖ / sInf (Norm.norm '' f '' s)) (𝓟 s) (fun _ => c) f := by
  refine isBigOWith_principal.mpr fun x hx ↦ ?_
  rw [mul_comm_div]
  replace hs := hs.image_of_continuousOn hf |>.image continuous_norm
  have h_sInf := hs.isGLB_sInf <| Set.image_nonempty.mpr <| Set.image_nonempty.mpr ⟨x, hx⟩
  refine le_mul_of_one_le_right (norm_nonneg c) <| (one_le_div ?_).mpr <|
    h_sInf.1 <| Set.mem_image_of_mem _ <| Set.mem_image_of_mem _ hx
  obtain ⟨_, ⟨x, hx, hCx⟩, hnormCx⟩ := hs.sInf_mem h_sInf.nonempty
  rw [← hnormCx, ← hCx]
  exact (norm_ne_zero_iff.mpr (hC x hx)).symm.lt_of_le (norm_nonneg _)
/-
**ContinuousOn.isBigO_rev_principal** 是 Mathlib 中的一个定理，位于命名空间 `ContinuousOn`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {F : Type u_3} [inst : TopologicalSpace α]
 {s : Set α} {f : α → E}   [inst_1 : NormedAddGroup E] [inst_2 : SeminormedAddGr
oup F],   ContinuousOn f s → IsCompact s → (∀ i ∈ s, f i ≠ 0) → ∀ (c : F), (fun 
x => c) =O[Filter.principal s] f
参数：∀ i ∈ s, f i ≠ 0；c : F；fun x => c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `ContinuousOn.isBigOWith_rev_principal`：∀ {α : Type u_1} {E : Type u_2} {
F : Type u_3} [inst : TopologicalSpace α] {s : Set α} {f : α → E}   [inst_1 : No
rmedAddGroup E] [inst_2 : S…
-/
protected theorem isBigO_rev_principal (hf : ContinuousOn f s)
    (hs : IsCompact s) (hC : ∀ i ∈ s, f i ≠ 0) (c : F) : (fun _ => c) =O[𝓟 s] f :=
  (hf.isBigOWith_rev_principal hs hC c).isBigO

end IsBigORev

end ContinuousOn

/-- The (scalar) product of a sequence that tends to zero with a bounded one also tends to zero. -/
/-
**NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 E : Type*} [
NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E
] {l : Filter ι} {ε : ι -> 𝕜} {f : ι -> E} (hε : Tendsto ε l (𝓝 0)) (hf : IsBoun
dedUnder (· <= ·) l (norm ∘ f)) : Tendsto (ε • f) l (𝓝 0)
参数：hε : Tendsto ε l (𝓝 0)；hf : IsBoundedUnder (· <= ·) l (norm ∘ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsLittleO.smul_isBigO`：∀ {α : Type u_1} {E' : Type u_6} {F' 
: Type u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E'] 
  [inst_1 : SeminormedA…
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Filter.IsBoundedUnder.isBigO_const`：∀ {α : Type u_1} {E : Type u_3} {F''
 : Type u_10} [inst : Norm E] [inst_1 : NormedAddCommGroup F''] {f : α → E}   {l
 : Filter α}, Filter.IsB…
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K

--- 原说明 ---
The (scalar) product of a sequence that tends to zero with a bounded one also te
nds to zero.
-/
lemma NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 E : Type*}
    [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
    {l : Filter ι} {ε : ι → 𝕜} {f : ι → E} (hε : Tendsto ε l (𝓝 0))
    (hf : IsBoundedUnder (· ≤ ·) l (norm ∘ f)) :
    Tendsto (ε • f) l (𝓝 0) := by
  rw [← isLittleO_one_iff 𝕜] at hε ⊢
  simpa using! IsLittleO.smul_isBigO hε (hf.isBigO_const (one_ne_zero : (1 : 𝕜) ≠ 0))
