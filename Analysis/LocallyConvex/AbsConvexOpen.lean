/-
Copyright (c) 2022 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
module

public import Mathlib.Analysis.LocallyConvex.AbsConvex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import Mathlib.Analysis.Convex.Gauge

/-!
# Absolutely convex open sets

A set `s` in a commutative monoid `E` equipped with a topology is said to be an absolutely convex
open set if it is absolutely convex and open. When `E` is a topological additive group, the topology
coincides with the topology induced by the family of seminorms arising as gauges of absolutely
convex open neighborhoods of zero.

## Main definitions

* `AbsConvexOpenSets`: sets which are absolutely convex and open
* `gaugeSeminormFamily`: the seminorm family induced by all open absolutely convex neighborhoods
  of zero.

## Main statements

* `with_gaugeSeminormFamily`: the topology of a locally convex space is induced by the family
  `gaugeSeminormFamily`.
* `LocallyConvexSpace.toPolynormableSpace`: a locally convex space is polynormable

-/

@[expose] public section

open NormedField Set

open NNReal Pointwise Topology

variable {𝕜 E : Type*}

section AbsolutelyConvexSets

variable [TopologicalSpace E] [AddCommMonoid E] [SeminormedRing 𝕜]
variable [SMul 𝕜 E]
variable (𝕜 E) [PartialOrder 𝕜]

/-- The type of absolutely convex open sets. -/
/-
**AbsConvexOpenSets** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AbsConvexOpenSets
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of absolutely convex open sets.
-/
def AbsConvexOpenSets :=
  { s : Set E // (0 : E) ∈ s ∧ IsOpen s ∧ AbsConvex 𝕜 s }
/-
**AbsConvexOpenSets.instCoeOut** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AbsConvexOpenSets.instCoeOut : CoeOut (AbsConvexOpenSets 𝕜 E) (Set E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance AbsConvexOpenSets.instCoeOut : CoeOut (AbsConvexOpenSets 𝕜 E) (Set E) :=
  ⟨Subtype.val⟩

namespace AbsConvexOpenSets

variable {𝕜 E}

/-
**AbsConvexOpenSets.coe_zero_mem** 是 Mathlib 中的一个定理，位于命名空间 `AbsConvexOpenSets`。
形式化陈述：coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) in (s : Set E)
参数：s : AbsConvexOpenSets 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_zero_mem (s : AbsConvexOpenSets 𝕜 E) : (0 : E) ∈ (s : Set E) :=
  s.2.1
/-
**AbsConvexOpenSets.coe_isOpen** 是 Mathlib 中的一个定理，位于命名空间 `AbsConvexOpenSets`。
形式化陈述：coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E)
参数：s : AbsConvexOpenSets 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : IsOpen (s : Set E) :=
  s.2.2.1
/-
**AbsConvexOpenSets.coe_nhds** 是 Mathlib 中的一个定理，位于命名空间 `AbsConvexOpenSets`。
形式化陈述：coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) in 𝓝 (0 : E)
参数：s : AbsConvexOpenSets 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `AbsConvexOpenSets.coe_isOpen`：coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : I
sOpen (s : Set E)
· 使用定理 `AbsConvexOpenSets.coe_zero_mem`：coe_zero_mem (s : AbsConvexOpenSets 𝕜 E)
 : (0 : E) in (s : Set E)
-/
theorem coe_nhds (s : AbsConvexOpenSets 𝕜 E) : (s : Set E) ∈ 𝓝 (0 : E) :=
  s.coe_isOpen.mem_nhds s.coe_zero_mem
/-
**AbsConvexOpenSets.coe_balanced** 是 Mathlib 中的一个定理，位于命名空间 `AbsConvexOpenSets`。
形式化陈述：coe_balanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E)
参数：s : AbsConvexOpenSets 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_balanced (s : AbsConvexOpenSets 𝕜 E) : Balanced 𝕜 (s : Set E) :=
  s.2.2.2.1
/-
**AbsConvexOpenSets.coe_convex** 是 Mathlib 中的一个定理，位于命名空间 `AbsConvexOpenSets`。
形式化陈述：coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex 𝕜 (s : Set E)
参数：s : AbsConvexOpenSets 𝕜 E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem coe_convex (s : AbsConvexOpenSets 𝕜 E) : Convex 𝕜 (s : Set E) :=
  s.2.2.2.2

end AbsConvexOpenSets

/-
**AbsConvexOpenSets.instNonempty** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：AbsConvexOpenSets.instNonempty : Nonempty (AbsConvexOpenSets 𝕜 E)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `exists_true_iff_nonempty`：exists_true_iff_nonempty {α : Sort*} : (exists
 _ : α, True) ↔ Nonempty α
· 使用定理 `Subtype.exists`：∀ {α : Sort u} {p : α → Prop} {q : { a // p a } → Prop},
 (∃ x, q x) ↔ ∃ a, ∃ (b : p a), q ⟨a, b⟩
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `balanced_univ`：balanced_univ : Balanced 𝕜 (univ : Set E)
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `trivial`：True
-/
instance AbsConvexOpenSets.instNonempty : Nonempty (AbsConvexOpenSets 𝕜 E) := by
  rw [← exists_true_iff_nonempty]
  dsimp only [AbsConvexOpenSets]
  rw [Subtype.exists]
  exact ⟨Set.univ, ⟨mem_univ 0, isOpen_univ, balanced_univ, convex_univ⟩, trivial⟩

end AbsolutelyConvexSets

variable [RCLike 𝕜]
variable [AddCommGroup E] [TopologicalSpace E]
variable [Module 𝕜 E] [Module ℝ E] [IsScalarTower ℝ 𝕜 E]
variable [ContinuousSMul ℝ E]
variable (𝕜 E)

open scoped ComplexOrder

/-- The family of seminorms defined by the gauges of absolute convex open sets. -/
/-
**gaugeSeminormFamily** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The family of seminorms defined by the gauges of absolute convex open sets.
-/
noncomputable def gaugeSeminormFamily : SeminormFamily 𝕜 E (AbsConvexOpenSets 𝕜 E) := fun s =>
  gaugeSeminorm s.coe_balanced (s.coe_convex.lift ℝ) (absorbent_nhds_zero s.coe_nhds)

variable {𝕜 E}
/-
**gaugeSeminormFamily_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：gaugeSeminormFamily_ball (s : AbsConvexOpenSets 𝕜 E) : (gaugeSeminormFamil
y 𝕜 E s).ball 0 1 = (s : Set E)
参数：s : AbsConvexOpenSets 𝕜 E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Seminorm.ball_zero_eq`：ball_zero_eq : ball p 0 r = { y : E | p y < r }
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `gaugeSeminorm_toFun`：∀ {𝕜 : Type u_1} {E : Type u_2} [inst : AddCommGrou
p E] [inst_1 : _root_.Module ℝ E] {s : Set E} [inst_2 : RCLike 𝕜]   [inst_3 : _r
oot_.Modu…
· 使用定理 `setOfPred_gauge_lt_one_eq_self_of_isOpen`：setOfPred_gauge_lt_one_eq_self
_of_isOpen (hs₁ : Convex Real s) (hs₀ : (0 : E) in s) (hs₂ : IsOpen s) : { x | g
auge s x < 1 } = s
· 使用定理 `Convex.lift`：Convex.lift [SMulPosMono R 𝕜] {s : Set E} (hs : Convex 𝕜 s)
 : Convex R s
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用引理 `RCLike.toIsOrderedAddMonoid`：toIsOrderedAddMonoid : IsOrderedAddMonoid K
 where add_le_add_left _ _
· 使用定理 `IsOrderedModule.toPosSMulMono`：∀ {α : Type u_1} {β : Type u_2} {inst : S
Mul α β} {inst_1 : Preorder α} {inst_2 : Preorder β} {inst_3 : Zero α}   {inst_4
 : Zero β} [self : …
· 使用定理 `instIsOrderedModule`：∀ {R : Type u_1} {A : Type u_2} [inst : Semiring R]
 [inst_1 : PartialOrder R] [inst_2 : StarRing R] [StarOrderedRing R]   [inst_4 :
 NonUnita…
· 使用引理 `RCLike.toStarOrderedRing`：toStarOrderedRing : StarOrderedRing K
· 使用定理 `RCLike.instStarModuleReal`：∀ {K : Type u_1} [inst : RCLike K], StarModul
e ℝ K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AbsConvexOpenSets.coe_convex`：coe_convex (s : AbsConvexOpenSets 𝕜 E) : C
onvex 𝕜 (s : Set E)
· 使用定理 `AbsConvexOpenSets.coe_zero_mem`：coe_zero_mem (s : AbsConvexOpenSets 𝕜 E)
 : (0 : E) in (s : Set E)
· 使用定理 `AbsConvexOpenSets.coe_isOpen`：coe_isOpen (s : AbsConvexOpenSets 𝕜 E) : I
sOpen (s : Set E)
-/
theorem gaugeSeminormFamily_ball (s : AbsConvexOpenSets 𝕜 E) :
    (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E) := by
  dsimp only [gaugeSeminormFamily]
  rw [Seminorm.ball_zero_eq]
  simp_rw [gaugeSeminorm_toFun]
  exact setOfPred_gauge_lt_one_eq_self_of_isOpen (s.coe_convex.lift ℝ) s.coe_zero_mem s.coe_isOpen

variable [IsTopologicalAddGroup E] [ContinuousSMul 𝕜 E]
variable [LocallyConvexSpace 𝕜 E]

set_option backward.isDefEq.respectTransparency false in
/-- The topology of a locally convex space is induced by the gauge seminorm family. -/
/-
**with_gaugeSeminormFamily** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：with_gaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormFamily.withSeminorms_of_hasBasis`：SeminormFamily.withSeminorms_o
f_hasBasis [IsTopologicalAddGroup E] (p : SeminormFamily 𝕜 E ι) (h : (𝓝 (0 : E))
.HasBasis (fun s : Set E => s …
· 使用定理 `Filter.HasBasis.to_hasBasis`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort 
u_5} {l : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : ι' →
 Set α},   l.HasB…
· 使用定理 `nhds_hasBasis_absConvex_open`：nhds_hasBasis_absConvex_open : (𝓝 (0 : E))
.HasBasis (fun s => (0 : E) in s ∧ IsOpen s ∧ AbsConvex 𝕜 s) id
· 使用引理 `RCLike.toZeroLEOneClass`：toZeroLEOneClass : ZeroLEOneClass K where zero_
le_one
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `gaugeSeminormFamily_ball`：gaugeSeminormFamily_ball (s : AbsConvexOpenSet
s 𝕜 E) : (gaugeSeminormFamily 𝕜 E s).ball 0 1 = (s : Set E)
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `SeminormFamily.basisSets_singleton_mem`：basisSets_singleton_mem (i : ι) 
{r : Real} (hr : 0 < r) : (p i).ball 0 r in p.basisSets
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `SeminormFamily.basisSets_iff`：basisSets_iff {U : Set E} : U in p.basisSe
ts ↔ exists (i : Finset ι) (r : Real), 0 < r ∧ U = ball (i.sup p) 0 r
· 使用定理 `Seminorm.ball_finset_sup_eq_iInter`：ball_finset_sup_eq_iInter (p : ι -> 
Seminorm 𝕜 E) (s : Finset ι) (x : E) {r : Real} (hr : 0 < r) : ball (s.sup p) x 
r = ⋂ i in s, ball (p i)…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddGroupSeminormClass.toZeroHomClass`：∀ {F : Type u_2} {α : Type u_3} {β
 : Type u_4} [inst : FunLike F α β] [inst_1 : AddGroup α] [inst_2 : AddCommMonoi
d β]   [inst_3 : PartialOr…
· 使用定理 `SeminormClass.toAddGroupSeminormClass`：∀ {F : Type u_12} {𝕜 : outParam (
Type u_13)} {E : outParam (Type u_14)} {inst : SeminormedRing 𝕜} {inst_1 : AddGr
oup E}   {inst_2 : SMul 𝕜 E…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `isOpen_biInter_finset`：isOpen_biInter_finset {s : Finset α} {f : α -> Se
t X} (h : forall i in s, IsOpen (f i)) : IsOpen (⋂ i in s, f i)
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `abs_of_pos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] {a
 : α} [AddLeftMono α], 0 < a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
The topology of a locally convex space is induced by the gauge seminorm family.
-/
theorem with_gaugeSeminormFamily : WithSeminorms (gaugeSeminormFamily 𝕜 E) := by
  refine SeminormFamily.withSeminorms_of_hasBasis _ ?_
  refine (nhds_hasBasis_absConvex_open 𝕜 E).to_hasBasis (fun s hs => ?_) fun s hs => ?_
  · refine ⟨s, ⟨?_, rfl.subset⟩⟩
    convert! (gaugeSeminormFamily _ _).basisSets_singleton_mem ⟨s, hs⟩ one_pos
    rw [gaugeSeminormFamily_ball, Subtype.coe_mk]
  refine ⟨s, ⟨?_, rfl.subset⟩⟩
  rw [SeminormFamily.basisSets_iff] at hs
  rcases hs with ⟨t, r, hr, rfl⟩
  rw [Seminorm.ball_finset_sup_eq_iInter _ _ _ hr]
  -- We have to show that the intersection contains zero, is open, balanced, and convex
  refine
    ⟨mem_iInter₂.mpr fun _ _ => by simp [hr],
      isOpen_biInter_finset fun S _ => ?_,
      balanced_iInter₂ fun _ _ => Seminorm.balanced_ball_zero _ _,
      convex_iInter₂ fun _ _ => (convex_of_nonneg_surjective_algebraMap _
        (fun _ => RCLike.nonneg_iff_exists_ofReal.mp) (Seminorm.convex_ball _ _ _) ..)⟩
  -- The only nontrivial part is to show that the ball is open
  have hr' : r = ‖(r : 𝕜)‖ * 1 := by simp [abs_of_pos hr]
  have hr'' : (r : 𝕜) ≠ 0 := by simp [hr.ne']
  rw [hr', ← Seminorm.smul_ball_zero hr'', gaugeSeminormFamily_ball]
  exact S.coe_isOpen.smul₀ hr''

/-- Any locally convex real or complex vector space is polynormable. -/
/-
**LocallyConvexSpace.toPolynormableSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LocallyConvexSpace.toPolynormableSpace : PolynormableSpace 𝕜 E
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `WithSeminorms.toPolynormableSpace`：WithSeminorms.toPolynormableSpace {p 
: SeminormFamily 𝕜 E ι} (hp : WithSeminorms p) : PolynormableSpace 𝕜 E where wit
hSeminorms'
· 使用定理 `with_gaugeSeminormFamily`：with_gaugeSeminormFamily : WithSeminorms (gaug
eSeminormFamily 𝕜 E)

--- 原说明 ---
Any locally convex real or complex vector space is polynormable.
-/
instance LocallyConvexSpace.toPolynormableSpace : PolynormableSpace 𝕜 E :=
  with_gaugeSeminormFamily.toPolynormableSpace
