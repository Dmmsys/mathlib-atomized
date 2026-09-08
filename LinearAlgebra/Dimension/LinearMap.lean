/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition

/-!
# The rank of a linear map

## Main Definition
-  `LinearMap.rank`: The rank of a linear map.
-/

public section


noncomputable section

universe u v v' v''

variable {K : Type u} {V V₁ : Type v} {V' V'₁ : Type v'} {V'' : Type v''}

open Cardinal Basis Submodule Function Set

namespace LinearMap

section Ring

variable [Semiring K] [AddCommMonoid V] [Module K V] [AddCommMonoid V₁] [Module K V₁]
variable [AddCommMonoid V'] [Module K V']

/-- `rank f` is the rank of a `LinearMap` `f`, defined as the dimension of `f.range`. -/
/-
**LinearMap.rank** 是 Mathlib 中的一个缩写定义，位于命名空间 `LinearMap`。
形式化陈述：rank (f : V ->ₗ[K] V') : Cardinal
参数：f : V ->ₗ[K] V'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`rank f` is the rank of a `LinearMap` `f`, defined as the dimension of `f.range`
.
-/
abbrev rank (f : V →ₗ[K] V') : Cardinal :=
  Module.rank K (LinearMap.range f)
/-
**LinearMap.rank_le_range** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_le_range (f : V ->ₗ[K] V') : rank f <= Module.rank K V'
参数：f : V ->ₗ[K] V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.rank_le`：Submodule.rank_le (s : Submodule R M) : Module.rank R
 s <= Module.rank R M
-/
theorem rank_le_range (f : V →ₗ[K] V') : rank f ≤ Module.rank K V' :=
  Submodule.rank_le _
/-
**LinearMap.rank_le_domain** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_le_domain (f : V ->ₗ[K] V₁) : rank f <= Module.rank K V
参数：f : V ->ₗ[K] V₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `rank_range_le`：rank_range_le (f : M ->ₗ[R] M₁) : Module.rank R (LinearMa
p.range f) <= Module.rank R M
-/
theorem rank_le_domain (f : V →ₗ[K] V₁) : rank f ≤ Module.rank K V :=
  rank_range_le _

@[simp]
/-
**LinearMap.rank_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_zero [Nontrivial K] : rank (0 : V ->ₗ[K] V') = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rank.eq_1`：∀ {K : Type u} {V : Type v} {V' : Type v'} [inst : 
Semiring K] [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module K V]   [inst_3 : 
AddCommMo…
· 使用定理 `LinearMap.range_zero`：range_zero [RingHomSurjective τ₁₂] : range (0 : M 
->ₛₗ[τ₁₂] M₂) = ⊥
· 使用定理 `rank_bot`：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
-/
theorem rank_zero [Nontrivial K] : rank (0 : V →ₗ[K] V') = 0 := by
  rw [rank, LinearMap.range_zero, rank_bot]

variable [AddCommMonoid V''] [Module K V'']
/-
**LinearMap.rank_comp_le_left** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_comp_le_left (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'') : rank (f.comp g) 
<= rank f
参数：g : V ->ₗ[K] V'；f : V' ->ₗ[K] V''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `LinearMap.map_le_range`：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} {p : Submodule R M} : map f p <= range f
-/
theorem rank_comp_le_left (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') : rank (f.comp g) ≤ rank f := by
  refine Submodule.rank_mono ?_
  rw [LinearMap.range_comp]
  exact LinearMap.map_le_range
/-
**LinearMap.lift_rank_comp_le_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lift_rank_comp_le_right (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'') : Cardinal.l
ift.{v'} (rank (f.comp g)) <= Cardinal.lift.{v''} (rank g)
参数：g : V ->ₗ[K] V'；f : V' ->ₗ[K] V''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rank.eq_1`：∀ {K : Type u} {V : Type v} {V' : Type v'} [inst : 
Semiring K] [inst_1 : AddCommMonoid V] [inst_2 : _root_.Module K V]   [inst_3 : 
AddCommMo…
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `lift_rank_map_le`：lift_rank_map_le (f : M ->ₗ[R] M') (p : Submodule R M)
 : Cardinal.lift.{v} (Module.rank R (p.map f)) <= Cardinal.lift.{v'} (Module.ran
k R p)
-/
theorem lift_rank_comp_le_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) ≤ Cardinal.lift.{v''} (rank g) := by
  rw [rank, rank, LinearMap.range_comp]; exact lift_rank_map_le _ _

/-- The rank of the composition of two maps is less than the minimum of their ranks. -/
/-
**LinearMap.lift_rank_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：lift_rank_comp_le (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'') : Cardinal.lift.{v
'} (rank (f.comp g)) <= min (Cardinal.lift.{v'} (rank f)) (Cardinal.lift.{v''} (
rank g))
参数：g : V ->ₗ[K] V'；f : V' ->ₗ[K] V''。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_min`：le_min (h₁ : c <= a) (h₂ : c <= b) : c <= min a b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `LinearMap.rank_comp_le_left`：rank_comp_le_left (g : V ->ₗ[K] V') (f : V'
 ->ₗ[K] V'') : rank (f.comp g) <= rank f
· 使用定理 `LinearMap.lift_rank_comp_le_right`：lift_rank_comp_le_right (g : V ->ₗ[K]
 V') (f : V' ->ₗ[K] V'') : Cardinal.lift.{v'} (rank (f.comp g)) <= Cardinal.lift
.{v''} (rank g)

--- 原说明 ---
The rank of the composition of two maps is less than the minimum of their ranks.
-/
theorem lift_rank_comp_le (g : V →ₗ[K] V') (f : V' →ₗ[K] V'') :
    Cardinal.lift.{v'} (rank (f.comp g)) ≤
      min (Cardinal.lift.{v'} (rank f)) (Cardinal.lift.{v''} (rank g)) :=
  le_min (Cardinal.lift_le.mpr <| rank_comp_le_left _ _) (lift_rank_comp_le_right _ _)

variable [AddCommGroup V'₁] [Module K V'₁]
/-
**LinearMap.rank_comp_le_right** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_comp_le_right (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁) : rank (f.comp g)
 <= rank g
参数：g : V ->ₗ[K] V'；f : V' ->ₗ[K] V'₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `LinearMap.lift_rank_comp_le_right`：lift_rank_comp_le_right (g : V ->ₗ[K]
 V') (f : V' ->ₗ[K] V'') : Cardinal.lift.{v'} (rank (f.comp g)) <= Cardinal.lift
.{v''} (rank g)
-/
theorem rank_comp_le_right (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) : rank (f.comp g) ≤ rank g := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le_right g f

/-- The rank of the composition of two maps is less than the minimum of their ranks.

See `lift_rank_comp_le` for the universe-polymorphic version. -/
/-
**LinearMap.rank_comp_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_comp_le (g : V ->ₗ[K] V') (f : V' ->ₗ[K] V'₁) : rank (f.comp g) <= mi
n (rank f) (rank g)
参数：g : V ->ₗ[K] V'；f : V' ->ₗ[K] V'₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `LinearMap.lift_rank_comp_le`：lift_rank_comp_le (g : V ->ₗ[K] V') (f : V'
 ->ₗ[K] V'') : Cardinal.lift.{v'} (rank (f.comp g)) <= min (Cardinal.lift.{v'} (
rank f)) (Cardina…

--- 原说明 ---
The rank of the composition of two maps is less than the minimum of their ranks.

See `lift_rank_comp_le` for the universe-polymorphic version.
-/
theorem rank_comp_le (g : V →ₗ[K] V') (f : V' →ₗ[K] V'₁) :
    rank (f.comp g) ≤ min (rank f) (rank g) := by
  simpa only [Cardinal.lift_id] using lift_rank_comp_le g f

end Ring

section DivisionRing

variable [DivisionRing K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
variable [AddCommGroup V'] [Module K V']

/-
**LinearMap.rank_add_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_add_le (f g : V ->ₗ[K] V') : rank (f + g) <= rank f + rank g
参数：f g : V ->ₗ[K] V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.range_le_iff_comap`：range_le_iff_comap [RingHomSurjective τ₁₂]
 {f : M ->ₛₗ[τ₁₂] M₂} {p : Submodule R₂ M₂} : range f <= p ↔ comap f p = ⊤
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Submodule.rank_add_le_rank_add_rank`：Submodule.rank_add_le_rank_add_rank
 (s t : Submodule R M) : Module.rank R (s ⊔ t : Submodule R M) <= Module.rank R 
s + Module.rank R t
-/
theorem rank_add_le (f g : V →ₗ[K] V') : rank (f + g) ≤ rank f + rank g :=
  calc
    rank (f + g) ≤ Module.rank K (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') := by
      refine Submodule.rank_mono ?_
      exact LinearMap.range_le_iff_comap.2 <| eq_top_iff'.2 fun x =>
        show f x + g x ∈ (LinearMap.range f ⊔ LinearMap.range g : Submodule K V') from
        mem_sup.2 ⟨_, ⟨x, rfl⟩, _, ⟨x, rfl⟩, rfl⟩
    _ ≤ rank f + rank g := Submodule.rank_add_le_rank_add_rank _ _
/-
**LinearMap.rank_finsetSum_le** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：rank_finsetSum_le {η} (s : Finset η) (f : η -> V ->ₗ[K] V') : rank (∑ d in
 s, f d) <= ∑ d in s, rank (f d)
参数：s : Finset η；f : η -> V ->ₗ[K] V'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.sum_hom_rel`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst
 : AddCommMonoid M] [inst_1 : AddCommMonoid N] {r : M → N → Prop}   {f : ι → M} 
{g : ι →…
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `LinearMap.rank_zero`：rank_zero [Nontrivial K] : rank (0 : V ->ₗ[K] V') =
 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LinearMap.rank_add_le`：rank_add_le (f g : V ->ₗ[K] V') : rank (f + g) <=
 rank f + rank g
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem rank_finsetSum_le {η} (s : Finset η) (f : η → V →ₗ[K] V') :
    rank (∑ d ∈ s, f d) ≤ ∑ d ∈ s, rank (f d) :=
  @Finset.sum_hom_rel _ _ _ _ _ (fun a b => rank a ≤ b) f (fun d => rank (f d)) s
    (le_of_eq rank_zero) fun _ _ _ h => le_trans (rank_add_le _ _) (by gcongr)

@[deprecated (since := "2026-04-08")] alias rank_finset_sum_le := rank_finsetSum_le
/-
**LinearMap.le_rank_iff_exists_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap`。
形式化陈述：le_rank_iff_exists_linearIndependent {c : Cardinal} {f : V ->ₗ[K] V'} : c 
<= rank f ↔ exists s : Set V, Cardinal.lift.{v'} #s = Cardinal.lift.{v} c ∧ Line
arIndepOn K f s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.exists_rightInverse_of_surjective`：∀ {R : Type u_1} [inst : Se
miring R] {P : Type u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]
   {M : Type u_3} [inst_3 : AddCo…
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_rank_iff_exists_linearIndependent`：le_rank_iff_exists_linearIndepende
nt [Module.Free K V] {c : Cardinal} : c <= Module.rank K V ↔ exists s : Set V, #
s = c ∧ LinearIndepOn K id…
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `DivisionSemiring.isPrincipalIdealRing`：∀ (K : Type u) [inst : DivisionSe
miring K], IsPrincipalIdealRing K
· 使用定理 `Cardinal.mk_image_eq_lift`：mk_image_eq_lift {α : Type u} {β : Type v} (f
 : α -> β) (s : Set α) (h : Injective f) : lift.{u} #(f '' s) = lift.{v} #s
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `LinearIndepOn.image_of_comp`：LinearIndepOn.image_of_comp (f : ι -> ι') (
g : ι' -> M) (hs : LinearIndepOn R (g ∘ f) s) : LinearIndepOn R g (f '' s)
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `Cardinal.lift_inj`：lift_inj {a b : Cardinal.{u}} : lift.{v, u} a = lift.
{v, u} b ↔ a = b
· 使用定理 `Cardinal.mk_image_eq_of_injOn_lift`：mk_image_eq_of_injOn_lift {α : Type 
u} {β : Type v} (f : α -> β) (s : Set α) (h : InjOn f s) : lift.{u} #(f '' s) = 
lift.{v} #s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.injOn_iff_injective`：injOn_iff_injective : InjOn f s ↔ Injective (s.
domRestrict f)
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
（共 31 条，此处仅展示前 30 条）
-/
theorem le_rank_iff_exists_linearIndependent {c : Cardinal} {f : V →ₗ[K] V'} :
    c ≤ rank f ↔ ∃ s : Set V,
    Cardinal.lift.{v'} #s = Cardinal.lift.{v} c ∧ LinearIndepOn K f s := by
  rcases f.rangeRestrict.exists_rightInverse_of_surjective f.range_rangeRestrict with ⟨g, hg⟩
  have fg : LeftInverse f.rangeRestrict g := LinearMap.congr_fun hg
  refine ⟨fun h => ?_, ?_⟩
  · rcases _root_.le_rank_iff_exists_linearIndependent.1 h with ⟨s, rfl, si⟩
    refine ⟨g '' s, Cardinal.mk_image_eq_lift _ _ fg.injective, ?_⟩
    replace fg : ∀ x, f (g x) = x := by
      intro x
      convert! congr_arg Subtype.val (fg x)
    replace si : LinearIndepOn K (fun x => f (g x)) s := by
      simpa only [fg] using! si.map' _ (ker_subtype _)
    exact si.image_of_comp
  · rintro ⟨s, hsc, si⟩
    have : LinearIndepOn K f.rangeRestrict s :=
      LinearIndependent.of_comp (LinearMap.range f).subtype (by convert! si)
    convert! this.id_image.cardinal_le_rank
    rw [← Cardinal.lift_inj, ← hsc, Cardinal.mk_image_eq_of_injOn_lift]
    exact injOn_iff_injective.2 this.injective
/-
**LinearMap.le_rank_iff_exists_linearIndependent_finset** 是 Mathlib 中的一个定理，位于命名空
间 `LinearMap`。
形式化陈述：le_rank_iff_exists_linearIndependent_finset {n : Nat} {f : V ->ₗ[K] V'} : 
↑n <= rank f ↔ exists s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s 
: Set V) => f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
-/
theorem le_rank_iff_exists_linearIndependent_finset {n : ℕ} {f : V →ₗ[K] V'} :
    ↑n ≤ rank f ↔ ∃ s : Finset V, s.card = n ∧ LinearIndependent K fun x : (s : Set V) => f x := by
  simp only [le_rank_iff_exists_linearIndependent, Cardinal.lift_natCast, Cardinal.lift_eq_nat_iff,
    Cardinal.mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

end DivisionRing

end LinearMap

