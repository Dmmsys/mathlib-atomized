/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Finite
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.Logic.Equiv.Fin.Rotate

/-!

# The rank nullity theorem

In this file we provide the rank nullity theorem as a typeclass, and prove various corollaries
of the theorem. The main definition is `HasRankNullity.{u} R`, which states that
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality `Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every `N : Submodule R M`.

The following instances are provided in mathlib:
1. `DivisionRing.hasRankNullity` for division rings in
   `Mathlib/LinearAlgebra/Dimension/DivisionRing.lean`.
2. `IsDomain.hasRankNullity` for commutative domains in
   `Mathlib/LinearAlgebra/Dimension/Localization.lean`.

TODO: prove the rank-nullity theorem for `[Ring R] [IsDomain R] [StrongRankCondition R]`.
See `nonempty_oreSet_of_strongRankCondition` for a start.
-/

public section
universe u v

open Function Set Cardinal Module Submodule LinearMap

variable {R} {M M₁ M₂ M₃ : Type u} {M' : Type v} [Ring R]
variable [AddCommGroup M] [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M']
variable [Module R M] [Module R M₁] [Module R M₂] [Module R M₃] [Module R M']

/--
`HasRankNullity.{u}` is a class of rings satisfying
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality `Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every `N : Submodule R M`.

Usually such a ring satisfies `HasRankNullity.{w}` for all universes `w`, and the universe
argument is there because of technical limitations to universe polymorphism.

See `DivisionRing.hasRankNullity` and `IsDomain.hasRankNullity`.
-/
@[pp_with_univ]
/-
**HasRankNullity** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type v) → [inst : Ring R] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasRankNullity.{u}` is a class of rings satisfying
1. Every `R`-module `M : Type u` has a linear independent subset of cardinality 
`Module.rank R M`.
2. `rank (M ⧸ N) + rank N = rank M` for every `R`-module `M : Type u` and every 
`N : Submodule R M`.

Usually such a ring satisfies `HasRankNullity.{w}` for all universes `w`, and th
e universe
argument is there because of technical limitations to universe polymorphism.

See `DivisionRing.hasRankNullity` and `IsDomain.hasRankNullity`.
-/
class HasRankNullity (R : Type v) [inst : Ring R] : Prop where
  exists_set_linearIndependent : ∀ (M : Type u) [AddCommGroup M] [Module R M],
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndepOn R id s
  rank_quotient_add_rank : ∀ {M : Type u} [AddCommGroup M] [Module R M] (N : Submodule R M),
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M

variable [HasRankNullity.{u} R]
/-
**Submodule.rank_quotient_add_rank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.rank_quotient_add_rank (N : Submodule R M) : Module.rank R (M ⧸ 
N) + Module.rank R N = Module.rank R M
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasRankNullity.rank_quotient_add_rank`：∀ {R : Type v} {inst : Ring R} [s
elf : HasRankNullity.{u, v} R] {M : Type u} [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] (N : S…
-/
lemma Submodule.rank_quotient_add_rank (N : Submodule R M) :
    Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M :=
  HasRankNullity.rank_quotient_add_rank N

variable (R M) in
/-
**exists_set_linearIndependent** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_set_linearIndependent : exists s : Set M, #s = Module.rank R M ∧ Li
nearIndependent (ι
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasRankNullity.exists_set_linearIndependent`：∀ {R : Type v} {inst : Ring
 R} [self : HasRankNullity.{u, v} R] (M : Type u) [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M], ∃ s, …
-/
lemma exists_set_linearIndependent :
    ∃ s : Set M, #s = Module.rank R M ∧ LinearIndependent (ι := s) R Subtype.val :=
  HasRankNullity.exists_set_linearIndependent M

variable (R) in
/-
**nontrivial_of_hasRankNullity** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nontrivial_of_hasRankNullity : Nontrivial R
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
-/
theorem nontrivial_of_hasRankNullity : Nontrivial R := by
  refine (subsingleton_or_nontrivial R).resolve_left fun H ↦ ?_
  have := rank_quotient_add_rank (R := R) (M := PUnit) ⊥
  simp [one_add_one_eq_two] at this

attribute [local instance] nontrivial_of_hasRankNullity
/-
**LinearMap.lift_rank_range_add_rank_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lift_rank_range_add_rank_ker (f : M ->ₗ[R] M') : lift.{u} (Modul
e.rank R (LinearMap.range f)) + lift.{v} (Module.rank R (LinearMap.ker f)) = lif
t.{v} (Module.rank R M)
参数：f : M ->ₗ[R] M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.lift_rank_eq`：LinearEquiv.lift_rank_eq (f : M ≃ₗ[R] M') : Ca
rdinal.lift.{v'} (Module.rank R M) = Cardinal.lift.{v} (Module.rank R M')
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M
-/
theorem LinearMap.lift_rank_range_add_rank_ker (f : M →ₗ[R] M') :
    lift.{u} (Module.rank R (LinearMap.range f)) + lift.{v} (Module.rank R (LinearMap.ker f)) =
      lift.{v} (Module.rank R M) := by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.lift_rank_eq, ← lift_add, rank_quotient_add_rank]

/-- The **rank-nullity theorem** -/
/-
**LinearMap.rank_range_add_rank_ker** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.rank_range_add_rank_ker (f : M ->ₗ[R] M₁) : Module.rank R (Linea
rMap.range f) + Module.rank R (LinearMap.ker f) = Module.rank R M
参数：f : M ->ₗ[R] M₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M

--- 原说明 ---
The **rank-nullity theorem**
-/
theorem LinearMap.rank_range_add_rank_ker (f : M →ₗ[R] M₁) :
    Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ker f) = Module.rank R M := by
  have := fun p : Submodule R M => Classical.decEq (M ⧸ p)
  rw [← f.quotKerEquivRange.rank_eq, rank_quotient_add_rank]
/-
**LinearMap.lift_rank_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lift_rank_eq_of_surjective {f : M ->ₗ[R] M'} (h : Surjective f) 
: lift.{v} (Module.rank R M) = lift.{u} (Module.rank R M') + lift.{v} (Module.ra
nk R (LinearMap.ker f))
参数：h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lift_rank_range_add_rank_ker`：LinearMap.lift_rank_range_add_ra
nk_ker (f : M ->ₗ[R] M') : lift.{u} (Module.rank R (LinearMap.range f)) + lift.{
v} (Module.rank R (LinearMap…
· 使用定理 `rank_range_of_surjective`：rank_range_of_surjective (f : M ->ₗ[R] M') (h 
: Surjective f) : Module.rank R (LinearMap.range f) = Module.rank R M'
-/
theorem LinearMap.lift_rank_eq_of_surjective {f : M →ₗ[R] M'} (h : Surjective f) :
    lift.{v} (Module.rank R M) =
      lift.{u} (Module.rank R M') + lift.{v} (Module.rank R (LinearMap.ker f)) := by
  rw [← lift_rank_range_add_rank_ker f, ← rank_range_of_surjective f h]
/-
**LinearMap.rank_eq_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.rank_eq_of_surjective {f : M ->ₗ[R] M₁} (h : Surjective f) : Mod
ule.rank R M = Module.rank R M₁ + Module.rank R (LinearMap.ker f)
参数：h : Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rank_range_add_rank_ker`：LinearMap.rank_range_add_rank_ker (f 
: M ->ₗ[R] M₁) : Module.rank R (LinearMap.range f) + Module.rank R (LinearMap.ke
r f) = Module.rank R M
· 使用定理 `rank_range_of_surjective`：rank_range_of_surjective (f : M ->ₗ[R] M') (h 
: Surjective f) : Module.rank R (LinearMap.range f) = Module.rank R M'
-/
theorem LinearMap.rank_eq_of_surjective {f : M →ₗ[R] M₁} (h : Surjective f) :
    Module.rank R M = Module.rank R M₁ + Module.rank R (LinearMap.ker f) := by
  rw [← rank_range_add_rank_ker f, ← rank_range_of_surjective f h]
/-
**LinearMap.lift_rank_comap_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lift_rank_comap_le {f : M ->ₗ[R] M'} (p : Submodule R M') : lift
.{v} (Module.rank R (comap f p)) <= lift.{u} (Module.rank R p) + lift.{v} (Modul
e.rank R f.ker)
参数：p : Submodule R M'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_map_eq`：rank_map_eq {f : M ->ₗ[R] M₁} (hf : Injective f) (p : Submo
dule R M) : Module.rank R (p.map f) = Module.rank R p
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用引理 `Submodule.rank_mono`：Submodule.rank_mono {s t : Submodule R M} (h : s <=
 t) : Module.rank R s <= Module.rank R t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `Submodule.rank_le`：Submodule.rank_le (s : Submodule R M) : Module.rank R
 s <= Module.rank R M
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `LinearMap.lift_rank_range_add_rank_ker`：LinearMap.lift_rank_range_add_ra
nk_ker (f : M ->ₗ[R] M') : lift.{u} (Module.rank R (LinearMap.range f)) + lift.{
v} (Module.rank R (LinearMap…
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem LinearMap.lift_rank_comap_le {f : M →ₗ[R] M'} (p : Submodule R M') :
    lift.{v} (Module.rank R (comap f p)) ≤
      lift.{u} (Module.rank R p) + lift.{v} (Module.rank R f.ker) := by
  let f' : comap f p →ₗ[R] p := f.restrict (by aesop)
  have hk : Module.rank R f'.ker ≤ Module.rank R f.ker := by
    rw [← rank_map_eq (injective_subtype (comap f p))]
    exact rank_mono fun x hx ↦ by aesop (add simp Subtype.ext_iff)
  have hr : Module.rank R f'.range ≤ Module.rank R p := by grw [Submodule.rank_le f'.range]
  rw [← f'.lift_rank_range_add_rank_ker]
  gcongr <;> rwa [lift_le]

omit [HasRankNullity.{u} R] in
/-
**LinearMap.rank_quot_submodule_map_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.rank_quot_submodule_map_eq [HasRankNullity.{v} R] {f : M ->ₗ[R] 
M'} (p : Submodule R M) : Module.rank R (M' ⧸ map f p) = Module.rank R (M' ⧸ f.r
ange) + Module.rank R (f.range ⧸ map f.rangeRestrict p)
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.map_le_range`：map_le_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} {p : Submodule R M} : map f p <= range f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Submodule.ker_mapQ`：ker_mapQ (f : M ->ₛₗ[τ₁₂] M₂) (h) : ker (p.mapQ q f 
h) = (comap f q).map p.mkQ
· 使用定理 `LinearMap.submoduleMap_surjective`：submoduleMap_surjective [RingHomSurje
ctive σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : Function.Surjective (f.sub
moduleMap p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.ker_comp`：ker_comp (l : M ->ₛₗ[σ₁₂] M₂) : LinearMap.ker (((e
'' : M₂ ->ₛₗ[σ₂₃] M₃).comp l : M ->ₛₗ[σ₁₃] M₃) : M ->ₛₗ[σ₁₃] M₃) = LinearMap.ker
 l
· 使用定理 `LinearMap.ker_restrict`：ker_restrict {p : Submodule R M} {q : Submodule 
R₂ M₂} {f : M ->ₛₗ[τ₁₂] M₂} (hf : forall x : M, x in p -> f x in q) : ker (f.res
trict hf) = …
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `LinearMap.map_codRestrict`：map_codRestrict [RingHomSurjective σ₂₁] (p : 
Submodule R M) (f : M₂ ->ₛₗ[σ₂₁] M) (h p') : map (codRestrict p f h) p' = comap 
p.subtype (p'.m…
· 使用定理 `LinearMap.mem_range_self`：mem_range_self [RingHomSurjective τ₁₂] (f : M 
->ₛₗ[τ₁₂] M₂) (x : M) : f x in range f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.rank_eq_of_surjective`：LinearMap.rank_eq_of_surjective {f : M 
->ₗ[R] M₁} (h : Surjective f) : Module.rank R M = Module.rank R M₁ + Module.rank
 R (LinearMap.ker f)
· 使用引理 `Submodule.factor_surjective`：factor_surjective (H : p <= p') : Function.
Surjective (factor H)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
-/
lemma LinearMap.rank_quot_submodule_map_eq [HasRankNullity.{v} R]
    {f : M →ₗ[R] M'} (p : Submodule R M) :
    Module.rank R (M' ⧸ map f p) =
      Module.rank R (M' ⧸ f.range) + Module.rank R (f.range ⧸ map f.rangeRestrict p) := by
  let f' : M' ⧸ map f p →ₗ[R] M' ⧸ f.range := factor map_le_range
  let +nondep e : (f.range ⧸ map f.rangeRestrict p) ≃ₗ[R] f'.ker := by
    let g : f.range →ₗ[R] f'.ker :=
      (LinearEquiv.ofEq (map (map f p).mkQ f.range) f'.ker) (by rw [ker_mapQ]; rfl) ∘ₗ
        (map f p).mkQ.submoduleMap f.range
    have g_surj : Surjective g := by simpa [g] using submoduleMap_surjective (map f p).mkQ f.range
    have g_ker : g.ker = map f.rangeRestrict p := by
      simp [g, submoduleMap, ker_restrict, map_codRestrict]
    let e := g.quotKerEquivOfSurjective g_surj
    rwa [g_ker] at e
  have := f'.rank_eq_of_surjective <| factor_surjective map_le_range
  rwa [← e.rank_eq] at this

omit [HasRankNullity.{u} R] in
/-
**LinearMap.lift_rank_quot_map_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearMap.lift_rank_quot_map_le [HasRankNullity.{v} R] {f : M ->ₗ[R] M'} (
p : Submodule R M) : lift.{u} (Module.rank R (M' ⧸ map f p)) <= lift.{u} (Module
.rank R (M' ⧸ f.range)) + lift.{v} (Module.rank R (M ⧸ p))
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearMap.rank_quot_submodule_map_eq`：LinearMap.rank_quot_submodule_map_
eq [HasRankNullity.{v} R] {f : M ->ₗ[R] M'} (p : Submodule R M) : Module.rank R 
(M' ⧸ map f p) = Module.ra…
· 使用定理 `Cardinal.lift_add`：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = li
ft.{v} a + lift.{v} b
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `LinearMap.lift_rank_le_of_surjective`：LinearMap.lift_rank_le_of_surjecti
ve (f : M ->ₗ[R] M') (h : Surjective f) : lift.{v} (Module.rank R M') <= lift.{v
'} (Module.rank R M)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.range_mapQ`：range_mapQ [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂
] M₂) (h : p <= comap f q) : (p.mapQ q f h).range = f.range.map q.mkQ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearMap.range_rangeRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Typ
e u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : Ad
dCommMonoid M] [ins…
· 使用定理 `Submodule.map_top`：map_top [RingHomSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) 
: map f ⊤ = range f
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LinearMap.lift_rank_quot_map_le [HasRankNullity.{v} R]
    {f : M →ₗ[R] M'} (p : Submodule R M) :
    lift.{u} (Module.rank R (M' ⧸ map f p)) ≤
      lift.{u} (Module.rank R (M' ⧸ f.range)) + lift.{v} (Module.rank R (M ⧸ p)) := by
  rw [rank_quot_submodule_map_eq, lift_add]; gcongr
  let f' : M ⧸ p →ₗ[R] f.range ⧸ map f.rangeRestrict p :=
    mapQ p (map f.rangeRestrict p) f.rangeRestrict <| by rw [comap_map_eq]; exact le_sup_left
  exact lift_rank_le_of_surjective f' <| by rw [← range_eq_top, range_mapQ]; simp
/-
**exists_linearIndepOn_of_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndepOn_of_lt_rank [StrongRankCondition R] {s : Set M} (hs : 
LinearIndepOn R id s) : exists t, s subseteq t ∧ #t = Module.rank R M ∧ LinearIn
depOn R id t
参数：hs : LinearIndepOn R id s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_set_linearIndependent`：exists_set_linearIndependent : exists s : 
Set M, #s = Module.rank R M ∧ LinearIndependent (ι
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `nontrivial_of_hasRankNullity`：nontrivial_of_hasRankNullity : Nontrivial 
R
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Cardinal.mk_union_of_disjoint`：mk_union_of_disjoint {α : Type u} {S T : 
Set α} (H : Disjoint S T) : #(S union T : Set α) = #S + #T
· 使用定理 `Cardinal.mk_image_eq`：mk_image_eq {α β : Type u} {f : α -> β} {s : Set α
} (hf : Injective f) : #(f '' s) = #s
· 使用定理 `Function.HasLeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : 
α → β}, Function.HasLeftInverse f → Function.Injective f
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `rank_span_set`：rank_span_set {s : Set M} (hs : LinearIndepOn R id s) : M
odule.rank R ↑(span R s) = #s
· 使用定理 `LinearIndepOn.union_id_of_quotient`：LinearIndepOn.union_id_of_quotient {
M' : Submodule R M} {s : Set M} (hs : s subseteq M') (hs' : LinearIndepOn R id s
) {t : Set M} (ht : Line…
· 使用定理 `linearIndepOn_iff_image`：linearIndepOn_iff_image {ι} {s : Set ι} {f : ι 
-> M} (hf : Set.InjOn f s) : LinearIndepOn R f s ↔ LinearIndepOn R id (f '' s)
· 使用定理 `Set.InjOn.image_of_comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} 
{s : Set α} {f : α → β} {g : β → γ},   Set.InjOn (g ∘ f) s → Set.InjOn g (f '' s
)
· 使用定理 `Function.Injective.injOn`：∀ {α : Type u_1} {β : Type u_2} {f : α → β}, F
unction.Injective f → ∀ {s : Set α}, Set.InjOn f s
· 使用定理 `Function.injective_id`：∀ {α : Sort u_1}, Function.Injective id
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `Set.image_id`：image_id (s : Set α) : id '' s = s
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem exists_linearIndepOn_of_lt_rank [StrongRankCondition R]
    {s : Set M} (hs : LinearIndepOn R id s) :
    ∃ t, s ⊆ t ∧ #t = Module.rank R M ∧ LinearIndepOn R id t := by
  obtain ⟨t, ht, ht'⟩ := exists_set_linearIndependent R (M ⧸ Submodule.span R s)
  choose sec hsec using Submodule.mkQ_surjective (Submodule.span R s)
  have hsec' : (Submodule.mkQ _) ∘ sec = _root_.id := funext hsec
  have hst : Disjoint s (sec '' t) := by
    rw [Set.disjoint_iff]
    rintro _ ⟨hxs, ⟨x, hxt, rfl⟩⟩
    apply ht'.ne_zero ⟨x, hxt⟩
    rw [Subtype.coe_mk, ← hsec x, mkQ_apply, Quotient.mk_eq_zero]
    exact Submodule.subset_span hxs
  refine ⟨s ∪ sec '' t, subset_union_left, ?_, ?_⟩
  · rw [Cardinal.mk_union_of_disjoint hst, Cardinal.mk_image_eq, ht,
      ← rank_quotient_add_rank (Submodule.span R s), add_comm, rank_span_set hs]
    exact HasLeftInverse.injective ⟨Submodule.Quotient.mk, hsec⟩
  · apply LinearIndepOn.union_id_of_quotient Submodule.subset_span hs
    rwa [linearIndepOn_iff_image (hsec'.symm ▸ injective_id).injOn.image_of_comp,
      ← image_comp, hsec', image_id]

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
/-
**exists_linearIndependent_cons_of_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_cons_of_lt_rank [StrongRankCondition R] {n : Nat}
 {v : Fin n -> M} (hv : LinearIndependent R v) (h : n < Module.rank R M) : exist
s (x : M), LinearIndependent R (Fin.cons x v)
参数：hv : LinearIndependent R v；h : n < Module.rank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndepOn_of_lt_rank`：exists_linearIndepOn_of_lt_rank [Strong
RankCondition R] {s : Set M} (hs : LinearIndepOn R id s) : exists t, s subseteq 
t ∧ #t = Module.rank …
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
· 使用定理 `Cardinal.mk_range_eq_of_injective`：mk_range_eq_of_injective {α : Type u}
 {β : Type v} {f : α -> β} (hf : Injective f) : lift.{u} #(range f) = lift.{v} #
α
· 使用定理 `LinearIndependent.injective`：LinearIndependent.injective [Nontrivial R] 
(hv : LinearIndependent R v) : Injective v
· 使用定理 `nontrivial_of_hasRankNullity`：nontrivial_of_hasRankNullity : Nontrivial 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Cardinal.lift_injective`：lift_injective : Injective lift.{u, v}
· 使用定理 `Set.nonempty_of_ssubset`：nonempty_of_ssubset (ht : s ⊂ t) : (t \ s).None
mpty
· 使用定理 `LE.le.ssubset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst 
: PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndepOn_id_range_iff`：linearIndepOn_id_range_iff {ι} {f : ι -> M} 
(hf : Injective f) : LinearIndepOn R id (range f) ↔ LinearIndependent R f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Fin.cons_injective_iff`：cons_injective_iff {α} {x₀ : α} {x : Fin n -> α}
 : Function.Injective (cons x₀ x : Fin n.succ -> α) ↔ x₀ ∉ Set.range x ∧ Functio
n.Injective …
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `Fin.range_cons`：range_cons {α} {n : Nat} (x : α) (b : Fin n -> α) : Set.
range (Fin.cons x b : Fin n.succ -> α) = insert x (Set.range b)

--- 原说明 ---
Given a family of `n` linearly independent vectors in a space of dimension `> n`
, one may extend
the family by another vector while retaining linear independence.
-/
theorem exists_linearIndependent_cons_of_lt_rank [StrongRankCondition R] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < Module.rank R M) :
    ∃ (x : M), LinearIndependent R (Fin.cons x v) := by
  obtain ⟨t, h₁, h₂, h₃⟩ := exists_linearIndepOn_of_lt_rank hv.linearIndepOn_id
  have : range v ≠ t := by
    refine fun e ↦ h.ne ?_
    rw [← e, ← lift_injective.eq_iff, mk_range_eq_of_injective hv.injective] at h₂
    simpa only [mk_fintype, Fintype.card_fin, lift_natCast, lift_id'] using h₂
  obtain ⟨x, hx, hx'⟩ := nonempty_of_ssubset (h₁.ssubset_of_ne this)
  exact ⟨x, (linearIndepOn_id_range_iff (Fin.cons_injective_iff.mpr ⟨hx', hv.injective⟩)).mp
    (h₃.mono (Fin.range_cons x v ▸ insert_subset hx h₁))⟩

/-- Given a family of `n` linearly independent vectors in a space of dimension `> n`, one may extend
the family by another vector while retaining linear independence. -/
/-
**exists_linearIndependent_snoc_of_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_snoc_of_lt_rank [StrongRankCondition R] {n : Nat}
 {v : Fin n -> M} (hv : LinearIndependent R v) (h : n < Module.rank R M) : exist
s (x : M), LinearIndependent R (Fin.snoc v x)
参数：hv : LinearIndependent R v；h : n < Module.rank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Fin.snoc_eq_cons_rotate`：Fin.snoc_eq_cons_rotate {α : Type*} (v : Fin n 
-> α) (a : α) : @Fin.snoc _ (fun _ => α) v a = fun i => @Fin.cons _ (fun _ => α)
 a v (finRota…
· 使用定理 `exists_linearIndependent_cons_of_lt_rank`：exists_linearIndependent_cons_
of_lt_rank [StrongRankCondition R] {n : Nat} {v : Fin n -> M} (hv : LinearIndepe
ndent R v) (h : n < Module.ran…
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Given a family of `n` linearly independent vectors in a space of dimension `> n`
, one may extend
the family by another vector while retaining linear independence.
-/
theorem exists_linearIndependent_snoc_of_lt_rank [StrongRankCondition R] {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < Module.rank R M) :
    ∃ (x : M), LinearIndependent R (Fin.snoc v x) := by
  simp only [Fin.snoc_eq_cons_rotate]
  have ⟨x, hx⟩ := exists_linearIndependent_cons_of_lt_rank hv h
  exact ⟨x, hx.comp _ (finRotate _).injective⟩

/-- Given a nonzero vector in a space of dimension `> 1`, one may find another vector linearly
independent of the first one. -/
/-
**exists_linearIndependent_pair_of_one_lt_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_pair_of_one_lt_rank [IsDomain R] [StrongRankCondi
tion R] [IsTorsionFree R M] (h : 1 < Module.rank R M) {x : M} (hx : x != 0) : ex
ists y, LinearIndependent R ![x, y]
参数：h : 1 < Module.rank R M；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent_snoc_of_lt_rank`：exists_linearIndependent_snoc_
of_lt_rank [StrongRankCondition R] {n : Nat} {v : Fin n -> M} (hv : LinearIndepe
ndent R v) (h : n < Module.ran…
· 使用引理 `LinearIndependent.of_subsingleton`：LinearIndependent.of_subsingleton [Su
bsingleton ι] (i : ι) (hi : v i != 0) : LinearIndependent R v
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.Fin.snoc_vecCons`：∀ {n : ℕ} {α : Type u_1} (x y : α) (p : Fin n →
 α), Fin.snoc (Matrix.vecCons y p) x = Matrix.vecCons y (Fin.snoc p x)
· 使用定理 `Matrix.Fin.snoc_vecEmpty`：∀ {α : Type u_1} (x : α), Fin.snoc ![] x = ![x
]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given a nonzero vector in a space of dimension `> 1`, one may find another vecto
r linearly
independent of the first one.
-/
theorem exists_linearIndependent_pair_of_one_lt_rank [IsDomain R] [StrongRankCondition R]
    [IsTorsionFree R M] (h : 1 < Module.rank R M) {x : M} (hx : x ≠ 0) :
    ∃ y, LinearIndependent R ![x, y] := by
  obtain ⟨y, hy⟩ := exists_linearIndependent_snoc_of_lt_rank (.of_subsingleton (v := ![x]) 0 hx) h
  have : Fin.snoc ![x] y = ![x, y] := by simp
  rw [this] at hy
  exact ⟨y, hy⟩

set_option backward.isDefEq.respectTransparency false in
/-
**Submodule.exists_smul_notMem_of_rank_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.exists_smul_notMem_of_rank_lt {N : Submodule R M} (h : Module.ra
nk R N < Module.rank R M) : exists m : M, forall r : R, r != 0 -> r • m ∉ N
参数：h : Module.rank R N < Module.rank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Function.Surjective.forall`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β},
   Function.Surjective f → ∀ {p : β → Prop}, (∀ (y : β), p y) ↔ ∀ (x : α), p (f 
x)
· 使用定理 `Submodule.Quotient.mk_surjective`：mk_surjective : Function.Surjective (@
mk _ _ _ _ _ p)
· 使用引理 `rank_eq_zero_iff`：rank_eq_zero_iff {R M} [Ring R] [AddCommGroup M] [Modu
le R M] : Module.rank R M = 0 ↔ forall x : M, exists a : R, a != 0 ∧ a • x = 0
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
-/
theorem Submodule.exists_smul_notMem_of_rank_lt {N : Submodule R M}
    (h : Module.rank R N < Module.rank R M) : ∃ m : M, ∀ r : R, r ≠ 0 → r • m ∉ N := by
  have : Module.rank R (M ⧸ N) ≠ 0 := by
    intro e
    rw [← rank_quotient_add_rank N, e, zero_add] at h
    exact h.ne rfl
  rw [ne_eq, rank_eq_zero_iff, (Submodule.Quotient.mk_surjective N).forall] at this
  push Not at this
  simp_rw [← N.mkQ_apply, ← map_smul, N.mkQ_apply, ne_eq, Submodule.Quotient.mk_eq_zero] at this
  exact this

open Cardinal Basis Submodule Function Set LinearMap
/-
**Submodule.rank_sup_add_rank_inf_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_sup_add_rank_inf_eq (s t : Submodule R M) : Module.rank R (
s ⊔ t : Submodule R M) + Module.rank R (s ⊓ t : Submodule R M) = Module.rank R s
 + Module.rank R t
参数：s t : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.rank_quotient_add_rank`：Submodule.rank_quotient_add_rank (N : 
Submodule R M) : Module.rank R (M ⧸ N) + Module.rank R N = Module.rank R M
· 使用定理 `Submodule.comap_inf`：comap_inf (f : M ->ₛₗ[σ₁₂] M₂) : comap f (q ⊓ q') =
 comap f q ⊓ comap f q'
· 使用定理 `LinearEquiv.rank_eq`：LinearEquiv.rank_eq (f : M ≃ₗ[R] M₁) : Module.rank 
R M = Module.rank R M₁
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
· 使用定理 `inf_assoc`：∀ {α : Type u} [inst : SemilatticeInf α] (a b c : α), a ⊓ b ⊓
 c = a ⊓ (b ⊓ c)
· 使用定理 `inf_idem`：∀ {α : Type u} [inst : SemilatticeInf α] (a : α), a ⊓ a = a
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
-/
theorem Submodule.rank_sup_add_rank_inf_eq (s t : Submodule R M) :
    Module.rank R (s ⊔ t : Submodule R M) + Module.rank R (s ⊓ t : Submodule R M) =
    Module.rank R s + Module.rank R t := by
  conv_rhs => enter [2]; rw [show t = (s ⊔ t) ⊓ t by simp]
  rw [← rank_quotient_add_rank ((s ⊓ t).comap s.subtype),
    ← rank_quotient_add_rank (t.comap (s ⊔ t).subtype),
    comap_inf, (quotientInfEquivSupQuotient s t).rank_eq, ← comap_inf,
    (equivSubtypeMap s (comap _ (s ⊓ t))).rank_eq, Submodule.map_comap_subtype,
    (equivSubtypeMap (s ⊔ t) (comap _ t)).rank_eq, Submodule.map_comap_subtype,
    ← inf_assoc, inf_idem, add_right_comm]
/-
**Submodule.rank_add_le_rank_add_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_add_le_rank_add_rank (s t : Submodule R M) : Module.rank R 
(s ⊔ t : Submodule R M) <= Module.rank R s + Module.rank R t
参数：s t : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.rank_sup_add_rank_inf_eq`：Submodule.rank_sup_add_rank_inf_eq (
s t : Submodule R M) : Module.rank R (s ⊔ t : Submodule R M) + Module.rank R (s 
⊓ t : Submodule R M) = M…
· 使用定理 `self_le_add_right`：∀ {α : Type u} [inst : Add α] [inst_1 : LE α] [Canoni
callyOrderedAdd α] (a b : α), a ≤ a + b
-/
theorem Submodule.rank_add_le_rank_add_rank (s t : Submodule R M) :
    Module.rank R (s ⊔ t : Submodule R M) ≤ Module.rank R s + Module.rank R t := by
  rw [← Submodule.rank_sup_add_rank_inf_eq]
  exact self_le_add_right _ _

section Finrank

open Submodule Module

variable [StrongRankCondition R]

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
/-
**exists_linearIndependent_snoc_of_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_snoc_of_lt_finrank {n : Nat} {v : Fin n -> M} (hv
 : LinearIndependent R v) (h : n < finrank R M) : exists (x : M), LinearIndepend
ent R (Fin.snoc v x)
参数：hv : LinearIndependent R v；h : n < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent_snoc_of_lt_rank`：exists_linearIndependent_snoc_
of_lt_rank [StrongRankCondition R] {n : Nat} {v : Fin n -> M} (hv : LinearIndepe
ndent R v) (h : n < Module.ran…
· 使用定理 `Module.lt_rank_of_lt_finrank`：lt_rank_of_lt_finrank {n : Nat} (h : n < f
inrank R M) : ↑n < Module.rank R M

--- 原说明 ---
Given a family of `n` linearly independent vectors in a finite-dimensional space
 of
dimension `> n`, one may extend the family by another vector while retaining lin
ear independence.
-/
theorem exists_linearIndependent_snoc_of_lt_finrank {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < finrank R M) :
    ∃ (x : M), LinearIndependent R (Fin.snoc v x) :=
  exists_linearIndependent_snoc_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a family of `n` linearly independent vectors in a finite-dimensional space of
dimension `> n`, one may extend the family by another vector while retaining linear independence. -/
/-
**exists_linearIndependent_cons_of_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_cons_of_lt_finrank {n : Nat} {v : Fin n -> M} (hv
 : LinearIndependent R v) (h : n < finrank R M) : exists (x : M), LinearIndepend
ent R (Fin.cons x v)
参数：hv : LinearIndependent R v；h : n < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent_cons_of_lt_rank`：exists_linearIndependent_cons_
of_lt_rank [StrongRankCondition R] {n : Nat} {v : Fin n -> M} (hv : LinearIndepe
ndent R v) (h : n < Module.ran…
· 使用定理 `Module.lt_rank_of_lt_finrank`：lt_rank_of_lt_finrank {n : Nat} (h : n < f
inrank R M) : ↑n < Module.rank R M

--- 原说明 ---
Given a family of `n` linearly independent vectors in a finite-dimensional space
 of
dimension `> n`, one may extend the family by another vector while retaining lin
ear independence.
-/
theorem exists_linearIndependent_cons_of_lt_finrank {n : ℕ} {v : Fin n → M}
    (hv : LinearIndependent R v) (h : n < finrank R M) :
    ∃ (x : M), LinearIndependent R (Fin.cons x v) :=
  exists_linearIndependent_cons_of_lt_rank hv (lt_rank_of_lt_finrank h)

/-- Given a nonzero vector in a finite-dimensional space of dimension `> 1`, one may find another
vector linearly independent of the first one. -/
/-
**exists_linearIndependent_pair_of_one_lt_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_pair_of_one_lt_finrank [IsDomain R] [Module.IsTor
sionFree R M] (h : 1 < finrank R M) {x : M} (hx : x != 0) : exists y, LinearInde
pendent R ![x, y]
参数：h : 1 < finrank R M；hx : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_linearIndependent_pair_of_one_lt_rank`：exists_linearIndependent_p
air_of_one_lt_rank [IsDomain R] [StrongRankCondition R] [IsTorsionFree R M] (h :
 1 < Module.rank R M) {x : M} (hx …
· 使用定理 `Module.one_lt_rank_of_one_lt_finrank`：one_lt_rank_of_one_lt_finrank (h :
 1 < finrank R M) : 1 < Module.rank R M

--- 原说明 ---
Given a nonzero vector in a finite-dimensional space of dimension `> 1`, one may
 find another
vector linearly independent of the first one.
-/
theorem exists_linearIndependent_pair_of_one_lt_finrank [IsDomain R] [Module.IsTorsionFree R M]
    (h : 1 < finrank R M) {x : M} (hx : x ≠ 0) :
    ∃ y, LinearIndependent R ![x, y] :=
  exists_linearIndependent_pair_of_one_lt_rank (one_lt_rank_of_one_lt_finrank h) hx

/-- Rank-nullity theorem using `finrank`. -/
/-
**Submodule.finrank_quotient_add_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.finrank_quotient_add_finrank [Module.Finite R M] (N : Submodule 
R M) : finrank R (M ⧸ N) + finrank R N = finrank R M
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Submodule.finrank_eq_rank`：∀ (R : Type u) (M : Type v) [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [StrongRankConditio
n R] [Module.Fi…
· 使用定理 `HasRankNullity.rank_quotient_add_rank`：∀ {R : Type v} {inst : Ring R} [s
elf : HasRankNullity.{u, v} R] {M : Type u} [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] (N : S…

--- 原说明 ---
Rank-nullity theorem using `finrank`.
-/
lemma Submodule.finrank_quotient_add_finrank [Module.Finite R M] (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N = finrank R M := by
  rw [← Nat.cast_inj (R := Cardinal), Module.finrank_eq_rank, Nat.cast_add, Module.finrank_eq_rank,
    Submodule.finrank_eq_rank]
  exact HasRankNullity.rank_quotient_add_rank _

/-- Rank-nullity theorem using `finrank` and subtraction. -/
/-
**Submodule.finrank_quotient** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.finrank_quotient [Module.Finite R M] {S : Type*} [Ring S] [SMul 
R S] [Module S M] [IsScalarTower R S M] (N : Submodule S M) : finrank R (M ⧸ N) 
= finrank R M - finrank R N
参数：N : Submodule S M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `Nat.eq_sub_of_add_eq`：∀ {a b c : ℕ}, c + b = a → c = a - b

--- 原说明 ---
Rank-nullity theorem using `finrank` and subtraction.
-/
lemma Submodule.finrank_quotient [Module.Finite R M] {S : Type*} [Ring S] [SMul R S] [Module S M]
    [IsScalarTower R S M] (N : Submodule S M) : finrank R (M ⧸ N) = finrank R M - finrank R N := by
  rw [← (N.restrictScalars R).finrank_quotient_add_finrank]
  exact Nat.eq_sub_of_add_eq rfl
/-
**Submodule.disjoint_ker_of_finrank_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.disjoint_ker_of_finrank_le [IsDomain R] [IsTorsionFree R M] {N :
 Type*} [AddCommGroup N] [Module R N] {L : Submodule R M} [Module.Finite R L] (f
 : M ->ₗ[R] N) (h : finrank R L <= finrank R (L.map f)) : Disjoint L (LinearMap.
ker f)
参数：f : M ->ₗ[R] N；h : finrank R L <= finrank R (L.map f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.injective_domRestrict_iff`：∀ {R : Type u_1} {R₂ : Type u_2} {M
 : Type u_5} {M₂ : Type u_7} [inst : Ring R] [inst_1 : Ring R₂]   [inst_2 : AddC
ommGroup M] [inst_3 : Add…
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `Submodule.rank_eq_zero`：Submodule.rank_eq_zero {S : Submodule R M} : Mod
ule.rank R S = 0 ↔ S = ⊥
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_eq_rank`：∀ (R : Type u) (M : Type v) [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [StrongRankConditio
n R] [Module.Fi…
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用引理 `Submodule.finrank_quotient_add_finrank`：Submodule.finrank_quotient_add_f
inrank [Module.Finite R M] (N : Submodule R M) : finrank R (M ⧸ N) + finrank R N
 = finrank R M
· 使用定理 `LinearMap.range_domRestrict`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type 
u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddC
ommMonoid M] [ins…
· 使用定理 `LinearEquiv.finrank_eq`：finrank_eq (f : M ≃ₗ[R] N) : finrank R M = finra
nk R N
-/
lemma Submodule.disjoint_ker_of_finrank_le [IsDomain R] [IsTorsionFree R M] {N : Type*}
    [AddCommGroup N] [Module R N] {L : Submodule R M} [Module.Finite R L] (f : M →ₗ[R] N)
    (h : finrank R L ≤ finrank R (L.map f)) :
    Disjoint L (LinearMap.ker f) := by
  refine LinearMap.injective_domRestrict_iff.mp <| LinearMap.ker_eq_bot.mp <|
    Submodule.rank_eq_zero.mp ?_
  rw [← Submodule.finrank_eq_rank, Nat.cast_eq_zero]
  rw [← LinearMap.range_domRestrict] at h
  have := (LinearMap.ker (f.domRestrict L)).finrank_quotient_add_finrank
  rw [LinearEquiv.finrank_eq (f.domRestrict L).quotKerEquivRange] at this
  lia

end Finrank

section

open Submodule Module

variable [StrongRankCondition R] [Module.Finite R M]

/-
**Submodule.exists_of_finrank_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.exists_of_finrank_lt (N : Submodule R M) (h : finrank R N < finr
ank R M) : exists m : M, forall r : R, r != 0 -> r • m ∉ N
参数：N : Submodule R M；h : finrank R N < finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_finset_linearIndependent_of_le_finrank`：exists_finset_linearIndep
endent_of_le_finrank {n : Nat} (hn : n <= finrank R M) : exists s : Finset M, s.
card = n ∧ LinearIndependent R ((↑)…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.nonempty_iff_ne_empty`：nonempty_iff_ne_empty {s : Finset α} : s.N
onempty ↔ s != ∅
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_eq_zero`：∀ {α : Type u_1} {s : Finset α}, s.card = 0 ↔ s = ∅
· 使用引理 `Submodule.finrank_quotient`：Submodule.finrank_quotient [Module.Finite R 
M] {S : Type*} [Ring S] [SMul R S] [Module S M] [IsScalarTower R S M] (N : Submo
dule S M) : finr…
· 使用定理 `tsub_eq_zero_iff_le`：tsub_eq_zero_iff_le : a - b = 0 ↔ a <= b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Submodule.mkQ_surjective`：mkQ_surjective : Function.Surjective p.mkQ
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.mkQ_apply`：mkQ_apply (x : M) : p.mkQ x = Quotient.mk x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finsupp.single_eq_zero`：single_eq_zero : single a b = 0 ↔ b = 0
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
-/
lemma Submodule.exists_of_finrank_lt (N : Submodule R M) (h : finrank R N < finrank R M) :
    ∃ m : M, ∀ r : R, r ≠ 0 → r • m ∉ N := by
  obtain ⟨s, hs, hs'⟩ :=
    exists_finset_linearIndependent_of_le_finrank (R := R) (M := M ⧸ N) le_rfl
  obtain ⟨v, hv⟩ : s.Nonempty := by rwa [Finset.nonempty_iff_ne_empty, ne_eq, ← Finset.card_eq_zero,
    hs, finrank_quotient, tsub_eq_zero_iff_le, not_le]
  obtain ⟨v, rfl⟩ := N.mkQ_surjective v
  refine ⟨v, fun r hr ↦ mt ?_ hr⟩
  have := linearIndependent_iff.mp hs' (Finsupp.single ⟨_, hv⟩ r)
  rwa [Finsupp.linearCombination_single, Finsupp.single_eq_zero, ← map_smul,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

end

