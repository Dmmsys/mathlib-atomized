/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Ideal

/-!
# Ideal operations for Lie algebras

Given a Lie module `M` over a Lie algebra `L`, there is a natural action of the Lie ideals of `L`
on the Lie submodules of `M`. In the special case that `M = L` with the adjoint action, this
provides a pairing of Lie ideals which is especially important. For example, it can be used to
define solvability / nilpotency of a Lie algebra via the derived / lower-central series.

## Main definitions

  * `LieSubmodule.hasBracket`
  * `LieSubmodule.lieIdeal_oper_eq_linear_span`
  * `LieIdeal.map_bracket_le`
  * `LieIdeal.comap_bracket_le`

## Notation

Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M` and a Lie
ideal `I ⊆ L`, we introduce the notation `⁅I, N⁆` for the Lie submodule of `M` corresponding to
the action defined in this file.

## Tags

lie algebra, ideal operation
-/

public section


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w} {M₂ : Type w₁}
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂]
variable (N N' : LieSubmodule R L M) (N₂ : LieSubmodule R L M₂)
variable (f : M →ₗ⁅R,L⁆ M₂)

section LieIdealOperations

/-
**LieSubmodule.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_comap_le : map f (comap f N₂) <= N₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
-/
theorem map_comap_le : map f (comap f N₂) ≤ N₂ :=
  (N₂ : Set M₂).image_preimage_subset f
/-
**LieSubmodule.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_comap_eq (hf : N₂ <= f.range) : map f (comap f N₂) = N₂
参数：hf : N₂ <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
-/
theorem map_comap_eq (hf : N₂ ≤ f.range) : map f (comap f N₂) = N₂ := by
  rw [SetLike.ext'_iff]
  exact Set.image_preimage_eq_of_subset hf
/-
**LieSubmodule.le_comap_map** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：le_comap_map : N <= comap f (map f N)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem le_comap_map : N ≤ comap f (map f N) :=
  (N : Set M).subset_preimage_image f
/-
**LieSubmodule.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N
参数：hf : f.ker = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieModuleHom.ker_eq_bot`：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
-/
theorem comap_map_eq (hf : f.ker = ⊥) : comap f (map f N) = N := by
  rw [SetLike.ext'_iff]
  exact (N : Set M).preimage_image_eq (f.ker_eq_bot.mp hf)

@[simp]
/-
**LieSubmodule.map_comap_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_comap_incl : map N.incl (comap N.incl N') = N ⊓ N'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `Submodule.map_comap_subtype`：map_comap_subtype : map p.subtype (comap p.
subtype p') = p ⊓ p'
-/
theorem map_comap_incl : map N.incl (comap N.incl N') = N ⊓ N' := by
  rw [← toSubmodule_inj]
  exact (N : Submodule R M).map_comap_subtype N'

variable [LieAlgebra R L] [LieModule R L M₂] (I J : LieIdeal R L)

/-- Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts on the set
of submodules of `M`. -/
/-
**LieSubmodule.hasBracket** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
形式化陈述：hasBracket : Bracket (LieIdeal R L) (LieSubmodule R L M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie module `M` over a Lie algebra `L`, the set of Lie ideals of `L` acts
 on the set
of submodules of `M`.
-/
instance hasBracket : Bracket (LieIdeal R L) (LieSubmodule R L M) :=
  ⟨fun I N => lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }⟩
/-
**LieSubmodule.lieIdeal_oper_eq_span** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lieIdeal_oper_eq_span : ⁅I, N⁆ = lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I
) (n : N) }
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lieIdeal_oper_eq_span :
    ⁅I, N⁆ = lieSpan R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } :=
  rfl

/-- See also `LieSubmodule.lieIdeal_oper_eq_linear_span'` and
`LieSubmodule.lieIdeal_oper_eq_tensor_map_range`. -/
/-
**LieSubmodule.lieIdeal_oper_eq_linear_span** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmod
ule`。
形式化陈述：lieIdeal_oper_eq_linear_span [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M)
 = Submodule.span R { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `instIsLieTower`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1 :
 AddCommGroup M] [inst_2 : LieRingModule L M], IsLieTower L L M
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `LieSubmodule.submodule_span_le_lieSpan`：submodule_span_le_lieSpan : Subm
odule.span R s <= lieSpan R L s

--- 原说明 ---
See also `LieSubmodule.lieIdeal_oper_eq_linear_span'` and
`LieSubmodule.lieIdeal_oper_eq_tensor_map_range`.
-/
theorem lieIdeal_oper_eq_linear_span [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) } := by
  apply le_antisymm
  · let s := { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
    have aux : ∀ (y : L), ∀ m' ∈ Submodule.span R s, ⁅y, m'⁆ ∈ Submodule.span R s := by
      intro y m' hm'
      refine Submodule.span_induction (R := R) (M := M) (s := s)
        (p := fun m' _ ↦ ⁅y, m'⁆ ∈ Submodule.span R s) ?_ ?_ ?_ ?_ hm'
      · rintro m'' ⟨x, n, hm''⟩; rw [← hm'', leibniz_lie]
        refine Submodule.add_mem _ ?_ ?_ <;> apply Submodule.subset_span
        · use ⟨⁅y, ↑x⁆, I.lie_mem x.property⟩, n
        · use x, ⟨⁅y, ↑n⁆, N.lie_mem n.property⟩
      · simp
      · intro m₁ m₂ _ _ hm₁ hm₂; rw [lie_add]; exact Submodule.add_mem _ hm₁ hm₂
      · intro t m'' _ hm''; rw [lie_smul]; exact Submodule.smul_mem _ t hm''
    change _ ≤ ({ Submodule.span R s with lie_mem := fun hm' => aux _ _ hm' } : LieSubmodule R L M)
    rw [lieIdeal_oper_eq_span, lieSpan_le]
    exact Submodule.subset_span
  · rw [lieIdeal_oper_eq_span]; apply submodule_span_le_lieSpan
/-
**LieSubmodule.lieIdeal_oper_eq_linear_span'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmo
dule`。
形式化陈述：lieIdeal_oper_eq_linear_span' [LieModule R L M] : (↑⁅I, N⁆ : Submodule R M
) = Submodule.span R { ⁅x, n⁆ | (x in I) (n in N) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem lieIdeal_oper_eq_linear_span' [LieModule R L M] :
    (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅x, n⁆ | (x ∈ I) (n ∈ N) } := by
  rw [lieIdeal_oper_eq_linear_span]
  congr
  ext m
  constructor
  · rintro ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
    exact ⟨x, hx, n, hn, rfl⟩
  · rintro ⟨x, hx, n, hn, rfl⟩
    exact ⟨⟨x, hx⟩, ⟨n, hn⟩, rfl⟩
/-
**LieSubmodule.lie_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_le_iff : ⁅I, N⁆ <= N' ↔ forall x in I, forall m in N, ⁅x, m⁆ in N'
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
-/
theorem lie_le_iff : ⁅I, N⁆ ≤ N' ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅x, m⁆ ∈ N' := by
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  refine ⟨fun h x hx m hm => h ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h _ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩
  exact h x hx m hm

variable {N I} in
/-
**LieSubmodule.lie_coe_mem_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ in ⁅I, N⁆
参数：x : I；m : N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L), (m : M)⁆ ∈ ⁅I, N⁆ := by
  rw [lieIdeal_oper_eq_span]; apply subset_lieSpan; use x, m

variable {N I} in
/-
**LieSubmodule.lie_mem_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_mem_lie {x : L} {m : M} (hx : x in I) (hm : m in N) : ⁅x, m⁆ in ⁅I, N⁆
参数：hx : x in I；hm : m in N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_coe_mem_lie`：lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L)
, (m : M)⁆ in ⁅I, N⁆
-/
theorem lie_mem_lie {x : L} {m : M} (hx : x ∈ I) (hm : m ∈ N) : ⁅x, m⁆ ∈ ⁅I, N⁆ :=
  lie_coe_mem_lie ⟨x, hx⟩ ⟨m, hm⟩
/-
**LieSubmodule.lie_comm** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_comm : ⁅I, J⁆ = ⁅J, I⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `lie_neg`：lie_neg : ⁅x, -m⁆ = -⁅x, m⁆
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `LieSubmodule.coe_neg`：coe_neg (m : N) : (↑(-m) : M) = -(m : M)
· 使用定理 `LieSubmodule.lie_coe_mem_lie`：lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L)
, (m : M)⁆ in ⁅I, N⁆
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem lie_comm : ⁅I, J⁆ = ⁅J, I⁆ := by
  suffices ∀ I J : LieIdeal R L, ⁅I, J⁆ ≤ ⁅J, I⁆ by exact le_antisymm (this I J) (this J I)
  clear! I J; intro I J
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro x ⟨y, z, h⟩; rw [← h]
  rw [← lie_skew, ← lie_neg, ← LieSubmodule.coe_neg]
  apply lie_coe_mem_lie
/-
**LieSubmodule.lie_le_right** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_le_right : ⁅I, N⁆ <= N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem lie_le_right : ⁅I, N⁆ ≤ N := by
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨x, n, hn⟩; rw [← hn]
  exact N.lie_mem n.property
/-
**LieSubmodule.lie_le_left** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_le_left : ⁅I, J⁆ <= I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lie_comm`：lie_comm : ⁅I, J⁆ = ⁅J, I⁆
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
-/
theorem lie_le_left : ⁅I, J⁆ ≤ I := by rw [lie_comm]; exact lie_le_right I J
/-
**LieSubmodule.lie_le_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_le_inf : ⁅I, J⁆ <= I ⊓ J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LieSubmodule.lie_le_left`：lie_le_left : ⁅I, J⁆ <= I
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
-/
theorem lie_le_inf : ⁅I, J⁆ ≤ I ⊓ J := by rw [le_inf_iff]; exact ⟨lie_le_left I J, lie_le_right J I⟩

@[simp]
/-
**LieSubmodule.lie_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_bot : ⁅I, (⊥ : LieSubmodule R L M)⁆ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `LieSubmodule.lie_le_right`：lie_le_right : ⁅I, N⁆ <= N
-/
theorem lie_bot : ⁅I, (⊥ : LieSubmodule R L M)⁆ = ⊥ := by rw [eq_bot_iff]; apply lie_le_right

@[simp]
/-
**LieSubmodule.bot_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：bot_lie : ⁅(⊥ : LieIdeal R L), N⁆ = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
theorem bot_lie : ⁅(⊥ : LieIdeal R L), N⁆ = ⊥ := by
  suffices ⁅(⊥ : LieIdeal R L), N⁆ ≤ ⊥ by exact le_bot_iff.mp this
  rw [lieIdeal_oper_eq_span, lieSpan_le]; rintro m ⟨⟨x, hx⟩, n, hn⟩; rw [← hn]
  change x ∈ (⊥ : LieIdeal R L) at hx; rw [mem_bot] at hx; simp [hx]
/-
**LieSubmodule.lie_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ forall x in I, forall m in N, ⁅(x : L), m⁆ =
 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_eq_bot_iff`：lieSpan_eq_bot_iff : lieSpan R L s = ⊥ 
↔ forall m in s, m = (0 : M)
-/
theorem lie_eq_bot_iff : ⁅I, N⁆ = ⊥ ↔ ∀ x ∈ I, ∀ m ∈ N, ⁅(x : L), m⁆ = 0 := by
  rw [lieIdeal_oper_eq_span, LieSubmodule.lieSpan_eq_bot_iff]
  refine ⟨fun h x hx m hm => h ⁅x, m⁆ ⟨⟨x, hx⟩, ⟨m, hm⟩, rfl⟩, ?_⟩
  rintro h - ⟨⟨x, hx⟩, ⟨⟨n, hn⟩, rfl⟩⟩
  exact h x hx n hn

variable {I J N N'} in
@[gcongr]
/-
**LieSubmodule.mono_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <= ⁅J, N'⁆
参数：h₁ : I <= J；h₂ : N <= N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.mem_lieSpan`：mem_lieSpan {x : M} : x in lieSpan R L s ↔ for
all N : LieSubmodule R L M, s subseteq N -> x in N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem mono_lie (h₁ : I ≤ J) (h₂ : N ≤ N') : ⁅I, N⁆ ≤ ⁅J, N'⁆ := by
  intro m h
  rw [lieIdeal_oper_eq_span, mem_lieSpan] at h; rw [lieIdeal_oper_eq_span, mem_lieSpan]
  intro N hN; apply h; rintro m' ⟨⟨x, hx⟩, ⟨n, hn⟩, hm⟩; rw [← hm]; apply hN
  use ⟨x, h₁ hx⟩, ⟨n, h₂ hn⟩

variable {I J} in
/-
**LieSubmodule.mono_lie_left** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mono_lie_left (h : I <= J) : ⁅I, N⁆ <= ⁅J, N⁆
参数：h : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mono_lie_left (h : I ≤ J) : ⁅I, N⁆ ≤ ⁅J, N⁆ :=
  mono_lie h (le_refl N)

variable {N N'} in
/-
**LieSubmodule.mono_lie_right** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I, N'⁆
参数：h : N <= N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem mono_lie_right (h : N ≤ N') : ⁅I, N⁆ ≤ ⁅I, N'⁆ :=
  mono_lie (le_refl I) h

@[simp]
/-
**LieSubmodule.lie_sup** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `LieSubmodule.mem_sup`：mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exi
sts z in N', y + z = x
· 使用定理 `LieSubmodule.lie_coe_mem_lie`：lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L)
, (m : M)⁆ in ⁅I, N⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem lie_sup : ⁅I, N ⊔ N'⁆ = ⁅I, N⁆ ⊔ ⁅I, N'⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅I, N'⁆ ≤ ⁅I, N ⊔ N'⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_right <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I, N ⊔ N'⁆ ≤ ⁅I, N⁆ ⊔ ⁅I, N'⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span, lieSpan_le]
  rintro m ⟨x, ⟨n, hn⟩, h⟩
  simp only [SetLike.mem_coe]
  rw [LieSubmodule.mem_sup] at hn ⊢
  rcases hn with ⟨n₁, hn₁, n₂, hn₂, hn'⟩
  use ⁅(x : L), (⟨n₁, hn₁⟩ : N)⁆; constructor; · apply lie_coe_mem_lie
  use ⁅(x : L), (⟨n₂, hn₂⟩ : N')⁆; constructor; · apply lie_coe_mem_lie
  simp [← h, ← hn']

@[simp]
/-
**LieSubmodule.sup_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_le_iff`：sup_le_iff : a ⊔ b <= c ↔ a <= c ∧ b <= c
· 使用定理 `LieSubmodule.mono_lie_left`：mono_lie_left (h : I <= J) : ⁅I, N⁆ <= ⁅J, N
⁆
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `LieSubmodule.mem_sup`：mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exi
sts z in N', y + z = x
· 使用定理 `LieSubmodule.lie_coe_mem_lie`：lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L)
, (m : M)⁆ in ⁅I, N⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem sup_lie : ⁅I ⊔ J, N⁆ = ⁅I, N⁆ ⊔ ⁅J, N⁆ := by
  have h : ⁅I, N⁆ ⊔ ⁅J, N⁆ ≤ ⁅I ⊔ J, N⁆ := by
    rw [sup_le_iff]; constructor <;>
    apply mono_lie_left <;> [exact le_sup_left; exact le_sup_right]
  suffices ⁅I ⊔ J, N⁆ ≤ ⁅I, N⁆ ⊔ ⁅J, N⁆ by exact le_antisymm this h
  rw [lieIdeal_oper_eq_span, lieSpan_le]
  rintro m ⟨⟨x, hx⟩, n, h⟩
  simp only [SetLike.mem_coe]
  rw [LieSubmodule.mem_sup] at hx ⊢
  rcases hx with ⟨x₁, hx₁, x₂, hx₂, hx'⟩
  use ⁅((⟨x₁, hx₁⟩ : I) : L), (n : N)⁆; constructor; · apply lie_coe_mem_lie
  use ⁅((⟨x₂, hx₂⟩ : J) : L), (n : N)⁆; constructor; · apply lie_coe_mem_lie
  simp [← h, ← hx']
/-
**LieSubmodule.lie_inf** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：lie_inf : ⁅I, N ⊓ N'⁆ <= ⁅I, N⁆ ⊓ ⁅I, N'⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LieSubmodule.mono_lie_right`：mono_lie_right (h : N <= N') : ⁅I, N⁆ <= ⁅I
, N'⁆
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem lie_inf : ⁅I, N ⊓ N'⁆ ≤ ⁅I, N⁆ ⊓ ⁅I, N'⁆ := by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_right <;> [exact inf_le_left; exact inf_le_right]
/-
**LieSubmodule.inf_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：inf_lie : ⁅I ⊓ J, N⁆ <= ⁅I, N⁆ ⊓ ⁅J, N⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LieSubmodule.mono_lie_left`：mono_lie_left (h : I <= J) : ⁅I, N⁆ <= ⁅J, N
⁆
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
theorem inf_lie : ⁅I ⊓ J, N⁆ ≤ ⁅I, N⁆ ⊓ ⁅J, N⁆ := by
  rw [le_inf_iff]; constructor <;>
  apply mono_lie_left <;> [exact inf_le_left; exact inf_le_right]
/-
**LieSubmodule.map_bracket_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：map_bracket_eq [LieModule R L M] : map f ⁅I, N⁆ = ⁅I, map f N⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.toSubmodule_map`：toSubmodule_map : (N.map f : Submodule R M
') = (N : Submodule R M).map (f : M ->ₗ[R] M')
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem map_bracket_eq [LieModule R L M] : map f ⁅I, N⁆ = ⁅I, map f N⁆ := by
  rw [← toSubmodule_inj, toSubmodule_map, lieIdeal_oper_eq_linear_span,
    lieIdeal_oper_eq_linear_span, Submodule.map_span]
  congr
  ext m
  simp
/-
**LieSubmodule.comap_bracket_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：comap_bracket_eq [LieModule R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ <= f.range)
 : comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆
参数：hf₁ : f.ker = ⊥；hf₂ : N₂ <= f.range。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.map_comap_eq`：map_comap_eq (hf : N₂ <= f.range) : map f (co
map f N₂) = N₂
· 使用定理 `LieSubmodule.map_bracket_eq`：map_bracket_eq [LieModule R L M] : map f ⁅I
, N⁆ = ⁅I, map f N⁆
· 使用定理 `LieSubmodule.comap_map_eq`：comap_map_eq (hf : f.ker = ⊥) : comap f (map 
f N) = N
-/
theorem comap_bracket_eq [LieModule R L M] (hf₁ : f.ker = ⊥) (hf₂ : N₂ ≤ f.range) :
    comap f ⁅I, N₂⁆ = ⁅I, comap f N₂⁆ := by
  conv_lhs => rw [← map_comap_eq N₂ f hf₂]
  rw [← map_bracket_eq, comap_map_eq _ f hf₁]

end LieIdealOperations

end LieSubmodule

namespace LieIdeal

open LieAlgebra

variable {R : Type u} {L : Type v} {L' : Type w₂}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- Note that the inequality can be strict; e.g., the inclusion of an Abelian subalgebra of a
simple algebra. -/
/-
**LieIdeal.map_bracket_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁, I₂⁆ <= ⁅map f I₁, map f
 I₂⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_span`：lieIdeal_oper_eq_span : ⁅I, N⁆ = lie
Span R L { ⁅(x : L), (n : M)⁆ | (x : I) (n : N) }
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.mem_map`：mem_map {x : L} (hx : x in I) : f x in map f I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `LieSubmodule.lie_coe_mem_lie`：lie_coe_mem_lie (x : I) (m : N) : ⁅(x : L)
, (m : M)⁆ in ⁅I, N⁆

--- 原说明 ---
Note that the inequality can be strict; e.g., the inclusion of an Abelian subalg
ebra of a
simple algebra.
-/
theorem map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅I₁, I₂⁆ ≤ ⁅map f I₁, map f I₂⁆ := by
  rw [map_le_iff_le_comap, LieSubmodule.lieIdeal_oper_eq_span, LieSubmodule.lieSpan_le]
  intro x hx
  obtain ⟨⟨y₁, hy₁⟩, ⟨y₂, hy₂⟩, hx⟩ := hx
  rw [← hx]
  let fy₁ : ↥(map f I₁) := ⟨f y₁, mem_map hy₁⟩
  let fy₂ : ↥(map f I₂) := ⟨f y₂, mem_map hy₂⟩
  change _ ∈ comap f ⁅map f I₁, map f I₂⁆
  simp only [mem_comap, LieHom.map_lie]
  exact LieSubmodule.lie_coe_mem_lie fy₁ fy₂
/-
**LieIdeal.map_bracket_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) : map f 
⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆
参数：h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (N
 : Submodule R M) <= N' ↔ N <= N'
· 使用定理 `LieIdeal.coe_map_of_surjective`：coe_map_of_surjective (h : Function.Surj
ective f) : LieSubmodule.toSubmodule (I.map f) = (LieSubmodule.toSubmodule I).ma
p (f : L ->ₗ[R] L')
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `LinearMap.map_span`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ 
: Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M…
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `LieIdeal.mem_map_of_surjective`：mem_map_of_surjective {y : L'} (h₁ : Fun
ction.Surjective f) (h₂ : y in I.map f) : exists x : I, f x = y
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieIdeal.map_bracket_le`：map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅
I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆
-/
theorem map_bracket_eq {I₁ I₂ : LieIdeal R L} (h : Function.Surjective f) :
    map f ⁅I₁, I₂⁆ = ⁅map f I₁, map f I₂⁆ := by
  suffices ⁅map f I₁, map f I₂⁆ ≤ map f ⁅I₁, I₂⁆ by exact le_antisymm (map_bracket_le f) this
  rw [← LieSubmodule.toSubmodule_le_toSubmodule, coe_map_of_surjective h,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  apply Submodule.span_mono
  rintro x ⟨⟨z₁, h₁⟩, ⟨z₂, h₂⟩, rfl⟩
  obtain ⟨y₁, rfl⟩ := mem_map_of_surjective h h₁
  obtain ⟨y₂, rfl⟩ := mem_map_of_surjective h h₂
  exact ⟨⁅(y₁ : L), (y₂ : L)⁆, ⟨y₁, y₂, rfl⟩, by apply f.map_lie⟩
/-
**LieIdeal.comap_bracket_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁, comap f J₂⁆ <= com
ap f ⁅J₁, J₂⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieIdeal.map_bracket_le`：map_bracket_le {I₁ I₂ : LieIdeal R L} : map f ⁅
I₁, I₂⁆ <= ⁅map f I₁, map f I₂⁆
· 使用定理 `LieSubmodule.mono_lie`：mono_lie (h₁ : I <= J) (h₂ : N <= N') : ⁅I, N⁆ <=
 ⁅J, N'⁆
· 使用定理 `LieIdeal.map_comap_le`：map_comap_le : map f (comap f J) <= J
-/
theorem comap_bracket_le {J₁ J₂ : LieIdeal R L'} : ⁅comap f J₁, comap f J₂⁆ ≤ comap f ⁅J₁, J₂⁆ := by
  rw [← map_le_iff_le_comap]
  exact le_trans (map_bracket_le f) (LieSubmodule.mono_lie map_comap_le map_comap_le)

variable {f}
/-
**LieIdeal.map_comap_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.incl (comap I₁.incl I₂) = I
₁ ⊓ I₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.incl_idealRange`：incl_idealRange : I.incl.idealRange = I
· 使用定理 `LieIdeal.map_comap_eq`：map_comap_eq (h : f.IsIdealMorphism) : map f (com
ap f J) = f.idealRange ⊓ J
· 使用定理 `LieIdeal.incl_isIdealMorphism`：incl_isIdealMorphism : I.incl.IsIdealMorp
hism
-/
theorem map_comap_incl {I₁ I₂ : LieIdeal R L} : map I₁.incl (comap I₁.incl I₂) = I₁ ⊓ I₂ := by
  conv_rhs => rw [← I₁.incl_idealRange]
  rw [← map_comap_eq]
  exact I₁.incl_isIdealMorphism
/-
**LieIdeal.comap_bracket_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) : comap f
 ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker
参数：h : f.IsIdealMorphism。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieIdeal.comap_toSubmodule`：comap_toSubmodule : (LieSubmodule.toSubmodul
e (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L ->ₗ[R] L')
· 使用定理 `LieSubmodule.sup_toSubmodule`：sup_toSubmodule : (↑(N ⊔ N') : Submodule R
 M) = (N : Submodule R M) ⊔ (N' : Submodule R M)
· 使用定理 `LieHom.ker_toSubmodule`：ker_toSubmodule : LieSubmodule.toSubmodule (ker 
f) = LinearMap.ker (f : L ->ₗ[R] L')
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
· 使用定理 `LieSubmodule.lieIdeal_oper_eq_linear_span`：lieIdeal_oper_eq_linear_span 
[LieModule R L M] : (↑⁅I, N⁆ : Submodule R M) = Submodule.span R { ⁅(x : L), (n 
: M)⁆ | (x : I) (n : N) }
· 使用定理 `LinearMap.map_span`：∀ {R : Type u_1} {R₂ : Type u_2} {M : Type u_4} {M₂ 
: Type u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R M…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
-/
theorem comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f J₁, comap f J₂⁆ ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj, comap_toSubmodule,
    LieSubmodule.sup_toSubmodule, f.ker_toSubmodule, ← Submodule.comap_map_eq,
    LieSubmodule.lieIdeal_oper_eq_linear_span, LieSubmodule.lieIdeal_oper_eq_linear_span,
    LinearMap.map_span]
  congr
  ext
  simp_all only [Subtype.exists, LieSubmodule.mem_inf, LieHom.mem_idealRange_iff, exists_prop,
    Set.mem_ofPred_eq, LieHom.coe_toLinearMap, mem_comap,
    exists_exists_and_exists_and_eq_and, LieHom.map_lie]
  grind
/-
**LieIdeal.map_comap_bracket_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) : map
 f ⁅comap f J₁, comap f J₂⁆ = ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆
参数：h : f.IsIdealMorphism。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.map_sup_ker_eq_map`：map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.
ker) = LieIdeal.map f I
· 使用定理 `LieIdeal.comap_bracket_eq`：comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h :
 f.IsIdealMorphism) : comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f 
J₁, comap f J₂⁆…
· 使用定理 `LieIdeal.map_comap_eq`：map_comap_eq (h : f.IsIdealMorphism) : map f (com
ap f J) = f.idealRange ⊓ J
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `LieSubmodule.lie_le_left`：lie_le_left : ⁅I, J⁆ <= I
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
-/
theorem map_comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h : f.IsIdealMorphism) :
    map f ⁅comap f J₁, comap f J₂⁆ = ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ := by
  rw [← map_sup_ker_eq_map, ← comap_bracket_eq h, map_comap_eq h, inf_eq_right]
  exact le_trans (LieSubmodule.lie_le_left _ _) inf_le_left
/-
**LieIdeal.comap_bracket_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_bracket_incl {I₁ I₂ : LieIdeal R L} : ⁅comap I.incl I₁, comap I.incl
 I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.incl_idealRange`：incl_idealRange : I.incl.idealRange = I
· 使用定理 `LieIdeal.comap_bracket_eq`：comap_bracket_eq {J₁ J₂ : LieIdeal R L'} (h :
 f.IsIdealMorphism) : comap f ⁅f.idealRange ⊓ J₁, f.idealRange ⊓ J₂⁆ = ⁅comap f 
J₁, comap f J₂⁆…
· 使用定理 `LieIdeal.incl_isIdealMorphism`：incl_isIdealMorphism : I.incl.IsIdealMorp
hism
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `LieIdeal.ker_incl`：ker_incl : I.incl.ker = ⊥
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comap_bracket_incl {I₁ I₂ : LieIdeal R L} :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆ := by
  conv_rhs =>
    congr
    next => skip
    rw [← I.incl_idealRange]
  rw [comap_bracket_eq]
  · simp
  · exact I.incl_isIdealMorphism

/-- This is a very useful result; it allows us to use the fact that inclusion distributes over the
Lie bracket operation on ideals, subject to the conditions shown. -/
/-
**LieIdeal.comap_bracket_incl_of_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ <= I) (h₂ : I₂ <=
 I) : ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆
参数：h₁ : I₁ <= I；h₂ : I₂ <= I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.comap_bracket_incl`：comap_bracket_incl {I₁ I₂ : LieIdeal R L} :
 ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I ⊓ I₁, I ⊓ I₂⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a

--- 原说明 ---
This is a very useful result; it allows us to use the fact that inclusion distri
butes over the
Lie bracket operation on ideals, subject to the conditions shown.
-/
theorem comap_bracket_incl_of_le {I₁ I₂ : LieIdeal R L} (h₁ : I₁ ≤ I) (h₂ : I₂ ≤ I) :
    ⁅comap I.incl I₁, comap I.incl I₂⁆ = comap I.incl ⁅I₁, I₂⁆ := by
    rw [comap_bracket_incl]; rw [← inf_eq_right] at h₁ h₂; rw [h₁, h₂]

end LieIdeal

